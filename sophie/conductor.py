"""
Conductor – pure scheduling and result-processing logic.

No LLM calls are made here.  Claude Code acts as the LLM for every agent role.
The Conductor decides WHICH agents to run each round (rule-based) and processes
their responses back into the knowledge base.
"""

from __future__ import annotations

import json
from typing import Any, Dict, List

from . import config
from .agents import Checker, Disprover, Experimenter, Prover, Researcher, Searcher
from .agents.formalizer import _conjecture_slug
from .agents.base_agent import BaseAgent
from .knowledge_base import KnowledgeBase


class Conductor:
    def __init__(self, kb: KnowledgeBase):
        self.kb = kb
        self._agents: Dict[str, BaseAgent] = {
            "Experimenter": Experimenter(kb),
            "Prover":       Prover(kb),
            "Disprover":    Disprover(kb),
            "Checker":      Checker(kb),
            "Searcher":     Searcher(kb),
            "Researcher":   Researcher(kb),
        }

    # ── Public API ───────────────────────────────────────────────────────────

    def get_round_tasks(self) -> Dict[str, Any]:
        """
        Advance to the next round and return the tasks Claude Code should execute.

        Returns a dict with:
          session_id, round, should_stop, stop_reason, tasks
        where each task has: agent, system_prompt, user_message.
        """
        if self.kb.status in ("proved", "disproved"):
            return self._stop(f"Already {self.kb.status}.")

        if self.kb.no_progress_rounds >= config.CONVERGENCE_PATIENCE:
            self.kb.set_status("unknown")
            return self._stop(
                f"No new findings for {config.CONVERGENCE_PATIENCE} consecutive rounds."
            )

        if self.kb.rounds_completed >= config.MAX_ROUNDS:
            self.kb.set_status("unknown")
            return self._stop(f"Reached maximum of {config.MAX_ROUNDS} rounds.")

        round_ = self.kb.rounds_completed + 1
        agents_to_run = self._decide_agents(round_)

        tasks = [self._agents[name].get_task(round_) for name in agents_to_run]

        return {
            "session_id": self.kb.session_id,
            "round": round_,
            "should_stop": False,
            "stop_reason": None,
            "tasks": tasks,
        }

    def process_results(self, round_: int, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Apply each agent's JSON response to the knowledge base.

        Each item in results: {"agent": str, "response_json": str | dict}
        Returns: {"status": str, "summaries": list[str], "resolved": bool}
        """
        summaries = []
        for item in results:
            agent_name = item.get("agent", "")
            agent = self._agents.get(agent_name)
            if agent is None:
                summaries.append(f"Unknown agent '{agent_name}' — skipped.")
                continue

            raw = item.get("response_json", "{}")
            parsed = BaseAgent._extract_json(raw) if isinstance(raw, str) else raw

            try:
                summary = agent.process_response(round_, parsed)
            except Exception as exc:
                summary = f"Error in {agent_name}: {exc}"

            self.kb.log(round_, agent_name, summary)
            summaries.append(f"{agent_name}: {summary}")

        self._update_stagnation()
        self.kb.log_round_summary(round_, summaries)
        self.kb.increment_round()

        return {
            "status": self.kb.status,
            "summaries": summaries,
            "resolved": self.kb.status in ("proved", "disproved"),
            "formalization_suggestions": self._formalization_suggestions(),
        }

    # ── Scheduling ───────────────────────────────────────────────────────────

    def _decide_agents(self, round_: int) -> List[str]:
        if round_ == 1:
            return ["Experimenter", "Prover", "Disprover", "Checker"]

        agents: List[str] = []
        no_proof = not self.kb.valid_proof_exists()
        no_disproof = not self.kb.valid_disproof_exists()
        stagnating = self.kb.no_progress_rounds > 0

        # Checker: always if there is unverified work
        if self.kb.unchecked_proofs() or self.kb.unchecked_disproofs():
            agents.append("Checker")

        if no_proof:
            agents.append("Prover")

        if no_disproof:
            agents.append("Disprover")

        # Experimenter: exploration phase (rounds 2–4), then every 4th round,
        # or when stagnating (fresh examples can unblock a stuck session)
        if (no_proof or no_disproof) and (round_ <= 4 or round_ % 4 == 0 or stagnating):
            agents.append("Experimenter")

        # Searcher: every even round — cheap computational search pairs well with Prover
        if (no_proof or no_disproof) and round_ % 2 == 0:
            agents.append("Searcher")

        # Researcher: round 3 for initial literature survey, then every 6th round,
        # or when the session has made no progress for 2+ consecutive rounds
        if (no_proof or no_disproof) and (
            round_ == 3
            or (round_ > 3 and (round_ - 3) % 6 == 0)
            or self.kb.no_progress_rounds >= 2
        ):
            agents.append("Researcher")

        if not agents:
            agents = ["Prover", "Disprover", "Checker", "Researcher"]

        return agents

    # ── Formalization suggestions ─────────────────────────────────────────────

    def _formalization_suggestions(self) -> List[Dict[str, Any]]:
        """Return proof/subproblem IDs worth formalizing, with reasons."""
        suggestions = []
        snap = self.kb.snapshot()
        already = {fa["source_id"] for fa in snap.get("formalization_attempts", [])}
        slug = _conjecture_slug(snap.get("conjecture", ""))
        lean_file = f"SophieFormalization/{slug}/Theorems.lean"

        for pa in snap["proof_attempts"]:
            if pa["id"] in already:
                continue
            if pa["status"] == "valid":
                suggestions.append({
                    "id": pa["id"],
                    "type": "proof_attempt",
                    "reason": "Checker-validated proof — strong candidate for formalization.",
                    "lean_file": lean_file,
                    "preview": pa["sketch"][:120],
                })
            elif pa["status"] == "unchecked" and len(pa["sketch"]) > 300:
                suggestions.append({
                    "id": pa["id"],
                    "type": "proof_attempt",
                    "reason": "Substantial unchecked proof sketch — formalization could reveal gaps.",
                    "lean_file": lean_file,
                    "preview": pa["sketch"][:120],
                })

        return suggestions

    # ── Stagnation ───────────────────────────────────────────────────────────

    def _update_stagnation(self) -> None:
        snap = self.kb.snapshot()
        current_hash = self._compute_hash(snap)
        prev = self.kb.prev_snapshot_hash
        if prev is not None and current_hash == prev:
            self.kb.increment_no_progress()
        else:
            self.kb.reset_no_progress()
        self.kb.set_prev_snapshot_hash(current_hash)

    @staticmethod
    def _compute_hash(snap: Dict[str, Any]) -> int:
        key = json.dumps(
            {
                "examples":          len(snap["examples"]),
                "subproblems":       len(snap["subproblems"]),
                "proof_attempts":    [(p["id"], p["status"]) for p in snap["proof_attempts"]],
                "disproof_attempts": [(d["id"], d["status"]) for d in snap["disproof_attempts"]],
            },
            sort_keys=True,
        )
        return hash(key)

    # ── Helpers ──────────────────────────────────────────────────────────────

    def _stop(self, reason: str) -> Dict[str, Any]:
        return {
            "session_id": self.kb.session_id,
            "round": self.kb.rounds_completed,
            "should_stop": True,
            "stop_reason": reason,
            "tasks": [],
        }
