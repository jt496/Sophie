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
from .agents.formalizer import Formalizer, _conjecture_slug
from .agents.base_agent import BaseAgent
from .knowledge_base import KnowledgeBase


class Conductor:
    def __init__(self, kb: KnowledgeBase):
        self.kb = kb
        self._agents: Dict[str, BaseAgent] = {
            "Experimenter": Experimenter(kb),
            "Formalizer":   Formalizer(kb),
            "Prover":       Prover(kb),
            "Disprover":    Disprover(kb),
            "Checker":      Checker(kb),
            "Searcher":     Searcher(kb),
            "Researcher":   Researcher(kb),
        }

    # Agent letter codes — unique first letters, alphabetical by letter
    AGENT_LETTERS: Dict[str, str] = {
        "C": "Checker",
        "D": "Disprover",
        "E": "Experimenter",
        "F": "Formalizer",
        "P": "Prover",
        "R": "Researcher",
        "S": "Searcher",
    }

    # ── Public API ───────────────────────────────────────────────────────────

    def get_round_tasks(self, agents: str = "") -> Dict[str, Any]:
        """
        Return the agent list for the current (or next) round.

        If a round is already in progress (e.g. after a token-exhaustion
        restart), returns only the agents that have not yet reported.
        Otherwise advances to the next round, saves the planned agent list to
        the KB, and returns all agents for that round.

        agents: optional string of letter codes (C/D/E/P/R/S) that overrides
                the automatic scheduler, e.g. "CPR" runs Checker, Prover,
                Researcher in that order.  Ignored when resuming a round.

        Returns a compact dict — no system prompts or user messages.
        Call get_agent_task(agent_name) for each agent in agents_pending.
        """
        crs = self.kb.current_round_state
        if crs is not None:
            pending = [a for a in crs["planned"] if a not in crs["completed"]]
            return {
                "session_id": self.kb.session_id,
                "round": crs["round"],
                "should_stop": False,
                "stop_reason": None,
                "agents_pending": pending,
                "agents_completed": crs["completed"],
                "resumed": True,
            }

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

        if agents:
            unknown = [c for c in agents.upper() if c not in self.AGENT_LETTERS]
            if unknown:
                return {"error": f"Unknown agent letter(s): {unknown}. Valid: {sorted(self.AGENT_LETTERS)}"}
            agents_to_run = [self.AGENT_LETTERS[c] for c in agents.upper()]
        else:
            agents_to_run = self._decide_agents(round_)

        self.kb.start_round(round_, agents_to_run)

        return {
            "session_id": self.kb.session_id,
            "round": round_,
            "should_stop": False,
            "stop_reason": None,
            "agents_pending": agents_to_run,
            "agents_completed": [],
            "resumed": False,
        }

    def get_agent_task(self, agent_name: str, round_: int, source_id: str = "") -> Dict[str, Any]:
        """Return the system_prompt + user_message for a single agent."""
        agent = self._agents.get(agent_name)
        if agent is None:
            return {"error": f"Unknown agent '{agent_name}'."}
        if agent_name == "Formalizer" and source_id:
            return agent.get_task(round_, source_id=source_id)
        return agent.get_task(round_)

    def submit_agent_result(
        self, agent_name: str, round_: int, response_json: Any
    ) -> Dict[str, Any]:
        """
        Process one agent's response immediately and persist it to the KB.

        If this is the last pending agent for the round, the round is
        automatically finalized (stagnation update, round counter increment,
        current_round_state cleared).

        Returns a dict with: agent, summary, round_complete, status, resolved,
        and (when round_complete) formalization_suggestions.
        """
        crs = self.kb.current_round_state
        if crs is None:
            return {"error": "No round in progress. Call get_round_tasks first."}
        if round_ != crs["round"]:
            return {"error": f"Round mismatch: expected {crs['round']}, got {round_}."}

        agent = self._agents.get(agent_name)
        if agent is None:
            return {"error": f"Unknown agent '{agent_name}'."}

        parsed = BaseAgent._extract_json(response_json) if isinstance(response_json, str) else response_json

        try:
            summary = agent.process_response(round_, parsed)
        except Exception as exc:
            summary = f"Error in {agent_name}: {exc}"

        self.kb.log(round_, agent_name, summary)
        self.kb.record_agent_completion(agent_name, summary)

        # Reload crs after save to get updated completed list
        crs = self.kb.current_round_state
        pending = [a for a in crs["planned"] if a not in crs["completed"]]
        round_complete = len(pending) == 0

        result: Dict[str, Any] = {
            "agent": agent_name,
            "summary": summary,
            "round_complete": round_complete,
            "agents_remaining": pending,
            "status": self.kb.status,
            "resolved": self.kb.status in ("proved", "disproved"),
        }

        if round_complete:
            self._update_stagnation()
            self.kb.log_round_summary(round_, crs["summaries"])
            self.kb.finish_round()
            self.kb.increment_round()
            result["formalization_suggestions"] = self._formalization_suggestions()

        return result

    def process_results(self, round_: int, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Apply each agent's JSON response to the knowledge base in one batch.

        Kept for backward compatibility. Prefer submit_agent_result for
        incremental, crash-safe submission.

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
        self.kb.finish_round()
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

        # Checker: always if there is unverified work (proofs, disproofs, or implications)
        if self.kb.unchecked_proofs() or self.kb.unchecked_disproofs() or self.kb.unchecked_implications():
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
                "implications":      [(i["id"], i.get("status", "unchecked")) for i in snap.get("implications", [])],
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
            "agents_pending": [],
            "agents_completed": [],
        }
