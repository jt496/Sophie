"""
Shared, persistent knowledge base for the conjecture exploration framework.

All agents read from and write to this structure. It is saved as a JSON file
after every update so that sessions survive restarts.

Schema
------
{
  "conjecture": str,
  "session_id": str,
  "status": "open" | "proved" | "disproved" | "unknown",
  "rounds_completed": int,

  "subproblems": [
    {
      "id": str,
      "description": str,
      "source_agent": str,
      "status": "open" | "resolved",
      "resolution": str | null
    }
  ],

  "examples": [
    {
      "id": str,
      "description": str,
      "supports_conjecture": bool | null,   # null = neutral/inconclusive
      "detail": str
    }
  ],

  "proof_attempts": [
    {
      "id": str,
      "round": int,
      "sketch": str,
      "status": "unchecked" | "valid" | "flawed",
      "checker_feedback": str | null
    }
  ],

  "disproof_attempts": [
    {
      "id": str,
      "round": int,
      "candidate_counterexample": str,
      "status": "unchecked" | "valid" | "flawed",
      "checker_feedback": str | null
    }
  ],

  "log": [
    {
      "round": int,
      "agent": str,
      "summary": str
    }
  ]
}
"""

from __future__ import annotations

import json
import os
import uuid
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

from . import config


class KnowledgeBase:
    """Thread-safe-ish (single-process) shared knowledge base."""

    def __init__(self, session_id: Optional[str] = None):
        Path(config.KB_DIR).mkdir(parents=True, exist_ok=True)

        if session_id is None:
            session_id = datetime.now().strftime("%Y%m%d_%H%M%S")

        self.session_id = session_id
        self._path = os.path.join(config.KB_DIR, f"{session_id}.json")

        if os.path.exists(self._path):
            with open(self._path, "r") as f:
                self._data: Dict[str, Any] = json.load(f)
            # Migrate older sessions
            if "round_summaries" not in self._data:
                self._data["round_summaries"] = []
                self._save()
            if "facts" not in self._data:
                self._data["facts"] = []
                self._save()
            if "current_round_state" not in self._data:
                self._data["current_round_state"] = None
                self._save()
            # Migrate: backfill added_round on examples that predate the field
            if any("added_round" not in ex for ex in self._data.get("examples", [])):
                for ex in self._data["examples"]:
                    ex.setdefault("added_round", 0)
                self._save()
        else:
            self._data = self._empty(session_id)
            self._save()

    # ── Initialisation ───────────────────────────────────────────────────────

    @staticmethod
    def _empty(session_id: str) -> Dict[str, Any]:
        return {
            "conjecture": "",
            "session_id": session_id,
            "status": "open",
            "rounds_completed": 0,
            "no_progress_rounds": 0,
            "prev_snapshot_hash": None,
            "facts": [],
            "subproblems": [],
            "examples": [],
            "proof_attempts": [],
            "disproof_attempts": [],
            "formalization_attempts": [],
            "log": [],
            "round_summaries": [],
            "current_round_state": None,
        }

    def set_conjecture(self, text: str) -> None:
        self._data["conjecture"] = text
        self._save()

    # ── Facts ────────────────────────────────────────────────────────────────

    def add_fact(self, text: str) -> str:
        prefix = text[:120].lower()
        for f in self._data["facts"]:
            if f["text"][:120].lower() == prefix:
                return f["id"]
        fid = f"FT-{uuid.uuid4().hex[:6].upper()}"
        self._data["facts"].append({
            "id": fid,
            "text": text,
            "added_round": self._data["rounds_completed"],
        })
        self._save()
        return fid

    def remove_fact(self, fact_id: str) -> bool:
        before = len(self._data["facts"])
        self._data["facts"] = [f for f in self._data["facts"] if f["id"] != fact_id]
        changed = len(self._data["facts"]) < before
        if changed:
            self._save()
        return changed

    # ── Generic accessors ────────────────────────────────────────────────────

    def snapshot(self) -> Dict[str, Any]:
        """Return a deep copy of the current state (safe for agent prompts)."""
        return json.loads(json.dumps(self._data))

    def _save(self) -> None:
        with open(self._path, "w") as f:
            json.dump(self._data, f, indent=2)

    # ── Logging ──────────────────────────────────────────────────────────────

    def log(self, round_: int, agent: str, summary: str) -> None:
        self._data["log"].append({"round": round_, "agent": agent, "summary": summary})

    def log_round_summary(self, round_: int, summaries: List[str], narrative: str = "") -> None:
        """Persist the full per-agent summary rollup for a completed round."""
        entry: dict = {"round": round_, "summaries": summaries}
        if narrative:
            entry["narrative"] = narrative
        self._data["round_summaries"].append(entry)
        self._save()

    def increment_round(self) -> int:
        self._data["rounds_completed"] += 1
        self._save()
        return self._data["rounds_completed"]

    # ── Subproblems ──────────────────────────────────────────────────────────

    def add_subproblem(self, description: str, source_agent: str) -> str:
        # Deduplicate by description prefix (first 80 chars)
        prefix = description[:80].lower()
        for sp in self._data["subproblems"]:
            if sp["description"][:80].lower() == prefix:
                return sp["id"]

        sid = f"SP-{uuid.uuid4().hex[:6].upper()}"
        self._data["subproblems"].append(
            {
                "id": sid,
                "description": description,
                "source_agent": source_agent,
                "status": "open",
                "resolution": None,
            }
        )
        self._save()
        return sid

    def resolve_subproblem(self, sp_id: str, resolution: str) -> None:
        for sp in self._data["subproblems"]:
            if sp["id"] == sp_id:
                sp["status"] = "resolved"
                sp["resolution"] = resolution
        self._save()

    # ── Examples ─────────────────────────────────────────────────────────────

    def add_example(
        self,
        description: str,
        detail: str,
        supports_conjecture: Optional[bool],
    ) -> str:
        # Deduplicate
        prefix = description[:80].lower()
        for ex in self._data["examples"]:
            if ex["description"][:80].lower() == prefix:
                return ex["id"]

        eid = f"EX-{uuid.uuid4().hex[:6].upper()}"
        self._data["examples"].append(
            {
                "id": eid,
                "description": description,
                "supports_conjecture": supports_conjecture,
                "detail": detail,
                "added_round": self._data["rounds_completed"],
            }
        )
        self._save()
        return eid

    # ── Proof attempts ───────────────────────────────────────────────────────

    def add_proof_attempt(self, round_: int, sketch: str) -> str:
        pid = f"PA-{uuid.uuid4().hex[:6].upper()}"
        self._data["proof_attempts"].append(
            {
                "id": pid,
                "round": round_,
                "sketch": sketch,
                "status": "unchecked",
                "checker_feedback": None,
            }
        )
        self._save()
        return pid

    def update_proof_attempt(self, pa_id: str, status: str, feedback: str) -> None:
        for pa in self._data["proof_attempts"]:
            if pa["id"] == pa_id:
                pa["status"] = status
                pa["checker_feedback"] = feedback
        self._save()

    # ── Disproof attempts ────────────────────────────────────────────────────

    def add_disproof_attempt(self, round_: int, candidate: str) -> str:
        did = f"DA-{uuid.uuid4().hex[:6].upper()}"
        self._data["disproof_attempts"].append(
            {
                "id": did,
                "round": round_,
                "candidate_counterexample": candidate,
                "status": "unchecked",
                "checker_feedback": None,
            }
        )
        self._save()
        return did

    def update_disproof_attempt(self, da_id: str, status: str, feedback: str) -> None:
        for da in self._data["disproof_attempts"]:
            if da["id"] == da_id:
                da["status"] = status
                da["checker_feedback"] = feedback
        self._save()

    # ── Formalization attempts ───────────────────────────────────────────────

    def add_formalization_attempt(
        self,
        source_id: str,
        lean_code: str,
        mathlib_imports: list,
        sorries: list,
        confidence: str,
        notes: str,
        summary: str,
        lean_file: str = "",
    ) -> str:
        fid = f"FA-{uuid.uuid4().hex[:6].upper()}"
        self._data.setdefault("formalization_attempts", []).append(
            {
                "id": fid,
                "source_id": source_id,
                "lean_file": lean_file,
                "lean_code": lean_code,
                "mathlib_imports": mathlib_imports,
                "sorries": sorries,
                "confidence": confidence,
                "status": "draft",
                "notes": notes,
                "summary": summary,
            }
        )
        self._save()
        return fid

    def formalization_attempts_for(self, source_id: str) -> list:
        return [
            fa for fa in self._data.get("formalization_attempts", [])
            if fa["source_id"] == source_id
        ]

    # ── Pruning ──────────────────────────────────────────────────────────────

    def prune(
        self,
        max_examples: int = 50,
        max_resolved_sps: int = 10,
        flawed_age_limit: int = 5,
        max_log_entries: int = 50,
        max_round_summaries: int = 10,
    ) -> Dict[str, int]:
        """
        Remove low-value entries to keep the KB compact.

        Priority for examples (highest first):
          contradicting > recent non-literature > supporting > old literature
        Flawed proof/disproof attempts older than flawed_age_limit rounds are removed.
        Only the most recent max_resolved_sps resolved subproblems are kept.
        Log and round_summaries are trimmed to their tail.

        Returns a dict of counts removed per category.
        """
        current_round = self._data["rounds_completed"]
        stats: Dict[str, int] = {}

        # ── Resolved subproblems ──────────────────────────────────────────────
        open_sps = [sp for sp in self._data["subproblems"] if sp["status"] == "open"]
        resolved_sps = [sp for sp in self._data["subproblems"] if sp["status"] == "resolved"]
        if len(resolved_sps) > max_resolved_sps:
            removed = len(resolved_sps) - max_resolved_sps
            self._data["subproblems"] = open_sps + resolved_sps[-max_resolved_sps:]
            stats["subproblems_removed"] = removed

        # ── Examples ─────────────────────────────────────────────────────────
        if len(self._data["examples"]) > max_examples:
            def _ex_priority(ex: Dict[str, Any]) -> tuple:
                is_lit = ex["description"].startswith("[Literature]")
                sup = ex.get("supports_conjecture")
                age = current_round - ex.get("added_round", 0)
                if sup is False:
                    return (0, age, is_lit)   # contradicting: highest priority
                elif not is_lit:
                    return (1, age, False)    # concrete supporting/neutral
                else:
                    return (2, age, True)     # literature: lowest priority

            sorted_ex = sorted(self._data["examples"], key=_ex_priority)
            removed = len(sorted_ex) - max_examples
            self._data["examples"] = sorted_ex[:max_examples]
            stats["examples_removed"] = removed

        # ── Old flawed proof attempts ─────────────────────────────────────────
        old_flawed_pa = [
            pa for pa in self._data["proof_attempts"]
            if pa["status"] == "flawed" and current_round - pa.get("round", 0) > flawed_age_limit
        ]
        if old_flawed_pa:
            drop = {pa["id"] for pa in old_flawed_pa}
            self._data["proof_attempts"] = [
                pa for pa in self._data["proof_attempts"] if pa["id"] not in drop
            ]
            stats["flawed_proofs_removed"] = len(old_flawed_pa)

        # ── Old flawed disproof attempts ──────────────────────────────────────
        old_flawed_da = [
            da for da in self._data["disproof_attempts"]
            if da["status"] == "flawed" and current_round - da.get("round", 0) > flawed_age_limit
        ]
        if old_flawed_da:
            drop = {da["id"] for da in old_flawed_da}
            self._data["disproof_attempts"] = [
                da for da in self._data["disproof_attempts"] if da["id"] not in drop
            ]
            stats["flawed_disproofs_removed"] = len(old_flawed_da)

        # ── Log ───────────────────────────────────────────────────────────────
        if len(self._data["log"]) > max_log_entries:
            removed = len(self._data["log"]) - max_log_entries
            self._data["log"] = self._data["log"][-max_log_entries:]
            stats["log_entries_removed"] = removed

        # ── Round summaries ───────────────────────────────────────────────────
        if len(self._data.get("round_summaries", [])) > max_round_summaries:
            removed = len(self._data["round_summaries"]) - max_round_summaries
            self._data["round_summaries"] = self._data["round_summaries"][-max_round_summaries:]
            stats["round_summaries_removed"] = removed

        self._save()
        return stats

    # ── Final verdict ────────────────────────────────────────────────────────

    def set_status(self, status: str) -> None:
        assert status in ("open", "proved", "disproved", "unknown")
        self._data["status"] = status
        self._save()

    # ── Helpers ──────────────────────────────────────────────────────────────

    @property
    def status(self) -> str:
        return self._data["status"]

    @property
    def conjecture(self) -> str:
        return self._data["conjecture"]

    @property
    def rounds_completed(self) -> int:
        return self._data["rounds_completed"]

    def open_subproblems(self) -> List[Dict]:
        return [s for s in self._data["subproblems"] if s["status"] == "open"]

    def unchecked_proofs(self) -> List[Dict]:
        return [p for p in self._data["proof_attempts"] if p["status"] == "unchecked"]

    def unchecked_disproofs(self) -> List[Dict]:
        return [d for d in self._data["disproof_attempts"] if d["status"] == "unchecked"]

    def valid_proof_exists(self) -> bool:
        return any(p["status"] == "valid" for p in self._data["proof_attempts"])

    def valid_disproof_exists(self) -> bool:
        return any(d["status"] == "valid" for d in self._data["disproof_attempts"])

    def path(self) -> str:
        return self._path

    # ── In-progress round state ──────────────────────────────────────────────

    @property
    def current_round_state(self) -> Optional[Dict[str, Any]]:
        return self._data.get("current_round_state")

    def start_round(self, round_: int, planned_agents: List[str]) -> None:
        self._data["current_round_state"] = {
            "round": round_,
            "planned": planned_agents,
            "completed": [],
            "summaries": [],
        }
        self._save()

    def record_agent_completion(self, agent_name: str, summary: str) -> None:
        crs = self._data.get("current_round_state")
        if crs is None:
            return
        if agent_name not in crs["completed"]:
            crs["completed"].append(agent_name)
        crs["summaries"].append(f"{agent_name}: {summary}")
        self._save()

    def finish_round(self) -> None:
        self._data["current_round_state"] = None
        self._save()

    # ── Stagnation tracking ──────────────────────────────────────────────────

    def increment_no_progress(self) -> None:
        self._data["no_progress_rounds"] = self._data.get("no_progress_rounds", 0) + 1
        self._save()

    def reset_no_progress(self) -> None:
        self._data["no_progress_rounds"] = 0
        self._save()

    def set_prev_snapshot_hash(self, h: int) -> None:
        self._data["prev_snapshot_hash"] = h
        self._save()

    @property
    def no_progress_rounds(self) -> int:
        return self._data.get("no_progress_rounds", 0)

    @property
    def prev_snapshot_hash(self) -> Optional[int]:
        return self._data.get("prev_snapshot_hash")
