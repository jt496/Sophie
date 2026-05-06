"""
Base class for all agents in the conjecture exploration framework.
"""

from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from typing import Any, Dict

from ..knowledge_base import KnowledgeBase


class BaseAgent(ABC):
    """
    Each agent builds a task (system prompt + user message) and processes
    Claude's JSON response back into the knowledge base.  No API calls are
    made here — Claude Code itself acts as the LLM for each agent role.
    """

    name: str = "Agent"

    def __init__(self, kb: KnowledgeBase):
        self.kb = kb

    # ── Subclasses must implement ────────────────────────────────────────────

    @abstractmethod
    def system_prompt(self) -> str:
        """Return the system prompt that defines this agent's behaviour."""
        ...

    @abstractmethod
    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        """Build the user-turn message from the current KB snapshot."""
        ...

    @abstractmethod
    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        """
        Parse the structured JSON response, update the KB, and return a
        plain-English summary string.
        """
        ...

    # ── Task construction ────────────────────────────────────────────────────

    def get_task(self, round_: int) -> Dict[str, Any]:
        """Return the prompt package for Claude Code to execute as this agent."""
        snapshot = self.kb.snapshot()
        return {
            "agent": self.name,
            "system_prompt": self.system_prompt(),
            "user_message": self.build_user_message(round_, snapshot),
        }

    # ── Helpers ──────────────────────────────────────────────────────────────

    @staticmethod
    def _check_schema(response: Dict[str, Any], required: list[str], agent_name: str) -> str | None:
        """
        Return an error string if none of the required fields are present but
        the response contains other keys — a strong signal that the wrong field
        names were used.  Returns None when the schema looks correct.
        """
        if response.get("parse_error"):
            return None  # already flagged elsewhere
        present = [f for f in required if response.get(f)]
        if present:
            return None  # at least one required field found — looks fine
        other_keys = [k for k in response if k not in ("summary", "parse_error", "raw_text")]
        if other_keys:
            return (
                f"{agent_name} response used unrecognised field names "
                f"{other_keys!r} instead of required {required!r}. "
                "Nothing was saved. Re-submit with the correct field names."
            )
        return None

    @staticmethod
    def _extract_json(text: str) -> Dict[str, Any]:
        """
        Extract the first JSON block from the LLM reply.
        Falls back to wrapping the whole text in an 'error' key.
        """
        # Try a fenced JSON block first
        match = re.search(r"```json\s*(.*?)```", text, re.DOTALL)
        if match:
            block = match.group(1).strip()
        else:
            # Try raw JSON object
            match = re.search(r"\{.*\}", text, re.DOTALL)
            block = match.group(0) if match else ""

        if block:
            try:
                return json.loads(block)
            except json.JSONDecodeError:
                pass

        return {"raw_text": text, "parse_error": True}

    @staticmethod
    def _kb_context(
        snapshot: Dict[str, Any],
        max_examples: int = 20,
        max_resolved_sps: int = 5,
        max_unchecked_attempts: int = 3,
        flawed_recency: int = 2,
    ) -> str:
        """
        Render key KB fields as a readable section for agent prompts.

        To keep prompts compact as sessions grow, this method:
        - Shows all open subproblems but caps resolved ones at max_resolved_sps.
        - Prioritises examples: contradicting > recent concrete > supporting > old literature.
        - Shows all valid proof/disproof attempts; caps unchecked at max_unchecked_attempts;
          only shows flawed attempts from the last flawed_recency rounds.
        """
        current_round = snapshot.get("rounds_completed", 0)
        lines = [
            f"CONJECTURE: {snapshot['conjecture']}",
            f"STATUS: {snapshot['status']}",
        ]

        facts = snapshot.get("facts", [])
        if facts:
            lines += ["", "── ESTABLISHED FACTS (treat as ground truth) ──"]
            for f in facts:
                lines.append(f"  [{f['id']}] {f['text']}")

        # Subproblems: all open, tail of resolved
        lines += ["", "── SUBPROBLEMS ──"]
        open_sps = [sp for sp in snapshot["subproblems"] if sp["status"] == "open"]
        resolved_sps = [sp for sp in snapshot["subproblems"] if sp["status"] == "resolved"]
        for sp in open_sps:
            lines.append(f"  [○] {sp['id']}: {sp['description']}")
        for sp in resolved_sps[-max_resolved_sps:]:
            lines.append(f"  [✓] {sp['id']}: {sp['description']}")
            if sp["resolution"]:
                lines.append(f"        Resolution: {sp['resolution']}")
        if len(resolved_sps) > max_resolved_sps:
            lines.append(
                f"  ... ({len(resolved_sps) - max_resolved_sps} older resolved subproblems omitted)"
            )

        # Examples: prioritised view
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

        all_examples = sorted(snapshot["examples"], key=_ex_priority)
        shown_examples = all_examples[:max_examples]
        omitted_examples = len(all_examples) - len(shown_examples)

        lines += ["", "── EXAMPLES ──"]
        for ex in shown_examples:
            sup = {True: "supports", False: "contradicts", None: "neutral"}.get(
                ex["supports_conjecture"], "?"
            )
            lines.append(f"  {ex['id']} [{sup}]: {ex['description']}")
        if omitted_examples:
            lines.append(f"  ... ({omitted_examples} lower-priority examples omitted)")

        # Implication graph
        implications = snapshot.get("implications", [])
        if implications:
            lines += ["", "── IMPLICATIONS ──"]
            for imp in implications:
                arrow = {
                    "proves": "⟹ proves",
                    "supports": "→ supports",
                    "blocks": "✗ blocks",
                    "equivalent": "⟺ equivalent",
                }.get(imp["type"], imp["type"])
                conf = "(certain)" if imp["confidence"] == "certain" else "(plausible)"
                note = f" — {imp['note']}" if imp.get("note") else ""
                lines.append(
                    f"  {imp['id']}: {imp['from_id']} {arrow} {imp['to_id']} {conf}{note}"
                )

        # Proof attempts: all valid, recent unchecked, very-recent flawed only
        valid_pa = [pa for pa in snapshot["proof_attempts"] if pa["status"] == "valid"]
        unchecked_pa = [pa for pa in snapshot["proof_attempts"] if pa["status"] == "unchecked"]
        recent_flawed_pa = [
            pa for pa in snapshot["proof_attempts"]
            if pa["status"] == "flawed" and current_round - pa.get("round", 0) <= flawed_recency
        ]
        shown_pa = valid_pa + unchecked_pa[-max_unchecked_attempts:] + recent_flawed_pa
        omitted_pa = len(snapshot["proof_attempts"]) - len(shown_pa)

        lines += ["", "── PROOF ATTEMPTS ──"]
        for pa in shown_pa:
            lines.append(f"  {pa['id']} [{pa['status']}]: {pa['sketch'][:120]}...")
        if omitted_pa:
            lines.append(f"  ... ({omitted_pa} older flawed attempts omitted)")

        # Disproof attempts: same logic
        valid_da = [da for da in snapshot["disproof_attempts"] if da["status"] == "valid"]
        unchecked_da = [da for da in snapshot["disproof_attempts"] if da["status"] == "unchecked"]
        recent_flawed_da = [
            da for da in snapshot["disproof_attempts"]
            if da["status"] == "flawed" and current_round - da.get("round", 0) <= flawed_recency
        ]
        shown_da = valid_da + unchecked_da[-max_unchecked_attempts:] + recent_flawed_da
        omitted_da = len(snapshot["disproof_attempts"]) - len(shown_da)

        lines += ["", "── DISPROOF ATTEMPTS ──"]
        for da in shown_da:
            lines.append(
                f"  {da['id']} [{da['status']}]: {da['candidate_counterexample'][:120]}..."
            )
        if omitted_da:
            lines.append(f"  ... ({omitted_da} older flawed attempts omitted)")

        return "\n".join(lines)
