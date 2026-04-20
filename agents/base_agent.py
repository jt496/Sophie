"""
Base class for all agents in the conjecture exploration framework.
"""

from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from typing import Any, Dict

from knowledge_base import KnowledgeBase


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
    def _kb_context(snapshot: Dict[str, Any]) -> str:
        """Render key KB fields as a readable section for prompts."""
        lines = [
            f"CONJECTURE: {snapshot['conjecture']}",
            f"STATUS: {snapshot['status']}",
            "",
            "── SUBPROBLEMS ──",
        ]
        for sp in snapshot["subproblems"]:
            flag = "✓" if sp["status"] == "resolved" else "○"
            lines.append(f"  [{flag}] {sp['id']}: {sp['description']}")
            if sp["resolution"]:
                lines.append(f"        Resolution: {sp['resolution']}")

        lines += ["", "── EXAMPLES ──"]
        for ex in snapshot["examples"]:
            sup = {True: "supports", False: "contradicts", None: "neutral"}.get(
                ex["supports_conjecture"], "?"
            )
            lines.append(f"  {ex['id']} [{sup}]: {ex['description']}")

        lines += ["", "── PROOF ATTEMPTS ──"]
        for pa in snapshot["proof_attempts"]:
            lines.append(f"  {pa['id']} [{pa['status']}]: {pa['sketch'][:120]}...")

        lines += ["", "── DISPROOF ATTEMPTS ──"]
        for da in snapshot["disproof_attempts"]:
            lines.append(
                f"  {da['id']} [{da['status']}]: {da['candidate_counterexample'][:120]}..."
            )

        return "\n".join(lines)
