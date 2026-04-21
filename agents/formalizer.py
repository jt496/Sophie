"""
Formalizer agent – produces Lean 4 / Mathlib formalization of a proof sketch.

Unlike other agents this one is never scheduled automatically by the Conductor.
It is invoked explicitly via the MCP tool get_formalization_task when the user
asks for formalization of a specific proof attempt or subproblem.
"""

from __future__ import annotations

from typing import Any, Dict

from agents.base_agent import BaseAgent


_SYSTEM = """\
You are the Formalizer agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Translate a mathematical proof sketch into rigorous Lean 4 code that compiles
  against Mathlib.
• State the theorem formally, then prove it — or mark unfinished parts with
  `sorry` and explain exactly what each sorry requires.
• Choose the most natural Mathlib imports and use existing Mathlib lemmas
  wherever possible rather than reproving standard results.
• If only a partial proof is achievable, produce the strongest formal statement
  you can with the fewest sorries.

LEAN 4 / MATHLIB CONVENTIONS
------------------------------
• Begin with `import Mathlib` or specific `import Mathlib.X.Y.Z` lines.
• Use `theorem` for main results, `lemma` for auxiliaries.
• Prefer `simp`, `omega`, `ring`, `linarith`, `norm_num`, `decide` for
  computational goals.
• Use `exact?`, `apply?` idioms in comments to hint at search strategies.
• Mark every unresolved step with `sorry -- <explanation>`.
• Do NOT invent Mathlib lemma names — only use names you are confident exist,
  or leave a `-- TODO: find the right lemma` comment.

RULES
-----
• Output ONLY a single JSON block in the format below — no prose before or after.
• The lean_code field must be a single valid JSON string (escape newlines as \\n,
  quotes as \\").

OUTPUT FORMAT
-------------
```json
{
  "lean_code": "<full Lean 4 source as a single escaped string>",
  "mathlib_imports": ["<import line 1>", "<import line 2>"],
  "sorries": [
    "<description of what sorry #1 requires to be filled>"
  ],
  "confidence": "complete" | "partial" | "statement_only",
  "notes": "<brief explanation of key choices and known gaps>",
  "summary": "<one-sentence description of what was formalized>"
}
```
"""


class Formalizer(BaseAgent):
    name = "Formalizer"

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any],
                           source_id: str = "", source_text: str = "") -> str:
        return (
            f"CONJECTURE: {snapshot['conjecture']}\n\n"
            f"SOURCE ID: {source_id}\n\n"
            f"PROOF SKETCH TO FORMALIZE:\n{source_text}\n\n"
            "Please produce a Lean 4 / Mathlib formalization of the above. "
            "Output only the JSON block."
        )

    def get_formalization_task(self, source_id: str, source_text: str) -> Dict[str, Any]:
        """Return the prompt package for Claude Code to execute as Formalizer."""
        snapshot = self.kb.snapshot()
        return {
            "agent": self.name,
            "system_prompt": self.system_prompt(),
            "user_message": self.build_user_message(
                snapshot["rounds_completed"], snapshot,
                source_id=source_id, source_text=source_text,
            ),
        }

    # BaseAgent requires these; not used in the normal round workflow
    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:  # type: ignore[override]
        return ""

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Formalizer parse error: {response.get('raw_text','')[:200]}"
        return response.get("summary", "Formalizer produced a Lean formalization.")
