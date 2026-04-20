"""
Prover agent – attempts to construct proofs and proof sketches.
"""

from __future__ import annotations

from typing import Any, Dict

import config
from agents.base_agent import BaseAgent


_SYSTEM = """\
You are the Prover agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Attempt to PROVE the conjecture (or useful sub-results toward it).
• Leverage examples from the Experimenter, open sub-problems, and any
  previous proof attempts as raw material.
• Propose proof strategies: induction, contradiction, construction,
  algebraic manipulation, known theorems, etc.
• If a complete proof is not yet in reach, produce the strongest PARTIAL
  result you can, making the gap explicit.
• Identify sub-problems whose resolution would unlock the full proof.

RULES
-----
• Mathematical rigour is paramount. Flag any step you are not 100% certain
  about with [UNVERIFIED].
• Do NOT claim a proof is complete unless every step is airtight.
• Always output ONLY a single JSON block in the format below.

OUTPUT FORMAT
-------------
```json
{
  "proof_sketch": "<full proof attempt or partial result, with LaTeX where helpful>",
  "completeness": "complete" | "partial" | "strategy_only",
  "gaps": ["<description of each unresolved gap>"],
  "new_subproblems": ["<sub-problem whose resolution would help>"],
  "resolved_subproblems": [
    {"id": "<SP-XXXXXX>", "resolution": "<how this attempt resolves it>"}
  ],
  "summary": "<one-sentence description of what was achieved>"
}
```
"""


class Prover(BaseAgent):
    name = "Prover"
    max_tokens = config.MAX_TOKENS_PROVER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        ctx = self._kb_context(snapshot)

        # highlight flawed previous attempts so Prover can learn from them
        flawed = [
            p for p in snapshot["proof_attempts"] if p["status"] == "flawed"
        ]
        flawed_section = ""
        if flawed:
            flawed_section = "\n\nFLAWED PREVIOUS ATTEMPTS (learn from these):\n"
            for p in flawed:
                flawed_section += (
                    f"  {p['id']}: {p['sketch'][:300]}\n"
                    f"  Checker feedback: {p['checker_feedback']}\n"
                )

        return (
            f"ROUND {round_}\n\n"
            f"{ctx}"
            f"{flawed_section}\n\n"
            "Attempt to prove the conjecture or make the strongest partial "
            "progress you can. Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Prover parse error: {response.get('raw_text','')[:200]}"

        sketch = response.get("proof_sketch", "")
        if sketch:
            pa_id = self.kb.add_proof_attempt(round_, sketch)

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        for res in response.get("resolved_subproblems", []):
            self.kb.resolve_subproblem(res["id"], res.get("resolution", ""))

        return response.get("summary", f"Prover produced a {response.get('completeness','?')} attempt.")
