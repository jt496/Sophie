"""
Checker agent – validates proof and disproof attempts.
"""

from __future__ import annotations

from typing import Any, Dict, List

import config
from agents.base_agent import BaseAgent


_SYSTEM = """\
You are the Checker agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Carefully VERIFY or REFUTE each proof or disproof attempt submitted by the
  Prover or Disprover.
• Go line-by-line through each argument; flag every unjustified step.
• For proofs: determine whether the argument is (a) valid, (b) fixable with
  minor corrections, or (c) fundamentally flawed.
• For counterexamples: verify the claimed counterexample satisfies all
  conditions of the conjecture and indeed violates the conclusion.
• Provide precise, actionable feedback so that other agents can improve.

RULES
-----
• Be the toughest critic: accept nothing on trust.
• Reference specific lines or steps when giving feedback.
• Never declare something valid unless you are convinced.
• If a proof has a fixable gap, say so and suggest how to fix it.
• Always output ONLY a single JSON block in the format below.

OUTPUT FORMAT
-------------
```json
{
  "proof_verdicts": [
    {
      "id": "<PA-XXXXXX>",
      "verdict": "valid" | "flawed",
      "feedback": "<detailed line-by-line commentary>"
    }
  ],
  "disproof_verdicts": [
    {
      "id": "<DA-XXXXXX>",
      "verdict": "valid" | "flawed",
      "feedback": "<detailed commentary>"
    }
  ],
  "overall_assessment": "<summary of where the exploration stands>",
  "summary": "<one-sentence summary of what you checked>"
}
```
"""


class Checker(BaseAgent):
    name = "Checker"
    max_tokens = config.MAX_TOKENS_CHECKER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        unchecked_proofs    = [p for p in snapshot["proof_attempts"]    if p["status"] == "unchecked"]
        unchecked_disproofs = [d for d in snapshot["disproof_attempts"] if d["status"] == "unchecked"]

        sections: List[str] = [
            f"ROUND {round_}",
            "",
            f"CONJECTURE: {snapshot['conjecture']}",
            "",
            "ITEMS TO CHECK",
            "==============",
        ]

        if unchecked_proofs:
            sections.append("\nPROOF ATTEMPTS:")
            for p in unchecked_proofs:
                sections.append(f"\n[{p['id']}]\n{p['sketch']}")

        if unchecked_disproofs:
            sections.append("\nDISPROOF/COUNTEREXAMPLE ATTEMPTS:")
            for d in unchecked_disproofs:
                sections.append(f"\n[{d['id']}]\n{d['candidate_counterexample']}")

        if not unchecked_proofs and not unchecked_disproofs:
            sections.append("Nothing to check this round.")

        sections.append("\nOutput only the JSON block.")
        return "\n".join(sections)

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Checker parse error: {response.get('raw_text','')[:200]}"

        for pv in response.get("proof_verdicts", []):
            self.kb.update_proof_attempt(
                pa_id=pv["id"],
                status=pv["verdict"],
                feedback=pv.get("feedback", ""),
            )
            # If a proof is declared valid, escalate KB status
            if pv["verdict"] == "valid":
                self.kb.set_status("proved")

        for dv in response.get("disproof_verdicts", []):
            self.kb.update_disproof_attempt(
                da_id=dv["id"],
                status=dv["verdict"],
                feedback=dv.get("feedback", ""),
            )
            if dv["verdict"] == "valid":
                self.kb.set_status("disproved")

        return response.get("summary", "Checker reviewed submitted attempts.")
