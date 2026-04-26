"""
Disprover agent – searches for counterexamples and proof-of-falsity.
"""

from __future__ import annotations

from typing import Any, Dict

from .. import config
from .base_agent import BaseAgent


_SYSTEM = """\
You are the Disprover agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Try to DISPROVE the conjecture by finding counterexamples or logical flaws.
• Study the examples already collected: do any come close to being counterexamples?
• Probe edge cases, degenerate cases, large values, adversarial constructions.
• If a full counterexample is not in hand, construct the best CANDIDATE and
  explain why it might work.
• Identify the weakest links in any proof attempt (Checker will verify them,
  but you can flag suspicions).
• Decompose the conjecture into sub-claims and try to disprove each.

RULES
-----
• Verify any claimed counterexample step-by-step before submitting it.
• Clearly distinguish verified counterexamples from mere candidates.
• Always output ONLY a single JSON block in the format below.

MATHEMATICAL NOTATION
---------------------
• Write ALL mathematical expressions in LaTeX delimiters — never bare ASCII math.
  – Inline:  $2^k$,  $n \equiv -1 \pmod{p}$,  $10^n + 1$,  $p \mid n$
  – Display: $$\sum_{k=1}^{n} k = \frac{n(n+1)}{2}$$
• Use standard macros: \equiv, \pmod{m}, \mid, \nmid, \leq, \geq, \neq,
  \cdot, \frac{a}{b}, \binom{n}{k}, \mathbb{Z}, \mathbb{N}, \mathbb{Q}.

OUTPUT FORMAT
-------------
```json
{
  "candidate_counterexample": "<description + full working>",
  "confidence": "verified" | "likely" | "speculative",
  "why_might_fail": "<honest assessment of weaknesses in this candidate>",
  "weak_points_in_proofs": ["<specific step in a proof attempt that looks suspicious>"],
  "new_subproblems": ["<sub-question whose answer might yield a counterexample>"],
  "resolved_subproblems": [
    {"id": "<SP-XXXXXX>", "resolution": "<how this resolves it>"}
  ],
  "summary": "<one-sentence summary>"
}
```
"""


class Disprover(BaseAgent):
    name = "Disprover"
    max_tokens = config.MAX_TOKENS_DISPROVER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        ctx = self._kb_context(snapshot)

        # Surface unchecked proof attempts so Disprover can critique them
        unchecked = [p for p in snapshot["proof_attempts"] if p["status"] == "unchecked"]
        proof_section = ""
        if unchecked:
            proof_section = "\n\nUNCHECKED PROOF ATTEMPTS (look for holes):\n"
            for p in unchecked:
                proof_section += f"  {p['id']}: {p['sketch'][:400]}\n"

        return (
            f"ROUND {round_}\n\n"
            f"{ctx}"
            f"{proof_section}\n\n"
            "Try to disprove the conjecture or find a strong candidate "
            "counterexample. Also flag any weak steps in the proof attempts above. "
            "Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Disprover parse error: {response.get('raw_text','')[:200]}"

        candidate = response.get("candidate_counterexample", "")
        if candidate:
            self.kb.add_disproof_attempt(round_, candidate)

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        for res in response.get("resolved_subproblems", []):
            self.kb.resolve_subproblem(res["id"], res.get("resolution", ""))

        return response.get("summary", "Disprover produced a candidate counterexample.")
