"""
Checker agent – validates proof and disproof attempts.
"""

from __future__ import annotations

from typing import Any, Dict, List

from .. import config
from .base_agent import BaseAgent


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
• Also verify implication claims: check that the stated logical relationship
  ("proves", "supports", "blocks", "equivalent") between two KB items is
  mathematically justified, and flag any that are unsound or overstated.

RULES
-----
• Be the toughest critic: accept nothing on trust.
• Reference specific lines or steps when giving feedback.
• Never declare something valid unless you are convinced.
• If a proof has a fixable gap, say so and suggest how to fix it.
• For implications: "valid" means the relationship genuinely holds;
  "flawed" means it is wrong, too strong, or unsupported.
• Always output ONLY a single JSON block in the format below.

MATHEMATICAL NOTATION
---------------------
• Write ALL mathematical expressions in LaTeX delimiters — never bare ASCII math.
  – Inline:  $2^k$,  $n \equiv -1 \pmod{p}$,  $10^n + 1$,  $p \mid n$
  – Display: $$\sum_{k=1}^{n} k = \frac{n(n+1)}{2}$$
• Use standard macros: \equiv, \pmod{m}, \mid, \nmid, \leq, \geq, \neq,
  \cdot, \frac{a}{b}, \binom{n}{k}, \mathbb{Z}, \mathbb{N}, \mathbb{Q}.

CRITICAL RULE FOR closes_conjecture
-------------------------------------
Set "closes_conjecture": true ONLY if the proof covers ALL cases of the
conjecture with no gaps, unverified steps, or missing sub-cases.  A proof
that handles some residue classes, special cases, or a subset of inputs
must have "closes_conjecture": false even if that partial proof is valid.
This field is what triggers the session to be marked proved — get it right.

OUTPUT FORMAT
-------------
```json
{
  "proof_verdicts": [
    {
      "id": "<PA-XXXXXX>",
      "verdict": "valid" | "flawed",
      "closes_conjecture": false,
      "feedback": "<detailed line-by-line commentary>"
    }
  ],
  "disproof_verdicts": [
    {
      "id": "<DA-XXXXXX>",
      "verdict": "valid" | "flawed",
      "closes_conjecture": false,
      "feedback": "<detailed commentary>"
    }
  ],
  "implication_verdicts": [
    {
      "id": "<IMP-XXXXXX>",
      "verdict": "valid" | "flawed",
      "feedback": "<brief justification>"
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

        unchecked_imps = [
            i for i in snapshot.get("implications", []) if i.get("status", "unchecked") == "unchecked"
        ]
        if unchecked_imps:
            # Build an id→description lookup
            id_map: dict = {}
            for sp in snapshot.get("subproblems", []):
                id_map[sp["id"]] = sp["description"][:120]
            for pa in snapshot.get("proof_attempts", []):
                id_map[pa["id"]] = pa["sketch"][:120]
            for f in snapshot.get("facts", []):
                id_map[f["id"]] = f["text"][:120]

            sections.append("\nIMPLICATION CLAIMS TO VERIFY:")
            for imp in unchecked_imps:
                from_desc = id_map.get(imp["from_id"], imp["from_id"])
                to_desc   = id_map.get(imp["to_id"],   imp["to_id"])
                sections.append(
                    f"\n[{imp['id']}] ({imp['type']}, {imp['confidence']}):"
                    f"\n  FROM {imp['from_id']}: {from_desc}"
                    f"\n  TO   {imp['to_id']}: {to_desc}"
                    + (f"\n  Note: {imp['note']}" if imp.get("note") else "")
                )

        if not unchecked_proofs and not unchecked_disproofs and not unchecked_imps:
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
            # Only close the session when the proof is complete for ALL cases
            if pv["verdict"] == "valid" and pv.get("closes_conjecture", False):
                self.kb.set_status("proved")

        for dv in response.get("disproof_verdicts", []):
            self.kb.update_disproof_attempt(
                da_id=dv["id"],
                status=dv["verdict"],
                feedback=dv.get("feedback", ""),
            )
            if dv["verdict"] == "valid" and dv.get("closes_conjecture", False):
                self.kb.set_status("disproved")

        n_imp = 0
        for iv in response.get("implication_verdicts", []):
            self.kb.update_implication(
                imp_id=iv["id"],
                verdict=iv["verdict"],
                feedback=iv.get("feedback", ""),
            )
            n_imp += 1

        summary = response.get("summary", "Checker reviewed submitted attempts.")
        if n_imp:
            summary += f" ({n_imp} implication(s) checked)"
        return summary
