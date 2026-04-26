"""
Searcher agent – computational counterexample search.

Claude Code is asked to WRITE and RUN Python code that systematically
searches for counterexamples to the current conjecture.  The system prompt
is entirely conjecture-agnostic; the conjecture and open subproblems are
injected via the user message at runtime.
"""

from __future__ import annotations

from typing import Any, Dict

from .. import config
from .base_agent import BaseAgent


_SYSTEM = """\
You are the Searcher agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
You do COMPUTATIONAL counterexample search.  Your job is to:

1. Read the conjecture and open subproblems from the knowledge base below.
2. Write concrete Python code that systematically searches for a counterexample
   or tests the boundary cases most likely to reveal one.
3. ACTUALLY RUN that code and report the exact output.
4. Interpret the results and record findings.

WHAT TO SEARCH FOR
------------------
Read the CONJECTURE carefully.  A counterexample is any specific instance that
satisfies the hypotheses but violates the conclusion.  Design your search to
target the cases flagged in the open subproblems and the weakest-looking parts
of any proof attempts.

SEARCH STRATEGY
---------------
• Choose appropriate Python libraries for the domain (e.g. itertools,
    fractions, numpy, sympy, networkx, scipy, matplotlib, z3-solver,
    hypothesis, joblib, igraph).
• If a conjecture-specific helper module exists, reuse it from
    `lib/<Conjecture_Name>/` instead of re-implementing it.
• For small search spaces: brute-force enumerate.
• For larger spaces: targeted search guided by the open subproblems.
• Always print enough output to verify your results.
• If a counterexample is found, verify it step-by-step before reporting it.

IMPORTANT RULES
---------------
• Write self-contained, runnable Python code.
• Run Python with the project interpreter: `uv run python`.
    Example: `uv run python your_script.py`.
• Actually run the code and include its EXACT output — never fabricate output.
• If a counterexample is found, set "counterexample_found": true.
• If nothing conclusive is found, record the search coverage clearly.

OUTPUT FORMAT
-------------
Respond with ONLY a single JSON block:

```json
{
  "code": "<the full Python code you wrote and ran>",
  "terminal_output": "<exact output from running the code>",
  "counterexample_found": false,
  "counterexample_detail": null,
  "cases_tested": "<brief description of what was searched and how many cases>",
  "near_misses": ["<any case that came close to being a counterexample>"],
  "new_subproblems": ["<computational open question revealed by this search>"],
  "resolved_subproblems": [
    {"id": "<SP-XXXXXX>", "resolution": "<how the search resolves this>"}
  ],
  "summary": "<one-sentence summary of what was searched and found>"
}
```
"""


class Searcher(BaseAgent):
    name = "Searcher"
    max_tokens = config.MAX_TOKENS_SEARCHER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        ctx = self._kb_context(snapshot)

        open_sps = [s for s in snapshot["subproblems"] if s["status"] == "open"]
        sp_section = ""
        if open_sps:
            sp_section = "\n\nOPEN SUBPROBLEMS (prioritise those suitable for computation):\n"
            for sp in open_sps[:10]:
                sp_section += f"  {sp['id']}: {sp['description']}\n"

        ex_section = ""
        if snapshot.get("examples"):
            ex_section = "\n\nKNOWN EXAMPLES (use as starting points):\n"
            for ex in snapshot["examples"][-6:]:
                ex_section += f"  • {ex['description']}\n"

        pa_section = ""
        pas = [p for p in snapshot.get("proof_attempts", []) if p["status"] != "valid"]
        if pas:
            pa_section = "\n\nUNCHECKED/FLAWED PROOF ATTEMPTS (search the cases they rely on):\n"
            for p in pas[-4:]:
                sketch = p.get("sketch", "")[:300].replace("\n", " ")
                pa_section += f"  [{p['id']} {p['status']}] {sketch}...\n"

        da_section = ""
        das = snapshot.get("disproof_attempts", [])
        if das:
            da_section = "\n\nDISPROOF ATTEMPTS (all inconclusive — can computation do better?):\n"
            for d in das[-3:]:
                cand = d.get("candidate_counterexample", "")[:300].replace("\n", " ")
                da_section += f"  [{d['id']} {d['status']}] {cand}...\n"

        return (
            f"ROUND {round_}\n\n"
            f"{ctx}"
            f"{sp_section}"
            f"{ex_section}"
            f"{pa_section}"
            f"{da_section}\n\n"
            "Write Python code to computationally search for a counterexample to "
            "the conjecture above. Run it using `uv run python` and report results. "
            "Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Searcher parse error: {response.get('raw_text', '')[:200]}"

        found = response.get("counterexample_found", False)
        detail = response.get("counterexample_detail")

        if found and detail:
            self.kb.add_disproof_attempt(round_, str(detail))
        else:
            cases = response.get("cases_tested", "")
            if cases:
                self.kb.add_example(
                    description=f"[Searcher r{round_}] {cases[:120]}",
                    supports_conjecture=True,
                    detail=(
                        f"Code:\n{response.get('code', '')[:500]}\n\n"
                        f"Output:\n{response.get('terminal_output', '')[:500]}"
                    ),
                )

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        for res in response.get("resolved_subproblems", []):
            self.kb.resolve_subproblem(res["id"], res.get("resolution", ""))

        near = response.get("near_misses", [])
        near_str = f" Near-misses: {near}." if near else ""
        return response.get("summary", f"Searcher completed round {round_} search.") + near_str
