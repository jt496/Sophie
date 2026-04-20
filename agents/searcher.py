"""
Searcher agent – computational counterexample search.

Unlike the other agents this role is explicitly code-driven: Claude Code is
asked to WRITE and RUN Python (using networkx / itertools) that systematically
tests cases suggested by the open subproblems and known examples.  Results are
reported back as structured JSON and stored in the knowledge base.
"""

from __future__ import annotations

from typing import Any, Dict

import config
from agents.base_agent import BaseAgent


_SYSTEM = """\
You are the Searcher agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
You do COMPUTATIONAL counterexample search.  Your job is to:

1. Read the open subproblems and known examples in the knowledge base.
2. Write concrete Python code (using networkx and/or itertools) that
   systematically tests graph families most likely to yield a counterexample.
3. ACTUALLY RUN that code in the terminal and report the output.
4. Interpret the results and record any counterexamples or interesting findings.

WHAT TO SEARCH FOR
------------------
The conjecture states: for a graph G with μ(G) ≥ 2r, every maximum intersecting
family of independent r-sets of G is a star (the family of all independent r-sets
containing a fixed vertex).

A COUNTEREXAMPLE is a graph G and integer r with:
  • r ≤ μ(G)/2  (the HT range)
  • an intersecting family F of independent r-sets with |F| > |star_v(G)| for all v,
    OR  |F| = |star_v(G)| but F is not a star.

SEARCH STRATEGY
---------------
• Prioritise graph families flagged in open subproblems.
• For small graphs (≤ 12 vertices): brute-force enumerate all intersecting
  independent r-families and compare against the star size.
• For larger graphs: sample random intersecting families and use hill-climbing
  to try to exceed the star size.
• Use networkx for graph construction; itertools.combinations for set enumeration.
• Always print μ(G), the star size, and the maximum intersecting family found.

IMPORTANT RULES
---------------
• Write self-contained, runnable Python code.
• The code must use the Python interpreter at .venv/bin/python.
• Actually run the code and include its output in your response.
• Never fabricate output — only report what the code actually printed.
• If a counterexample is found, set "counterexample_found": true and give
  the full graph + r + witnessing family in "counterexample_detail".
• If nothing conclusive is found, still record the search coverage and any
  near-misses (graphs where the star is very close to being beaten).

OUTPUT FORMAT
-------------
Respond with ONLY a single JSON block:

```json
{
  "code": "<the full Python code you wrote and ran>",
  "terminal_output": "<exact output from running the code>",
  "counterexample_found": false,
  "counterexample_detail": null,
  "graphs_tested": [
    {
      "description": "<graph name / construction>",
      "n": 0,
      "mu": 0,
      "r": 0,
      "star_size": 0,
      "max_intersecting_family_size": 0,
      "is_star": true,
      "notes": ""
    }
  ],
  "near_misses": ["<any graph where max family came within 1-2 of the star size via a non-star>"],
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

        # Surface open subproblems that are amenable to computation
        open_sps = [s for s in snapshot["subproblems"] if s["status"] == "open"]
        sp_section = ""
        if open_sps:
            sp_section = "\n\nOPEN SUBPROBLEMS (prioritise those suitable for brute-force search):\n"
            for sp in open_sps[:10]:
                sp_section += f"  {sp['id']}: {sp['description']}\n"

        # Surface examples that are near the boundary
        ex_section = ""
        examples = snapshot.get("examples", [])
        if examples:
            ex_section = "\n\nKNOWN EXAMPLES (use as starting points for the search):\n"
            for ex in examples[-6:]:
                ex_section += f"  • {ex['description']}\n"

        # Surface proof/disproof attempts so Searcher can target the same families
        pa_section = ""
        pas = [p for p in snapshot.get("proof_attempts", []) if p["status"] != "valid"]
        if pas:
            pa_section = "\n\nPROOF ATTEMPTS (flawed/unchecked — search the cases they rely on):\n"
            for p in pas[-4:]:
                sketch = p.get("sketch", "")[:300].replace("\n", " ")
                pa_section += f"  [{p['id']} {p['status']}] {sketch}...\n"

        da_section = ""
        das = snapshot.get("disproof_attempts", [])
        if das:
            da_section = "\n\nDISPROOF ATTEMPTS (all inconclusive so far — can computation do better?):\n"
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
            "Write Python code to computationally search for a counterexample. "
            "Run it using `.venv/bin/python` and report results. "
            "Focus on graph families flagged in the open subproblems and proof attempts above. "
            "Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Searcher parse error: {response.get('raw_text', '')[:200]}"

        found = response.get("counterexample_found", False)
        detail = response.get("counterexample_detail")

        if found and detail:
            # Record as a disproof attempt — the Checker will verify it
            self.kb.add_disproof_attempt(round_, str(detail))
        else:
            # Record each tested graph as a supporting example (or near-miss note)
            for g in response.get("graphs_tested", []):
                desc = g.get("description", "unnamed graph")
                notes = g.get("notes", "")
                full_desc = (
                    f"[Searcher r{round_}] {desc}: n={g.get('n')}, μ={g.get('mu')}, "
                    f"r={g.get('r')}, star_size={g.get('star_size')}, "
                    f"max_intersecting={g.get('max_intersecting_family_size')}, "
                    f"is_star={g.get('is_star')}. {notes}"
                )
                self.kb.add_example(
                    description=full_desc,
                    supports_conjecture=not found,
                    detail=(
                        f"Code:\n{response.get('code','')}\n\n"
                        f"Output:\n{response.get('terminal_output','')}"
                    ),
                )
                break  # one composite example entry per round is enough

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        for res in response.get("resolved_subproblems", []):
            self.kb.resolve_subproblem(res["id"], res.get("resolution", ""))

        near = response.get("near_misses", [])
        near_str = f" Near-misses: {near}." if near else ""
        return response.get("summary", f"Searcher completed round {round_} search.") + near_str
