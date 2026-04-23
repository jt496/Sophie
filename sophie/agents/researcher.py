"""
Researcher agent – literature and web search.

Claude Code is asked to use its WebSearch / WebFetch tools to look up
relevant results, known theorems, prior work, and references that bear on
the conjecture and open subproblems.  Findings are stored as examples and
subproblems in the knowledge base.
"""

from __future__ import annotations

from typing import Any, Dict

from .. import config
from .base_agent import BaseAgent


_SYSTEM = """\
You are the Researcher agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Search the mathematical literature and the web for:
  – Prior results, theorems, or papers directly relevant to the conjecture.
  – Known partial results, special cases already proved, or related conjectures.
  – Counterexamples or obstructions reported in the literature.
  – Relevant techniques (combinatorics, number theory, graph theory, etc.)
    that other agents could apply.
• Summarise what you find and record it as structured knowledge.
• Do NOT attempt to prove or disprove anything yourself — surface evidence
  and references for the other agents.

HOW TO SEARCH
-------------
• Use your WebSearch tool for keyword queries (e.g. conjecture name, authors,
  relevant mathematical terms).
• Use WebFetch to read promising pages (Wikipedia, arXiv abstracts, OEIS,
  MathOverflow, etc.).
• Search for the conjecture by name if it has one, and by its mathematical
  content if not.
• Always verify facts from at least one source before recording them.

IMPORTANT RULES
---------------
• Only report what your searches actually return — never fabricate citations.
• Include URLs for every source you cite.
• Flag anything uncertain with [UNVERIFIED].
• Always output ONLY a single JSON block in the format below — no prose
  before or after it.

OUTPUT FORMAT
-------------
```json
{
  "search_queries": ["<query 1>", "<query 2>", "..."],
  "sources_consulted": [
    {"title": "<page/paper title>", "url": "<url>", "relevance": "<one line>"}
  ],
  "known_results": [
    {
      "description": "<statement of the result>",
      "source": "<author(s), year, or URL>",
      "relevance": "<how this bears on the conjecture or open subproblems>"
    }
  ],
  "new_subproblems": ["<sub-question suggested by the literature>"],
  "resolved_subproblems": [
    {"id": "<SP-XXXXXX>", "resolution": "<what the literature says>"}
  ],
  "summary": "<one-sentence summary of what was found>"
}
```
"""


class Researcher(BaseAgent):
    name = "Researcher"
    max_tokens = config.MAX_TOKENS_RESEARCHER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        ctx = self._kb_context(snapshot)

        open_sps = [s for s in snapshot["subproblems"] if s["status"] == "open"]
        sp_section = ""
        if open_sps:
            sp_section = "\n\nOPEN SUBPROBLEMS (search for prior work on these):\n"
            for sp in open_sps[:8]:
                sp_section += f"  {sp['id']}: {sp['description']}\n"

        return (
            f"ROUND {round_}\n\n"
            f"{ctx}"
            f"{sp_section}\n\n"
            "Search the mathematical literature and web for results relevant to "
            "the conjecture and the open subproblems above. "
            "Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Researcher parse error: {response.get('raw_text', '')[:200]}"

        for result in response.get("known_results", []):
            desc = result.get("description", "")
            source = result.get("source", "")
            relevance = result.get("relevance", "")
            detail = f"Source: {source}\nRelevance: {relevance}"
            self.kb.add_example(
                description=f"[Literature] {desc[:120]}",
                supports_conjecture=None,
                detail=detail,
            )

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        for res in response.get("resolved_subproblems", []):
            self.kb.resolve_subproblem(res["id"], res.get("resolution", ""))

        n_results = len(response.get("known_results", []))
        n_sources = len(response.get("sources_consulted", []))
        summary = response.get("summary", f"Researcher found {n_results} results from {n_sources} sources.")
        return summary
