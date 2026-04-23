"""
Experimenter agent – explores concrete examples and special cases.
"""

from __future__ import annotations

import json
from typing import Any, Dict

from .. import config
from .base_agent import BaseAgent


_SYSTEM = """\
You are the Experimenter agent in a mathematical conjecture-exploration system.

YOUR ROLE
---------
• Explore CONCRETE examples, small cases, boundary cases, and special cases
  relevant to the conjecture.
• Identify patterns in the examples that might hint at why the conjecture is
  true or false.
• Break the problem into simple sub-cases that other agents can tackle.
• Check whether any existing disproof candidates are plausible by examining
  them concretely.

RULES
-----
• Be rigorous: verify each numerical or combinatorial claim explicitly.
• Prioritise examples that are INFORMATIVE (edge cases, extremes, random sample).
• Do NOT attempt a full proof or disproof; leave that to other agents.
• Always output ONLY a single JSON block in the format below – no prose before
  or after it.

OUTPUT FORMAT
-------------
```json
{
  "new_examples": [
    {
      "description": "<one-line label>",
      "detail": "<full working showing the example>",
      "supports_conjecture": true | false | null
    }
  ],
  "new_subproblems": [
    "<description of a sub-case or sub-question worth investigating>"
  ],
  "observations": "<free-form observations for other agents>",
  "summary": "<one-sentence summary of what you found>"
}
```
"""


class Experimenter(BaseAgent):
    name = "Experimenter"
    max_tokens = config.MAX_TOKENS_EXPERIMENTER

    def system_prompt(self) -> str:
        return _SYSTEM

    def build_user_message(self, round_: int, snapshot: Dict[str, Any]) -> str:
        ctx = self._kb_context(snapshot)
        return (
            f"ROUND {round_}\n\n"
            f"{ctx}\n\n"
            "Please explore 2–4 informative concrete examples or special cases "
            "that have not yet been recorded. Identify any new sub-questions. "
            "Output only the JSON block."
        )

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        if response.get("parse_error"):
            return f"Experimenter parse error: {response.get('raw_text','')[:200]}"

        for ex in response.get("new_examples", []):
            self.kb.add_example(
                description=ex.get("description", ""),
                detail=ex.get("detail", ""),
                supports_conjecture=ex.get("supports_conjecture"),
            )

        for sp_desc in response.get("new_subproblems", []):
            self.kb.add_subproblem(sp_desc, source_agent=self.name)

        return response.get(
            "summary", f"Experimenter added {len(response.get('new_examples', []))} examples."
        )
