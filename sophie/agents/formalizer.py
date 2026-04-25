"""
Formalizer agent – produces Lean 4 / Mathlib formalization of a proof sketch.

Can be run in two ways:
  • Explicitly: get_formalization_task(source_id) → act → submit_formalization
  • Via round:  include "F" in the agents string passed to get_round_tasks;
                the agent auto-selects the best unformalized candidate.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Dict, Optional

from .base_agent import BaseAgent

# Root of the Lean project relative to the Sophie repo root.
LEAN_ROOT = Path(__file__).parent.parent.parent / "formalization" / "SophieFormalization"
LEAN_MODULE_ROOT = "SophieFormalization"


def _conjecture_slug(conjecture: str) -> str:
    """
    Turn a conjecture string into a CamelCase module name suitable for use as a
    subdirectory and Lean module prefix, e.g.:
      "Does 4/n = 1/x+1/y+1/z ..."  →  "ErdosStraus"
      "Holroyd-Talbot conjecture ..."  →  "HolroydTalbot"
    Falls back to a sanitised title-case slug if no known conjecture matches.
    """
    c = conjecture.lower()
    if "erdos" in c or "straus" in c or "4/n" in c or "egyptian fraction" in c:
        return "ErdosStraus"
    if "holroyd" in c or "talbot" in c or "r-ekr" in c or "rekr" in c:
        return "HolroydTalbot"
    # Generic fallback: take first few significant words
    words = re.findall(r"[a-zA-Z]+", conjecture)
    slug = "".join(w.capitalize() for w in words[:4] if len(w) > 2)
    return slug or "Unknown"


def _existing_lean_files() -> list[str]:
    """Return module paths of all .lean files currently in the formalization tree."""
    if not LEAN_ROOT.exists():
        return []
    paths = []
    for p in sorted(LEAN_ROOT.rglob("*.lean")):
        rel = p.relative_to(LEAN_ROOT.parent)
        module = str(rel).replace("/", ".").removesuffix(".lean")
        paths.append(module)
    return paths


def write_lean_file(lean_code: str, lean_file: str) -> Optional[str]:
    """
    Write (or append) lean_code to lean_file inside the formalization/ tree.
    Updates the root SophieFormalization.lean import list for new files.
    Returns the lean_file path on success, None if lean_code or lean_file is empty.
    """
    if not lean_file or not lean_code:
        return None
    lean_root = LEAN_ROOT.parent
    target = lean_root / lean_file
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        existing = target.read_text(encoding="utf-8")
        target.write_text(existing.rstrip() + "\n\n" + lean_code + "\n", encoding="utf-8")
    else:
        target.write_text(lean_code + "\n", encoding="utf-8")
        root_module = lean_root / "SophieFormalization.lean"
        if root_module.exists():
            module_name = lean_file.replace("/", ".").removesuffix(".lean")
            import_line = f"import {module_name}"
            content = root_module.read_text(encoding="utf-8")
            if import_line not in content:
                root_module.write_text(
                    content.rstrip() + f"\nimport {module_name}\n", encoding="utf-8"
                )
    return lean_file


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

FILE PLACEMENT
--------------
• Each conjecture has its own subdirectory under SophieFormalization/:
    SophieFormalization/HolroydTalbot/   — Holroyd-Talbot conjecture
    SophieFormalization/ErdosStraus/     — Erdős–Straus conjecture
    SophieFormalization/<Slug>/          — any new conjecture
• Choose the target file from EXISTING FILES shown in the user message, or
  propose a new path following the pattern above.
• Set "lean_file" to the path relative to the formalization/ directory, e.g.:
    "SophieFormalization/ErdosStraus/Theorems.lean"

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
  "lean_file": "<path relative to formalization/, e.g. SophieFormalization/ErdosStraus/Theorems.lean>",
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

    def build_user_message(self, round_: int, snapshot: Dict[str, Any],  # type: ignore[override]
                           source_id: str = "", source_text: str = "") -> str:
        if not source_id:
            return ""
        slug = _conjecture_slug(snapshot.get("conjecture", ""))
        existing = _existing_lean_files()
        existing_str = "\n".join(f"  • {f}" for f in existing) if existing else "  (none yet)"
        suggested = f"SophieFormalization/{slug}/Theorems.lean"
        return (
            f"CONJECTURE: {snapshot['conjecture']}\n\n"
            f"SOURCE ID: {source_id}\n\n"
            f"EXISTING LEAN FILES IN REPO:\n{existing_str}\n\n"
            f"SUGGESTED TARGET FILE: {suggested}\n"
            f"(Append to it if it already exists, or create it if not.)\n\n"
            f"PROOF SKETCH TO FORMALIZE:\n{source_text}\n\n"
            "Please produce a Lean 4 / Mathlib formalization of the above. "
            "Output only the JSON block."
        )

    # ── Auto-selection for round workflow ─────────────────────────────────────

    def _select_source(self, snapshot: Dict[str, Any]) -> Optional[tuple[str, str]]:
        """
        Pick the best unformalized candidate. Returns (source_id, source_text)
        or None if there is nothing to formalize.

        Priority:
          1. Valid proof attempts not yet formalized
          2. Unchecked proof attempts with a substantial sketch (>300 chars)
          3. Resolved subproblems not yet formalized
        """
        already = {fa["source_id"] for fa in snapshot.get("formalization_attempts", [])}

        for pa in snapshot["proof_attempts"]:
            if pa["id"] not in already and pa["status"] == "valid":
                return pa["id"], pa["sketch"]

        for pa in snapshot["proof_attempts"]:
            if pa["id"] not in already and pa["status"] == "unchecked" and len(pa["sketch"]) > 300:
                return pa["id"], pa["sketch"]

        for sp in snapshot["subproblems"]:
            if sp["id"] not in already and sp["status"] == "resolved" and sp.get("resolution"):
                text = sp["description"] + f"\n\nResolution: {sp['resolution']}"
                return sp["id"], text

        return None

    def get_task(self, round_: int) -> Dict[str, Any]:
        """
        Override base get_task to auto-select a source and store the choice in
        the KB's agent_context so process_response can retrieve it.
        """
        snapshot = self.kb.snapshot()
        candidate = self._select_source(snapshot)
        if candidate is None:
            return {
                "agent": self.name,
                "error": (
                    "No unformalized candidates found. "
                    "There must be at least one valid, unchecked, or resolved proof attempt "
                    "that has not yet been formalized."
                ),
            }
        source_id, source_text = candidate
        self.kb.set_agent_context(self.name, {"source_id": source_id})
        return {
            "agent": self.name,
            "system_prompt": self.system_prompt(),
            "user_message": self.build_user_message(
                round_, snapshot, source_id=source_id, source_text=source_text
            ),
        }

    # ── Explicit task builder (used by get_formalization_task MCP tool) ───────

    def get_formalization_task(self, source_id: str, source_text: str) -> Dict[str, Any]:
        """Return the prompt package for an explicitly requested formalization."""
        snapshot = self.kb.snapshot()
        return {
            "agent": self.name,
            "system_prompt": self.system_prompt(),
            "user_message": self.build_user_message(
                snapshot["rounds_completed"], snapshot,
                source_id=source_id, source_text=source_text,
            ),
        }

    # ── Response processing ───────────────────────────────────────────────────

    def process_response(self, round_: int, response: Dict[str, Any]) -> str:
        """
        Write the Lean file, persist the formalization attempt in the KB, and
        return a summary string.  Reads source_id from the KB's agent_context
        (set by get_task during the round workflow).
        """
        if response.get("parse_error"):
            return f"Formalizer parse error: {response.get('raw_text', '')[:200]}"

        source_id = self.kb.get_agent_context(self.name).get("source_id", "")
        lean_code: str = response.get("lean_code", "")
        lean_file: str = response.get("lean_file", "")

        write_lean_file(lean_code, lean_file)

        self.kb.add_formalization_attempt(
            source_id=source_id,
            lean_code=lean_code,
            lean_file=lean_file,
            mathlib_imports=response.get("mathlib_imports", []),
            sorries=response.get("sorries", []),
            confidence=response.get("confidence", "partial"),
            notes=response.get("notes", ""),
            summary=response.get("summary", ""),
        )

        sorry_count = len(response.get("sorries", []))
        summary = response.get("summary", "Lean formalization produced.")
        return f"{summary} ({sorry_count} sorries, confidence: {response.get('confidence', '?')})"
