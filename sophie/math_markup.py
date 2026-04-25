"""
math_markup.py
--------------
Convert plain-text mathematical notation written by agents into LaTeX inline
math ($...$) so that the viewer can render it via KaTeX.

Design goals:
  - Conservative: only convert patterns with very low false-positive risk.
  - Idempotent: already-converted text (contains $) is left unchanged per-token.
  - Focused: handles the patterns that actually appear in agent output.

Patterns handled (in order):
  1. Congruences      n ≡ 3 mod 4  /  n ≡ 3 (mod 4)  / n \\equiv 3 mod 4
  2. Superscripts     (nb)^2  /  n^k  /  x^{2}  (already-braced pass-through)
  3. Capital subscripts  b_k  /  D_k  /  p_k  (capital letter + underscore + id)
  4. Inequalities     n ≥ 2  /  n ≤ 0
  5. Divisibility     4|(n+3)  /  p|n
  6. Not-equal        a ≠ b
"""

from __future__ import annotations
import re


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _already_math(m: re.Match, text: str) -> bool:
    """Return True if the match is already inside a $...$ span."""
    start = m.start()
    # Count unescaped $ before the match — odd count means we're inside math.
    dollar_count = text[:start].count('$')
    return dollar_count % 2 == 1


def _sub_safe(pattern: str, repl, text: str, flags: int = 0) -> str:
    """re.sub, but skip matches that are already inside $...$."""
    def safe_repl(m: re.Match) -> str:
        if _already_math(m, text):
            return m.group(0)
        if callable(repl):
            return repl(m)
        return repl
    return re.sub(pattern, safe_repl, text, flags=flags)


# ---------------------------------------------------------------------------
# Individual converters (applied in sequence)
# ---------------------------------------------------------------------------

def _congruences(text: str) -> str:
    r"""n ≡ b (mod m)  /  n ≡ b mod m  /  n \equiv b mod m  →  $n \equiv b \pmod{m}$"""
    # Unicode ≡ with parenthesised mod
    text = _sub_safe(
        r'(-?[\w()]+)\s*≡\s*(-?[\w()]+)\s*\(mod\s+([\w()]+)\)',
        lambda m: f'${m.group(1)} \\equiv {m.group(2)} \\pmod{{{m.group(3)}}}$',
        text,
    )
    # Unicode ≡ without parentheses
    text = _sub_safe(
        r'(-?[\w()]+)\s*≡\s*(-?[\w()]+)\s+mod\s+([\w()]+)',
        lambda m: f'${m.group(1)} \\equiv {m.group(2)} \\pmod{{{m.group(3)}}}$',
        text,
    )
    # Backslash \equiv (agents sometimes use LaTeX mid-text without delimiters)
    text = _sub_safe(
        r'(-?[\w()]+)\s*\\equiv\s*(-?[\w()]+)\s+mod\s+([\w()]+)',
        lambda m: f'${m.group(1)} \\equiv {m.group(2)} \\pmod{{{m.group(3)}}}$',
        text,
    )
    return text


def _superscripts(text: str) -> str:
    """expr^exp  →  $expr^{exp}$  (e.g. (nb)^2, n^k)"""
    # Handle already-braced: e^{...} — just wrap in $
    text = _sub_safe(
        r'([\w()]+)\^\{([^}]+)\}',
        lambda m: f'${m.group(1)}^{{{m.group(2)}}}$',
        text,
    )
    # Simple: word^word or word^digit
    text = _sub_safe(
        r'([\w()]+)\^([\w()]+)',
        lambda m: f'${m.group(1)}^{{{m.group(2)}}}$',
        text,
    )
    return text


def _subscripts(text: str) -> str:
    """Capital-letter identifiers with underscore: b_k, D_k, p_k → $b_{k}$"""
    text = _sub_safe(
        r'\b([a-zA-Z][a-zA-Z]?)_([a-z0-9]+)\b',
        lambda m: f'${m.group(1)}_{{{m.group(2)}}}$',
        text,
    )
    return text


def _inequalities(text: str) -> str:
    r"""token ≥ token  /  token ≤ token  →  $token \geq token$"""
    text = _sub_safe(
        r'(-?[\w()]+)\s*≥\s*(-?[\w()]+)',
        lambda m: f'${m.group(1)} \\geq {m.group(2)}$',
        text,
    )
    text = _sub_safe(
        r'(-?[\w()]+)\s*≤\s*(-?[\w()]+)',
        lambda m: f'${m.group(1)} \\leq {m.group(2)}$',
        text,
    )
    return text


def _not_equal(text: str) -> str:
    """a ≠ b  →  $a \\neq b$"""
    text = _sub_safe(
        r'(-?[\w()]+)\s*≠\s*(-?[\w()]+)',
        lambda m: f'${m.group(1)} \\neq {m.group(2)}$',
        text,
    )
    return text


def _divisibility(text: str) -> str:
    r"""p|n  /  4|(n+3)  →  $p \mid n$"""
    # Handle parenthesised RHS like 4|(n+3)
    text = _sub_safe(
        r'\b([\w]+)\|(\([^)]+\))',
        lambda m: f'${m.group(1)} \\mid {m.group(2)}$',
        text,
    )
    # Simple word RHS
    text = _sub_safe(
        r'\b([\w]+)\|([\w]+)',
        lambda m: f'${m.group(1)} \\mid {m.group(2)}$',
        text,
    )
    return text


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

_CONVERTERS = [
    _congruences,
    _divisibility,   # before subscripts so q|D_k is matched before D_k→$D_{k}$
    _superscripts,
    _subscripts,
    _inequalities,
    _not_equal,
]


def mathify(text: str) -> str:
    """Apply all math-markup converters to *text* and return the result."""
    if not text:
        return text
    for conv in _CONVERTERS:
        text = conv(text)
    return text


# ---------------------------------------------------------------------------
# Migration helper: apply mathify to all text fields in a session JSON file
# ---------------------------------------------------------------------------

_TEXT_FIELDS: dict[str, list[str]] = {
    'proof_attempts':     ['sketch', 'checker_feedback'],
    'disproof_attempts':  ['candidate_counterexample', 'checker_feedback'],
    'subproblems':        ['description', 'resolution'],
    'examples':           ['description', 'detail'],
    'facts':              ['text'],
    'implications':       ['note', 'checker_feedback'],
}


def migrate_session(path: str) -> int:
    """
    Apply mathify() to all text fields in the session JSON at *path*.
    Returns the number of fields changed.  Saves the file in-place.
    """
    import json
    with open(path, encoding='utf-8') as fh:
        data = json.load(fh)

    changed = 0
    for collection, fields in _TEXT_FIELDS.items():
        for item in data.get(collection, []):
            for field in fields:
                old = item.get(field)
                if old and isinstance(old, str):
                    new = mathify(old)
                    if new != old:
                        item[field] = new
                        changed += 1

    # Also round_summaries narrative / summary lines
    for rs in data.get('round_summaries', []):
        for key in ('narrative', 'summary'):
            old = rs.get(key)
            if old and isinstance(old, str):
                new = mathify(old)
                if new != old:
                    rs[key] = new
                    changed += 1
        for entry in rs.get('entries', []):
            old = entry.get('summary')
            if old and isinstance(old, str):
                new = mathify(old)
                if new != old:
                    entry['summary'] = new
                    changed += 1

    if changed:
        with open(path, 'w', encoding='utf-8') as fh:
            json.dump(data, fh, indent=2, ensure_ascii=False)

    return changed
