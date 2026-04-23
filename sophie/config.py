"""
Configuration for the conjecture exploration framework.
"""

import os

# ── LLM ──────────────────────────────────────────────────────────────────────
ANTHROPIC_API_KEY: str = os.environ.get("ANTHROPIC_API_KEY", "")

# Model used for all agents (override per-agent if desired)
DEFAULT_MODEL: str = "claude-opus-4-5"

# Token budgets per agent call
MAX_TOKENS_EXPERIMENTER: int = 4096
MAX_TOKENS_PROVER:       int = 8192
MAX_TOKENS_DISPROVER:    int = 8192
MAX_TOKENS_CHECKER:      int = 8192
MAX_TOKENS_SEARCHER:     int = 8192   # writes + runs code; needs room for output
MAX_TOKENS_RESEARCHER:   int = 8192   # web search + fetch; needs room for results
MAX_TOKENS_CONDUCTOR:    int = 4096

# ── Conductor loop ────────────────────────────────────────────────────────────
MAX_ROUNDS: int = 200          # hard cap on Conductor iterations
CONVERGENCE_PATIENCE: int = 3 # stop after this many rounds with no new findings

# ── Persistence ───────────────────────────────────────────────────────────────
KB_DIR: str = os.path.join(os.path.dirname(__file__), "sessions")
