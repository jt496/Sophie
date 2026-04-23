#!/usr/bin/env python3
"""
Sophie – multi-agent mathematical conjecture explorer.

Usage
-----
  # Start a new session
  python main.py

  # Resume an existing session by its ID
  python main.py --session 20240420_143022

  # Pass the conjecture non-interactively
  python main.py --conjecture "Every even integer greater than 2 is the sum of two primes."

  # Override the number of rounds
  python main.py --rounds 10
"""

from __future__ import annotations

import argparse
import sys

from rich.console import Console
from rich.prompt import Prompt

from sophie import config
from sophie.conductor import Conductor
from sophie.knowledge_base import KnowledgeBase

console = Console()


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Sophie – multi-agent mathematical conjecture explorer"
    )
    p.add_argument("--conjecture", type=str, default=None,
                   help="The mathematical conjecture to explore.")
    p.add_argument("--session", type=str, default=None,
                   help="Resume an existing session by its ID.")
    p.add_argument("--rounds", type=int, default=None,
                   help=f"Maximum rounds (default: {config.MAX_ROUNDS}).")
    p.add_argument("--model", type=str, default=None,
                   help=f"Claude model to use (default: {config.DEFAULT_MODEL}).")
    return p.parse_args()


def main() -> None:
    args = parse_args()

    # ── API key check ────────────────────────────────────────────────────────
    if not config.ANTHROPIC_API_KEY:
        console.print(
            "[bold red]Error:[/bold red] ANTHROPIC_API_KEY environment variable is not set.\n"
            "Export it before running:  export ANTHROPIC_API_KEY=sk-ant-..."
        )
        sys.exit(1)

    # ── Override config from CLI flags ───────────────────────────────────────
    if args.rounds:
        config.MAX_ROUNDS = args.rounds
    if args.model:
        config.DEFAULT_MODEL = args.model

    # ── Load or create knowledge base ────────────────────────────────────────
    kb = KnowledgeBase(session_id=args.session)

    # ── Set conjecture ───────────────────────────────────────────────────────
    if not kb.conjecture:
        conjecture = args.conjecture or Prompt.ask(
            "\n[bold cyan]Enter the mathematical conjecture to explore[/bold cyan]"
        )
        if not conjecture.strip():
            console.print("[red]No conjecture provided. Exiting.[/red]")
            sys.exit(1)
        kb.set_conjecture(conjecture.strip())
    else:
        console.print(
            f"\n[dim]Resuming session [bold]{kb.session_id}[/bold] "
            f"(round {kb.rounds_completed}, status: {kb.status})[/dim]"
        )

    # ── Run ──────────────────────────────────────────────────────────────────
    conductor = Conductor(kb)
    conductor.run()


if __name__ == "__main__":
    main()
