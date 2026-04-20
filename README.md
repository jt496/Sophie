# Sophie – Multi-Agent Mathematical Conjecture Explorer

Sophie is a terminal application that orchestrates several LLM agents (powered
by Claude) to collaboratively explore a mathematical conjecture: gathering
evidence, attempting proofs, hunting for counterexamples, verifying arguments,
and recording everything in a persistent knowledge base.

---

## Architecture

```
┌──────────────────────────────────────────────────────────────────────────┐
│                              Conductor                                   │
│  (LLM-backed)  decides which agents to run each round                    │
└──┬──────────────────────────────────────────────────────────────────┬───┘
   │                                                                  │
   ▼                                                                  ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ ┌──────────────┐
│ Experimenter│ │   Prover    │ │  Disprover  │ │ Checker │ │   Searcher   │
│             │ │             │ │             │ │         │ │              │
│ Concrete    │ │ Constructs  │ │ Hunts for   │ │Verifies │ │ Writes &     │
│ examples &  │ │ proofs and  │ │ counterex-  │ │ proofs &│ │ runs Python  │
│ special     │ │ partial     │ │ amples and  │ │ counter-│ │ code; brute- │
│ cases       │ │ results     │ │ flaws       │ │ examples│ │ force search │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └────┬────┘ └──────┬───────┘
       │               │               │             │             │
       └───────────────┴───────────────┴─────────────┴─────────────┘
                                       │
                               ┌───────▼────────┐
                               │ Knowledge Base │
                               │  (JSON on disk)│
                               └────────────────┘
```

### Agents

| Agent | Role |
|---|---|
| **Experimenter** | Generates concrete examples, boundary cases, and numerical checks. Identifies sub-cases. |
| **Prover** | Attempts to construct rigorous proofs or partial results. Learns from Checker feedback. |
| **Disprover** | Searches for counterexamples. Probes weaknesses in proof attempts. |
| **Checker** | Verifies every proof and disproof attempt line-by-line. Issues verdicts. |
| **Searcher** | Writes and executes Python code (networkx, itertools, `lib/graph_utils`) to brute-force search for counterexamples across graph families. |
| **Conductor** | Orchestrates the loop: decides the agent schedule, detects convergence, presents the final report. |

### Knowledge Base

All findings are stored in `sessions/<session_id>.json` and persist across
restarts. The schema tracks:

- The conjecture and current status (`open` / `proved` / `disproved` / `unknown`)
- **Subproblems** – decomposed sub-questions from any agent
- **Examples** – concrete cases with a support/contradict/neutral label
- **Proof attempts** – with Checker verdicts and feedback
- **Disproof attempts** – with Checker verdicts
- **Log** – per-round summary from every agent

---

## Quickstart

### 1. Install dependencies

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

### 2. Set your Anthropic API key

```bash
export ANTHROPIC_API_KEY=sk-ant-...
```

### 3. Run

```bash
source .venv/bin/activate   # if not already active
python main.py
```

You will be prompted to enter your conjecture. For example:

```
Every even integer greater than 2 is the sum of two primes.
```

### CLI options

```
python main.py --conjecture "..."  # skip the interactive prompt
python main.py --session 20240420_143022  # resume a previous session
python main.py --rounds 5          # limit to 5 rounds
python main.py --model claude-opus-4-5  # use a specific model
```

---

## Configuration

Edit `config.py` to tune:

| Setting | Default | Meaning |
|---|---|---|
| `DEFAULT_MODEL` | `claude-opus-4-5` | Claude model for all agents |
| `MAX_ROUNDS` | `20` | Hard cap on Conductor iterations |
| `CONVERGENCE_PATIENCE` | `3` | Rounds with no new findings before stopping |
| `MAX_TOKENS_*` | varies | Per-agent token budgets |
| `MAX_TOKENS_SEARCHER` | `8192` | Token budget for Searcher's code-writing response |
| `KB_DIR` | `sessions/` | Where JSON session files are written |

---

## Reusable algorithm library (`lib/`)

Algorithms discovered or used by the Searcher are saved in `lib/graph_utils.py`
so that subsequent rounds can import them directly without re-deriving them.

| Function | Description |
|---|---|
| `mu(G)` | Minimum maximal independent set size of a networkx graph (brute force) |
| `mu_witness(G)` | Same, also returns the witness set |
| `independent_sets_of_size(G, r)` | All independent r-subsets of G |
| `star_size(v, indep_sets)` | Number of r-sets containing vertex v |
| `max_star_size(G, indep_sets)` | Largest star size and its centre |
| `max_intersecting_family_size(indep_sets)` | Exact maximum intersecting family (Bron–Kerbosch) |
| `verify_ht(G, r)` | Check HT conjecture for (G, r); returns a result dict |
| `verify_ht_all_r(G)` | Run `verify_ht` for all valid r ≤ μ(G)//2 |

In Searcher scripts, import with:

```python
import sys; sys.path.insert(0, '.')
from lib.graph_utils import mu, independent_sets_of_size, max_intersecting_family_size, verify_ht
```

---

## Session files

Each run creates `sessions/<timestamp>.json`. You can inspect this file at
any time while Sophie is running or after it finishes. Resume a stopped
session with `--session <id>`.

---

## Example output

```
╭──────────────────────────── Sophie – Conjecture Explorer ─────────────────────╮
│ Conjecture                                                                     │
│ Every even integer greater than 2 is the sum of two primes.                   │
╰────────────────────────────────────────────────────────────────────────────────╯
──────────────────────────────── Round 1 ────────────────────────────────────────
Conductor → agents: Experimenter, Prover, Disprover, Checker

▶ Experimenter
  Collected 3 supporting examples (4=2+2, 6=3+3, 100=3+97) and 1 sub-question.

▶ Prover
  Produced a strategy-only sketch based on sieve heuristics.

▶ Disprover
  No counterexample found; highlighted the large-number gap in the proof.

▶ Checker
  Marked proof attempt PA-3A1F2B as flawed: step 3 relies on unproven density claim.
...
```

---

## Using Sophie as an MCP skill inside Claude

Sophie exposes a **Model Context Protocol (MCP) server** so Claude can invoke
it directly as a set of tools — no separate terminal required.

### MCP tools

| Tool | Description |
|---|---|
| `explore_conjecture(conjecture, max_rounds)` | Full investigation loop — returns a complete report |
| `start_session(conjecture)` | Create a session and get a `session_id` |
| `run_round(session_id)` | Run exactly one Conductor round |
| `resume_session(session_id, rounds)` | Continue a session for N more rounds |
| `get_session_status(session_id)` | Inspect the current knowledge base |
| `list_sessions()` | List all saved sessions |

### Claude Desktop setup

Add the following to your Claude Desktop config file
(`~/.config/Claude/claude_desktop_config.json` on Linux,
`~/Library/Application Support/Claude/claude_desktop_config.json` on macOS):

```json
{
  "mcpServers": {
    "sophie": {
      "command": "/home/john/Reps/Sophie/.venv/bin/python",
      "args": ["/home/john/Reps/Sophie/mcp_server.py"],
      "env": {
        "ANTHROPIC_API_KEY": "sk-ant-..."
      }
    }
  }
}
```

Restart Claude Desktop — you will see a Sophie tools icon in the chat interface.

### VS Code / Claude Code setup

A `.mcp.json` file is provided in the repo root. VS Code picks it up
automatically; just ensure `ANTHROPIC_API_KEY` is set in your environment.

### Example Claude prompt (once MCP is active)

> Use Sophie to explore: "For all n ≥ 1, the sum of the first n odd numbers
> equals n²." Run 3 rounds and show me the full report.

Claude will call `explore_conjecture(conjecture="...", max_rounds=3)` and
stream back structured findings from all six agents.

### Debugging the server

```bash
source .venv/bin/activate
export ANTHROPIC_API_KEY=sk-ant-...
python mcp_server.py          # raw stdio transport
mcp dev mcp_server.py         # interactive MCP Inspector UI
```
