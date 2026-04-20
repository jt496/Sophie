# Sophie – Multi-Agent Mathematical Conjecture Explorer

Sophie is a terminal application that orchestrates several LLM agents (powered
by Claude) to collaboratively explore a mathematical conjecture: gathering
evidence, attempting proofs, hunting for counterexamples, verifying arguments,
and recording everything in a persistent knowledge base.

---

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                          Conductor                               │
│  (LLM-backed)  decides which agents to run each round            │
└────────┬──────────────────────────────────────────────────┬──────┘
         │                                                  │
         ▼                                                  ▼
  ┌─────────────┐   ┌─────────────┐   ┌─────────────┐   ┌─────────┐
  │ Experimenter│   │   Prover    │   │  Disprover  │   │ Checker │
  │             │   │             │   │             │   │         │
  │ Concrete    │   │ Constructs  │   │ Hunts for   │   │ Verifies│
  │ examples &  │   │ proofs and  │   │ counterex-  │   │ proofs &│
  │ special     │   │ partial     │   │ amples and  │   │ counter-│
  │ cases       │   │ results     │   │ flaws       │   │ examples│
  └──────┬──────┘   └──────┬──────┘   └──────┬──────┘   └────┬────┘
         │                 │                 │               │
         └─────────────────┴─────────────────┴───────────────┘
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
| `KB_DIR` | `sessions/` | Where JSON session files are written |

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
stream back structured findings from all five agents.

### Debugging the server

```bash
source .venv/bin/activate
export ANTHROPIC_API_KEY=sk-ant-...
python mcp_server.py          # raw stdio transport
mcp dev mcp_server.py         # interactive MCP Inspector UI
```
