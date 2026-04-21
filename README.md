# Sophie – Multi-Agent Mathematical Conjecture Explorer

Sophie orchestrates several specialised agents to collaboratively explore a
mathematical conjecture: gathering evidence, attempting proofs, hunting for
counterexamples, verifying arguments, and recording everything in a persistent
knowledge base.

**No separate API key required.** Sophie is designed to run inside
[Claude Code](https://claude.ai/code) — Claude itself acts as every agent.
The MCP server handles only state management and prompt construction.

---

## Architecture

```
┌──────────────────────────────────────────────────────────────────────────┐
│                        Claude Code (you)                                  │
│  Acts as every agent in turn, guided by system prompts from the server    │
└──┬──────────────────────────────────────────────────────────────────┬───┘
   │  get_round_tasks()                    submit_round_results()     │
   ▼                                                                  ▼
┌──────────────────────────────────────────────────────────────────────────┐
│                          MCP Server (Sophie)                              │
│  Rule-based Conductor · Knowledge Base I/O · Prompt construction         │
└──────────────────────────────────────┬───────────────────────────────────┘
                                       │
                               ┌───────▼────────┐
                               │ Knowledge Base │
                               │ sessions/*.json│
                               └────────────────┘
```

### Agents

| Agent | Role |
| --- | --- |
| **Experimenter** | Generates concrete examples, boundary cases, and numerical checks. Identifies sub-cases. |
| **Prover** | Attempts to construct rigorous proofs or partial results. Learns from Checker feedback. |
| **Disprover** | Searches for counterexamples. Probes weaknesses in proof attempts. |
| **Checker** | Verifies every proof and disproof attempt line-by-line. Issues verdicts. |
| **Searcher** | Writes and executes Python code (networkx, itertools, `lib/graph_utils`) to brute-force search for counterexamples across graph families. |
| **Conductor** | Rule-based scheduler: decides which agents run each round and detects convergence. No LLM call — pure logic. |
| **Formalizer** | *(on-demand)* Translates proof sketches and results into Lean 4 / Mathlib code. Never scheduled automatically — call `get_formalization_task` explicitly. |

### Knowledge Base

All findings are stored in `sessions/<session_id>.json` and persist across
restarts. The schema tracks:

- The conjecture and current status (`open` / `proved` / `disproved` / `unknown`)
- **Subproblems** – decomposed sub-questions from any agent
- **Examples** – concrete cases with a support/contradict/neutral label
- **Proof attempts** – with Checker verdicts and feedback
- **Disproof attempts** – with Checker verdicts
- **Formalization attempts** – Lean 4 code with sorry tracking, confidence, and mathlib imports
- **Log** – per-round summary from every agent

---

## Quickstart (Claude Code — no API key needed)

### 1. Install dependencies

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

### 2. Wire up the MCP server

The repo includes a `.mcp.json` that Claude Code picks up automatically.
No environment variables are needed.

### 3. Explore a conjecture

Ask Claude Code naturally:

> Start a Sophie session for: "Every even integer greater than 2 is the sum
> of two primes." Then run round 1.

Claude will call `start_session`, then `get_round_tasks`, act as each agent
in turn, and call `submit_round_results` with the responses.

To continue:

> Run another round of the Sophie session.

---

## MCP Tools

| Tool | Description |
| --- | --- |
| `start_session(conjecture)` | Create a session and return a `session_id`. Also sets it as the current session. |
| `get_round_tasks(session_id)` | Advance to the next round; returns a list of agent tasks (system prompt + user message) for Claude to execute. |
| `submit_round_results(session_id, round, results_json)` | Submit Claude's agent responses; updates the knowledge base and current session. |
| `get_session_status(session_id)` | Inspect the full knowledge base snapshot. |
| `list_sessions()` | List all saved sessions. |
| `get_formalization_task(session_id, source_id)` | Return a Formalizer task for a proof attempt or subproblem ID. Act as the Formalizer agent and pass the response to `submit_formalization`. |
| `submit_formalization(session_id, source_id, response_json)` | Store the Formalizer's Lean 4 output in the knowledge base. |

### Round workflow

```
start_session(conjecture)
  → { session_id }

get_round_tasks(session_id)
  → { round, should_stop, tasks: [{ agent, system_prompt, user_message }] }

# Claude reads each task and responds as that agent (JSON output only)

submit_round_results(session_id, round, results_json)
  → { status, summaries, resolved }

# Repeat until resolved=true or should_stop=true
```

---

## Session Viewer

Open **`sessions/viewer.html`** in any browser to see the current session
instantly — no interaction required. The viewer is automatically updated
with the latest session data after every `submit_round_results` call.

**Features:**

- Rounds timeline — collapsible, colour-coded by agent (including Formalizer in teal)
- Tabs for Examples, Subproblems, Proof Attempts, Disproof Attempts, and **Lean**
- Expandable detail cards with Checker feedback inline
- **"Open sessions folder"** button (Chrome/Edge) — lists all sessions by
  conjecture name with status badges; click any row to load it
- Drag & drop / single-file fallback for Firefox

The active session is tracked in `sessions/current.json` and highlighted
with a "current" badge in the session list.

---

## Session files

Session filenames include a short slug derived from the conjecture, e.g.:

```
sessions/20260420_100815_holroyd-talbot-conjecture-2005.json
```

This makes it easy to identify sessions in the file browser and viewer.
`sessions/current.json` always points to the most recently started or updated session.

---

## Lean 4 Formalization

Sophie can optionally formalize results in Lean 4 / Mathlib. The Formalizer
agent is never scheduled automatically — it is invoked on-demand when you want
to harden a proof sketch into verified code.

### Workflow

```
get_formalization_task(session_id, source_id)
  → { agent: "Formalizer", system_prompt, user_message }

# Act as the Formalizer: output JSON { lean_code, mathlib_imports, sorries, confidence, notes, summary }

submit_formalization(session_id, source_id, response_json)
  → { formalization_id, summary, confidence, sorry_count }
```

After each `submit_round_results`, Sophie surfaces `formalization_suggestions`
— a list of proof attempts that are strong candidates for formalization, with
reasons and previews. You can also request formalization of any proof attempt
(`PA-XXXXXX`) or subproblem (`SP-XXXXXX`) at any time.

Lean source files live in `formalization/`. The viewer's **Lean** tab shows all
formalization attempts with sorry counts, confidence badges, and full code.

---

## Reusable algorithm library (`lib/`)

Algorithms discovered or used by the Searcher are saved in `lib/graph_utils.py`
so subsequent rounds can import them without re-deriving them.

| Function | Description |
| --- | --- |
| `mu(G)` | Minimum maximal independent set size (brute force) |
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
from lib.graph_utils import mu, independent_sets_of_size, verify_ht
```

---

## Configuration

Edit `config.py` to tune:

| Setting | Default | Meaning |
| --- | --- | --- |
| `MAX_ROUNDS` | `20` | Hard cap on rounds |
| `CONVERGENCE_PATIENCE` | `3` | Rounds with no new findings before stopping |
| `KB_DIR` | `sessions/` | Where JSON session files are written |

---

## CLI (requires Anthropic API key)

A standalone terminal interface is available for running Sophie without Claude Code.
This mode makes direct API calls and requires a key:

```bash
export ANTHROPIC_API_KEY=sk-ant-...
source .venv/bin/activate
python main.py
```

CLI options:

```bash
python main.py --conjecture "..."       # skip the interactive prompt
python main.py --session 20240420_...   # resume a previous session
python main.py --rounds 5               # limit to 5 rounds
python main.py --model claude-opus-4-5  # use a specific model
```

---

## VS Code / Claude Code setup

A `.mcp.json` is included in the repo root. Claude Code picks it up
automatically when you open the project folder. No environment variables
are needed for normal use.

To inspect the MCP server interactively:

```bash
source .venv/bin/activate
mcp dev mcp_server.py
```
