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
   │  get_round_tasks()    get_agent_task()    submit_agent_result()  │
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
| **Searcher** | Writes and executes Python code (networkx, sympy, itertools, etc.) to brute-force search for counterexamples. |
| **Researcher** | Searches the mathematical literature and the web (Wikipedia, arXiv, MathOverflow, OEIS) for prior results, known partial proofs, and relevant techniques. Runs on round 3 (initial survey), then every 6th round, or whenever the session stagnates for 2+ rounds. |
| **Conductor** | Rule-based scheduler: decides which agents run each round and detects convergence. No LLM call — pure logic. |
| **Formalizer** | *(on-demand)* Translates proof sketches and results into Lean 4 / Mathlib code. Each formalization is recorded as its own round in the session timeline. Never scheduled automatically — call `get_formalization_task` explicitly. |

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

Claude will call `start_session`, then `get_round_tasks`, fetch each agent's
prompts with `get_agent_task`, act as that agent, and call `submit_agent_result`
immediately after each one (results are persisted one by one, so a token-exhaustion
restart can resume mid-round).

To continue:

> Run another round of the Sophie session.

---

## MCP Tools

| Tool | Description |
| --- | --- |
| `start_session(conjecture)` | Create a session and return a `session_id`. Also sets it as the current session. |
| `get_round_tasks(session_id?)` | Return the compact agent list for the current (or next) round: `{round, agents_pending, agents_completed, resumed}`. If a round is in progress after a restart, returns only remaining agents. |
| `get_agent_task(agent_name, session_id?)` | Return the `system_prompt` and `user_message` for one agent. Call once per agent in `agents_pending`. |
| `submit_agent_result(agent_name, response_json, session_id?)` | Persist one agent's result immediately. Finalizes the round automatically when the last agent reports. |
| `submit_round_results(session_id, round, results_json)` | *(Legacy)* Submit all agent responses for a round in one batch. Prefer `submit_agent_result` for crash-safe incremental submission. |
| `get_session_status(session_id?)` | Inspect the full knowledge base snapshot. |
| `list_sessions()` | List all saved sessions. |
| `refresh_viewer(session_id?)` | Update `sessions/manifest.json` and `current.json`. Call after every completed round. |
| `add_fact(text, session_id?)` | Inject a verified fact as ground truth shown to every agent every round. Returns a `FT-XXXXXX` ID. |
| `remove_fact(fact_id, session_id?)` | Remove a previously injected fact by its ID. |
| `get_formalization_task(source_id, session_id?)` | Return a Formalizer task for a proof attempt (`PA-XXXXXX`) or subproblem (`SP-XXXXXX`) ID. Act as the Formalizer agent and pass the response to `submit_formalization`. |
| `submit_formalization(source_id, response_json, session_id?)` | Store the Formalizer's Lean 4 output in the knowledge base and write it to `formalization/`. |
| `prune_session(session_id?)` | Archive low-value KB entries to reduce context size: caps examples, trims resolved subproblems, removes old flawed attempts, and compresses the log. |

### Round workflow

```
start_session(conjecture)
  → { session_id }

get_round_tasks(session_id?)
  → { round, should_stop, agents_pending, agents_completed, resumed }

# For each agent in agents_pending:

  get_agent_task(agent_name, session_id?)
    → { agent, system_prompt, user_message }

  # Claude acts as that agent and produces JSON

  submit_agent_result(agent_name, response_json, session_id?)
    → { agent, summary, round_complete, agents_remaining, status, resolved }

refresh_viewer(session_id?)         ← call after round_complete=true

# Repeat until resolved=true or should_stop=true
#
# If tokens run out mid-round, call get_round_tasks again:
#   resumed=true, agents_completed shows what's done, agents_pending shows what's left
```

---

## Session Viewer

Serve the `sessions/` directory over HTTP and open `viewer.html` in any browser:

```bash
python sophie/serve.py        # default port 8765
# then open http://localhost:8765/viewer.html
```

The viewer reads `manifest.json` (auto-generated by `refresh_viewer`) to list
all sessions and loads the current one automatically. No drag-and-drop or
folder-picker interaction required. `serve.py` also exposes a `POST /set-current`
endpoint so clicking any session in the list updates `current.json` on disk.

**Features:**

- Session list — all sessions shown with conjecture, status badge, and round count;
  click any row to load it and promote it to "current" (updates `current.json` via `serve.py`)
- Rounds timeline — collapsible, colour-coded by agent (including Formalizer in teal)
- Tabs for Examples, Subproblems, Proof Attempts, Disproof Attempts, and **Lean**
- Expandable detail cards with Checker feedback inline
- **"Open sessions folder"** button (Chrome/Edge) — alternative to the HTTP server
- Drag & drop / single-file fallback for Firefox

`sessions/current.json` tracks the active session (updated after every
`submit_agent_result` or `refresh_viewer` call) and is highlighted with a
"current" badge in the session list.

`sessions/manifest.json` is regenerated automatically; call the `refresh_viewer`
tool to force a rebuild if needed.

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

### Install Lean and fetch Mathlib cache

1. Install Lean using the official instructions:
  https://lean-lang.org/install/
2. From this repo, enter the formalization project directory and fetch cached
  build artifacts:

```bash
cd formalization
lake exe cache get
```

This avoids rebuilding all of Mathlib locally and makes first-time checks much
faster.

### Workflow

```
get_formalization_task(source_id, session_id?)
  → { agent: "Formalizer", system_prompt, user_message }

# Act as the Formalizer: output JSON { lean_code, mathlib_imports, sorries, confidence, notes, summary }

submit_formalization(source_id, response_json, session_id?)
  → { formalization_id, summary, confidence, sorry_count }
```

After each round completes, Sophie surfaces `formalization_suggestions`
— a list of proof attempts that are strong candidates for formalization, with
reasons and previews. You can also request formalization of any proof attempt
(`PA-XXXXXX`) or subproblem (`SP-XXXXXX`) at any time.

Lean source files live in `formalization/`. The viewer's **Lean** tab shows all
formalization attempts with sorry counts, confidence badges, and full code.

---

## Configuration

Edit `sophie/config.py` to tune:

| Setting | Default | Meaning |
| --- | --- | --- |
| `MAX_ROUNDS` | `200` | Hard cap on rounds |
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
