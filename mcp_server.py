"""
Sophie MCP Server – exposes the conjecture exploration framework as MCP tools
for Claude Code (Claude Pro) to use without a separate Anthropic API key.

How it works
------------
The MCP server manages persistent session state (the knowledge base) and
builds the prompts for each agent role.  Claude Code itself acts as every
agent — no LLM calls are made inside the server.

Typical workflow
----------------
1. start_session(conjecture)          → session_id
2. get_round_tasks(session_id)        → {round, tasks, should_stop, ...}
   [Claude reads each task's system_prompt + user_message and responds as
    that agent, producing the required JSON output]
3. submit_round_results(session_id, round, results_json)
                                      → {status, summaries, resolved}
4. Repeat steps 2–3 until should_stop or resolved is true.
5. get_session_status(session_id)     → full KB snapshot at any time.

Running
-------
  .venv/bin/python mcp_server.py
"""

from __future__ import annotations

import glob
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path

from mcp.server.fastmcp import FastMCP

sys.path.insert(0, str(Path(__file__).parent))

import config
from conductor import Conductor
from knowledge_base import KnowledgeBase

mcp = FastMCP(
    name="Sophie",
    instructions=(
        "Sophie is a multi-agent mathematical conjecture explorer that runs "
        "entirely inside Claude Code — no external API key required.\n\n"
        "Workflow:\n"
        "1. start_session(conjecture) → get a session_id\n"
        "2. get_round_tasks(session_id) → receive a list of agent tasks\n"
        "3. For each task, read system_prompt + user_message and respond as "
        "that agent (output only valid JSON matching the agent's format)\n"
        "4. submit_round_results(session_id, round, results_json) → update KB\n"
        "5. Repeat until should_stop=true or resolved=true\n"
        "6. Use get_session_status at any time to inspect progress."
    ),
)


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def _format_snapshot(snap: dict) -> str:
    lines = [
        f"CONJECTURE: {snap['conjecture']}",
        f"STATUS:     {snap['status'].upper()}",
        f"ROUNDS:     {snap['rounds_completed']}",
        f"SESSION ID: {snap['session_id']}",
        "",
        "── SUBPROBLEMS ──────────────────────────────────────────",
    ]
    for sp in snap["subproblems"]:
        flag = "✓" if sp["status"] == "resolved" else "○"
        lines.append(f"  [{flag}] {sp['id']}: {sp['description']}")
        if sp.get("resolution"):
            lines.append(f"        Resolution: {sp['resolution']}")

    lines += ["", "── EXAMPLES ─────────────────────────────────────────────"]
    for ex in snap["examples"]:
        sup = {True: "supports", False: "contradicts", None: "neutral"}.get(
            ex["supports_conjecture"], "?"
        )
        lines.append(f"  {ex['id']} [{sup}]: {ex['description']}")
        lines.append(f"    {ex['detail'][:200]}")

    lines += ["", "── PROOF ATTEMPTS ───────────────────────────────────────"]
    for pa in snap["proof_attempts"]:
        lines.append(f"  {pa['id']} [{pa['status']}]:")
        lines.append(f"    {pa['sketch'][:300]}")
        if pa.get("checker_feedback"):
            lines.append(f"    Checker: {pa['checker_feedback'][:200]}")

    lines += ["", "── DISPROOF ATTEMPTS ────────────────────────────────────"]
    for da in snap["disproof_attempts"]:
        lines.append(f"  {da['id']} [{da['status']}]:")
        lines.append(f"    {da['candidate_counterexample'][:300]}")
        if da.get("checker_feedback"):
            lines.append(f"    Checker: {da['checker_feedback'][:200]}")

    lines += ["", "── RECENT LOG ───────────────────────────────────────────"]
    for entry in snap["log"][-10:]:
        lines.append(f"  [round {entry['round']}] {entry['agent']}: {entry['summary']}")

    return "\n".join(lines)


def _slugify(text: str, max_len: int = 40) -> str:
    text = text.lower()
    text = re.sub(r'[^a-z0-9\s]', ' ', text)
    text = re.sub(r'\s+', '-', text.strip())
    return text[:max_len].rstrip('-')


def _load_kb(session_id: str) -> KnowledgeBase | None:
    kb_path = os.path.join(config.KB_DIR, f"{session_id}.json")
    if not os.path.exists(kb_path):
        return None
    return KnowledgeBase(session_id=session_id)


# ─────────────────────────────────────────────────────────────────────────────
# Tools
# ─────────────────────────────────────────────────────────────────────────────

@mcp.tool()
def start_session(conjecture: str) -> str:
    """
    Create a new exploration session for a conjecture.

    Returns the session_id and instructions for the next step.

    Args:
        conjecture: The mathematical statement to investigate.
    """
    slug = _slugify(conjecture.strip())
    session_id = datetime.now().strftime("%Y%m%d_%H%M%S") + (f"_{slug}" if slug else "")
    kb = KnowledgeBase(session_id=session_id)
    kb.set_conjecture(conjecture.strip())
    return json.dumps({
        "session_id": kb.session_id,
        "file": kb.path(),
        "next_step": f"Call get_round_tasks('{kb.session_id}') to begin round 1.",
    })


@mcp.tool()
def get_round_tasks(session_id: str) -> str:
    """
    Advance to the next round and return the agent tasks for Claude to execute.

    For each task in the returned list, read the system_prompt and
    user_message, then respond as that agent (output only the JSON block
    described in the system prompt).  Collect all responses and pass them
    to submit_round_results.

    Returns JSON with: session_id, round, should_stop, stop_reason, tasks.
    Each task: {agent, system_prompt, user_message}.

    Args:
        session_id: The session ID returned by start_session.
    """
    kb = _load_kb(session_id)
    if kb is None:
        return json.dumps({"error": f"Session '{session_id}' not found."})

    conductor = Conductor(kb)
    result = conductor.get_round_tasks()
    return json.dumps(result)


@mcp.tool()
def submit_round_results(session_id: str, round: int, results_json: str) -> str:
    """
    Submit the agent responses for a completed round.

    results_json must be a JSON array where each element has:
      {"agent": "<AgentName>", "response_json": "<the JSON string the agent produced>"}

    Returns JSON with: status, summaries, resolved, next_step.

    Args:
        session_id:   The session ID.
        round:        The round number (as returned by get_round_tasks).
        results_json: JSON-encoded array of agent results.
    """
    kb = _load_kb(session_id)
    if kb is None:
        return json.dumps({"error": f"Session '{session_id}' not found."})

    try:
        results = json.loads(results_json)
    except json.JSONDecodeError as e:
        return json.dumps({"error": f"Invalid results_json: {e}"})

    conductor = Conductor(kb)
    outcome = conductor.process_results(round, results)

    if outcome["resolved"]:
        outcome["next_step"] = (
            f"Conjecture {outcome['status'].upper()}. "
            f"Call get_session_status('{session_id}') for the full report."
        )
    else:
        outcome["next_step"] = (
            f"Call get_round_tasks('{session_id}') to continue, "
            "or get_session_status to inspect progress."
        )

    return json.dumps(outcome)


@mcp.tool()
def get_session_status(session_id: str) -> str:
    """
    Return a detailed snapshot of a session's knowledge base.

    Args:
        session_id: The session ID to inspect.
    """
    kb = _load_kb(session_id)
    if kb is None:
        return f"Error: session '{session_id}' not found."
    return _format_snapshot(kb.snapshot())


@mcp.tool()
def list_sessions() -> str:
    """
    List all saved Sophie sessions with their conjecture, status, and round count.
    """
    Path(config.KB_DIR).mkdir(parents=True, exist_ok=True)
    files = sorted(glob.glob(os.path.join(config.KB_DIR, "*.json")), reverse=True)

    if not files:
        return json.dumps({"result": "No sessions found."})

    sessions = []
    for f in files:
        try:
            with open(f) as fh:
                data = json.load(fh)
            sessions.append({
                "session_id": data.get("session_id", Path(f).stem),
                "status":     data.get("status", "?"),
                "rounds":     data.get("rounds_completed", 0),
                "conjecture": data.get("conjecture", "")[:80],
            })
        except Exception:
            sessions.append({"session_id": Path(f).stem, "error": "unreadable"})

    return json.dumps(sessions)


# ─────────────────────────────────────────────────────────────────────────────
# Entry point
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    mcp.run(transport="stdio")
