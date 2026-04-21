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
        "5. refresh_viewer(session_id) → ALWAYS call after submit_round_results\n"
        "6. Repeat steps 2-5 until should_stop=true or resolved=true\n"
        "7. Use get_session_status at any time to inspect progress."
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


def _set_current_session(session_id: str) -> None:
    current_path = os.path.join(config.KB_DIR, "current.json")
    with open(current_path, "w") as f:
        json.dump({"session_id": session_id}, f)
    _write_manifest(current_id=session_id)


def _write_manifest(current_id: str | None = None) -> None:
    kb_dir = config.KB_DIR
    skip = {"current.json", "manifest.json"}
    entries = []
    for fname in sorted(os.listdir(kb_dir), reverse=True):
        if not fname.endswith(".json") or fname in skip:
            continue
        fpath = os.path.join(kb_dir, fname)
        try:
            with open(fpath) as f:
                d = json.load(f)
            if not d.get("session_id"):
                continue
            entries.append({
                "filename": fname,
                "session_id": d["session_id"],
                "conjecture": d.get("conjecture", ""),
                "status": d.get("status", "open"),
                "rounds_completed": d.get("rounds_completed", 0),
                "current": d["session_id"] == current_id,
            })
        except Exception:
            pass
    manifest_path = os.path.join(kb_dir, "manifest.json")
    with open(manifest_path, "w") as f:
        json.dump(entries, f, indent=2)


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
    _set_current_session(kb.session_id)
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
    _set_current_session(session_id)

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
def refresh_viewer(session_id: str) -> str:
    """
    Refresh sessions/viewer.html and sessions/current.json for a session.

    Call this after every submit_round_results to ensure the viewer is
    up to date.  This is a lightweight call — safe to invoke every round.

    Args:
        session_id: The session ID to make current and inject into the viewer.
    """
    kb_path = os.path.join(config.KB_DIR, f"{session_id}.json")
    if not os.path.exists(kb_path):
        return json.dumps({"error": f"Session '{session_id}' not found."})
    _set_current_session(session_id)
    return json.dumps({"status": "ok", "session_id": session_id})


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
# Formalization tools
# ─────────────────────────────────────────────────────────────────────────────

@mcp.tool()
def get_formalization_task(session_id: str, source_id: str) -> str:
    """
    Return the Formalizer agent task for a specific proof attempt or subproblem.

    Call this when the user asks to formalize a result.  source_id should be a
    proof attempt ID (PA-XXXXXX) or subproblem ID (SP-XXXXXX) from the session.

    Returns JSON with: agent, system_prompt, user_message.
    Read the system_prompt and user_message, respond as the Formalizer agent
    (output only the JSON block described in the system prompt), then pass the
    response to submit_formalization.

    Args:
        session_id: The session ID.
        source_id:  The ID of the proof attempt or subproblem to formalize.
    """
    from agents.formalizer import Formalizer

    kb = _load_kb(session_id)
    if kb is None:
        return json.dumps({"error": f"Session '{session_id}' not found."})

    snap = kb.snapshot()

    # Locate the source text
    source_text = None
    for pa in snap["proof_attempts"]:
        if pa["id"] == source_id:
            source_text = pa["sketch"]
            break
    if source_text is None:
        for sp in snap["subproblems"]:
            if sp["id"] == source_id:
                source_text = sp["description"]
                if sp.get("resolution"):
                    source_text += f"\n\nResolution: {sp['resolution']}"
                break
    if source_text is None:
        return json.dumps({"error": f"ID '{source_id}' not found in session '{session_id}'."})

    formalizer = Formalizer(kb)
    task = formalizer.get_formalization_task(source_id=source_id, source_text=source_text)
    return json.dumps(task)


@mcp.tool()
def submit_formalization(session_id: str, source_id: str, response_json: str) -> str:
    """
    Store the Formalizer agent's Lean 4 output in the knowledge base AND write
    it to the Lean repository under formalization/.

    The Formalizer's response must include a "lean_file" field (path relative to
    formalization/) telling us which file to write to.  If the file already
    exists the new code is appended; if not it is created and the root module
    SophieFormalization.lean is updated with the new import.

    Returns JSON with: formalization_id, lean_file, summary, confidence, sorry_count.

    Args:
        session_id:    The session ID.
        source_id:     The proof attempt or subproblem ID that was formalized.
        response_json: The Formalizer's JSON response string.
    """
    from pathlib import Path
    from agents.base_agent import BaseAgent

    kb = _load_kb(session_id)
    if kb is None:
        return json.dumps({"error": f"Session '{session_id}' not found."})

    parsed = BaseAgent._extract_json(response_json)
    if parsed.get("parse_error"):
        return json.dumps({"error": "Could not parse Formalizer response JSON."})

    lean_code: str = parsed.get("lean_code", "")
    lean_file: str = parsed.get("lean_file", "")

    # ── Write to the Lean repo ────────────────────────────────────────────────
    lean_root = Path(__file__).parent / "formalization"
    file_written: str | None = None
    if lean_file and lean_code:
        target = lean_root / lean_file
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            # Append, separated by a blank line
            existing = target.read_text(encoding="utf-8")
            target.write_text(existing.rstrip() + "\n\n" + lean_code + "\n",
                              encoding="utf-8")
        else:
            target.write_text(lean_code + "\n", encoding="utf-8")
            # Add import to root module if not already present
            root_module = lean_root / "SophieFormalization.lean"
            if root_module.exists():
                module_name = lean_file.replace("/", ".").removesuffix(".lean")
                import_line = f"import {module_name}"
                content = root_module.read_text(encoding="utf-8")
                if import_line not in content:
                    root_module.write_text(content.rstrip() + f"\nimport {module_name}\n",
                                          encoding="utf-8")
        file_written = lean_file

    # ── Store in knowledge base ───────────────────────────────────────────────
    fid = kb.add_formalization_attempt(
        source_id=source_id,
        lean_code=lean_code,
        lean_file=lean_file or "",
        mathlib_imports=parsed.get("mathlib_imports", []),
        sorries=parsed.get("sorries", []),
        confidence=parsed.get("confidence", "partial"),
        notes=parsed.get("notes", ""),
        summary=parsed.get("summary", ""),
    )
    kb.log(kb.rounds_completed, "Formalizer", parsed.get("summary", ""))
    _set_current_session(session_id)

    return json.dumps({
        "formalization_id": fid,
        "lean_file": file_written,
        "summary": parsed.get("summary", ""),
        "confidence": parsed.get("confidence", "partial"),
        "sorry_count": len(parsed.get("sorries", [])),
        "next_step": f"Use get_session_status('{session_id}') to see the full formalization.",
    })


# ─────────────────────────────────────────────────────────────────────────────
# CLI helper: refresh viewer from the command line
# ─────────────────────────────────────────────────────────────────────────────

def _cli_refresh(session_id: str | None = None) -> None:
    """Update current.json and manifest.json.  Used by refresh_viewer.py."""
    if session_id is None:
        current_path = os.path.join(config.KB_DIR, "current.json")
        if os.path.exists(current_path):
            with open(current_path) as f:
                session_id = json.load(f).get("session_id")
    if session_id:
        _set_current_session(session_id)
        print(f"Viewer updated for session: {session_id}")
    else:
        print("No session found.", file=sys.stderr)


# ─────────────────────────────────────────────────────────────────────────────
# Entry point
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    mcp.run(transport="stdio")
