#!/usr/bin/env python3
"""
Sophie session viewer server.

Serves the sessions/ directory as static files AND handles a
POST /set-current endpoint so the viewer can promote any session
to "current" without leaving the browser.

Usage:
    python serve.py [port]          # default port 8765

Then open http://localhost:8765/viewer.html
"""

import json
import os
import re
import sys
from datetime import datetime
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path

try:
    from sophie import config  # imported as a package module
except ImportError:
    import config  # fallback when run directly from sophie/

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
SESSIONS_DIR = Path(config.KB_DIR).resolve()


class SophieHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(SESSIONS_DIR), **kwargs)

    def log_message(self, fmt, *args):  # quieter logs
        if self.path not in ("/set-current", "/ping"):
            super().log_message(fmt, *args)

    def do_GET(self):
        if self.path == "/ping":
            self._handle_ping()
        else:
            super().do_GET()

    def _handle_ping(self):
        """Return current session mtime + rounds_completed for change detection."""
        try:
            current_path = SESSIONS_DIR / "current.json"
            if not current_path.exists():
                self._json_response({"session_id": None, "mtime": 0, "rounds_completed": 0})
                return
            with open(current_path) as f:
                cur = json.load(f)
            session_id = cur.get("session_id")
            # Find the session file
            session_file = None
            for fname in os.listdir(SESSIONS_DIR):
                if not fname.endswith(".json") or fname in {"current.json", "manifest.json"}:
                    continue
                fpath = SESSIONS_DIR / fname
                try:
                    with open(fpath) as f:
                        d = json.load(f)
                    if d.get("session_id") == session_id:
                        session_file = fpath
                        rounds = d.get("rounds_completed", 0)
                        break
                except Exception:
                    pass
            if session_file is None:
                self._json_response({"session_id": session_id, "mtime": 0, "rounds_completed": 0})
                return
            mtime = session_file.stat().st_mtime
            self._json_response({"session_id": session_id, "mtime": mtime, "rounds_completed": rounds})
        except Exception as exc:
            self._json_response({"session_id": None, "mtime": 0, "rounds_completed": 0, "error": str(exc)})

    # ── helpers ──────────────────────────────────────────────────────────

    def _write_manifest(self, current_id: str | None = None) -> None:
        """Rebuild manifest.json from all session files in SESSIONS_DIR."""
        skip = {"current.json", "manifest.json"}
        entries = []
        for fname in sorted(os.listdir(SESSIONS_DIR), reverse=True):
            if not fname.endswith(".json") or fname in skip:
                continue
            fpath = SESSIONS_DIR / fname
            try:
                with open(fpath) as f:
                    fd = json.load(f)
                sid = fd.get("session_id")
                if not sid:
                    continue
                mtime = datetime.fromtimestamp(fpath.stat().st_mtime).strftime("%Y%m%d_%H%M%S")
                entries.append({
                    "filename": fname,
                    "session_id": sid,
                    "conjecture": fd.get("conjecture", ""),
                    "status": fd.get("status", "open"),
                    "rounds_completed": fd.get("rounds_completed", 0),
                    "current": sid == current_id,
                    "last_updated": mtime,
                })
            except Exception:
                pass
        with open(SESSIONS_DIR / "manifest.json", "w") as f:
            json.dump(entries, f, indent=2)

    def _json_response(self, data: dict, status: int = 200) -> None:
        resp = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(resp)))
        self.end_headers()
        self.wfile.write(resp)

    def _read_body(self) -> dict | None:
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length)
        try:
            return json.loads(body)
        except (json.JSONDecodeError, AttributeError):
            return None

    # ── POST router ──────────────────────────────────────────────────────────

    def do_POST(self):
        if self.path == "/set-current":
            self._handle_set_current()
        elif self.path == "/prune-round":
            self._handle_prune_round()
        elif self.path == "/fork-session":
            self._handle_fork_session()
        elif self.path == "/accept-proof":
            self._handle_accept_proof()
        elif self.path == "/delete-session":
            self._handle_delete_session()
        else:
            self.send_error(404)

    def _handle_set_current(self):
        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        filename = data.get("filename", "")

        target = SESSIONS_DIR / filename
        if (
            not filename
            or not filename.endswith(".json")
            or "/" in filename
            or not target.exists()
        ):
            self.send_error(400, "Invalid filename"); return

        try:
            with open(target) as f:
                d = json.load(f)
            session_id = d.get("session_id")
            if not session_id:
                raise ValueError("No session_id in file")

            with open(SESSIONS_DIR / "current.json", "w") as f:
                json.dump({"session_id": session_id}, f)

            self._write_manifest(session_id)
            self._json_response({"ok": True, "session_id": session_id})
            print(f"[Sophie] Current session \u2192 {session_id}")
        except Exception as exc:
            self.send_error(500, str(exc))

    def _handle_prune_round(self):
        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        filename = data.get("filename", "")
        round_num = data.get("round")

        if not isinstance(round_num, int) or round_num < 1:
            self.send_error(400, "Invalid round"); return

        target = SESSIONS_DIR / filename
        if not filename or not filename.endswith(".json") or "/" in filename or not target.exists():
            self.send_error(400, "Invalid filename"); return

        try:
            with open(target) as f:
                d = json.load(f)

            r = round_num
            d["log"] = [e for e in d.get("log", []) if e.get("round") != r]
            d["round_summaries"] = [rs for rs in d.get("round_summaries", []) if rs.get("round") != r]
            d["proof_attempts"] = [pa for pa in d.get("proof_attempts", []) if pa.get("round") != r]
            d["disproof_attempts"] = [da for da in d.get("disproof_attempts", []) if da.get("round") != r]
            d["examples"] = [ex for ex in d.get("examples", []) if ex.get("added_round") != r]
            d["facts"] = [f for f in d.get("facts", []) if f.get("added_round") != r]
            d["implications"] = [imp for imp in d.get("implications", []) if imp.get("added_round") != r]

            crs = d.get("current_round_state")
            if crs and crs.get("round") == r:
                d["current_round_state"] = None

            # Collect remaining round numbers and build a contiguous renumbering map
            old_rounds = sorted({
                e.get("round", 0) for e in d.get("log", [])
            } | {
                rs.get("round", 0) for rs in d.get("round_summaries", [])
            } | {
                pa.get("round", 0) for pa in d.get("proof_attempts", [])
            } | {
                da.get("round", 0) for da in d.get("disproof_attempts", [])
            } - {0})
            remap = {old: new for new, old in enumerate(old_rounds, start=1)}

            def _rr(n):  # round renumber, preserve 0 / missing
                return remap.get(n, n)

            for e in d.get("log", []):
                e["round"] = _rr(e.get("round", 0))
            for rs in d.get("round_summaries", []):
                rs["round"] = _rr(rs.get("round", 0))
            for pa in d.get("proof_attempts", []):
                pa["round"] = _rr(pa.get("round", 0))
            for da in d.get("disproof_attempts", []):
                da["round"] = _rr(da.get("round", 0))
            for ex in d.get("examples", []):
                ex["added_round"] = _rr(ex.get("added_round", 0))
            for f in d.get("facts", []):
                f["added_round"] = _rr(f.get("added_round", 0))
            for imp in d.get("implications", []):
                imp["added_round"] = _rr(imp.get("added_round", 0))

            d["rounds_completed"] = max(remap.values()) if remap else 0

            with open(target, "w") as f:
                json.dump(d, f, indent=2)

            current_id = None
            try:
                with open(SESSIONS_DIR / "current.json") as f:
                    current_id = json.load(f).get("session_id")
            except Exception:
                pass
            self._write_manifest(current_id)
            self._json_response({"ok": True, "rounds_completed": d["rounds_completed"]})
        except Exception as exc:
            self.send_error(500, str(exc))

    def _handle_fork_session(self):
        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        filename = data.get("filename", "")
        round_num = data.get("round")

        if not isinstance(round_num, int) or round_num < 0:
            self.send_error(400, "Invalid round"); return

        target = SESSIONS_DIR / filename
        if not filename or not filename.endswith(".json") or "/" in filename or not target.exists():
            self.send_error(400, "Invalid filename"); return

        try:
            with open(target) as f:
                d = json.load(f)

            r = round_num
            new_pas = [pa for pa in d.get("proof_attempts", []) if pa.get("round", 0) <= r]
            new_das = [da for da in d.get("disproof_attempts", []) if da.get("round", 0) <= r]

            # Always start the fork as open — "valid" on a proof attempt only means
            # the Checker found that attempt logically sound, not that the full conjecture
            # is resolved. The Checker sets the session status separately.
            status = "open"

            slug = re.sub(r'[^a-z0-9]+', '-', d.get("conjecture", "")[:35].lower()).strip('-')
            new_session_id = datetime.now().strftime("%Y%m%d_%H%M%S") + (f"_{slug}" if slug else "") + f"_fork_r{r}"

            new_data = {
                "conjecture": d.get("conjecture", ""),
                "session_id": new_session_id,
                "status": status,
                "rounds_completed": r,
                "no_progress_rounds": 0,
                "prev_snapshot_hash": None,
                "facts": [f for f in d.get("facts", []) if f.get("added_round", 0) <= r],
                "implications": [imp for imp in d.get("implications", []) if imp.get("added_round", 0) <= r],
                "subproblems": d.get("subproblems", []),
                "examples": [ex for ex in d.get("examples", []) if ex.get("added_round", 0) <= r],
                "proof_attempts": new_pas,
                "disproof_attempts": new_das,
                "formalization_attempts": [],
                "log": [e for e in d.get("log", []) if e.get("round", 0) <= r],
                "round_summaries": [rs for rs in d.get("round_summaries", []) if rs.get("round", 0) <= r],
                "current_round_state": None,
            }

            new_filename = f"{new_session_id}.json"
            with open(SESSIONS_DIR / new_filename, "w") as f:
                json.dump(new_data, f, indent=2)

            with open(SESSIONS_DIR / "current.json", "w") as f:
                json.dump({"session_id": new_session_id}, f)

            self._write_manifest(new_session_id)
            self._json_response({"ok": True, "session_id": new_session_id, "filename": new_filename})
            print(f"[Sophie] Forked session → {new_session_id} (round {r})")
        except Exception as exc:
            self.send_error(500, str(exc))

    def _handle_accept_proof(self):
        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        filename = data.get("filename", "")
        formalization_id = data.get("formalization_id", "")

        if not formalization_id:
            self.send_error(400, "Missing formalization_id"); return

        target = SESSIONS_DIR / filename
        if not filename or not filename.endswith(".json") or "/" in filename or not target.exists():
            self.send_error(400, "Invalid filename"); return

        try:
            with open(target) as f:
                d = json.load(f)

            fa = next(
                (f for f in d.get("formalization_attempts", []) if f["id"] == formalization_id),
                None,
            )
            if fa is None:
                self._json_response({"error": f"Formalization '{formalization_id}' not found."}, 404)
                return

            sorries = fa.get("sorries") or []
            if sorries:
                self._json_response({
                    "error": f"Cannot accept: formalization has {len(sorries)} unresolved sorry(s).",
                    "sorries": sorries,
                }, 400)
                return

            d["status"] = "proved"
            with open(target, "w") as f:
                json.dump(d, f, indent=2)

            current_id = None
            try:
                with open(SESSIONS_DIR / "current.json") as f:
                    current_id = json.load(f).get("session_id")
            except Exception:
                pass
            self._write_manifest(current_id)
            self._json_response({"ok": True, "status": "proved", "formalization_id": formalization_id})
            print(f"[Sophie] Proof accepted → {d.get('session_id')} now proved")
        except Exception as exc:
            self.send_error(500, str(exc))

    def _handle_delete_session(self):
        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        filename = data.get("filename", "")

        target = SESSIONS_DIR / filename
        if not filename or not filename.endswith(".json") or "/" in filename or not target.exists():
            self.send_error(400, "Invalid filename"); return

        try:
            with open(target) as f:
                d = json.load(f)
            deleted_id = d.get("session_id", "")

            target.unlink()

            # If this was the current session, clear current.json
            current_path = SESSIONS_DIR / "current.json"
            try:
                with open(current_path) as f:
                    current_id = json.load(f).get("session_id")
                if current_id == deleted_id:
                    current_path.unlink(missing_ok=True)
            except Exception:
                pass

            self._write_manifest(current_id=None)
            self._json_response({"ok": True, "deleted": filename})
            print(f"[Sophie] Deleted session {deleted_id}")
        except Exception as exc:
            self.send_error(500, str(exc))


if __name__ == "__main__":
    server = HTTPServer(("", PORT), SophieHandler)
    print(f"Sophie viewer at  http://localhost:{PORT}/viewer.html")
    print(f"Serving sessions: {SESSIONS_DIR}")
    print("Press Ctrl-C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
