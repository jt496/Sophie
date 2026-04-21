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
import sys
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import config

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
SESSIONS_DIR = Path(config.KB_DIR).resolve()


class SophieHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(SESSIONS_DIR), **kwargs)

    def log_message(self, fmt, *args):  # quieter logs
        if self.path not in ("/set-current", "/new-session"):
            super().log_message(fmt, *args)

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
                entries.append({
                    "filename": fname,
                    "session_id": sid,
                    "conjecture": fd.get("conjecture", ""),
                    "status": fd.get("status", "open"),
                    "rounds_completed": fd.get("rounds_completed", 0),
                    "current": sid == current_id,
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
        elif self.path == "/new-session":
            self._handle_new_session()
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

    def _handle_new_session(self):
        import re
        from datetime import datetime

        data = self._read_body()
        if data is None:
            self.send_error(400, "Bad JSON"); return
        conjecture = (data.get("conjecture") or "").strip()
        if not conjecture:
            self._json_response({"error": "conjecture is required"}, 400); return

        # Build a session_id: timestamp + slug
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        slug = re.sub(r'[^a-z0-9]+', '_', conjecture.lower())[:40].strip('_')
        session_id = f"{ts}_{slug}" if slug else ts
        filename = f"{session_id}.json"
        target = SESSIONS_DIR / filename

        stub = {
            "session_id": session_id,
            "conjecture": conjecture,
            "status": "open",
            "rounds_completed": 0,
            "round_summaries": [],
            "proof_attempts": [],
            "disproofs": [],
        }
        with open(target, "w") as f:
            json.dump(stub, f, indent=2)

        # Read current session_id to preserve current flag
        current_id = None
        try:
            with open(SESSIONS_DIR / "current.json") as f:
                current_id = json.load(f).get("session_id")
        except Exception:
            pass

        self._write_manifest(current_id)
        self._json_response({"ok": True, "session_id": session_id, "filename": filename})
        print(f"[Sophie] New session created: {session_id}")


if __name__ == "__main__":
    server = HTTPServer(("", PORT), SophieHandler)
    print(f"Sophie viewer at  http://localhost:{PORT}/viewer.html")
    print(f"Serving sessions: {SESSIONS_DIR}")
    print("Press Ctrl-C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
