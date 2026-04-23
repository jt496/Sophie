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

from sophie import config

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
SESSIONS_DIR = Path(config.KB_DIR).resolve()


class SophieHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(SESSIONS_DIR), **kwargs)

    def log_message(self, fmt, *args):  # quieter logs
        if self.path not in ("/set-current",):
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



if __name__ == "__main__":
    server = HTTPServer(("", PORT), SophieHandler)
    print(f"Sophie viewer at  http://localhost:{PORT}/viewer.html")
    print(f"Serving sessions: {SESSIONS_DIR}")
    print("Press Ctrl-C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
