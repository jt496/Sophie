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
        if self.path not in ("/set-current",):
            super().log_message(fmt, *args)

    def do_POST(self):
        if self.path != "/set-current":
            self.send_error(404)
            return

        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length)
        try:
            data = json.loads(body)
            filename = data.get("filename", "")
        except (json.JSONDecodeError, AttributeError):
            self.send_error(400, "Bad JSON")
            return

        # Validate: must be a .json file that exists in the sessions dir
        target = SESSIONS_DIR / filename
        if (
            not filename
            or not filename.endswith(".json")
            or "/" in filename
            or not target.exists()
        ):
            self.send_error(400, "Invalid filename")
            return

        try:
            with open(target) as f:
                d = json.load(f)
            session_id = d.get("session_id")
            if not session_id:
                raise ValueError("No session_id in file")

            # Write current.json
            current_path = SESSIONS_DIR / "current.json"
            with open(current_path, "w") as f:
                json.dump({"session_id": session_id}, f)

            # Regenerate manifest.json
            skip = {"current.json", "manifest.json"}
            entries = []
            for fname in sorted(os.listdir(SESSIONS_DIR), reverse=True):
                if not fname.endswith(".json") or fname in skip:
                    continue
                fpath = SESSIONS_DIR / fname
                try:
                    with open(fpath) as f:
                        fd = json.load(f)
                    if not fd.get("session_id"):
                        continue
                    entries.append({
                        "filename": fname,
                        "session_id": fd["session_id"],
                        "conjecture": fd.get("conjecture", ""),
                        "status": fd.get("status", "open"),
                        "rounds_completed": fd.get("rounds_completed", 0),
                        "current": fd["session_id"] == session_id,
                    })
                except Exception:
                    pass
            manifest_path = SESSIONS_DIR / "manifest.json"
            with open(manifest_path, "w") as f:
                json.dump(entries, f, indent=2)

            resp = json.dumps({"ok": True, "session_id": session_id}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(resp)))
            self.end_headers()
            self.wfile.write(resp)
            print(f"[Sophie] Current session → {session_id}")

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
