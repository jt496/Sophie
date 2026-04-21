#!/usr/bin/env python3
"""Refresh sessions/viewer.html with the current session's data.

Usage:
    python refresh_viewer.py [session_id]

If session_id is omitted, reads sessions/current.json.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from mcp_server import _cli_refresh

_cli_refresh(sys.argv[1] if len(sys.argv) > 1 else None)
