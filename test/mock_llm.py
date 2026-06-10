#!/usr/bin/env python3
"""Mock OpenAI-compatible chat backend for the Qed chat screenshot test.

- Serves the static build (the transpiled bundle + index.html).
- POST /v1/chat/completions streams a canned reply as Server-Sent Events in the
  OpenAI `chat.completions` streaming shape, token by token, then `[DONE]`.

Usage: mock_llm.py [port] [dir]
"""
import http.server
import json
import os
import sys
import time
from http.server import ThreadingHTTPServer

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8124
DIR = sys.argv[2] if len(sys.argv) > 2 else "."

# Keep this in sync with the test's expected text.
REPLY = "Hello! I am a mock LLM, streaming this reply token by token."


def tokenize(s):
    """Split into word-ish tokens (keeping trailing spaces) so it streams."""
    out, cur = [], ""
    for ch in s:
        cur += ch
        if ch == " ":
            out.append(cur)
            cur = ""
    if cur:
        out.append(cur)
    return out


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=DIR, **k)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def log_message(self, *a):
        pass

    def do_GET(self):
        if self.path == "/__build_id":  # live-reload poll — keep it quiet
            body = b"test"
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        super().do_GET()

    def do_POST(self):
        if self.path.rstrip("/") != "/v1/chat/completions":
            self.send_error(404)
            return
        length = int(self.headers.get("Content-Length", "0"))
        self.rfile.read(length)  # consume (and ignore) the request — it's a mock

        # Close the connection at end of stream so the browser's reader sees EOF
        # (that EOF is what fires the client's end-of-stream / `done`).
        self.close_connection = True
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Connection", "close")
        self.end_headers()

        def emit(obj):
            self.wfile.write(("data: " + json.dumps(obj) + "\n\n").encode())
            self.wfile.flush()

        for tok in tokenize(REPLY):
            emit({"choices": [{"delta": {"content": tok}}]})
            time.sleep(0.03)
        emit({"choices": [{"delta": {}, "finish_reason": "stop"}]})
        self.wfile.write(b"data: [DONE]\n\n")
        self.wfile.flush()


with ThreadingHTTPServer(("", PORT), Handler) as httpd:
    print(f"mock-llm → http://localhost:{PORT}  (serving {DIR})", flush=True)
    httpd.serve_forever()
