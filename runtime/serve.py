#!/usr/bin/env python3
"""Static server for a Qed build.

Sends the COOP/COEP headers the `-pthread` WASM build needs for SharedArrayBuffer.
Usage: `serve.py [port] [dir]` (dir defaults to this file's directory).
"""
import http.server
import os
import socketserver
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
DIR = sys.argv[2] if len(sys.argv) > 2 else os.path.dirname(os.path.abspath(__file__))
os.chdir(DIR)


class Handler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Embedder-Policy", "require-corp")
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def log_message(self, *args):
        pass


with socketserver.TCPServer(("", PORT), Handler) as httpd:
    print(f"Qed → http://localhost:{PORT}  (serving {DIR})")
    httpd.serve_forever()
