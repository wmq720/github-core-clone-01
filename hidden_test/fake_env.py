import json, threading
from http.server import BaseHTTPRequestHandler, HTTPServer
port_holder = {}
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def do_POST(self):
        n = int(self.headers.get('Content-Length') or 0)
        body = self.rfile.read(n)
        print("REGISTER:", body.decode(), flush=True)
        port_holder['port'] = json.loads(body)['port']
        self.send_response(200); self.send_header('Content-Type','application/json'); self.end_headers()
        self.wfile.write(b'{}')
    def do_GET(self):
        # keep done=false so the forge keeps serving
        self.send_response(200); self.send_header('Content-Type','application/json'); self.end_headers()
        self.wfile.write(b'{"done": false}')
srv = HTTPServer(('127.0.0.1', 0), H)
print("ENV_PORT", srv.server_address[1], flush=True)
threading.Thread(target=srv.serve_forever, daemon=True).start()
import time
while True: time.sleep(3600)
