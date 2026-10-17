"""Controlled mechanical MCP peer for isolated checkpoint pilots, never Lean.

The existing server.command seam invokes this file inside a newly isolated OS.
It never imports controller code, invents registry ownership or signals unrelated
processes. Request/response bytes and real bounded descendant lifetimes are fixture
evidence; its positive diagnostics do not establish a theorem or real build.
"""
from __future__ import annotations

import argparse
import datetime
import faulthandler
import hashlib
import json
import os
from pathlib import Path
import secrets
import math
import re
import signal
import stat
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


def append_record(path: Path, record: dict) -> None:
    data = (json.dumps(record, sort_keys=True) + "\n").encode()
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        if os.write(fd, data) != len(data):
            raise RuntimeError("incomplete native peer evidence write")
        os.fsync(fd)
    finally:
        os.close(fd)


def startup_remaining(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise RuntimeError("native fixture recursive startup deadline expired")
    return remaining


def native_identity(pid: int, deadline: float) -> dict:
    """Linux pilot identity from actual argv, birth ticks, parent and native ps."""
    startup_remaining(deadline)
    base = Path('/proc') / str(pid)
    def bounded(path):
        startup_remaining(deadline)
        with path.open('rb') as stream:
            value = stream.read(65537)
        if len(value) > 65536:
            raise RuntimeError("native fixture process identity exceeds bound")
        return value
    before = bounded(base/'stat').decode().rsplit(')', 1)[1].split()
    argv = bounded(base/'cmdline')
    if len(before) < 20 or not argv.endswith(b'\0') or not argv[:-1]:
        raise RuntimeError("native fixture process identity incomplete")
    result = subprocess.run(['ps','-p',str(pid),'-o','lstart='], capture_output=True, text=True,
                            timeout=min(2.0, startup_remaining(deadline)),
                            env={**os.environ,'LC_ALL':'C'})
    startup_remaining(deadline)
    birth = result.stdout.strip()
    if result.returncode or result.stderr.strip() or len(birth) > 64:
        raise RuntimeError("native fixture birth observation unavailable")
    datetime.datetime.strptime(birth, '%a %b %d %H:%M:%S %Y')
    after = bounded(base/'stat').decode().rsplit(')', 1)[1].split()
    if (before[1],before[19]) != (after[1],after[19]):
        raise RuntimeError("native fixture process identity changed during observation")
    return {'pid':pid,'ppid':int(after[1]),'birth':birth,'start_ticks':after[19],
            'argv':[os.fsdecode(value) for value in argv[:-1].split(b'\0')]}


def publish_startup(path: Path, value: dict, deadline: float) -> None:
    startup_remaining(deadline)
    payload = (json.dumps(value,sort_keys=True)+'\n').encode()
    if len(payload) > 65536:
        raise RuntimeError("native fixture startup acknowledgment exceeds bound")
    fd = os.open(path, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
    try:
        if os.write(fd,payload) != len(payload):
            raise RuntimeError("native fixture startup acknowledgment incomplete")
        os.fsync(fd)
    finally:
        os.close(fd)
    parent = os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try: os.fsync(parent)
    finally: os.close(parent)
    startup_remaining(deadline)


def read_startup(path: Path, deadline: float) -> dict:
    startup_remaining(deadline)
    fd = os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        info=os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink!=1 or info.st_uid!=os.getuid() or info.st_mode&0o077 or info.st_size>65536:
            raise RuntimeError("native fixture startup acknowledgment is untrusted")
        value=os.read(fd,65537)
        if len(value)>65536:
            raise RuntimeError("native fixture startup acknowledgment exceeds bound")
    finally: os.close(fd)
    startup_remaining(deadline)
    parsed=json.loads(value)
    if not isinstance(parsed,dict):raise RuntimeError("native fixture startup acknowledgment is not an object")
    return parsed


def child_argv(args, level: str, generation: str, deadline: float) -> list[str]:
    return [sys.executable,'-B',str(Path(__file__).resolve()),'--fixture-child',level,
            '--lean-project-path',str(args.lean_project_path),'--control-dir',str(args.control_dir),
            '--fixture-generation',generation,'--fixture-startup-deadline',repr(deadline),
            '--fixture-leaf-delay',repr(args.fixture_leaf_delay),
            '--fixture-middle-delay',repr(args.fixture_middle_delay),
            '--fixture-startup-timeout',repr(args.fixture_startup_timeout),
            *(['--fixture-late-child'] if args.fixture_late_child else [])]


def wait_startup(control: Path, level: str, generation: str, child, argv: list[str],
                 parent: int, deadline: float, stopped) -> dict:
    path=control/f'startup-{generation}-{level}.json'
    while True:
        startup_remaining(deadline)
        if stopped() or child.poll() is not None:
            raise RuntimeError("native fixture owned startup child exited or parent stopped")
        try: value=read_startup(path,deadline)
        except FileNotFoundError:
            time.sleep(min(0.01,startup_remaining(deadline)));continue
        if value.get('generation')!=generation or value.get('node')!=level:
            raise RuntimeError("native fixture startup generation/node mismatch")
        actual=native_identity(child.pid,deadline)
        if value.get('identity')!=actual or actual['ppid']!=parent or actual['argv']!=argv:
            raise RuntimeError("native fixture startup PID/birth/argv/parent mismatch")
        return value


def validate_leaf(value: dict, args, generation: str, parent: int, deadline: float) -> None:
    if value.get('generation')!=generation or value.get('node')!='leaf':
        raise RuntimeError("native fixture recursive leaf acknowledgment mismatch")
    wanted=value.get('identity',{})
    if type(wanted.get('pid')) is not int:
        raise RuntimeError("native fixture recursive leaf lacks PID")
    actual=native_identity(wanted['pid'],deadline)
    if wanted!=actual or actual['ppid']!=parent or actual['argv']!=child_argv(args,'leaf',generation,deadline):
        raise RuntimeError("native fixture recursive leaf identity mismatch")


def startup_pause(seconds: float, deadline: float, stopped) -> None:
    until=time.monotonic()+seconds
    while time.monotonic()<until:
        if stopped():raise RuntimeError("native fixture startup stopped")
        time.sleep(max(0.0,min(0.01,startup_remaining(deadline),until-time.monotonic())))
    startup_remaining(deadline)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transport", choices=("streamable-http",), default="streamable-http")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int)
    parser.add_argument("--lean-project-path", type=Path, required=True)
    parser.add_argument("--disable-tools", default="lean_build")
    parser.add_argument("--instructions", default="controlled mechanical peer, not Lean")
    parser.add_argument("--control-dir", type=Path, required=True)
    parser.add_argument("--fixture-descendants", action="store_true")
    parser.add_argument("--fixture-child", choices=("middle", "leaf"))
    parser.add_argument("--fixture-generation")
    parser.add_argument("--fixture-startup-deadline",type=float)
    parser.add_argument("--fixture-startup-timeout",type=float,default=5.0)
    parser.add_argument("--fixture-leaf-delay",type=float,default=0.0)
    parser.add_argument("--fixture-middle-delay",type=float,default=0.0)
    parser.add_argument("--fixture-late-child",action="store_true",help="Explicit negative control: withhold leaf until after graph freeze")
    args = parser.parse_args()
    if args.host != "127.0.0.1" or args.lean_project_path.resolve(strict=True) != args.lean_project_path:
        parser.error("native fixture requires exact local project/loopback")
    control = args.control_dir
    control.mkdir(parents=True, exist_ok=True)
    if any(not math.isfinite(value) or value<0 for value in (args.fixture_leaf_delay,args.fixture_middle_delay)) or not 0<args.fixture_startup_timeout<=10:
        parser.error("native fixture startup bounds invalid")
    if args.fixture_child:
        if not isinstance(args.fixture_generation,str) or not re.fullmatch(r'[0-9a-f]{32}',args.fixture_generation) or args.fixture_startup_deadline is None or not math.isfinite(args.fixture_startup_deadline):
            parser.error("native fixture child requires exact launch generation/deadline")
        generation=args.fixture_generation;startup_deadline=args.fixture_startup_deadline
    else:
        if args.fixture_generation is not None or args.fixture_startup_deadline is not None:
            parser.error("native fixture root creates its own fresh launch generation")
        generation=secrets.token_hex(16);startup_deadline=time.monotonic()+args.fixture_startup_timeout
    # A Python signal handler must not acquire Event's condition lock: it may
    # interrupt that same thread while the non-reentrant lock is held.
    stopping = False
    def stopped(*_):
        nonlocal stopping
        stopping = True
    for value in (signal.SIGTERM, signal.SIGINT):
        signal.signal(value, stopped)
    faulthandler.register(signal.SIGUSR1)
    label = args.fixture_child or "root"
    descriptors = {}
    directory = Path("/proc/self/fd")
    if directory.exists():
        for path in directory.iterdir():
            try:
                descriptors[path.name] = os.readlink(path)
            except FileNotFoundError:
                pass
    append_record(control / "native-nodes.jsonl", {"pid": os.getpid(), "ppid": os.getppid(),
        "node": label, "argv": sys.argv, "opened_descriptors": descriptors,
        "recorded_at_unix": time.time(), "fixture_peer_not_Lean": True,
        "startup_generation":generation})
    child = None
    try:
        if args.fixture_child=='middle':startup_pause(args.fixture_middle_delay,startup_deadline,lambda:stopping)
        if args.fixture_child=='leaf':startup_pause(args.fixture_leaf_delay,startup_deadline,lambda:stopping)
        recursive=[]
        if args.fixture_descendants or args.fixture_child=='middle' and not args.fixture_late_child:
            level='middle' if not args.fixture_child else 'leaf'
            argv=child_argv(args,level,generation,startup_deadline)
            child=subprocess.Popen(argv,stdin=subprocess.DEVNULL,close_fds=True)
            ready=wait_startup(control,level,generation,child,argv,os.getpid(),startup_deadline,lambda:stopping)
            recursive=[ready]
            if level=='middle' and not args.fixture_late_child:
                if len(ready.get('children',[]))!=1:raise RuntimeError("native fixture middle lacks recursive leaf")
                validate_leaf(ready['children'][0],args,generation,child.pid,startup_deadline)
        publish_startup(control/f'startup-{generation}-{label}.json',
                        {'generation':generation,'node':label,'identity':native_identity(os.getpid(),startup_deadline),
                         'children':recursive,'negative_late_child_pending':args.fixture_late_child},startup_deadline)
    except BaseException:
        if child is not None and child.poll() is None:
            child.terminate();child.wait(timeout=5)
        raise
    deadline = time.monotonic() + 300
    if args.fixture_child:
        while not stopping and time.monotonic() < deadline:
            time.sleep(0.05)
            if args.fixture_child=='middle' and args.fixture_late_child and child is None and (control/f'release-late-child-{generation}').exists():
                late_deadline=time.monotonic()+args.fixture_startup_timeout
                argv=child_argv(args,'leaf',generation,late_deadline)
                child=subprocess.Popen(argv,stdin=subprocess.DEVNULL,close_fds=True)
                wait_startup(control,'leaf',generation,child,argv,os.getpid(),late_deadline,lambda:stopping)
            if child is not None:
                child.poll()  # Reap a genuinely exited leaf before middle stop.
        if child is not None and child.poll() is None:
            child.terminate()  # This exact handle was created by this fixture.
            child.wait(timeout=5)
        append_record(control / "native-exits.jsonl", {"pid": os.getpid(), "node": label, "at": time.time()})
        return 0
    if not args.port:
        parser.error("root fixture peer requires a port")
    token = os.environ.get("LEAN_LSP_MCP_TOKEN")
    if not token:
        parser.error("existing supervisor backend token was not supplied")
    sessions: set[str] = set()
    mutex = threading.Lock()

    class Peer(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *_):
            pass  # No authorization, capability, opaque session or tool logging.

        def reply(self, status: int, payload, request: bytes, *, session=None) -> None:
            response = json.dumps(payload).encode() if payload is not None else b""
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(response)))
            if session:
                self.send_header("Mcp-Session-Id", session)
            self.end_headers()
            self.wfile.write(response)
            append_record(control / "actual-rpc.jsonl", {"http_method": self.command, "status": status,
                "request_hex": request.hex(), "response_hex": response.hex(),
                "request_sha256": hashlib.sha256(request).hexdigest(),
                "response_sha256": hashlib.sha256(response).hexdigest(),
                "header_names": sorted(key.lower() for key in self.headers),
                "internal_capability_forwarded": bool(self.headers.get_all("X-Lean-Checkpoint-Smoke", [])),
                "completed_at_unix": time.time(), "fixture_peer_not_Lean": True})

        def handle_rpc(self) -> None:
            length = int(self.headers.get("Content-Length", "0"))
            request = self.rfile.read(length)
            if self.headers.get("Authorization") != "Bearer " + token:
                self.reply(401, {"error": {"message": "fixture authentication refused"}}, request)
                return
            try:
                value = json.loads(request) if request else {}
            except ValueError:
                self.reply(400, {"error": {"message": "fixture JSON refused"}}, request)
                return
            identifier = value.get("id")
            method = value.get("method")
            session = self.headers.get("Mcp-Session-Id")
            if method == "initialize":
                session = secrets.token_hex(16)
                with mutex:
                    sessions.add(session)
                self.reply(200, {"jsonrpc": "2.0", "id": identifier, "result": {
                    "protocolVersion": "2025-06-18", "capabilities": {"tools": {}},
                    "serverInfo": {"name": "controlled-checkpoint-native-peer-NOT-LEAN", "version": "1"}}}, request, session=session)
                return
            with mutex:
                valid_session = session in sessions
            if not valid_session:
                self.reply(400, {"jsonrpc": "2.0", "id": identifier, "error": {"code": -32602, "message": "fixture session invalid"}}, request)
                return
            if self.command == "DELETE":
                with mutex:
                    sessions.discard(session)
                self.reply(200, {"jsonrpc": "2.0", "id": identifier, "result": {}}, request)
            elif method == "notifications/initialized":
                self.reply(202, None, request)
            elif method == "tools/list":
                self.reply(200, {"jsonrpc": "2.0", "id": identifier, "result": {"tools": [{
                    "name": "lean_diagnostic_messages", "description": "Mechanical fixture only; no Lean execution",
                    "inputSchema": {"type": "object", "properties": {"file_path": {"type": "string"}}, "required": ["file_path"]}}]}}, request)
            elif method == "tools/call":
                append_record(control / "actual-starts.jsonl", {"pid": os.getpid(),
                    "request_hex": request.hex(), "request_sha256": hashlib.sha256(request).hexdigest(),
                    "started_at_unix": time.time(), "fixture_peer_not_Lean": True})
                barrier = control / "block-diagnostic"
                bounded = time.monotonic() + 15
                while barrier.exists() and not stopping and time.monotonic() < bounded:
                    time.sleep(0.025)
                retry = control / "retry-once"
                if retry.exists():
                    retry.rename(control / ("retry-consumed-" + secrets.token_hex(4)))
                    self.reply(400, {"jsonrpc": "2.0", "id": identifier, "error": {"code": -32602, "message": "fixture requested session retry"}}, request)
                    return
                successful = not (control / "fail-diagnostic").exists() and not barrier.exists()
                self.reply(200, {"jsonrpc": "2.0", "id": identifier, "result": {"isError": False,
                    "structuredContent": {"success": successful, "timed_out": barrier.exists(),
                        "items": [] if successful else [{"message": "controlled fixture diagnostic failure"}],
                        "failed_dependencies": [], "fixture_peer_not_Lean": True}}}, request)
            else:
                self.reply(200, {"jsonrpc": "2.0", "id": identifier, "result": {}}, request)

        do_POST = handle_rpc
        do_DELETE = handle_rpc
        do_GET = handle_rpc

    server = ThreadingHTTPServer((args.host, args.port), Peer)
    server.daemon_threads = True
    worker = threading.Thread(target=lambda: server.serve_forever(poll_interval=0.05), daemon=True)
    worker.start()
    try:
        while not stopping and time.monotonic() < deadline:
            time.sleep(0.025)
            if child is not None:
                child.poll()
    finally:
        server.shutdown()
        server.server_close()
        worker.join(timeout=5)
        if child is not None and child.poll() is None:
            child.terminate()
            child.wait(timeout=5)
        append_record(control / "native-exits.jsonl", {"pid": os.getpid(), "node": label, "at": time.time()})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
