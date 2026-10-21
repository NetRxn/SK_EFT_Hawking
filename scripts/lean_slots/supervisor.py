"""Deterministic local process lifecycle for fixed-root Lean MCP endpoints."""

from __future__ import annotations

import json
import ast
import errno
import secrets
import stat
import shlex
import http.client
import os
import signal
import socket
import subprocess
import sys
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

from .state import (
    SCHEMA_VERSION,
    Inventory,
    SlotError,
    atomic_json,
    canonical_digest,
    directory_lock,
    now_iso,
    observe_process,
    _observe_created_handle,
    process_snapshot,
    Observation,
    observe_path,
    observe_directory,
    MAX_JSON_BYTES,
    tool_cache_path,
    tool_list_key,
    read_json,
    sha256_bytes,
    exclusive_durable_json,
    observation_budget,
    observation_timeout,
    observe_shutdown_process,
    observe_shutdown_family,
    observe_tcp_sockets,
    signature_birth,
    _signature_command,
    _OBSERVATION_DEADLINE,
    _wire_number,
    diagnostic_stamp,
    diagnostic_span,
    diagnostic_error,
    diagnostic_text,
    bound_diagnostics,
    validate_startup_evidence,
)


def _port_observation(host: str, port: int, timeout: float = 0.15) -> Observation:
    try:
        with socket.create_connection((host, port), timeout=observation_timeout(timeout)):
            return Observation("present", target=f"{host}:{port}", operation="connect")
    except OSError as exc:
        if exc.errno == errno.ECONNREFUSED:
            return Observation("absent", detail="connection refused", errno=exc.errno,
                               target=f"{host}:{port}", operation="connect", error_class=type(exc).__name__)
        return Observation("unavailable", detail=str(exc), errno=exc.errno,
                           target=f"{host}:{port}", operation="connect", error_class=type(exc).__name__)


def _port_open(host: str, port: int, timeout: float = 0.15) -> bool:
    """Observed-only compatibility reader; never a destructive absence gate."""
    return _port_observation(host, port, timeout).state == "present"


# Source inputs describe expected launch bytes, never process memory or PID authority.
_FP_REQUIRED = frozenset({"__init__.py", "state.py", "supervisor.py", "controller.py",
                          "cli.py", "proxy.py", "claude_config.py", "host_limits.py"})
_FP_ENTRIES, _FP_DIRECTORIES, _FP_DEPTH, _FP_FILES = 4096, 256, 16, 1024
_FP_ORIGINS = _FP_FILES
_FP_TOTAL_BYTES, _FP_PATH_BYTES = 32 * 1024 * 1024, 4096


@dataclass(frozen=True)
class _RuntimePath:
    value: Path
    last: str = "source"
    parent_steps: int = 0


@dataclass(frozen=True)
class _RuntimeText:
    value: str
    last: str
    parent_steps: int


class _RuntimeSourcePass:
    """One bounded observation pass over the actual supported source inputs."""

    def __init__(self, supervisor, kind, number, command, environment):
        self.supervisor, self.inventory = supervisor, supervisor.inventory
        self.kind, self.number, self.command = kind, number, list(command)
        self.environment = dict(environment)
        self.predicted_environment = dict(environment)
        self.observations = []
        self.capabilities = {}
        self.total_bytes = 0
        self.bindings = {}
        self.path_bindings = 0
        self.selections, self.transforms = [], []

    def fail(self, target, operation, detail, exc=None):
        evidence = Observation("unavailable", target=str(target), operation=operation,
                               detail=detail, errno=getattr(exc, "errno", None),
                               error_class=type(exc).__name__ if exc else "ValueError")
        raise SlotError(f"runtime source unavailable: {detail}",
                        observations=tuple(self.observations) + (evidence,)) from exc

    def text(self, value, target):
        if isinstance(value, _RuntimeText):
            value = value.value
        if not isinstance(value, str) or any(x in value for x in ("\x00", "\r", "\n")):
            self.fail(target, "runtime-source-path", "malformed source path/value")
        try:
            if len(value.encode("utf-8")) > _FP_PATH_BYTES:
                self.fail(target, "runtime-source-path", "source path/value exceeds bound")
        except UnicodeError as exc:
            self.fail(target, "runtime-source-path", "invalid source path encoding", exc)
        return value

    def remember(self, key, value):
        if key in self.capabilities and self.capabilities[key] != value:
            self.fail(key, "runtime-source-reobserve", "input changed within source pass")
        self.capabilities[key] = value

    def canonical(self, path):
        path = Path(path)
        self.text(str(path), path)
        if not path.is_absolute():
            self.fail(path, "runtime-source-resolve", "relative/unexpanded source path unsupported")
        try:
            result = path.resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            self.fail(path, "runtime-source-resolve", "canonical path unavailable", exc)
        self.text(str(result), path)
        return result

    def path(self, path, mode=None, *, optional=False, contained=None):
        path = Path(path)
        observed = observe_path(path)
        self.observations.append(observed)
        if observed.state == "absent" and optional:
            self.remember("path:" + str(path), {"state": "absent"})
            return None
        if observed.state != "present":
            self.fail(path, "runtime-source-stat", "required path not capably present")
        try:
            native, lexical = os.stat(path), os.lstat(path)
            resolved = self.canonical(path)
        except (OSError, ValueError) as exc:
            self.fail(path, "runtime-source-stat", "native identity unavailable", exc)
        if mode is not None and stat.S_IFMT(native.st_mode) != mode:
            self.fail(path, "runtime-source-stat", "required path has wrong shape")
        if contained is not None and not resolved.is_relative_to(contained):
            self.fail(path, "runtime-source-resolve", "source link escapes package")
        identity = (native.st_dev, native.st_ino, stat.S_IFMT(native.st_mode),
                    native.st_size, native.st_mtime_ns, native.st_ctime_ns,
                    lexical.st_dev, lexical.st_ino, lexical.st_mode,
                    lexical.st_mtime_ns, lexical.st_ctime_ns, str(resolved))
        self.remember("path:" + str(path), identity)
        if (native.st_dev, native.st_ino) != (observed.identity["device"], observed.identity["inode"]):
            self.fail(path, "runtime-source-stat", "stat observations disagree")
        return resolved

    def read(self, path, *, contained=None):
        resolved = self.path(path, stat.S_IFREG, contained=contained)
        try:
            with Path(path).open("rb") as handle:
                content = handle.read(MAX_JSON_BYTES + 1)
            if len(content) > MAX_JSON_BYTES:
                self.fail(path, "runtime-source-read", "source file exceeds bounded read")
            self.total_bytes += len(content)
            if self.total_bytes > _FP_TOTAL_BYTES:
                self.fail(path, "runtime-source-read", "total source read exceeds bound")
        except OSError as exc:
            self.fail(path, "runtime-source-read", "source read unavailable", exc)
        self.path(path, stat.S_IFREG, contained=contained)
        if len(content) != self.capabilities["path:" + str(path)][3]:
            self.fail(path, "runtime-source-read", "source read is incomplete for native size")
        digest = sha256_bytes(content)
        self.remember("bytes:" + str(path), digest)
        return content, resolved

    def manifest(self, path, *, required):
        root = self.path(path, stat.S_IFDIR)
        pending, directories, identities, files = [(Path(path), 0)], 0, set(), {}
        entries_count = 0
        while pending:
            directory, depth = pending.pop()
            if depth > _FP_DEPTH:
                self.fail(directory, "runtime-source-scandir", "source depth exceeds bound")
            self.path(directory, stat.S_IFDIR, contained=root)
            inode = self.capabilities["path:" + str(directory)][:2]
            if inode in identities:
                self.fail(directory, "runtime-source-scandir", "source directory cycle/alias")
            identities.add(inode)
            directories += 1
            if directories > _FP_DIRECTORIES:
                self.fail(directory, "runtime-source-scandir", "source directory count exceeds bound")
            entries, evidence = observe_directory(directory)
            self.observations.append(evidence)
            if evidence.state != "present":
                self.fail(directory, "runtime-source-scandir", "source enumeration unavailable")
            entries_count += len(entries)
            if entries_count > _FP_ENTRIES:
                self.fail(directory, "runtime-source-scandir", "source entries exceed bound")
            self.remember("members:" + str(directory), tuple(str(p) for p in entries))
            for entry in entries:
                self.path(entry, contained=root)
                mode = self.capabilities["path:" + str(entry)][2]
                if entry.suffix == ".py" and mode != stat.S_IFREG:
                    self.fail(entry, "runtime-source-read", "nonregular Python source")
                if mode == stat.S_IFDIR:
                    pending.append((entry, depth + 1))
                elif entry.suffix == ".py":
                    key = entry.relative_to(path).as_posix()
                    if mode != stat.S_IFREG or key in files:
                        self.fail(entry, "runtime-source-read", "nonregular/duplicate Python source")
                    content, _ = self.read(entry, contained=root)
                    files[key] = sha256_bytes(content)
                    if len(files) > _FP_FILES:
                        self.fail(entry, "runtime-source-read", "Python source count exceeds bound")
        if not required.issubset(files):
            self.fail(path, "runtime-source-membership", "required initialized source missing")
        return {"root": str(root), "files": dict(sorted(files.items()))}

    def loaded_root(self):
        module = sys.modules.get(__name__)
        state_module = sys.modules.get(Inventory.__module__)
        if module is None or state_module is None or getattr(state_module, "Inventory", None) is not Inventory:
            self.fail(__name__, "runtime-source-origin", "actual loaded state identity unavailable")
        for function in (observe_path, observe_directory, observe_process, read_json):
            if sys.modules.get(function.__module__) is not state_module:
                self.fail(function.__module__, "runtime-source-origin", "loaded state functions incoherent")
        prefix = __name__.rsplit(".", 1)[0]
        origins = {}
        peers = {}
        for name, value in tuple(sys.modules.items()):
            if name == prefix or name.startswith(prefix + "."):
                peers[name] = value
                if len(peers) > _FP_ORIGINS:
                    self.fail(prefix, "runtime-source-origin", "loaded source origin count exceeds bound")
        peers[__name__], peers[Inventory.__module__] = module, state_module
        instance_module = sys.modules.get(type(self.inventory).__module__)
        if instance_module is None:
            self.fail("inventory", "runtime-source-origin", "actual inventory type origin unavailable")
        peers[type(self.inventory).__module__] = instance_module
        # Count aliases too: native origin observations must not grow beyond the
        # complete-source budget merely because one file has many loaded names.
        if len(peers) > _FP_ORIGINS:
            self.fail(prefix, "runtime-source-origin", "loaded source origin count exceeds bound")
        root = None
        for name, value in sorted(peers.items()):
            origin = getattr(value, "__file__", None)
            declared = getattr(getattr(value, "__spec__", None), "origin", None)
            if not isinstance(origin, str) or not isinstance(declared, str) or not origin.endswith(".py"):
                self.fail(name, "runtime-source-origin", "source module origin unavailable")
            actual = self.path(Path(origin), stat.S_IFREG)
            if self.canonical(declared) != actual:
                self.fail(name, "runtime-source-origin", "module spec/file origins disagree")
            if name == __name__:
                if actual.name != "supervisor.py":
                    self.fail(name, "runtime-source-origin", "supervisor source origin malformed")
                root = actual.parent
            if name == Inventory.__module__ and actual.name != "state.py":
                self.fail(name, "runtime-source-origin", "state source origin malformed")
            origins[name] = str(actual)
        if root is None or any(not Path(p).is_relative_to(root) for p in origins.values()):
            self.fail(prefix, "runtime-source-origin", "loaded package peer roots disagree")
        self.remember("loaded-origins", origins)
        return root

    def symbol(self, node, kind):
        return isinstance(node, ast.Name) and self.bindings.get(node.id) == ("symbol", kind)

    def os_method(self, node, method):
        if not isinstance(node, ast.Attribute) or node.attr != method:
            return False
        if method in {"get", "setdefault"}:
            return (isinstance(node.value, ast.Attribute) and node.value.attr == "environ"
                    and self.symbol(node.value.value, "os"))
        return method == "getenv" and self.symbol(node.value, "os")

    def expand(self, value):
        raw = self.text(str(value.value), "expanduser")
        if value.last in {"resolved", "expanded"}:
            self.fail(raw, "runtime-source-template", "reordered/repeated home transform")
        if raw.startswith("~"):
            if raw != "~" and not raw.startswith("~/"):
                self.fail(raw, "runtime-source-home", "named/unsupported tilde home")
            present = "HOME" in self.environment
            home = self.text(self.environment.get("HOME"), "HOME") if present else ""
            if not home or not Path(home).is_absolute():
                self.fail("HOME", "runtime-source-home", "required captured HOME invalid")
            canonical_home = self.path(Path(home), stat.S_IFDIR)
            expanded = home if raw == "~" else str(Path(home) / raw[2:])
            self.text(expanded, raw)
            event = {"raw": raw, "branch": "captured-home", "HOME_present": present,
                     "HOME": home, "canonical_home": str(canonical_home), "expanded": expanded}
        else:
            if not value.value.is_absolute():
                self.fail(raw, "runtime-source-home", "nonabsolute expansion unsupported")
            expanded = raw
            event = {"raw": raw, "branch": "absolute-noop", "expanded": expanded}
        self.transforms.append(event)
        return _RuntimePath(Path(expanded), "expanded", value.parent_steps)

    def value(self, node, *, depth=0, allow_expand=False):
        if depth > 64:
            self.fail("launcher", "runtime-source-template", "path expression depth exceeds bound")
        def val(x, **kw):
            return self.value(x, depth=depth + 1, **kw)
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return self.text(node.value, "launcher literal")
        if isinstance(node, ast.Name):
            if node.id == "__file__":
                return str(self.launcher)
            value = self.bindings.get(node.id)
            if isinstance(value, _RuntimePath):
                return value
            self.fail(node.id, "runtime-source-template", "unbound/nonpath expression")
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div) and isinstance(node.right, ast.Constant):
            left, right = val(node.left), val(node.right)
            if isinstance(left, _RuntimePath) and isinstance(right, str):
                return _RuntimePath(left.value / right, "derived", left.parent_steps)
        if isinstance(node, ast.Attribute) and node.attr == "parent":
            base = val(node.value)
            if isinstance(base, _RuntimePath):
                if base.parent_steps + 1 > 4:
                    self.fail("launcher", "runtime-source-template", "parent selection exceeds bound")
                return _RuntimePath(base.value.parent, "derived", base.parent_steps + 1)
        if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
                and node.value.attr == "parents" and isinstance(node.slice, ast.Constant)
                and type(node.slice.value) is int and 0 <= node.slice.value <= 4):
            base = val(node.value.value)
            if isinstance(base, _RuntimePath):
                steps = base.parent_steps + node.slice.value + 1
                if steps > 4:
                    self.fail("launcher", "runtime-source-template", "parent selection exceeds bound")
                if node.slice.value >= len(base.value.parents):
                    self.fail(base.value, "runtime-source-template", "requested parent index is unavailable")
                return _RuntimePath(base.value.parents[node.slice.value], "derived", steps)
        if isinstance(node, ast.Call) and not node.keywords:
            if self.symbol(node.func, "Path") and len(node.args) == 1:
                operand = val(node.args[0])
                if isinstance(operand, (str, _RuntimePath, _RuntimeText)):
                    provenance = isinstance(operand, (_RuntimePath, _RuntimeText))
                    value = Path(operand.value if provenance else operand)
                    if not value.is_absolute() and not str(value).startswith("~"):
                        self.fail(value, "runtime-source-template", "relative Path source unsupported")
                    return _RuntimePath(value, operand.last if provenance else "source",
                                        operand.parent_steps if provenance else 0)
            if isinstance(node.func, ast.Name) and node.func.id == "str" and len(node.args) == 1:
                operand = val(node.args[0])
                if isinstance(operand, _RuntimePath):
                    return _RuntimeText(self.text(str(operand.value), "launcher str"),
                                        operand.last, operand.parent_steps)
            if self.os_method(node.func, "get") or self.os_method(node.func, "getenv"):
                if 1 <= len(node.args) <= 2 and isinstance(node.args[0], ast.Constant):
                    key = val(node.args[0])
                    if key == "LEAN_LSP_MCP_TOKEN":
                        self.fail(key, "runtime-source-template", "token cannot select source")
                    # Python evaluates defaults eagerly even if the key is present.
                    fallback = val(node.args[1]) if len(node.args) == 2 else None
                    if isinstance(fallback, _RuntimePath):
                        self.fail(key, "runtime-source-template", "selector fallback must be a string")
                    chosen = self.predicted_environment.get(key, fallback)
                    selected_text = self.text(chosen, key)
                    self.selections.append({"key": key, "present": key in self.predicted_environment,
                                            "fallback": self.text(fallback, key) if fallback is not None else None,
                                            "selected": selected_text})
                    return chosen
            if isinstance(node.func, ast.Attribute) and not node.args:
                if node.func.attr == "resolve":
                    if isinstance(node.func.value, ast.Call) and isinstance(node.func.value.func, ast.Attribute) and node.func.value.func.attr == "expanduser":
                        base = val(node.func.value, allow_expand=True)
                    else:
                        base = val(node.func.value)
                    if isinstance(base, _RuntimePath) and base.last != "resolved":
                        result = self.canonical(base.value)
                        self.transforms.append({"raw": str(base.value), "branch": "resolve", "canonical": str(result)})
                        return _RuntimePath(result, "resolved", base.parent_steps)
                if node.func.attr == "expanduser" and allow_expand:
                    base = val(node.func.value)
                    if isinstance(base, _RuntimePath):
                        return self.expand(base)
        self.fail("launcher", "runtime-source-template", "unsupported path expression/transform")

    def bind_symbol(self, name, kind):
        if name in self.bindings or name in {"str", "SystemExit", "__file__", "__name__"}:
            self.fail(name, "runtime-source-template", "reassigned/reserved symbol")
        self.bindings[name] = ("symbol", kind)

    def guard(self, statement):
        test = statement.test
        if not (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
                and isinstance(test.operand, ast.Call) and isinstance(test.operand.func, ast.Attribute)
                and test.operand.func.attr in {"exists", "is_file"} and not test.operand.args
                and not test.operand.keywords and not statement.orelse and len(statement.body) == 1):
            self.fail("launcher", "runtime-source-template", "unsupported selected CLI guard")
        target = test.operand.func.value
        if not (isinstance(target, ast.BinOp) and isinstance(target.op, ast.Div)
                and isinstance(target.right, ast.Constant) and target.right.value == "cli.py"
                and isinstance(target.left, ast.BinOp) and isinstance(target.left.op, ast.Div)
                and isinstance(target.left.right, ast.Constant) and target.left.right.value == "lean_slots"
                and isinstance(target.left.left, ast.Name)):
            self.fail("launcher", "runtime-source-template", "guard not selected CLI")
        selected_name = target.left.left.id
        selected = self.value(target.left.left)
        self.path(selected.value / "lean_slots" / "cli.py", stat.S_IFREG)
        raised = statement.body[0]
        if not (isinstance(raised, ast.Raise) and raised.cause is None
                and isinstance(raised.exc, ast.Call) and isinstance(raised.exc.func, ast.Name)
                and raised.exc.func.id == "SystemExit" and len(raised.exc.args) == 1 and not raised.exc.keywords):
            self.fail("launcher", "runtime-source-template", "unsupported guard body")
        message = raised.exc.args[0]
        if isinstance(message, ast.Constant) and isinstance(message.value, str):
            text = message.value
        elif isinstance(message, ast.JoinedStr):
            parts = []
            for item in message.values:
                if isinstance(item, ast.Constant) and isinstance(item.value, str):
                    parts.append(item.value)
                elif (isinstance(item, ast.FormattedValue) and isinstance(item.value, ast.Name)
                      and isinstance(self.bindings.get(item.value.id), _RuntimePath)
                      and self.canonical(self.bindings[item.value.id].value) == self.canonical(selected.value)
                      and item.conversion == -1 and item.format_spec is None):
                    parts.append(str(self.bindings[item.value.id].value))
                else:
                    self.fail("launcher", "runtime-source-template", "unsupported guard f-string")
            text = "".join(parts)
        else:
            self.fail("launcher", "runtime-source-template", "unsupported guard message")
        try:
            if len(text.encode("utf-8")) > _FP_PATH_BYTES:
                self.fail("guard diagnostic", "runtime-source-template", "guard diagnostic exceeds bound")
        except UnicodeError as exc:
            self.fail("guard diagnostic", "runtime-source-template", "guard diagnostic encoding", exc)
        return {"selected": str(self.canonical(selected.value)),
                "method": test.operand.func.attr, "message": text}

    def route(self, launcher_content, loaded_root):
        try:
            tree = ast.parse(launcher_content.decode("utf-8"))
        except (SyntaxError, UnicodeError, ValueError, RecursionError) as exc:
            self.fail(self.launcher, "runtime-source-template", "launcher syntax unavailable", exc)
        if sum(1 for _ in ast.walk(tree)) > 2048:
            self.fail(self.launcher, "runtime-source-template", "launcher AST exceeds bound")
        inserted, guard, default, imported, terminal = None, None, None, None, False
        for index, statement in enumerate(tree.body):
            if terminal:
                self.fail(self.launcher, "runtime-source-template", "statements after terminal main")
            if imported:
                if (isinstance(statement, ast.If) and not statement.orelse and len(statement.body) == 1
                        and isinstance(statement.test, ast.Compare) and isinstance(statement.test.left, ast.Name)
                        and statement.test.left.id == "__name__" and len(statement.test.ops) == 1
                        and isinstance(statement.test.ops[0], ast.Eq) and len(statement.test.comparators) == 1
                        and isinstance(statement.test.comparators[0], ast.Constant)
                        and statement.test.comparators[0].value == "__main__"):
                    body = statement.body[0]
                    if (isinstance(body, ast.Raise) and body.cause is None
                            and isinstance(body.exc, ast.Call) and isinstance(body.exc.func, ast.Name)
                            and body.exc.func.id == "SystemExit" and len(body.exc.args) == 1
                            and not body.exc.keywords and isinstance(body.exc.args[0], ast.Call)
                            and self.symbol(body.exc.args[0].func, "main") and not body.exc.args[0].args
                            and not body.exc.args[0].keywords):
                        terminal = True
                        continue
                self.fail(self.launcher, "runtime-source-template", "unsupported terminal main")
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str) and index == 0:
                continue
            if isinstance(statement, ast.Import):
                for item in statement.names:
                    if item.name not in {"os", "sys"}:
                        self.fail(self.launcher, "runtime-source-template", "unsupported launcher import")
                    self.bind_symbol(item.asname or item.name, item.name)
                continue
            if isinstance(statement, ast.ImportFrom) and not statement.level:
                if statement.module == "__future__" and [(x.name, x.asname) for x in statement.names] == [("annotations", None)]:
                    leading = 1 if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str) else 0
                    if index != leading or self.path_bindings or inserted or guard or default:
                        self.fail(self.launcher, "runtime-source-template", "future import order")
                    continue
                if statement.module == "pathlib" and len(statement.names) == 1 and statement.names[0].name == "Path":
                    self.bind_symbol(statement.names[0].asname or "Path", "Path")
                    continue
                if statement.module == "lean_slots.cli" and len(statement.names) == 1 and statement.names[0].name == "main":
                    self.bind_symbol(statement.names[0].asname or "main", "main")
                    imported = statement.names[0].asname or "main"
                    continue
            if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
                name = statement.targets[0].id
                if name in self.bindings or name in {"str", "SystemExit", "__file__", "__name__"}:
                    self.fail(name, "runtime-source-template", "launcher reassignment")
                value = self.value(statement.value)
                if not isinstance(value, _RuntimePath):
                    self.fail(name, "runtime-source-template", "binding is not a validated Path")
                self.path_bindings += 1
                if self.path_bindings > 8:
                    self.fail(name, "runtime-source-template", "path bindings exceed bound")
                self.bindings[name] = value
                continue
            if isinstance(statement, ast.If) and guard is None:
                guard = self.guard(statement)
                continue
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call):
                call = statement.value
                if not call.keywords and self.os_method(call.func, "setdefault") and default is None:
                    if not (len(call.args) == 2 and isinstance(call.args[0], ast.Constant)
                            and call.args[0].value == "LEAN_SLOT_CONFIG"):
                        self.fail(self.launcher, "runtime-source-template", "unsupported inventory default")
                    if not (isinstance(call.args[1], ast.Call) and isinstance(call.args[1].func, ast.Name)
                            and call.args[1].func.id == "str" and len(call.args[1].args) == 1):
                        self.fail(self.launcher, "runtime-source-template", "default is not source Path str")
                    fallback = self.value(call.args[1])  # Eager regardless of key presence.
                    present = "LEAN_SLOT_CONFIG" in self.predicted_environment
                    effective = self.text(self.predicted_environment.setdefault("LEAN_SLOT_CONFIG", fallback), "LEAN_SLOT_CONFIG")
                    default = {"key": "LEAN_SLOT_CONFIG", "present": present,
                               "default": self.text(fallback, "LEAN_SLOT_CONFIG"),
                               "applied": not present, "effective": effective}
                    continue
                if (not call.keywords and isinstance(call.func, ast.Attribute) and call.func.attr == "insert"
                        and isinstance(call.func.value, ast.Attribute) and call.func.value.attr == "path"
                        and self.symbol(call.func.value.value, "sys") and inserted is None
                        and len(call.args) == 2 and isinstance(call.args[0], ast.Constant)
                        and type(call.args[0].value) is int and call.args[0].value == 0
                        and isinstance(call.args[1], ast.Call) and isinstance(call.args[1].func, ast.Name)
                        and call.args[1].func.id == "str" and len(call.args[1].args) == 1
                        and not call.args[1].keywords):
                    value = self.value(call.args[1].args[0])
                    if isinstance(value, _RuntimePath):
                        inserted = value.value
                        continue
            self.fail(self.launcher, "runtime-source-template", "unsupported executable launcher statement")
        if not imported or not terminal:
            self.fail(self.launcher, "runtime-source-template", "complete entry point missing")
        selected = inserted if inserted is not None else self.launcher.parent
        if not selected.is_absolute():
            self.fail(selected, "runtime-source-template", "selected scripts path not absolute")
        selected = self.path(selected, stat.S_IFDIR)
        package = self.path(selected / "lean_slots", stat.S_IFDIR)
        self.path(package / "__init__.py", stat.S_IFREG)
        self.path(package / "cli.py", stat.S_IFREG)
        if package != loaded_root or guard is not None and guard["selected"] != str(selected):
            self.fail(selected, "runtime-source-route", "selected and actual loaded roots disagree")
        if "--inventory" in self.command:
            offset = self.command.index("--inventory") + 1
            if offset >= len(self.command) or self.canonical(self.command[offset]) != self.canonical(self.inventory.source):
                self.fail(self.launcher, "runtime-source-route", "command inventory differs")
        return {"template": "shared" if inserted is not None else "direct",
                "selected_scripts": str(selected), "selected_package": str(package),
                "selectors": self.selections, "transforms": self.transforms,
                "guard": guard, "inventory_default": default,
                "inventory_source": str(self.inventory.source), "inventory_precedence": "explicit/configured"}

    def build(self):
        if self.kind not in {"proxy", "backend"}:
            self.fail(self.kind, "runtime-source-input", "unsupported managed kind")
        root = self.loaded_root()
        shared = self.manifest(root, required=_FP_REQUIRED)
        self.launcher = self.inventory.repo_root / "scripts" / "slotctl.py"
        content, launcher_path = self.read(self.launcher)
        routing = self.route(content, root)
        local_path = self.inventory.repo_root / "scripts" / "lean_slots"
        local_root = self.path(local_path, stat.S_IFDIR, optional=True)
        local = self.manifest(local_path, required=frozenset({"__init__.py"})) if local_root else {"absent": True}
        if local_root == root:
            if local["files"] != shared["files"]:
                self.fail(local_path, "runtime-source-membership", "shared/local alias manifests disagree")
            local = {"alias_of": "shared", "root": str(root), "files": local["files"]}
        return {"kind": self.kind, "repo_role": self.inventory.repo_role,
                "command": self.command,
                "server": json.loads(json.dumps(self.inventory.raw.get("server", {}))),
                "slot": json.loads(json.dumps(self.inventory.slot(self.number))),
                "sources": {"version": 2, "shared": shared, "local": local,
                            "launcher": {"path": str(launcher_path), "sha256": sha256_bytes(content)},
                            "routing": routing}}


MAX_SHUTDOWN_IDENTITIES = 4096  # One bound for retained/root/discovered persisted identities.


def _startup_deadline(deadline: float) -> None:
    if time.monotonic() >= deadline:
        raise TimeoutError("startup admission deadline expired")


class _StartupEvidence:
    """One in-memory exact launch transaction; persisted data is diagnostic only."""
    def __init__(self, pending, allowance, started, enclosing):
        local = started['mono'] + allowance
        _wire_number(local, minimum=0)
        if enclosing is not None:
            _wire_number(enclosing, minimum=0)
        self.local = local
        self.effective = local if enclosing is None else min(local, enclosing)
        self.pending = pending
        self.first = self.last = None
        self.observations = []
        self.value = {'version': 1, 'launch_token': pending['launch_token'],
                      'observer_pid': pending['initiator_pid'], 'configured_seconds': allowance,
                      'started': started, 'local_deadline': local, 'enclosing_deadline': enclosing,
                      'effective_deadline': self.effective, 'stage': 'creation',
                      'creation_attempts': 0, 'creation_succeeded': False, 'failure_count': 0,
                      'failures': [], 'first_failure_ref': None, 'last_failure_ref': None,
                      'terminal': None, 'rollback': None, 'updated': started, 'utc_regressed': False}

    def refusal(self, observation, stage):
        if observation.reason is None or observation.diagnostics is None:
            raise SlotError('launch refusal lacks representable same-call evidence', observations=(observation,))
        self.value['failure_count'] += 1
        number = self.value['failure_count']
        failure = {'id': number, 'stage': stage,
                   'attempt': self.value['creation_attempts'] if stage == 'creation' else 1,
                   'state': observation.state, 'reason': observation.reason,
                   'observed_at': observation.observed_at, 'diagnostics': observation.diagnostics}
        if self.first is None:
            self.first = failure
            self.observations.append(observation)
        self.last = failure
        self.value.update(failures=[self.first] if number == 1 else [self.first, failure],
                          first_failure_ref=1, last_failure_ref=number)
        self.observations[:] = self.observations[:1] if number == 1 else [self.observations[0], observation]

    def fault(self, exc, phase, *, rollback=False, witness=None):
        reference = self.value['last_failure_ref']
        try:
            error = diagnostic_error(exc) if witness is None else {
                'error_class': witness.error_class or type(exc).__name__, 'errno': witness.errno,
                'message': diagnostic_text(witness.detail)}
            fault = {'phase': phase, 'at': diagnostic_stamp(), 'error': error,
                     'observation_ref': reference}
        except (ValueError, UnicodeError, OverflowError):
            # Reporting cannot disable guarded cleanup. Invalid new evidence is
            # never persisted as legacy/free state; retain the earlier record.
            return
        self.value['rollback' if rollback else 'terminal'] = fault

    def snapshot(self, stage):
        self.value['stage'] = stage
        self.value['updated'] = diagnostic_stamp()
        self.value['utc_regressed'] = diagnostic_span(self.value['started'], self.value['updated'])['utc_regressed']
        return bound_diagnostics(self.value, 196608)

    def publish(self, path, stage):
        _startup_deadline(self.effective)
        self.pending['startup_evidence'] = self.snapshot(stage)
        validate_startup_evidence(self.pending)
        _startup_deadline(self.effective)
        atomic_json(path, self.pending)
        # This is also the final producer success boundary for a running write.
        # No later observer/Controller check may hide a missing effective guard.
        _startup_deadline(self.effective)

    def retain_failed(self, path):
        self.pending['startup_evidence'] = self.snapshot('failed')
        validate_startup_evidence(self.pending)
        atomic_json(path, self.pending)


class Supervisor:
    def __init__(self, inventory: Inventory | None = None):
        self.inventory = inventory or Inventory.load()

    def _validate_record(self, value: dict[str, Any], kind: str, number: int) -> dict[str, Any]:
        """One existing-record shape for status, capacity, stop and quiescence."""
        path = self.inventory.process_path(kind, number)
        def invalid(detail: str) -> None:
            evidence = Observation("unavailable", detail=detail, target=str(path), operation="process-record-validate")
            error = SlotError(f"invalid process record for {kind} wt{number}: {detail}", observations=(evidence,))
            error.recorded_pid = value.get("pid")
            raise error
        if type(value.get("schema_version")) is not int or value["schema_version"] != SCHEMA_VERSION:
            invalid("unsupported process schema")
        if value.get("kind") != kind or type(value.get("slot")) is not int or value["slot"] != number or value.get("repo_role") != self.inventory.repo_role:
            invalid("process identity fields do not match the configured domain")
        version, phase = value.get("process_schema_version", 1), value.get("phase", "running")
        if type(version) is not int or version not in (1, 2) or not isinstance(phase, str) or phase not in ("running", "launch_pending", "uncertain_residual"):
            invalid("unsupported process version/phase")
        pid, signature = value.get("pid"), value.get("signature")
        if "pid" in value and (type(pid) is not int or pid <= 0):
            invalid("root PID must be a positive integer")
        if "signature" in value and (not isinstance(signature, str) or not signature.strip() or "\n" in signature or "\r" in signature):
            invalid("root signature must be a nonempty single-line string")
        if signature is not None and pid is None:
            invalid("root signature lacks its PID")
        if phase == "running" and (pid is None or signature is None):
            invalid("running record lacks a complete root identity")
        if "descendants" in value:
            descendants = value["descendants"]
            if not isinstance(descendants, list) or len(descendants) > MAX_SHUTDOWN_IDENTITIES:
                invalid("descendants must be a bounded list of complete identities")
            identities = {}
            for child in descendants:
                if not isinstance(child, dict) or type(child.get("pid")) is not int or child["pid"] <= 0:
                    invalid("descendant PID must be a positive integer")
                child_signature = child.get("signature")
                if not isinstance(child_signature, str) or not child_signature.strip() or "\n" in child_signature or "\r" in child_signature:
                    invalid("descendant signature must be a nonempty single-line string")
                if child["pid"] in identities:
                    invalid("duplicate descendant PID")
                identities[child["pid"]] = child_signature
                if child["pid"] == pid and signature is not None and child_signature != signature:
                    invalid("root and retained descendant signatures conflict")
        origin = value.get("record_origin")
        if "record_origin" in value or "recovery" in value:
            if origin != "operator_stop_only" or kind != "backend" or version != 2 or phase != "uncertain_residual":
                invalid("invalid stop-only recovery origin/phase")
            if any(key in value for key in ("runtime_fingerprint", "launch_token", "command", "started_at", "initiator_pid", "backend_token")):
                invalid("stop-only recovery cannot claim a managed launch")
            recovery = value.get("recovery")
            if not isinstance(recovery, dict) or set(recovery) != {"authorization", "expected_root", "expected_family", "reserved_at", "admission_observations", "error_observations"}:
                invalid("incomplete recovery provenance")
            if (not isinstance(recovery["reserved_at"], str) or not recovery["reserved_at"] or
                    len(json.dumps(recovery)) > 262144):
                invalid("unbounded recovery provenance")
            for key in ("admission_observations", "error_observations"):
                if (not isinstance(recovery[key], list) or len(recovery[key]) > 16 or
                        any(not isinstance(row, dict) for row in recovery[key])):
                    invalid("invalid bounded recovery observations")
            root, family = recovery["expected_root"], recovery["expected_family"]
            if root != {"pid": pid, "signature": signature} or not isinstance(family, list) or not family or len(family) > 4096:
                invalid("recovery root/family mismatch")
            expected = {}
            for row in family:
                if (not isinstance(row, dict) or set(row) != {"pid", "ppid", "signature"} or
                        type(row["pid"]) is not int or row["pid"] <= 0 or type(row["ppid"]) is not int or row["ppid"] < 0 or
                        row["pid"] in expected or not isinstance(row["signature"], str) or signature_birth(row["signature"]) is None):
                    invalid("invalid recovery family identity")
                expected[row["pid"]] = row["signature"]
            if expected != {row["pid"]: row["signature"] for row in value.get("descendants", [])}:
                invalid("recovery original identities changed")
            auth = recovery["authorization"]
            if (not isinstance(auth, dict) or set(auth) != {"approval_ref", "drain_receipt", "dispatch_frozen", "requests_drained", "owner_session_hash", "backend_target", "lease_owner"} or
                    auth["dispatch_frozen"] is not True or auth["requests_drained"] is not True or
                    any(not isinstance(auth[key], str) or not auth[key].strip() or len(auth[key]) > 2048 for key in ("approval_ref", "drain_receipt")) or
                    not isinstance(auth["owner_session_hash"], str) or len(auth["owner_session_hash"]) != 64):
                invalid("invalid recovery approval/drain/owner binding")
            target = auth["backend_target"]
            if target != self.recovery_target(number):
                invalid("recovery target authority mismatch")
            owner = auth["lease_owner"]
            if owner is not None and (not isinstance(owner, dict) or set(owner) != {"inventory_source", "inventory_domain", "repo_role", "worktree", "state_root", "slot", "public_dependency_sha", "lease_sha256"} or
                                      owner["state_root"] != str(self.inventory.state_root) or owner["slot"] != number or
                                      not isinstance(owner["inventory_domain"], str) or len(owner["inventory_domain"]) != 64):
                invalid("invalid recovery lease-owner authority")
        try:
            validate_startup_evidence(value)
        except ValueError as exc:
            invalid(f"startup evidence invalid: {exc}")
        return value  # Preserve legacy fields/bytes; never manufacture or silently drop pins.

    def recovery_target(self, number: int) -> dict[str, Any]:
        return {"inventory_source": str(self.inventory.source), "repo_role": self.inventory.repo_role,
                "inventory_domain": self._inventory_domain(self.inventory),
                "worktree": str(self.inventory.worktree(number)), "project": str(self.inventory.lean_root(number)),
                "state_root": str(self.inventory.state_root), "slot": number,
                "process_path": str(self.inventory.process_path("backend", number))}

    def _read_metadata(self, kind: str, number: int) -> tuple[dict[str, Any] | None, tuple[Observation, ...]]:
        path = self.inventory.process_path(kind, number)
        observed = observe_path(path)
        if observed.state == "absent":
            return None, (observed,)
        if observed.state != "present":
            raise SlotError(f"process record observation unavailable: {observed.detail}", observations=(observed,))
        if observed.identity["mode"] != stat.S_IFREG:
            evidence = Observation("unavailable", detail="process record is not a regular file", target=str(path), operation="process-record-read")
            raise SlotError(evidence.detail, observations=(observed, evidence))
        value = self._validate_record(read_json(path), kind, number)
        evidence = Observation("present", target=str(path), operation="process-record-validate",
                               identity={"pid": value.get("pid"), "signature": value.get("signature"),
                                         "phase": value.get("phase", "running")})
        return value, (observed, evidence)

    def _metadata(self, kind: str, number: int) -> dict[str, Any] | None:
        return self._read_metadata(kind, number)[0]

    def _running(self, kind: str, number: int) -> bool:
        return self.process_state(kind, number) == "running"

    def process_state(self, kind: str, number: int) -> str:
        return self._resource_status(kind, number)["state"]

    def _runtime_fingerprint(
        self, kind: str, number: int, command: list[str] | None = None
    ) -> str:
        """Compare expected launch-source/config inputs, never process-memory code."""
        command = command if command is not None else (
            self.proxy_command(number) if kind == "proxy" else self.backend_command(number))
        return self._runtime_inputs(kind, number, command, self._capture_runtime_environment())

    def _capture_runtime_environment(self):
        try:
            return os.environ.copy()
        except (OSError, RuntimeError, ValueError, TypeError) as exc:
            evidence = Observation("unavailable", target="launch environment",
                                   operation="runtime-environment-capture", detail=str(exc),
                                   error_class=type(exc).__name__, errno=getattr(exc, "errno", None))
            raise SlotError("runtime launch environment capture unavailable", observations=(evidence,)) from exc

    def _runtime_inputs(self, kind, number, command, environment):
        first = _RuntimeSourcePass(self, kind, number, command, environment)
        payload = first.build()
        second = _RuntimeSourcePass(self, kind, number, command, environment)
        repeated = second.build()
        if payload != repeated or first.capabilities != second.capabilities:
            evidence = Observation("unavailable", target="runtime source inputs",
                                   operation="runtime-source-reobserve",
                                   detail="source origin/membership/identity/bytes/route changed between passes")
            raise SlotError("runtime source inputs changed between bounded passes",
                            observations=tuple(first.observations + second.observations) + (evidence,))
        return canonical_digest(payload)

    def _role_inventories(self, *, retain_aliases: bool = False,
                          observations: list[Observation] | None = None) -> tuple[list[Inventory], list[str]]:
        """Resolve the existing bounded family; native enumeration must be capable."""
        resolved = {str(self.inventory.source): self.inventory}
        errors = []
        witnesses = observations if observations is not None else []
        try:
            candidates = {self.inventory.source}
            repositories, seen = observe_directory(self.inventory.workspace_root)
            witnesses.append(seen)
            if seen.state != "present":
                raise SlotError("workspace role enumeration unavailable", observations=(seen,))
            for repository in repositories:
                entry = observe_path(repository); witnesses.append(entry)
                if entry.state == "unavailable":
                    raise SlotError("repository role observation unavailable", observations=(entry,))
                if entry.state != "present" or entry.identity["mode"] != stat.S_IFDIR:
                    continue
                configs, seen = observe_directory(repository / "config"); witnesses.append(seen)
                if seen.state == "unavailable":
                    raise SlotError("inventory family enumeration unavailable", observations=(seen,))
                candidates.update(path for path in configs if path.name.startswith("lean-slots.") and path.suffix == ".json")
            paired = self.inventory.paired_inventory()
            if paired:
                candidates.add(paired.source)
            if len(candidates) > 128:
                raise SlotError("inventory family exceeds complete resolution bound")
            for source in sorted(candidates):
                entry = observe_path(source); witnesses.append(entry)
                if entry.state != "present" or entry.identity["mode"] != stat.S_IFREG:
                    raise SlotError("configured inventory observation unavailable", observations=(entry,))
                inv = Inventory.load(source)
                if inv.state_root != self.inventory.state_root:
                    errors.append("inventory runtime-root mismatch")
                else:
                    resolved[str(inv.source)] = inv
        except (OSError, SlotError, ValueError, TypeError) as exc:
            witnesses.extend(getattr(exc, "observations", ()))
            errors.append(f"role universe unavailable: {str(exc)[:2048]}")
        # A checkout name or copied config cannot establish repository identity.
        identities = {root: self._checkout_identity(root, witnesses)
                      for root in {inv.repo_root for inv in resolved.values()}}
        canonical = [inv for inv in resolved.values()
                     if identities[inv.repo_root] is not None
                     and identities[inv.repo_root]["git_dir"] == identities[inv.repo_root]["common_dir"]]
        retained = {}
        for source, inv in resolved.items():
            identity = identities[inv.repo_root]
            if identity is None:
                errors.append("inventory checkout identity unavailable")
                retained[source] = inv
                continue
            if identity["git_dir"] == identity["common_dir"]:
                retained[source] = inv
                continue
            counterparts = [other for other in canonical
                            if identities[other.repo_root]["common_dir"] == identity["common_dir"]]
            if not counterparts:
                errors.append("secondary checkout lacks a capable canonical primary")
                retained[source] = inv
                continue
            if not any(other.repo_role == inv.repo_role and
                       self._inventory_domain(inv, other.repo_root) == self._inventory_domain(other)
                       for other in counterparts):
                errors.append("secondary checkout has a conflicting inventory domain")
                retained[source] = inv
        resolved = retained
        # An override may alter dependency inputs without adding a physical role.
        # Compare resolved domains and complete server mappings, not JSON location.
        roles: dict[str, tuple[str, Inventory]] = {}
        for inv in resolved.values():
            domain = self._inventory_domain(inv)
            prior = roles.get(inv.repo_role)
            if prior and prior[0] != domain:
                errors.append("multiple conflicting inventory domains for one role")
            elif prior is None or inv.source == self.inventory.source:
                roles[inv.repo_role] = (domain, inv)
        # Quiescence also needs every resolved input filename: old wrappers
        # can survive a supported override even though physical capacity is one role.
        return (list(resolved.values()) if retain_aliases else
                [entry[1] for entry in roles.values()]), errors

    @staticmethod
    def _inventory_domain(inv: Inventory, root=None) -> str:
        root = inv.repo_root if root is None else root
        return canonical_digest({
            "repo_root": str(root), "state_root": str(inv.state_root),
            "server": inv.raw.get("server", {}),
            "slots": [{"worktree": str((root / inv.slot(n)["worktree"]).resolve()),
                       "lean_root": str((root / inv.slot(n)["worktree"] / "lean").resolve()),
                       "branch": inv.slot(n).get("branch"),
                       "endpoint_name": inv.slot(n).get("endpoint_name"),
                       "proxy_port": int(inv.slot(n)["proxy_port"]),
                       "backend_port": int(inv.slot(n)["backend_port"])} for n in (1, 2, 3)]})

    @staticmethod
    def _checkout_identity(root, witnesses: list[Observation]):
        """Three bounded Git fields; only proven linked copies may be excluded."""
        def unavailable(detail, *, result=None, exc=None):
            witnesses.append(Observation("unavailable", detail=detail, target=str(root),
                operation="git-checkout-identity", returncode=result.returncode if result else None,
                error_class=type(exc).__name__ if exc else "ValueError", errno=getattr(exc, "errno", None)))
            return None
        try:
            result = subprocess.run(["git", "rev-parse", "--show-toplevel", "--git-common-dir", "--git-dir"],
                                    cwd=root, check=False, capture_output=True, text=True, timeout=observation_timeout())
        except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
            return unavailable(str(exc), exc=exc)
        lines = result.stdout.splitlines()
        if result.returncode != 0 or result.stderr.strip() or len(result.stdout) > 16384 or len(lines) != 3 or any(not line.strip() or "\x00" in line for line in lines):
            return unavailable("incomplete/ambiguous Git checkout observation: " + result.stderr, result=result)
        try:
            paths = [(root / line).resolve() for line in lines]
        except (OSError, ValueError) as exc:
            return unavailable(str(exc), result=result, exc=exc)
        top, common, git_dir = paths
        if top != root or (git_dir != common and not git_dir.is_relative_to(common / "worktrees")):
            return unavailable("Git checkout top-level/common-directory identity mismatch", result=result)
        for path in (top, common, git_dir):
            seen = observe_path(path); witnesses.append(seen)
            if seen.state != "present" or seen.identity["mode"] != stat.S_IFDIR:
                return unavailable("Git checkout directory observation unavailable", result=result)
        identity = {"top_level": top, "common_dir": common, "git_dir": git_dir}
        witnesses.append(Observation("present", target=str(root), operation="git-checkout-identity",
                                    returncode=result.returncode, identity={k: str(v) for k, v in identity.items()}))
        return identity

    @staticmethod
    def _project_roots(census, project_rows, project: str, witnesses: list[Observation]):
        """Validate complete relevant chains, including generic intermediates."""
        rows = {row.pid: row for row in census.rows}
        matching = {row.pid for row in project_rows}
        def invalid(detail):
            evidence = Observation("unavailable", detail=detail, target=project,
                                   operation="process-ancestry", error_class="ValueError")
            witnesses.append(evidence)
            raise SlotError(detail, observations=(evidence,))
        if census.state != "present" or len(rows) != len(census.rows):
            invalid("complete unique process ancestry unavailable")
        roots = []
        for row in project_rows:
            visited = {row.pid}; parent = row.ppid; has_matching_ancestor = False
            while parent != 0:
                if parent in visited:
                    invalid("cyclic/self-parented relevant process ancestry")
                visited.add(parent)
                if parent not in rows:
                    invalid("missing relevant process ancestor")
                has_matching_ancestor = has_matching_ancestor or parent in matching
                parent = rows[parent].ppid
            if not has_matching_ancestor:
                roots.append(row)
        witnesses.append(Observation("present", target=project, operation="process-ancestry",
                                     identity={"project_pids": sorted(matching), "roots": [row.pid for row in roots]}))
        return roots

    def capacity_census(self) -> dict[str, Any]:
        observations = []
        inventories, errors = self._role_inventories(observations=observations)
        unbounded = bool(errors)
        census = process_snapshot()
        census_witness = census.as_dict()
        if census.state != "present":
            errors.append(census.detail or "process census unavailable"); unbounded = True
        declared = {(inv.repo_role, n): inv for inv in inventories for n in (1, 2, 3)}
        reservations: dict[int, list[str]] = {n: [] for n in (1, 2, 3)}
        confirmed = 0
        retained_pids = set()
        for (role, number), inv in declared.items():
            sup = self if inv.source == self.inventory.source else Supervisor(inv)
            port = _port_observation(str(inv.raw["server"]["host"]), int(inv.slot(number)["backend_port"]))
            observations.append(port)
            occupied = port.state != "absent"
            if port.state == "unavailable":
                errors.append(f"{role} wt{number} endpoint observation unavailable")
            try:
                m, record_witnesses = sup._read_metadata("backend", number)
                observations.extend(record_witnesses)
                if m is not None:
                    if m.get("phase", "running") != "running":
                        occupied = True
                    if m.get("signature"):
                        seen = observe_process(m["pid"], m["signature"]); observations.append(seen)
                        occupied = occupied or seen.state != "absent"
                        if seen.state == "present":
                            confirmed += 1
                        elif seen.state in {"unavailable", "mismatch"}:
                            errors.append(f"{role} wt{number} identity {seen.state}")
                    for child in m.get("descendants", []):
                        seen = observe_process(child["pid"], child["signature"]); observations.append(seen)
                        if seen.state != "absent":
                            occupied = True; retained_pids.add(child["pid"])
                        if seen.state in {"unavailable", "mismatch"}:
                            errors.append(f"{role} wt{number} retained descendant {seen.state}")
            except SlotError as exc:
                occupied = True; observations.extend(exc.observations)
                errors.append(f"{role} wt{number} record unavailable: {str(exc)[:2048]}")
            project_rows = [row for row in census.rows if str(inv.lean_root(number)) in row.command]
            if project_rows:
                occupied = True
                try:
                    roots = self._project_roots(census, project_rows, str(inv.lean_root(number)), observations)
                    if len(roots) > 1:
                        errors.append(f"multiple service roots for {role} wt{number}")
                except SlotError as exc:
                    errors.append(f"{role} wt{number} ancestry unavailable: {exc}"); unbounded = True
            if occupied:
                reservations[number].append(role)
        projects = [str(inv.lean_root(n)) for inv in inventories for n in (1, 2, 3)]
        mapped_pids = set(retained_pids)
        for row in census.rows:
            if any(project in row.command for project in projects):
                mapped_pids.update(census.descendants(row.pid))
        for row in census.rows:
            if any(mark in row.command for mark in ("lean-lsp-mcp", "lake serve", "lean --server", "lean --worker")) and row.pid not in mapped_pids:
                errors.append("unmapped heavy process: complete reverse-role capacity authority unavailable"); unbounded = True
        root = self.inventory.state_root / "processes"
        records, seen = observe_directory(root); observations.append(seen)
        if seen.state == "unavailable":
            errors.append("backend registry enumeration unavailable"); unbounded = True
        for record in records:
            if not record.name.endswith("-backend.json"):
                continue
            try:
                m = read_json(record)
                if (m.get("repo_role"), m.get("slot")) not in declared:
                    errors.append("process record outside resolved role universe"); unbounded = True
            except (SlotError, TypeError) as exc:
                observations.extend(getattr(exc, "observations", ()))
                errors.append("unreadable backend registry record"); unbounded = True
        conflicts = [n for n, owners in reservations.items() if len(owners) > 1]
        if unbounded:
            for n in (1, 2, 3):
                if not reservations[n]:
                    reservations[n].append("unavailable")
        return {"complete": not errors, "errors": errors, "confirmed_services": confirmed,
                "reserved_physical_slots": [n for n, owners in reservations.items() if owners],
                "owners": reservations, "conflicts": conflicts,
                "observations": [item.as_dict() for item in observations] + [census_witness]}

    def global_backend_count(self) -> int:
        """Observed registered services only; admission uses capacity_census."""
        return self.capacity_census()["confirmed_services"]

    def global_backend_owners(self, number: int) -> list[str]:
        return sorted(self.capacity_census()["owners"][number])

    def _assert_quiescent(self, kind: str, number: int, *,
                          observations: list[Observation] | None = None) -> None:
        host = str(self.inventory.raw["server"]["host"])
        port = _port_observation(host, int(self.inventory.slot(number)[f"{kind}_port"]))
        witnesses = observations if observations is not None else []
        witnesses.append(port)
        if port.state != "absent":
            raise SlotError(f"{kind} wt{number} not quiescent: endpoint {port.state}", observations=(port,))
        census = process_snapshot(); witnesses.append(census.as_observation())
        if census.state != "present":
            raise SlotError(f"{kind} wt{number} process census unavailable: {census.detail}", observations=(census.as_observation(),))
        registry, registry_seen = observe_directory(self.inventory.state_root / "processes")
        witnesses.append(registry_seen)
        if registry_seen.state == "unavailable":
            raise SlotError("process registry quiescence observation unavailable", observations=(registry_seen,))
        metadata, record_witnesses = self._read_metadata(kind, number); witnesses.extend(record_witnesses)
        if metadata:
            pids = ({metadata["pid"]} if "pid" in metadata else set()) | {child["pid"] for child in metadata.get("descendants", [])}
            if any(row.pid in pids for row in census.rows):
                raise SlotError(f"{kind} wt{number} owned process/descendant remains", observations=(census.as_observation(),))
        if kind == "proxy":
            family, errors = self._role_inventories(retain_aliases=True, observations=witnesses)
            if errors:
                raise SlotError("proxy inventory-alias quiescence unavailable: " + "; ".join(errors), observations=tuple(witnesses))
            aliases = {str(inv.source) for inv in family if inv.repo_role == self.inventory.repo_role}
            wrapper = str(self.inventory.repo_root / "scripts" / "slotctl.py")
            for row in census.rows:
                try:
                    arguments = shlex.split(row.command)
                except ValueError as exc:
                    raise SlotError("proxy command observation unavailable", observations=tuple(witnesses)) from exc
                if wrapper in arguments and "_proxy" in arguments and "--inventory" in arguments and "--slot" in arguments:
                    try:
                        inventory = arguments[arguments.index("--inventory") + 1]
                        slot = arguments[arguments.index("--slot") + 1]
                    except IndexError as exc:
                        raise SlotError("proxy command observation incomplete", observations=tuple(witnesses)) from exc
                    if slot == str(number):
                        if inventory not in aliases:
                            raise SlotError(f"proxy wt{number} unclassified fixed-slot wrapper remains", observations=tuple(witnesses))
                        # Same-domain aliases count once but retain every filename
                        # for observation; no missing record authorizes adoption.
                        raise SlotError(f"proxy wt{number} fixed-inventory wrapper remains (inventory={inventory})", observations=tuple(witnesses))
        if kind == "backend":
            project = str(self.inventory.lean_root(number))
            if any(project in row.command for row in census.rows):
                raise SlotError(f"backend wt{number} fixed-project process remains", observations=tuple(witnesses))
            invs, errors = self._role_inventories(observations=witnesses)
            mapped = set()
            for row in census.rows:
                if any(str(inv.lean_root(n)) in row.command for inv in invs for n in (1, 2, 3)):
                    mapped.update(census.descendants(row.pid))
            if errors or any(any(mark in row.command for mark in ("lean-lsp-mcp", "lake serve", "lean --server", "lean --worker")) and row.pid not in mapped for row in census.rows):
                raise SlotError("fixed-project descendant quiescence unavailable", observations=tuple(witnesses))

    def _wait_port(self, host: str, port: int, *, open_: bool, deadline: float | None = None) -> None:
        if deadline is None:
            deadline = time.monotonic() + float(self.inventory.raw["server"].get("startup_timeout_seconds", 45))
            expected = "present" if open_ else "absent"
            while time.monotonic() < deadline:
                seen = _port_observation(host, port)
                if seen.state == "unavailable":
                    raise SlotError(f"port observation unavailable: {seen.detail}", observations=(seen,))
                if seen.state == expected:
                    return
                time.sleep(0.1)
            raise SlotError(f"timed out waiting for {host}:{port} to {expected}")
        expected = "present" if open_ else "absent"
        while True:
            _startup_deadline(deadline)
            seen = _port_observation(host, port)
            _startup_deadline(deadline)
            if seen.state == "unavailable":
                raise SlotError(f"port observation unavailable: {seen.detail}", observations=(seen,))
            if seen.state == expected:
                return
            time.sleep(min(0.1, max(0, deadline - time.monotonic())))
            _startup_deadline(deadline)

    def _spawn(self, kind: str, number: int, command: list[str], port: int) -> None:
        allowance = self.inventory.raw["server"].get("startup_timeout_seconds", 45)
        _wire_number(allowance, positive=True)  # Before reservation or Popen; bool is not numeric.
        environment = self._capture_runtime_environment()
        fingerprint = self._runtime_inputs(kind, number, command, environment)
        metadata = self._metadata(kind, number)
        if metadata:
            seen = observe_process(int(metadata.get("pid", 0)), metadata.get("signature"))
            if metadata.get("phase", "running") == "running" and metadata.get("signature") and seen.state == "present":
                if metadata.get("runtime_fingerprint") != fingerprint:
                    raise SlotError("managed process is stale; root must coordinate drained reload")
                endpoint = _port_observation(str(self.inventory.raw["server"]["host"]), port)
                if endpoint.state != "present":
                    raise SlotError(f"managed process endpoint {endpoint.state}; registration retained")
                return
            raise SlotError(f"{kind} wt{number} has retained registration/reservation; no adoption")
        self._assert_quiescent(kind, number)
        path = self.inventory.process_path(kind, number)
        pending = {"schema_version": SCHEMA_VERSION, "process_schema_version": 2,
                   "phase": "launch_pending", "launch_token": secrets.token_hex(16),
                   "repo_role": self.inventory.repo_role, "slot": number, "kind": kind,
                   "inventory_source": str(self.inventory.source), "project": str(self.inventory.lean_root(number)),
                   "command": command, "runtime_fingerprint": fingerprint, "port": port,
                   "started_at": now_iso(), "initiator_pid": os.getpid()}
        atomic_json(path, pending)
        process = None
        creation_signature = None
        startup = None
        phase = 'spawn'
        try:
            if kind == "backend":
                environment["LEAN_LSP_MCP_TOKEN"] = self.inventory.backend_token(number)
            log_path = self.inventory.log_path(kind, number)
            log_path.parent.mkdir(parents=True, exist_ok=True)
            with log_path.open("ab", buffering=0) as log:
                started = diagnostic_stamp()  # Immediately before this one Popen.
                startup = _StartupEvidence(pending, allowance, started, _OBSERVATION_DEADLINE.get())
                with observation_budget(deadline=startup.local) as effective:
                    if effective != startup.effective:
                        raise SlotError('startup context effective deadline changed')
                    _startup_deadline(effective)
                    process = subprocess.Popen(command, cwd=self.inventory.repo_root, env=environment,
                                               stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                               start_new_session=True)
                    log.close()  # Include returned spawn/log IO, not an unchecked final close.
                    _startup_deadline(effective)
                    while True:
                        phase = 'handle'
                        _startup_deadline(effective)
                        if process.poll() is not None:
                            raise SlotError('identity unavailable: new creation handle exited/reaped; no identity adoption')
                        phase = 'creation'
                        startup.value['creation_attempts'] += 1
                        created = observe_process(process.pid)  # Actual local expected signature is None.
                        if created.state != 'present':
                            startup.refusal(created, 'creation')
                        if process.poll() is not None:
                            phase = 'handle'
                            raise SlotError('identity unavailable: creation handle exited/reaped during observation', observations=(created,))
                        if created.state == 'present' and created.signature:
                            creation_signature = created.signature
                            startup.value['creation_succeeded'] = True
                            pending.update(pid=process.pid, signature=creation_signature)
                            _startup_deadline(effective)
                            phase = 'signature_write'
                            startup.publish(path, 'readiness')
                            break
                        _startup_deadline(effective)
                        if not (created.state == 'unavailable' and created.reason == 'selected_census_signature_drift'
                                and created.diagnostics is not None
                                and created.diagnostics['expected_signature_supplied'] is False
                                and created.diagnostics['pid'] == process.pid):
                            raise SlotError('new process coherent creation identity unavailable', observations=(created,))
                        phase = 'diagnostic_write'
                        startup.publish(path, 'creation')  # No top-level PID/signature during retry.
                        _startup_deadline(effective)
                        time.sleep(min(0.1, max(0, effective - time.monotonic())))
                        _startup_deadline(effective)
                    phase = 'readiness'
                    self._wait_port(str(self.inventory.raw['server']['host']), port, open_=True, deadline=effective)
                    _startup_deadline(effective)
                    phase = 'final_observation'
                    seen = observe_process(process.pid)
                    if seen.state != 'present':
                        startup.refusal(seen, 'final')
                    if seen.state == 'present' and seen.signature:
                        creation_signature = seen.signature
                        pending['signature'] = seen.signature
                    _startup_deadline(effective)
                    if process.poll() is not None or seen.state != 'present' or not seen.signature:
                        raise SlotError('new process final identity unavailable', observations=(seen,))
                    phase = 'running_write'
                    pending['phase'] = 'running'
                    startup.publish(path, 'complete')
        except BaseException as original:
            rollback_error = None
            rollback_phase = 'rollback_identity'
            reporting = []
            rollback_contexts = []
            terminal = Observation('unavailable', detail=str(original), errno=getattr(original, 'errno', None),
                                   target=f'{kind} wt{number}', operation=f'startup-{phase}',
                                   error_class=type(original).__name__)
            def retain_cause(exc, operation, *, native=False):
                witnesses = tuple(getattr(exc, 'observations', ())) if native else ()
                if witnesses:
                    for witness in witnesses:
                        reporting.append(Observation(witness.state, signature=witness.signature,
                                                     detail=witness.detail, errno=witness.errno,
                                                     target=witness.target, operation=operation,
                                                     observed_at=witness.observed_at, returncode=witness.returncode,
                                                     identity=witness.identity, error_class=witness.error_class,
                                                     reason=witness.reason, diagnostics=witness.diagnostics))
                else:
                    reporting.append(Observation('unavailable', detail=str(exc), errno=getattr(exc, 'errno', None),
                                                 target=str(path), operation=operation,
                                                 error_class=type(exc).__name__))
            def retain_rollback(exc, operation, *, native=False):
                nonlocal rollback_error
                first_new = len(reporting)
                retain_cause(exc, operation, native=native)
                context = Observation('unavailable', detail=str(exc)).detail
                native_operations = [w.operation for w in getattr(exc, 'observations', ())]
                rollback_contexts.append((operation, context, native_operations))
                if rollback_error is None:
                    rollback_error = exc
                    if startup is not None:
                        actual = next((w for w in reporting[first_new:]
                                       if w.state in {'unavailable', 'mismatch'} and w.error_class is not None), None)
                        startup.fault(exc, operation, rollback=True,
                                      witness=actual if native else None)
            pending['phase'] = 'launch_pending'
            if startup is not None:
                startup.fault(original, phase)
            if process is not None:
                try:
                    if getattr(process, "returncode", None) is not None and not creation_signature:
                        raise SlotError("rollback created handle already reaped without identity; reservation retained; identity unavailable/mismatch")
                    observation_timeout()
                    identity = observe_process(process.pid, creation_signature or pending.get("signature"))
                    if identity.state == "unavailable" and creation_signature:
                        identity = _observe_created_handle(process, creation_signature)
                    if identity.state not in {"present", "absent"} or (identity.state == "present" and not identity.signature):
                        raise SlotError("rollback owned identity unavailable/mismatch; reservation retained", observations=(identity,))
                    # An observation/write failure cannot disable bounded cleanup of a
                    # valid exact creation handle. Descendant uncertainty still retains
                    # the prelaunch reservation after cleanup rather than declaring free.
                    rollback_phase = 'rollback_census'
                    snapshot = process_snapshot()
                    descendant_error = None
                    descendants = []
                    if snapshot.state != "present":
                        descendant_error = SlotError("rollback descendant census unavailable", observations=(snapshot.as_observation(),))
                    elif identity.state == "present":
                        root = next((row for row in snapshot.rows if row.pid == process.pid), None)
                        if root is None or root.signature != identity.signature:
                            descendant_error = SlotError("rollback wrapper census identity inconsistent", observations=(snapshot.as_observation(),))
                        for row in snapshot.rows:
                            if descendant_error is None and row.pid in snapshot.descendants(process.pid):
                                expected = identity.signature if row.pid == process.pid else row.signature
                                seen = observe_process(row.pid, expected)
                                if seen.state != "present" or not seen.signature:
                                    descendant_error = SlotError("rollback descendant identity unavailable/mismatch", observations=(seen,))
                                    break
                                descendants.append({"pid": row.pid, "signature": expected})
                    if descendant_error is not None:
                        retain_rollback(descendant_error, rollback_phase, native=True)
                    pending.update(phase="launch_pending", descendants=descendants)
                    try:
                        if startup is not None:
                            startup.retain_failed(path)
                        else:
                            atomic_json(path, pending)
                    except BaseException as exc:
                        # Keep the earlier durable reservation and the actual failed
                        # publication cause while independently safe cleanup proceeds.
                        retain_cause(exc, 'rollback-diagnostic-write')
                    rollback_phase = 'rollback_signal'
                    if descendant_error is None:
                        for child in descendants:
                            if child["pid"] == process.pid:
                                continue
                            check = observe_process(child["pid"], child["signature"])
                            if check.state != "present":
                                descendant_error = SlotError("rollback child identity changed/unavailable", observations=(check,))
                                retain_rollback(descendant_error, rollback_phase, native=True)
                                break
                            observation_timeout()
                            os.kill(child["pid"], signal.SIGTERM)
                            observation_timeout()
                    # Check the original creation identity again immediately before
                    # using its unreaped handle; never signal a guessed replacement PID.
                    check = observe_process(process.pid, identity.signature)
                    if check.state == "unavailable" and creation_signature:
                        check = _observe_created_handle(process, creation_signature)
                    if check.state not in {"present", "absent"}:
                        raise SlotError("rollback wrapper identity changed/unavailable", observations=(check,))
                    if process.poll() is None:
                        observation_timeout()
                        process.terminate()
                        observation_timeout()
                    rollback_phase = 'rollback_wait'
                    observation_timeout()
                    process.wait(timeout=5)
                    observation_timeout()
                    if descendant_error is not None:
                        raise descendant_error
                    deadline = time.monotonic() + 5
                    while True:
                        seen = [observe_process(child["pid"], child["signature"]) for child in descendants]
                        if any(item.state in {"unavailable", "mismatch"} for item in seen):
                            raise SlotError("rollback descendant exit observation unavailable/mismatch", observations=tuple(seen))
                        if all(item.state == "absent" for item in seen):
                            break
                        if time.monotonic() >= deadline:
                            raise SlotError("rollback descendants remain after bounded wait", observations=tuple(seen))
                        time.sleep(0.1)
                    rollback_phase = 'rollback_quiescence'
                    self._assert_quiescent(kind, number)
                    observation_timeout()
                    path.unlink(missing_ok=True)
                except BaseException as exc:
                    if exc is not rollback_error:
                        retain_rollback(exc, rollback_phase, native=True)
            else:
                # Popen never returned a handle: conservatively retain pending evidence.
                retain_rollback(SlotError("launch did not return an owned handle"), rollback_phase)
            if rollback_error is not None:
                if process is not None:
                    pending.setdefault('pid', process.pid)  # Original raw residual, never signature authority.
                # First rollback fault was recorded at detection; subsequent causes
                # remain ordered outward evidence and cannot change that phase.
                pending.update(phase="uncertain_residual", error=str(original), rollback_error=str(rollback_error))
                try:
                    if startup is not None:
                        startup.retain_failed(path)
                    else:
                        atomic_json(path, pending)
                except BaseException as exc:
                    retain_cause(exc, 'residual_write')
                refused = tuple(startup.observations) if startup is not None else ()
                if not refused:
                    refused = tuple(getattr(original, 'observations', ()))
                raise SlotError(f"launch failed: {original}; residual retained: {rollback_error}; rollback contexts: {rollback_contexts}",
                                observations=(*refused, terminal, *reporting)) from original
            if reporting:
                refused = tuple(startup.observations) if startup is not None else ()
                if not refused:
                    refused = tuple(getattr(original, 'observations', ()))
                raise SlotError(f"launch failed: {original}; diagnostic publication failed; owned cleanup completed",
                                observations=(*refused, terminal, *reporting)) from original
            raise

    def _confirm_stop_quiescence(self, kind: str, number: int) -> None:
        self._assert_quiescent(kind, number)
        if kind == "backend":
            capacity = self.capacity_census()
            if not capacity["complete"] or capacity["conflicts"]:
                raise SlotError("stop capacity/registry quiescence unavailable or conflicting")
        observation_timeout()

    def _stop(self, kind: str, number: int, port: int, *, recovery_sha256: str | None = None) -> None:
        with observation_budget(10):
            try:
                self._stop_owned(kind, number, port, recovery_sha256=recovery_sha256)
            except (OSError, subprocess.TimeoutExpired) as exc:
                raise SlotError(f"owned stop failed; registration retained: {exc}") from exc

    def _persist_stop(self, path: Path, metadata: dict[str, Any]) -> None:
        observation_timeout()
        self._validate_record(metadata, metadata["kind"], metadata["slot"])
        atomic_json(path, metadata)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
        observation_timeout()

    def _stop_owned(self, kind: str, number: int, port: int, *, recovery_sha256=None) -> None:
        path = self.inventory.process_path(kind, number)
        metadata = self._metadata(kind, number)
        if metadata and metadata.get("record_origin") == "operator_stop_only":
            if recovery_sha256 is None or sha256_bytes(path.read_bytes()) != recovery_sha256:
                raise SlotError("stop-only residual requires explicit controller recovery and exact hash")
        if metadata is None or not metadata.get("signature"):
            self._confirm_stop_quiescence(kind, number)
            observation_timeout()
            path.unlink(missing_ok=True)
            return
        seen = observe_process(int(metadata.get("pid", 0)), metadata["signature"])
        if seen.state == "absent":
            self._confirm_stop_quiescence(kind, number)
            observation_timeout()
            path.unlink(missing_ok=True)
            return
        if seen.state != "present":
            raise SlotError(f"refusing stop: process identity {seen.state}; registration retained", observations=(seen,))
        census = process_snapshot()
        if census.state != "present":
            raise SlotError("refusing stop: descendant observation unavailable", observations=(census.as_observation(),))
        identities = {int(child["pid"]): child["signature"] for child in metadata.get("descendants", [])}
        identities[int(metadata["pid"])] = metadata["signature"]
        census_identities = {row.pid: row.signature for row in census.rows}
        if census_identities.get(int(metadata["pid"])) != metadata["signature"]:
            raise SlotError("refusing stop: wrapper census identity unavailable/mismatch", observations=(census.as_observation(),))
        retained = set(identities)
        pids = census.descendants(int(metadata["pid"])) | set(identities)
        if len(pids) > MAX_SHUTDOWN_IDENTITIES:  # RR combined retained/root/discovered identity bound.
            raise SlotError("combined shutdown family exceeds retained identity bound")
        for pid in sorted(pids):
            child = observe_process(pid, identities.get(pid, census_identities.get(pid)))
            if child.state == "absent":
                continue
            if pid in retained:
                continue  # Classified below, without replacing the original signature.
            native = observe_shutdown_process(pid)
            if (child.state != "present" or not child.signature or native.state != "present" or
                    native.identity["native_state"].startswith("Z")):
                raise SlotError("refusing stop: descendant identity unavailable/mismatch", observations=(child,))
            identities[pid] = child.signature
        if metadata.get("record_origin") == "operator_stop_only" and set(identities) != retained:
            raise SlotError("recovery family drift; original reservation retained")
        # Newly discovered children have just supplied genuine live identities.
        # Persist these originals before any effect, just like legacy retained IDs.
        terminal_eligible = set(identities)
        root = int(metadata["pid"])

        results = []

        def family_observation():
            nonlocal results
            snapshot, generic, native = observe_shutdown_family(identities, root, max_identities=MAX_SHUTDOWN_IDENTITIES)
            results = [snapshot.as_observation(), *generic.values(), *native.values()][-16:]
            if snapshot.state != "present":
                raise SlotError("shutdown ancestry unavailable: " + snapshot.detail, observations=tuple(results))
            return snapshot, generic, native

        def classified():
            snapshot, generic, natives = family_observation()
            rows = {row.pid: row for row in snapshot.rows}
            if snapshot.descendants(root) - set(identities):
                raise SlotError("new shutdown descendant; retained graph cannot authorize it")
            states, depths = {}, {}
            for pid, signature in identities.items():
                observed = generic[pid]
                if observed.state == "absent":
                    if pid in rows:
                        raise SlotError("shutdown absence/census drift")
                    states[pid] = "absent"; depths[pid] = -1
                    continue
                native = natives[pid]
                if native.state != "present" or pid not in rows or native.identity["ppid"] != rows[pid].ppid:
                    raise SlotError("shutdown native state unavailable/drifting", observations=(observed, native))
                terminal = native.identity["native_state"].startswith("Z")
                if terminal:
                    if (pid == root or pid not in terminal_eligible or
                            _signature_command(signature) in {None, "<defunct>"} or
                            signature_birth(signature) != native.identity["birth"] or
                            observed.state not in {"present", "mismatch"}):
                        raise SlotError("unqualified terminal shutdown identity", observations=(observed, native))
                    states[pid] = "terminal"
                elif (observed.state == "present" and native.identity["birth"] == signature_birth(signature) and
                      native.identity["command"] == _signature_command(signature)):
                    states[pid] = "live"
                else:
                    raise SlotError("shutdown live identity mismatch/unavailable", observations=(observed, native))
            for pid, state in states.items():
                if state == "absent":
                    continue
                ancestor, chain = pid, set()
                while ancestor != root:
                    if ancestor in chain or ancestor not in rows:
                        raise SlotError("shutdown ancestry incomplete/cyclic")
                    chain.add(ancestor); ancestor = rows[ancestor].ppid
                    if ancestor not in identities:
                        raise SlotError("retained descendant reparented outside owned root")
                    if states.get(ancestor) != "live":
                        raise SlotError("shutdown ancestor is not independently exact/live")
                depths[pid] = len(chain)
            if states.get(root) != "live" and any(value != "absent" for value in states.values()):
                raise SlotError("shutdown root is not independently live")
            return states, depths, {pid: rows[pid].ppid for pid in states if states[pid] != "absent"}

        states, depths, parents = classified()
        metadata["descendants"] = [{"pid": pid, "signature": sig} for pid, sig in sorted(identities.items())]
        receipts = []  # This invocation only; old descendant lists prove no signal history.
        metadata["shutdown"] = {"attempted_at": now_iso(), "delivered_sigterm": receipts}
        self._validate_record(metadata, kind, number)
        self._persist_stop(path, metadata)  # RR persist original identities before any signal.
        order = sorted((pid for pid in identities if states[pid] != "absent"), key=lambda pid: (-depths[pid], pid))
        first_refusal = None
        first_observations = ()
        phase, pending = "signal classification", None
        try:
            index = 0
            while index < len(order):
                pid = pending = order[index]
                try:
                    phase = "signal classification"
                    states, _, parents = classified()
                    if states[pid] == "absent":
                        index += 1
                        continue
                    if states[pid] == "terminal":  # RR terminal descendants never receive signals.
                        index += 1
                        continue
                    phase = "durable persistence"
                    self._persist_stop(path, metadata)
                    # A new complete pass is mandatory after every durable write.
                    phase = "post-write classification"
                    final_states, _, final_parents = classified()
                    if final_parents != parents or final_states != states:
                        raise SlotError("shutdown rooted ancestry changed after durable write", observations=tuple(results))
                    phase = "final target check"
                    check = observe_process(pid, identities[pid])
                    native = observe_shutdown_process(pid)
                    results = [*results, check, native][-16:]
                    if (check.state != "present" or native.state != "present" or native.identity["native_state"].startswith("Z") or
                            native.identity["birth"] != signature_birth(identities[pid]) or
                            native.identity["command"] != _signature_command(identities[pid]) or
                            native.identity["ppid"] != final_parents[pid]):  # RR final observed parent guard.
                        raise SlotError("live target changed before SIGTERM", observations=(check, native))
                except SlotError as exc:
                    if not receipts:
                        raise
                    if first_refusal is None:
                        first_refusal = f"{phase} PID {pid}: {str(exc)[:2048]}"
                        first_observations = tuple(exc.observations or results)[-8:]
                    # Passive waiting grants no authority. Retry every original guard.
                    time.sleep(observation_timeout(0.1))
                    continue  # RR resume only through a fresh full-family classification.
                observation_timeout()
                os.kill(pid, signal.SIGTERM)
                receipts.append({"pid": pid, "signature": identities[pid], "delivered_at": now_iso()})
                self._persist_stop(path, metadata)
                index += 1
            phase, pending = "final passive absence", None
            while True:
                try:
                    _, generic, _ = family_observation()
                    results = list(generic.values())
                except SlotError as exc:
                    if first_refusal is None and receipts:
                        first_refusal = f"{phase}: {str(exc)[:2048]}"
                        first_observations = tuple(exc.observations)[-8:]
                    time.sleep(observation_timeout(0.1))
                    continue
                if all(item.state == "absent" for item in results):  # RR actual every-PID absence.
                    self._confirm_stop_quiescence(kind, number)
                    observation_timeout()
                    path.unlink(missing_ok=True)
                    return
                time.sleep(observation_timeout(0.1))
        except (OSError, subprocess.TimeoutExpired) as exc:
            cause = f"; first refusal: {first_refusal}" if first_refusal else ""
            stage = "post-SIGTERM" if receipts else "pre-SIGTERM"
            raise SlotError(f"{stage} passive observation failed during {phase} PID {pending}; registration retained: {exc}{cause}",
                            observations=(*first_observations, *results[-16:])) from exc

    def _recover_orphan_backend_stop_unlocked(self, number, *, expected_root, expected_family,
                                               authorization, expected_residual_sha256=None,
                                               revalidate_authority) -> None:
        """Only the explicit controller entry calls this under slot/lifecycle locks."""
        path = self.inventory.process_path("backend", number)
        initial, _ = self._read_metadata("backend", number)
        retry = expected_residual_sha256 is not None
        if retry:
            if (initial is None or initial.get("record_origin") != "operator_stop_only" or
                    sha256_bytes(path.read_bytes()) != expected_residual_sha256):
                raise SlotError("recovery retry requires exact stop-only residual hash")
            retained = initial["recovery"]
            if (retained["authorization"] != authorization or retained["expected_root"] != expected_root or
                    retained["expected_family"] != expected_family):
                raise SlotError("recovery retry authority/original identity changed")
            record = initial
        else:
            if initial is not None:
                raise SlotError("initial recovery requires absent backend registration")
            record = {"schema_version": SCHEMA_VERSION, "process_schema_version": 2,
                      "phase": "uncertain_residual", "record_origin": "operator_stop_only",
                      "kind": "backend", "slot": number, "repo_role": self.inventory.repo_role,
                      "pid": expected_root.get("pid"), "signature": expected_root.get("signature"),
                      "descendants": [{"pid": row.get("pid"), "signature": row.get("signature")} for row in expected_family],
                      "recovery": {"expected_root": expected_root, "expected_family": expected_family,
                                   "authorization": authorization, "reserved_at": now_iso(),
                                   "admission_observations": [], "error_observations": []}}
        self._validate_record(record, "backend", number)

        def fresh_family():
            revalidate_authority()
            capacity = self.capacity_census()
            # Terminal retained signatures remain generic mismatches; retry stop owns
            # their separate classification. All other capacity errors still refuse.
            allowed = {f"{self.inventory.repo_role} wt{number} retained descendant mismatch"}
            if capacity["conflicts"] or any(error not in allowed or not retry for error in capacity["errors"]):
                raise SlotError("orphan recovery capacity unavailable/conflicting")
            census = process_snapshot()
            if census.state != "present":
                raise SlotError("orphan family census unavailable", observations=(census.as_observation(),))
            rows = {row.pid: row for row in census.rows}
            root = expected_root["pid"]
            expected = {row["pid"]: row for row in expected_family}
            observed = set(rows) & set(expected)
            if (not retry and observed != set(expected)) or (root not in observed and observed):
                raise SlotError("orphan root/family absent or reparented")
            actual = census.descendants(root) & set(rows)
            if actual != observed:
                raise SlotError("orphan family incomplete or contains unexpected descendants")
            project = str(self.inventory.lean_root(number))
            project_rows = [row for row in census.rows if project in row.command]
            roots = self._project_roots(census, project_rows, project, [])
            if {row.pid for row in roots} != ({root} if observed else set()):
                raise SlotError("orphan project has ambiguous or competing roots")
            for pid in observed:
                wanted = expected[pid]
                if rows[pid].ppid != wanted["ppid"]:
                    raise SlotError("orphan ancestry changed")
                seen = observe_process(pid, wanted["signature"])
                native = observe_shutdown_process(pid)
                zombie = (retry and pid != root and native.state == "present" and
                          native.identity["native_state"].startswith("Z") and
                          native.identity["birth"] == signature_birth(wanted["signature"]))
                if (native.state != "present" or native.identity["ppid"] != wanted["ppid"] or
                        (seen.state != "present" and not (seen.state == "mismatch" and zombie)) or
                        (native.identity["native_state"].startswith("Z") and not zombie)):
                    raise SlotError("orphan exact native identity unavailable/mismatch", observations=(seen, native))
            if observed:
                args = shlex.split(rows[root].command)
                for flag, value in (("--lean-project-path", project), ("--host", str(self.inventory.raw["server"]["host"])),
                                    ("--port", str(self.inventory.slot(number)["backend_port"])), ("--transport", "streamable-http")):
                    if args.count(flag) != 1 or args.index(flag) + 1 >= len(args) or args[args.index(flag) + 1] != value:
                        raise SlotError("orphan fixed project/host/port command mismatch")
            sockets, witness = observe_tcp_sockets()
            if witness.state != "present":
                raise SlotError("orphan listener/TCP observation unavailable", observations=(witness,))
            port = int(self.inventory.slot(number)["backend_port"])
            address = f"{self.inventory.raw['server']['host']}:{port}"
            listeners = [row for row in sockets if row["state"] == "LISTEN" and row["name"].rsplit(":", 1)[-1] == str(port)]
            if (not retry and len(listeners) != 1) or len(listeners) > 1:
                raise SlotError("orphan listener is not unique")
            if any(row["pid"] not in observed or row["name"] != address for row in listeners):
                raise SlotError("orphan listener has foreign ownership/address")
            if any(row["pid"] in observed and (row not in listeners or row["state"] != "LISTEN") for row in sockets):
                raise SlotError("orphan family has unaccounted TCP activity")
            endpoint = _port_observation(str(self.inventory.raw["server"]["host"]), port)
            if endpoint.state != ("present" if listeners else "absent"):
                raise SlotError("orphan endpoint/listener observations disagree", observations=(endpoint,))
            return {"observed_at": now_iso(), "operation": "orphan-stop-admission", "state": "present",
                    "family_pids": sorted(observed), "listener_pids": [row["pid"] for row in listeners],
                    "inventory_domain": self._inventory_domain(self.inventory),
                    "capacity_complete": capacity["complete"], "capacity_errors": capacity["errors"][:16],
                    "tcp": witness.as_dict(), "endpoint": endpoint.as_dict()}

        admission = fresh_family()
        if not retry:
            record["recovery"]["admission_observations"] = [admission]
            self._validate_record(record, "backend", number)
            exclusive_durable_json(path, record)  # RR no signal before complete durable reservation.
        try:
            current = self._metadata("backend", number)
            if current != record:
                raise SlotError("recovery reservation changed before stop")
            admission = fresh_family()
            record["recovery"]["admission_observations"] = (record["recovery"]["admission_observations"] + [admission])[-16:]
            self._validate_record(record, "backend", number)
            self._persist_stop(path, record)
            digest = sha256_bytes(path.read_bytes())
            self._stop("backend", number, int(self.inventory.slot(number)["backend_port"]), recovery_sha256=digest)
        except (SlotError, OSError) as exc:
            # Keep bounded admission/error evidence on our own reserved record.
            # Failure to write evidence never removes the durable reservation.
            try:
                residual = self._metadata("backend", number)
                if (residual and residual.get("record_origin") == "operator_stop_only" and
                        residual["recovery"]["authorization"] == authorization and
                        residual["recovery"]["expected_root"] == expected_root and
                        residual["recovery"]["expected_family"] == expected_family):
                    evidence = {"observed_at": now_iso(), "operation": "orphan-stop-failure",
                                "error_class": type(exc).__name__, "detail": str(exc)[:2048],
                                "observations": [item.as_dict() for item in getattr(exc, "observations", ())[:8]]}
                    residual["recovery"]["error_observations"] = (residual["recovery"]["error_observations"] + [evidence])[-16:]
                    self._validate_record(residual, "backend", number)
                    self._persist_stop(path, residual)
            except (SlotError, OSError):
                pass
            raise

    def backend_command(self, number: int) -> list[str]:
        slot = self.inventory.slot(number)
        server = self.inventory.raw["server"]
        disabled = ",".join(str(item) for item in server["disabled_tools"])
        return [
            *(str(item) for item in server["command"]),
            "--transport",
            "streamable-http",
            "--host",
            str(server["host"]),
            "--port",
            str(slot["backend_port"]),
            "--lean-project-path",
            str(self.inventory.lean_root(number)),
            "--disable-tools",
            disabled,
            "--instructions",
            str(server["instructions"]),
        ]

    def proxy_command(self, number: int) -> list[str]:
        wrapper = self.inventory.repo_root / "scripts" / "slotctl.py"
        return [
            sys.executable,
            str(wrapper),
            "--inventory",
            str(self.inventory.source),
            "_proxy",
            "--slot",
            str(number),
        ]

    def _start_backend_unlocked(self, number: int) -> None:
        if self._running("backend", number):
            return
        census = self.capacity_census()
        if not census["complete"] or census["conflicts"]:
            raise SlotError(f"global capacity unavailable/conflicting: {census['errors']}")
        if len(census["reserved_physical_slots"]) >= int(self.inventory.raw["max_active_slots"]):
            raise SlotError("global heavy-backend limit reached; residual capacity reserved")
        if census["owners"][number]:
            raise SlotError(f"physical wt{number} already reserved by {census['owners'][number]}")
        self._spawn("backend", number, self.backend_command(number), int(self.inventory.slot(number)["backend_port"]))

    def _stop_backend_unlocked(self, number: int) -> None:
        self._stop("backend", number, int(self.inventory.slot(number)["backend_port"]))

    def _assert_backend_owned_or_stopped(self, number: int) -> None:
        state = self.process_state("backend", number)
        if state in {"running", "stale"}:
            return
        if state != "down":
            raise SlotError(f"backend wt{number} is {state}; no unknown process management")
        self._assert_quiescent("backend", number)

    def _start_proxy_unlocked(self, number: int) -> None:
        slot = self.inventory.slot(number)
        self._spawn(
            "proxy", number, self.proxy_command(number), int(slot["proxy_port"])
        )

    def _stop_proxy_unlocked(self, number: int) -> None:
        self._stop("proxy", number, int(self.inventory.slot(number)["proxy_port"]))

    @contextmanager
    def lifecycle(self) -> Iterator[None]:
        with directory_lock(
            self.inventory.state_root / "locks" / "supervisor.lock",
            purpose="shared Lean endpoint lifecycle",
        ):
            yield

    def start_backend(self, number: int) -> None:
        with self.lifecycle():
            self._start_backend_unlocked(number)

    def stop_backend(self, number: int) -> None:
        with self.lifecycle():
            self._stop_backend_unlocked(number)

    def start_proxy(self, number: int) -> None:
        with self.lifecycle():
            self._start_proxy_unlocked(number)

    def stop_proxy(self, number: int) -> None:
        with self.lifecycle():
            self._stop_proxy_unlocked(number)

    @contextmanager
    def paused_backend(self, number: int) -> Iterator[None]:
        """Keep one backend stopped across an atomic cache/branch transition.

        Entry requires a healthy proxy and confirmed backend/project quiescence.
        A legitimately stopped leased backend is allowed; unavailable observations
        never permit the caller's cache transition. Exit attempts healthy rewarm,
        retaining both the body failure and any restoration failure.
        """
        with self.lifecycle():
            self.assert_proxy_healthy(number)
            self._assert_backend_owned_or_stopped(number)
            if self.process_state("backend", number) in {"running", "stale"}:
                self._stop_backend_unlocked(number)
            self._assert_quiescent("backend", number)
            try:
                yield
            except BaseException as original:
                try:
                    self._start_backend_unlocked(number)
                    self.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"transition failed: {original}; restoration failed: {restoration}") from original
                raise
            else:
                self._start_backend_unlocked(number)
                self.assert_healthy(number)

    @contextmanager
    def activating_from(self, number: int, counterpart: "Supervisor") -> Iterator[None]:
        """Park a paired backend, mutate the target cache, then activate target.

        The shared lifecycle lock makes the handoff atomic with respect to all
        controller-managed endpoints. Failure attempts bounded restoration; a
        restoration failure retains reservations and both error explanations.
        """
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            self._start_proxy_unlocked(number)
            self._assert_backend_owned_or_stopped(number)
            counterpart._assert_backend_owned_or_stopped(number)
            if self.process_state("backend", number) in {"running", "stale"}:
                raise SlotError(
                    f"target backend for {self.inventory.repo_role} wt{number} is already running"
                )
            counterpart_was_running = counterpart.process_state("backend", number) in {"running", "stale"}
            if counterpart_was_running:
                counterpart._stop_backend_unlocked(number)
            self._assert_quiescent("backend", number)
            counterpart._assert_quiescent("backend", number)
            try:
                yield
                self._start_backend_unlocked(number)
                self.assert_healthy(number)
            except BaseException as original:
                try:
                    self._assert_backend_owned_or_stopped(number)
                    if self.process_state("backend", number) in {"running", "stale"}:
                        self._stop_backend_unlocked(number)
                    self._assert_quiescent("backend", number)
                    counterpart._assert_backend_owned_or_stopped(number)
                    if counterpart_was_running and not counterpart._running("backend", number):
                        counterpart._start_backend_unlocked(number)
                        counterpart.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"paired transition failed: {original}; restoration failed: {restoration}") from original
                raise

    def restore_counterpart(self, number: int, counterpart: "Supervisor") -> None:
        """Return one leased slot to its default paired backend without overlap."""
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            self._assert_backend_owned_or_stopped(number)
            counterpart._assert_backend_owned_or_stopped(number)
            target_was_running = self.process_state("backend", number) in {"running", "stale"}
            if target_was_running:
                self._stop_backend_unlocked(number)
            try:
                if not counterpart._running("backend", number):
                    counterpart._start_backend_unlocked(number)
            except BaseException as original:
                try:
                    counterpart._assert_backend_owned_or_stopped(number)
                    if counterpart.process_state("backend", number) in {"running", "stale"}:
                        counterpart._stop_backend_unlocked(number)
                    counterpart._assert_quiescent("backend", number)
                    if target_was_running and not self._running("backend", number):
                        self._start_backend_unlocked(number)
                        self.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"paired restoration failed: {original}; target recovery failed: {restoration}") from original
                raise

    def start(self) -> dict[str, Any]:
        started: list[tuple[str, int]] = []
        with self.lifecycle():
            try:
                for number in (1, 2, 3):
                    if self.process_state("proxy", number) not in {"running", "down"}:
                        raise SlotError("proxy unknown/unavailable/stale; coordinate drained diagnosis/reload")
                    if self.process_state("backend", number) not in {"running", "down"}:
                        raise SlotError("backend unknown/unavailable/stale; retain physical reservation")
                    if not self._running("proxy", number):
                        self._start_proxy_unlocked(number)
                        started.append(("proxy", number))
                    expected_backend = self.inventory.backend_expected(number)
                    if expected_backend and not self._running("backend", number):
                        self._start_backend_unlocked(number)
                        started.append(("backend", number))
                    elif not expected_backend and self._running("backend", number):
                        self._stop_backend_unlocked(number)
                # Do this while the front doors are up but before any client attaches:
                # an empty tool list at attach time is permanent for that session.
                self._harvest_tool_list_unlocked()
            except Exception as original:
                rollback_errors = []
                for kind, number in reversed(started):
                    slot = self.inventory.slot(number)
                    port = int(slot[f"{kind}_port"])
                    try:
                        self._stop(kind, number, port)
                    except (SlotError, OSError) as exc:
                        rollback_errors.append(str(exc))
                if rollback_errors:
                    raise SlotError(f"global startup failed: {original}; rollback residuals: {rollback_errors}") from original
                raise
        return self.status()

    def stop(self) -> dict[str, Any]:
        with self.lifecycle():
            for number in (1, 2, 3):
                self._stop_proxy_unlocked(number)
            for number in (1, 2, 3):
                self._stop_backend_unlocked(number)
        return self.status()

    def assert_proxy_healthy(self, number: int) -> None:
        """The front door must be up and running current code; the backend may be down."""
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        if not self._running("proxy", number) or not _port_open(
            host, int(slot["proxy_port"])
        ):
            raise SlotError(
                f"proxy for wt{number} is not healthy; diagnose ownership/observation before coordinated reload"
            )

    def assert_healthy(self, number: int) -> None:
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        self.assert_proxy_healthy(number)
        if not self._running("backend", number) or not _port_open(
            host, int(slot["backend_port"])
        ):
            raise SlotError(
                f"backend for wt{number} is not healthy; diagnose ownership/observation before coordinated reload"
            )

    @staticmethod
    def _sse_json(body: bytes) -> dict[str, Any]:
        for line in body.decode("utf-8").splitlines():
            if line.startswith("data: "):
                value = json.loads(line.removeprefix("data: "))
                if isinstance(value, dict):
                    return value
        value = json.loads(body)
        if not isinstance(value, dict):
            raise SlotError("MCP probe response was not a JSON object")
        return value

    def cached_tool_list(self) -> list[dict[str, Any]] | None:
        """The tool list to advertise when a slot's backend is down, or None.

        Keyed on `tool_list_key`, so a pinned-server bump or a `disabled_tools` edit
        invalidates it while ordinary slot churn does not.
        """
        try:
            cached = read_json(tool_cache_path(self.inventory.state_root))
        except (SlotError, OSError):
            return None
        if cached.get("key") != tool_list_key(self.inventory.raw["server"]):
            return None
        tools = cached.get("tools")
        return tools if isinstance(tools, list) and tools else None

    def _fetch_tool_list(self, number: int) -> list[dict[str, Any]] | None:
        """Ask a RUNNING backend what it offers. Returns None on any failure."""
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        headers = {
            "Accept": "application/json, text/event-stream",
            "Content-Type": "application/json",
        }
        if self.inventory.client_auth_mode == "bearer":
            headers["Authorization"] = f"Bearer {self.inventory.token('codex')}"

        def request(payload, session_id=None):
            connection = http.client.HTTPConnection(
                host, int(slot["proxy_port"]), timeout=120
            )
            current = dict(headers)
            if session_id:
                current["Mcp-Session-Id"] = session_id
            connection.request(
                "POST", "/mcp?client=codex", body=json.dumps(payload), headers=current
            )
            response = connection.getresponse()
            body = response.read()
            response_headers = dict(response.getheaders())
            connection.close()
            if response.status not in {200, 202}:
                raise SlotError(f"tool-list harvest failed ({response.status})")
            return (self._sse_json(body) if body else {}), response_headers

        try:
            _, response_headers = request(
                {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "protocolVersion": "2025-06-18",
                        "capabilities": {},
                        "clientInfo": {"name": "slotctl-harvest", "version": "1"},
                    },
                }
            )
            session_id = response_headers.get("Mcp-Session-Id") or response_headers.get(
                "mcp-session-id"
            )
            request({"jsonrpc": "2.0", "method": "notifications/initialized"}, session_id)
            listed, _ = request(
                {"jsonrpc": "2.0", "id": 2, "method": "tools/list"}, session_id
            )
        except (SlotError, OSError, http.client.HTTPException, ValueError):
            return None
        tools = (listed.get("result") or {}).get("tools")
        return tools if isinstance(tools, list) and tools else None

    def _harvest_tool_list_unlocked(self) -> bool:
        """Populate the cache once, briefly borrowing a backend if none is running.

        Without this, the FIRST session on a fresh clone sees no slot tools at all under
        `backend_policy: "leased"` — every backend is down at attach time, and MCP tools
        are registered at session start. Borrowed backends undergo bounded cleanup;
        failed cleanup retains its reservation and prevents publishing a new cache.
        """
        if self.cached_tool_list() is not None:
            return False
        for number in (1, 2, 3):
            if not self._running("backend", number):
                continue
            tools = self._fetch_tool_list(number)
            if tools:
                self._write_tool_cache(tools)
                return True
        for number in (1, 2, 3):
            if not self.inventory.slot(number):
                continue
            try:
                self._start_backend_unlocked(number)
            except SlotError as exc:
                raise SlotError(f"tool discovery cannot borrow safe capacity: {exc}") from exc
            try:
                tools = self._fetch_tool_list(number)
            except BaseException as original:
                try:
                    self._stop_backend_unlocked(number)
                except BaseException as cleanup:
                    raise SlotError(f"tool discovery failed: {original}; borrowed cleanup failed: {cleanup}") from original
                raise
            else:
                self._stop_backend_unlocked(number)
            if tools:
                self._write_tool_cache(tools)
                return True
        return False

    def _write_tool_cache(self, tools: list[dict[str, Any]]) -> None:
        atomic_json(
            tool_cache_path(self.inventory.state_root),
            {
                "key": tool_list_key(self.inventory.raw["server"]),
                "tools": tools,
                "harvested_at": now_iso(),
            },
        )

    def probe(self, number: int, *, client: str = "codex") -> dict[str, Any]:
        """Exercise initialization, lease gating, and the no-build tool list."""
        self.assert_healthy(number)
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        headers = {
            "Accept": "application/json, text/event-stream",
            "Content-Type": "application/json",
        }
        if self.inventory.client_auth_mode == "bearer":
            headers["Authorization"] = f"Bearer {self.inventory.token(client)}"

        def request(payload: dict[str, Any], session_id: str | None = None):
            connection = http.client.HTTPConnection(
                host, int(slot["proxy_port"]), timeout=120
            )
            current = dict(headers)
            if session_id:
                current["Mcp-Session-Id"] = session_id
            connection.request(
                "POST",
                f"/mcp?client={client}",
                body=json.dumps(payload),
                headers=current,
            )
            response = connection.getresponse()
            body = response.read()
            response_headers = dict(response.getheaders())
            connection.close()
            if response.status not in {200, 202}:
                raise SlotError(
                    f"MCP probe failed for wt{number} ({response.status}): "
                    f"{body.decode('utf-8', errors='replace')}"
                )
            return (self._sse_json(body) if body else {}), response_headers

        initialized, response_headers = request(
            {
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": {
                    "protocolVersion": "2025-06-18",
                    "capabilities": {},
                    "clientInfo": {"name": "slotctl-probe", "version": "1"},
                },
            }
        )
        session_id = next(
            (
                value
                for key, value in response_headers.items()
                if key.lower() == "mcp-session-id"
            ),
            None,
        )
        if not session_id or "result" not in initialized:
            raise SlotError(
                f"MCP initialize response for wt{number} lacked a session/result"
            )
        request(
            {"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}},
            session_id,
        )
        listed, _ = request(
            {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
            session_id,
        )
        tools = [
            str(item.get("name"))
            for item in ((listed.get("result") or {}).get("tools") or [])
            if isinstance(item, dict)
        ]
        if "lean_build" in tools:
            raise SlotError(
                f"MCP worker endpoint wt{number} exposed forbidden lean_build"
            )
        if not any(name.startswith("lean_") for name in tools):
            raise SlotError(f"MCP worker endpoint wt{number} exposed no Lean tools")
        active_dispatch: bool | str = False
        lease = self.inventory.lease(number, required=False)
        if lease and lease.get("state") == "ACTIVE" and lease.get("client") == client:
            diagnostics, _ = request(
                {
                    "jsonrpc": "2.0",
                    "id": 3,
                    "method": "tools/call",
                    "params": {
                        "name": "lean_diagnostic_messages",
                        "arguments": {
                            "file_path": self.inventory.raw["server"]["probe_file"]
                        },
                    },
                },
                session_id,
            )
            if diagnostics.get("error") or "result" not in diagnostics:
                raise SlotError(
                    f"active MCP dispatch failed for wt{number}: {diagnostics}"
                )
            active_dispatch = True
        elif lease:
            active_dispatch = "skipped-nonmatching-lease"
        connection = http.client.HTTPConnection(
            host, int(slot["proxy_port"]), timeout=10
        )
        cleanup_headers = {"Mcp-Session-Id": session_id}
        if self.inventory.client_auth_mode == "bearer":
            cleanup_headers["Authorization"] = headers["Authorization"]
        connection.request("DELETE", f"/mcp?client={client}", headers=cleanup_headers)
        cleanup = connection.getresponse()
        cleanup.read()
        connection.close()
        return {
            "slot": number,
            "repo_role": self.inventory.repo_role,
            "server": initialized["result"].get("serverInfo"),
            "tool_count": len(tools),
            "lean_build_exposed": False,
            "active_dispatch": active_dispatch,
            "cleanup_status": cleanup.status,
        }

    def _resource_status(self, kind: str, number: int) -> dict[str, Any]:
        errors = []
        witnesses = []
        metadata = None
        metadata_error = False
        unvalidated_pid = None
        try:
            metadata, record_witnesses = self._read_metadata(kind, number)
            witnesses.extend(record_witnesses)
        except SlotError as exc:
            metadata_error = True; unvalidated_pid = exc.recorded_pid
            witnesses.extend(exc.observations); errors.append(str(exc))
        endpoint = _port_observation(str(self.inventory.raw["server"]["host"]),
                                     int(self.inventory.slot(number)[f"{kind}_port"]))
        witnesses.append(endpoint)
        process = Observation("unavailable", detail="no authoritative recorded PID",
                              target=f"{kind} wt{number}", operation="identity-unresolved")
        if metadata and metadata.get("signature"):
            process = observe_process(metadata["pid"], metadata["signature"])
        witnesses.append(process)
        children = [observe_process(child["pid"], child["signature"])
                    for child in metadata.get("descendants", [])] if metadata else []
        witnesses.extend(children)
        identity_error = any(child.state in {"unavailable", "mismatch"} for child in children)
        if endpoint.state == "unavailable":
            errors.append(f"endpoint observation unavailable: {endpoint.detail}")
        if metadata and process.state in {"unavailable", "mismatch"}:
            errors.append(f"process observation {process.state}: {process.detail}")
        if identity_error:
            errors.append("retained descendant identity observation unavailable/mismatch")
        state = "unavailable"
        if not metadata_error and not identity_error and endpoint.state != "unavailable":
            if metadata and metadata.get("phase", "running") != "running":
                state = "uncertain_residual"
            elif metadata and process.state in {"unavailable", "mismatch"}:
                state = process.state
            elif metadata and process.state == "present":
                if endpoint.state == "present":
                    try:
                        state = "running" if metadata.get("runtime_fingerprint") == self._runtime_fingerprint(kind, number) else "stale"
                    except SlotError as exc:
                        witnesses.extend(exc.observations); errors.append(str(exc))
            elif any(child.state == "present" for child in children):
                state = "uncertain_residual"
            elif endpoint.state == "present":
                state = "unknown"
            else:
                try:
                    self._assert_quiescent(kind, number, observations=witnesses)
                    state = "down"
                except SlotError as exc:
                    witnesses.extend(exc.observations); errors.append(str(exc))
        return {"state": state,
                "record_phase": "unavailable" if metadata_error else metadata.get("phase", "running") if metadata else "missing",
                "identity_authority": "unavailable" if metadata_error or identity_error else "stop_only_recovery" if metadata and metadata.get("record_origin") == "operator_stop_only" else "managed" if metadata and metadata.get("signature") else "unverified" if metadata else "none",
                "recorded_pid": metadata.get("pid") if metadata else unvalidated_pid,
                "process_observation": process.state, "process_detail": process.detail,
                "endpoint_observation": endpoint.state, "endpoint_detail": endpoint.detail,
                "observations": [item.as_dict() for item in witnesses], "errors": errors}

    def status(self) -> dict[str, Any]:
        slots = []
        for number in (1, 2, 3):
            slot = self.inventory.slot(number)
            resources = {kind: self._resource_status(kind, number) for kind in ("proxy", "backend")}
            slots.append(
                {
                    "slot": number,
                    "repo_role": self.inventory.repo_role,
                    "lease_state": (self.inventory.lease(number, required=False) or {}).get("state", "FREE"),
                    "proxy_port": int(slot["proxy_port"]),
                    "backend_port": int(slot["backend_port"]),
                    "proxy_running": resources["proxy"]["state"] == "running",
                    "backend_running": resources["backend"]["state"] == "running",
                    "proxy_state": resources["proxy"]["state"],
                    "backend_state": resources["backend"]["state"],
                    "resources": resources,
                }
            )
        census = self.capacity_census()
        return {
            "schema_version": SCHEMA_VERSION,
            "global_running_backends": census["confirmed_services"],
            "capacity_complete": census["complete"],
            "capacity_errors": census["errors"],
            "capacity_observations": census["observations"],
            "capacity_conflicts": census["conflicts"],
            "reserved_physical_slots": census["reserved_physical_slots"],
            "slots": slots,
        }
