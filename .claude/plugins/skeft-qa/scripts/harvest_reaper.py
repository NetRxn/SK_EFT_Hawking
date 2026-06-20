#!/usr/bin/env python3
"""Self-cleaning reaper for leaked headless-harvest `claude` processes (System-2 harvest).

ROOT CAUSE: the scheduler launches the harvest as `claude --input-format stream-json …`; that
mode blocks on stdin until EOF, but the launcher never closes stdin, so each firing's claude
process never exits — it idles forever (stat S, ~0% CPU), accumulating one per cadence.

FIX (forward-facing — ships in the public plugin + projects to the private mirror): at harvest
startup, resolve THIS firing's claude PID, append it to a local PID log, and reap any PRIOR
self-logged firing that is now a leaked idle lingerer.

SAFETY is keyed on the SELF-LOGGED PID, NOT on the process relationship — so it is
TOPOLOGY-INDEPENDENT. Only a harvest firing writes its own PID to the log; the launcher (whether
the goal conversation as the direct parent, or the Desktop scheduler as a sibling) NEVER
self-logs, so it is never a reap candidate. A PID is reaped ONLY if ALL hold (any one failing
spares it):
  * it is in the harvest PID log (a harvest firing logged it — never a goal/interactive session);
  * it is NOT the current firing's claude PID;
  * it is still alive AND idle (stat starts with 'S' AND %cpu below a floor — a working harvest
    is CPU-active; a leaked one is blocked on stdin);
  * it is older than a min-age floor (well past the ~minutes of real harvest work, far under the
    cadence) — so a hypothetical concurrent just-started firing is spared;
  * its cmdline is still a `claude` process (PID-REUSE guard — the OS may have recycled the PID).

Stdlib only; macOS `ps`. Local state under <repo>/.claude/dev-harness/ (untracked). `--dry-run`
reports what it WOULD reap without killing or rewriting the log.
"""
import os
import re
import signal
import subprocess
import sys
from pathlib import Path

REAP_MIN_AGE_S = 1800  # 30 min: > harvest active time, << the (≥2h) cadence
CPU_IDLE_FLOOR = 1.0   # %cpu strictly below this == idle
_PS_RE = re.compile(r"^\s*(\d+)\s+(\S+)\s+([\d.]+)\s+(\d+)\s+(.*)$")


def _proc(pid):
    """ps one PID -> {pid, ppid, stat, cpu, etimes, cmd} or None if dead/unreadable."""
    try:
        out = subprocess.run(
            ["ps", "-o", "ppid=,stat=,%cpu=,etimes=,command=", "-p", str(pid)],
            capture_output=True, text=True,
        )
        m = _PS_RE.match(out.stdout.strip())
        if not m:
            return None
        return {"pid": int(pid), "ppid": int(m.group(1)), "stat": m.group(2),
                "cpu": float(m.group(3)), "etimes": int(m.group(4)), "cmd": m.group(5)}
    except Exception:
        return None


def _claude_pid(start_pid=None):
    """Walk the parent chain from `start_pid` (default this process) up to the first `claude`
    process and return its PID — the harvest FIRING's claude, NOT the bash subshell ($$)."""
    pid = start_pid if start_pid is not None else os.getpid()
    seen = set()
    while pid and pid > 1 and pid not in seen:
        seen.add(pid)
        rec = _proc(pid)
        if rec is None:
            break
        if "claude" in rec["cmd"].lower():
            return pid
        pid = rec["ppid"]
    return None


def qualifies_for_reap(rec, current_pid, min_age=REAP_MIN_AGE_S, cpu_floor=CPU_IDLE_FLOOR):
    """PURE predicate (no IO) — True iff `rec` is a leaked, reapable prior harvest firing.
    `rec` is a _proc() dict for a SELF-LOGGED pid (caller guarantees log membership), or None."""
    if rec is None:
        return False                                   # dead / not found
    if rec["pid"] == current_pid:
        return False                                   # never the current firing
    if not str(rec.get("stat", "")).startswith("S"):
        return False                                   # only idle/sleeping (a working one is R)
    if float(rec.get("cpu", 100.0)) >= cpu_floor:
        return False                                   # only ~0% CPU
    if int(rec.get("etimes", 0)) < min_age:
        return False                                   # only clearly-finished (not just-started)
    if "claude" not in str(rec.get("cmd", "")).lower():
        return False                                   # PID-reuse guard
    return True


def _log_path(state_dir):
    return Path(state_dir) / "harvest_pids.log"


def reap(state_dir, dry_run=False, _proc_fn=_proc, _kill_fn=os.kill, _current=None):
    """Reap leaked prior harvest firings. Returns a report dict. `_proc_fn`/`_kill_fn`/`_current`
    are injectable for unit tests (so tests never ps/kill real processes)."""
    state_dir = Path(state_dir)
    current = _current if _current is not None else (_claude_pid() or os.getpid())
    logged = []
    lp = _log_path(state_dir)
    if lp.exists():
        for ln in lp.read_text().splitlines():
            ln = ln.strip()
            if ln.isdigit():
                logged.append(int(ln))
    reaped, survivors = [], []
    for pid in dict.fromkeys(logged):                  # dedup, preserve order
        if pid == current:
            continue
        rec = _proc_fn(pid)
        if qualifies_for_reap(rec, current):
            if not dry_run:
                try:
                    _kill_fn(pid, signal.SIGTERM)
                except Exception:
                    pass
            reaped.append(pid)
        elif rec is not None:
            survivors.append(pid)                      # alive but not reapable -> keep tracking
    if not dry_run:
        state_dir.mkdir(parents=True, exist_ok=True)
        keep = [p for p in survivors if p != current] + [current]
        lp.write_text("\n".join(str(p) for p in dict.fromkeys(keep)) + "\n")
    return {"current": current, "reaped": reaped, "survivors": survivors, "dry_run": dry_run}


def _resolve_state_dir(argv):
    for i, a in enumerate(argv):
        if a == "--state-dir" and i + 1 < len(argv):
            return argv[i + 1]
    try:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import harness_common as hc

        root = hc.repo_root(os.getcwd())
        return str(Path(root) / ".claude" / "dev-harness") if root else None
    except Exception:
        return None


def main(argv):
    dry = "--dry-run" in argv
    sd = _resolve_state_dir(argv)
    if sd is None:
        print("[harvest-reaper] ERROR: --state-dir required (could not resolve repo)")
        return 2
    r = reap(sd, dry_run=dry)
    tag = "DRY-RUN would reap" if dry else "reaped"
    print(f"[harvest-reaper] current claude pid={r['current']}; {tag} "
          f"{len(r['reaped'])} leaked {r['reaped']}; tracking {len(r['survivors'])} survivor(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
