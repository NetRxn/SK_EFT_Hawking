#!/usr/bin/env python3
"""Thin Bash entrypoint over harness_common's Plan-3 helpers, so the Bash-driven,
unattended harvest skill can call them without import gymnastics. Resolve from a skill via
`${CLAUDE_SKILL_DIR}/../../scripts/harness_common_cli.py`. Stdlib only; fail-open.

Subcommands:
  repo-root                      -> print the resolved repo root (empty if unresolved)
  jsonl-path <sid>               -> print this session's transcript path (deterministic; first-turn-safe)
  is-managed <sid>               -> MANAGED if any workspace marker for <sid> exists, else CLEAR
  gc                             -> prune dead markers + watermarks under this repo
  read-watermark <sid>           -> print the byte-offset watermark (0 if absent)
  advance-watermark <sid> <off>  -> advance the watermark (atomic, monotonic)
  harvest-state-get              -> print the harvest_state JSON ({} if absent)
  harvest-state-set <ts> <cad>   -> record last_run_ts + cadence_hours
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import harness_common as hc


def main(argv=None):
    argv = argv if argv is not None else sys.argv[1:]
    cmd = argv[0] if argv else ""
    try:
        if cmd == "repo-root":
            r = hc.repo_root(os.getcwd())
            print(str(r) if r else "")
        elif cmd == "jsonl-path":
            print(hc.jsonl_path(argv[1] if len(argv) > 1 else "", os.getcwd()))
        elif cmd == "is-managed":
            sid = argv[1] if len(argv) > 1 else ""
            print("MANAGED" if (sid and hc.any_managed_marker_in_workspace(sid)) else "CLEAR")
        elif cmd == "gc":
            hc.gc_dead_markers()
            print("gc ok")
        elif cmd == "read-watermark":
            print(hc.read_watermark(argv[1] if len(argv) > 1 else ""))
        elif cmd == "advance-watermark":
            hc.advance_watermark(argv[1], int(argv[2]))
            print("ok")
        elif cmd == "harvest-state-get":
            print(json.dumps(hc.read_harvest_state()))
        elif cmd == "harvest-state-set":
            hc.write_harvest_state(float(argv[1]), float(argv[2]))
            print("ok")
        else:
            print(__doc__)
            return 2
    except Exception as e:
        # fail-open: a CLI error must never wedge the harvest; print + non-fatal rc.
        print("harness_common_cli error: " + str(e), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
