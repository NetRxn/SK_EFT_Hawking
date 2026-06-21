#!/usr/bin/env python3
"""
Web-egress guard — PreToolUse(WebSearch|WebFetch) dev-harness SECURITY control.

Two jobs, on EVERY WebSearch/WebFetch call in the repo (main loop or any subagent):
  1. DENY if the query/URL contains a denylisted local/private identifier.
  2. DENY a WebFetch to a non-whitelisted domain.

Unlike the question-guard this is UNCONDITIONAL (not gated on a /goal marker) and
FAILS CLOSED: any internal error => deny. The launcher in hooks.json adds a second
fail-closed layer (a printf-deny fallback if this script cannot even start).

Denylist = committed research_egress_denylist.sample.txt (baseline, always)
         UNION untracked research_egress_denylist.txt (operator literals, if installed).
Both live in this script's directory; the local file is gitignored so it may hold
literals (incl. firewall terms) without ever being committed.

Stdlib only. Full spec: docs/dev-loops/RESEARCH_LADDER_AND_WEB_EGRESS.md.
"""
from __future__ import annotations

import json
import os
import re
import sys
from urllib.parse import urlparse

_HERE = os.path.dirname(os.path.abspath(__file__))
_SAMPLE = os.path.join(_HERE, "research_egress_denylist.sample.txt")
_LOCAL = os.path.join(_HERE, "research_egress_denylist.txt")

# Whitelisted WebFetch destinations (registrable hostnames). A host passes iff it equals
# an entry or is a subdomain of one (endswith "." + entry) — so export.arxiv.org passes
# but arxiv.org.evil.com / notarxiv.org do not. WebSearch is a search engine: not domain-gated.
_WHITELIST = (
    "arxiv.org", "export.arxiv.org", "doi.org", "link.aps.org", "journals.aps.org",
    "iopscience.iop.org", "projecteuclid.org", "stacks.math.columbia.edu",
    "leanprover-community.github.io", "leanprover.github.io", "oeis.org", "pdg.lbl.gov",
    "en.wikipedia.org", "ncatlab.org", "encyclopediaofmath.org",
    "mathoverflow.net", "math.stackexchange.com",
)

_HEADER = re.compile(r"^#\s*-+\s*(.+?)\s*-+\s*$")


def _load_patterns():
    """(compiled_regex, category) from sample (always) UNION local (if present).

    A `# --- label ---` line sets the category. Active rows: a `/regex/` line, or a
    bare case-insensitive literal. Blank lines and other `#` lines are inert, so the
    sample's commented placeholders stay off until copied into the local file.
    """
    out = []
    for path in (_SAMPLE, _LOCAL):
        try:
            with open(path, encoding="utf-8") as fh:
                lines = fh.readlines()
        except FileNotFoundError:
            continue  # local may be absent — baseline (sample) still applies
        category = "denylisted identifier"
        for raw in lines:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("#"):
                m = _HEADER.match(line)
                if m:
                    category = m.group(1)
                continue
            if len(line) >= 2 and line.startswith("/") and line.endswith("/"):
                try:
                    out.append((re.compile(line[1:-1], re.IGNORECASE), category))
                except re.error:
                    continue
            else:
                out.append((re.compile(re.escape(line), re.IGNORECASE), category))
    return out


def _host_allowed(host: str) -> bool:
    host = (host or "").lower()
    return any(host == d or host.endswith("." + d) for d in _WHITELIST)


def evaluate(ev: dict):
    """Return a deny-reason string, or None to allow.

    Pure apart from reading the denylist files. Anything it raises propagates to
    main(), which fails closed.
    """
    tool = ev.get("tool_name", "")
    if tool not in ("WebSearch", "WebFetch"):
        return None
    tool_input = ev.get("tool_input") or {}
    text = json.dumps(tool_input, ensure_ascii=False)
    for rx, category in _load_patterns():
        if rx.search(text):
            return (
                f"[web-egress] blocked: this {tool} query/URL matches a denylisted "
                f"'{category}'. Strip local paths / private identifiers from the request "
                f"and retry. (dev-harness web-egress guard)"
            )
    if tool == "WebFetch":
        host = urlparse(tool_input.get("url", "")).hostname or ""
        if not _host_allowed(host):
            return (
                f"[web-egress] WebFetch to non-whitelisted domain "
                f"'{host or tool_input.get('url', '')}'. Only scholarly primaries / greylist "
                f"are allowed (see docs/dev-loops/RESEARCH_LADDER_AND_WEB_EGRESS.md §6)."
            )
    return None


def _deny(reason: str) -> None:
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": "deny",
        "permissionDecisionReason": reason,
    }}))


def main() -> int:
    try:
        ev = json.loads(sys.stdin.read() or "{}")
        reason = evaluate(ev)
    except Exception:
        _deny("[web-egress] guard internal error; failing closed.")
        return 0
    if reason is not None:
        _deny(reason)
    return 0


if __name__ == "__main__":
    sys.exit(main())
