#!/usr/bin/env python3
"""System-2 dev-process findings register + consolidator (spec 6.2/6.3/A.4).

A tracked, tiered, human-readable markdown register that is ALSO structured: each
finding is a `### <id>` block carrying its full record as a fenced ```json``` payload,
so load()->upsert()->render() is lossless (escaping is JSON's job). Mirrors QI_REGISTER.md
so it reads familiar, but is a SEPARATE store from System 1 (no ReviewFinding/graph/AGE).

Finding record:
  {id, class, title, why, how_to_apply, tier in {automatic,agent-reviewed,human-reviewed},
   first_seen, last_seen, occurrences:[{date, session_id, goal_id, goal_prompt, roadmap,
   compact_event_id}], status in {open,closed}, evidence}

Key invariants (test-locked):
  * dedup by `id` (stable slug of class+title); append-or-update, never duplicate.
  * occurrences idempotent by `(session_id, compact_event_id)` — the GAP-A tally depends on it.
  * tier is MONOTONE-UP (automatic < agent-reviewed < human-reviewed): upsert never downgrades.
  * `write_active_issues` is REGISTER-WIDE (every open finding, any session/goal), bounded to
    the top-8 by tier desc then tally desc (the bounded source for Plan 1's <9000-char payload).
  * public-only leak-scrub DROP-GATE at the write choke point: when the register lives under a
    `SK_EFT_Hawking` dir, DROP any finding whose serialized text contains a RUNTIME-DISCOVERED
    private token (a workspace child repo whose name != SK_EFT_Hawking + variants). The public
    source NEVER hardcodes the private name (the pre-commit leak-guard greps for it).

Bash-callable CLIs (so the unattended harvest writes without the Write tool):
  --upsert (read one finding as JSON from stdin) · --render · --write-active-issues [--out P].
  (--propose-gate is added by Plan 3 Task 5.)

Stdlib only; Python-3.9-safe (no `X | Y` runtime unions, no `match`). The public,
private-name-free resolver from Foundation (a):
"""
import argparse
import json
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # repo root for `src`
from src.core.workspace import find_workspace  # noqa: E402

TIER_ORDER = {"automatic": 0, "agent-reviewed": 1, "human-reviewed": 2}
# active-issues sort priority (human-reviewed first): lower rank = higher priority
TIER_PRIORITY = {"human-reviewed": 0, "agent-reviewed": 1, "automatic": 2}
ACTIVE_ISSUES_MAX = 8   # MUST match Plan 1's build_reorientation_payload top-N
_JSON_FENCE = re.compile(r"```json\n(.*?)\n```", re.DOTALL)


def slug(f):
    """Stable id from class+title (append-or-update keyed by this)."""
    raw = (str(f.get("class", "")) + "-" + str(f.get("title", ""))).lower()
    return re.sub(r"[^a-z0-9]+", "-", raw).strip("-")[:80] or "finding"


def load(path):
    """Parse every fenced ```json``` block into a finding dict. Absent file -> []."""
    p = Path(path)
    if not p.exists():
        return []
    out = []
    for m in _JSON_FENCE.finditer(p.read_text()):
        try:
            out.append(json.loads(m.group(1)))
        except Exception:
            continue
    return out


def _occ_dates(finding):
    return [o.get("date") for o in finding.get("occurrences", []) if o.get("date")]


def _merge_occurrences(existing, new):
    """Merge keyed by (session_id, compact_event_id) — idempotent (no double-count)."""
    seen = set()
    merged = []
    for o in list(existing) + list(new):
        key = (o.get("session_id"), o.get("compact_event_id"))
        if key in seen:
            continue
        seen.add(key)
        merged.append(o)
    return merged


# ── public-only leak-scrub drop-gate (the choke point) ──────────────────────────────
def _private_tokens(reg_path):
    """Runtime-discovered private tokens: workspace child repos whose name != SK_EFT_Hawking,
    plus hyphen-stripped / lower-underscore variants. NEVER a hardcoded private name."""
    try:
        ws = find_workspace(Path(reg_path).resolve().parent)
    except Exception:
        ws = None
    if ws is None:
        return []
    toks = set()
    try:
        for child in Path(ws).iterdir():
            if child.is_dir() and child.name != "SK_EFT_Hawking" and (child / ".git").exists():
                n = child.name
                toks.update({n.lower(), n.replace("-", "").lower(), n.replace("-", "_").lower()})
    except Exception:
        pass
    return [t for t in toks if t]


def _should_drop(reg_path, finding):
    """Active iff the register lives under a SK_EFT_Hawking dir (public). When active, DROP a
    finding whose serialized text contains any runtime-discovered private token."""
    if not any(par.name == "SK_EFT_Hawking" for par in Path(reg_path).resolve().parents):
        return False
    toks = _private_tokens(reg_path)
    if not toks:
        return False
    blob = json.dumps(finding, ensure_ascii=False).lower()
    return any(t in blob for t in toks)


def upsert(path, finding):
    """Insert or merge `finding` into the register at `path`. Returns True if written,
    False if dropped by the public leak-scrub. Dedups by id; merges occurrences
    idempotently; widens first/last_seen; raises tier monotonically (never downgrades)."""
    if _should_drop(path, finding):
        return False
    finding = dict(finding)
    fid = finding.get("id") or slug(finding)
    finding["id"] = fid
    finding.setdefault("status", "open")
    finding.setdefault("occurrences", [])
    findings = load(path)
    idx = next((i for i, x in enumerate(findings) if x.get("id") == fid), None)
    if idx is None:
        dates = _occ_dates(finding)
        finding["first_seen"] = finding.get("first_seen") or (min(dates) if dates else None)
        finding["last_seen"] = finding.get("last_seen") or (max(dates) if dates else None)
        findings.append(finding)
    else:
        existing = findings[idx]
        existing_is_human = existing.get("tier") == "human-reviewed"
        merged = dict(existing)
        # tier monotone-up: never downgrade a human-reviewed finding
        et, nt = existing.get("tier", "automatic"), finding.get("tier", "automatic")
        merged["tier"] = et if TIER_ORDER.get(nt, 0) <= TIER_ORDER.get(et, 0) else nt
        # text fields: preserve human-curated content; otherwise adopt the fresher values
        for k in ("class", "title", "why", "how_to_apply", "evidence"):
            if not existing_is_human and finding.get(k) is not None:
                merged[k] = finding.get(k)
        merged["occurrences"] = _merge_occurrences(existing.get("occurrences", []),
                                                   finding.get("occurrences", []))
        # status: a new explicit status wins (e.g. /debrief closing a finding)
        merged["status"] = finding.get("status") or existing.get("status", "open")
        dates = [d for d in (_occ_dates(merged)) if d]
        merged["first_seen"] = min([d for d in [existing.get("first_seen")] + dates if d] or [None])
        merged["last_seen"] = max([d for d in [existing.get("last_seen")] + dates if d] or [None])
        findings[idx] = merged
    render(path, findings)
    return True


def render(path, findings=None):
    """Write the register: ## Open / ## Closed sections of `### <id>` blocks, each carrying
    the full record as a fenced ```json```. Idempotent + round-trip-safe."""
    if findings is None:
        findings = load(path)
    lines = ["# System-2 Register — dev-process / harness findings",
             "",
             "Tiered (`automatic` < `agent-reviewed` < `human-reviewed`), dev-loop/harness "
             "process findings. SEPARATE from System 1 (paper-correctness QI / `QI_REGISTER.md`). "
             "Each block's fenced `json` payload is the source of truth (round-trip-safe).",
             ""]

    def _block(f):
        head = "### {0}\n\n**{1}**  ·  tier: `{2}`  ·  status: {3}\n".format(
            f.get("id", "?"), f.get("title", ""), f.get("tier", "automatic"),
            f.get("status", "open"))
        body = json.dumps(f, indent=2, ensure_ascii=False)
        return head + "\n```json\n" + body + "\n```\n"

    for status, header in (("open", "## Open"), ("closed", "## Closed")):
        group = [f for f in findings if f.get("status", "open") == status]
        lines.append(header)
        lines.append("")
        if not group:
            lines.append("_(none)_")
            lines.append("")
        for f in group:
            lines.append(_block(f))
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text("\n".join(lines) + "\n")


def write_active_issues(reg_path, out_path=None):
    """Refresh the REGISTER-WIDE active-issues view (spec 6.3/A.4): every open finding,
    NOT scoped to any session/goal/loop, bounded to the top-ACTIVE_ISSUES_MAX by tier desc
    then tally desc. Shape: {generated, issues:[{title, tier, tally}]}. The gitignored cache
    Plan 1's SessionStart re-inject + AskUserQuestion redirect read."""
    findings = load(reg_path)
    open_f = [f for f in findings if f.get("status", "open") == "open"]
    open_f.sort(key=lambda f: (TIER_PRIORITY.get(f.get("tier", "automatic"), 3),
                               -len(f.get("occurrences", []))))
    issues = [{"title": f.get("title", ""), "tier": f.get("tier", "automatic"),
               "tally": len(f.get("occurrences", []))}
              for f in open_f[:ACTIVE_ISSUES_MAX]]
    if out_path is None:
        ws = find_workspace()
        out_path = Path(ws) / "SK_EFT_Hawking" / ".claude" / "skeft-harness" / "active_issues.json"
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"generated": time.time(), "issues": issues}, indent=2))
    return out_path


def _default_register():
    """The tracked public register path (<repo>/docs/dev-loops/SYSTEM2_REGISTER.md)."""
    return Path(__file__).resolve().parent.parent / "docs" / "dev-loops" / "SYSTEM2_REGISTER.md"


def main(argv=None):
    ap = argparse.ArgumentParser(description="System-2 dev-process findings register.")
    ap.add_argument("--register", default=str(_default_register()),
                    help="register path (default: <repo>/docs/dev-loops/SYSTEM2_REGISTER.md)")
    ap.add_argument("--upsert", action="store_true", help="read one finding as JSON from stdin and upsert")
    ap.add_argument("--render", action="store_true", help="rewrite the register from its own contents")
    ap.add_argument("--write-active-issues", action="store_true", help="refresh active_issues.json")
    ap.add_argument("--out", default=None, help="active_issues.json path (with --write-active-issues)")
    a = ap.parse_args(argv)
    if a.upsert:
        try:
            finding = json.load(sys.stdin)
        except Exception as e:
            print("ERROR: --upsert expects one finding as JSON on stdin: " + str(e), file=sys.stderr)
            return 2
        ok = upsert(a.register, finding)
        print("upserted" if ok else "dropped (leak-scrub)")
        return 0 if ok else 1
    if a.render:
        render(a.register)
        print("rendered " + a.register)
        return 0
    if getattr(a, "write_active_issues"):
        out = write_active_issues(a.register, a.out)
        print("active-issues -> " + str(out))
        return 0
    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
