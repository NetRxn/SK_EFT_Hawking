#!/usr/bin/env python3
"""System-2 dev-process findings register + consolidator (spec 6.2/6.3/A.4).

A tracked, tiered, human-readable markdown register that is ALSO structured: each
finding is a `### <id>` block carrying its full record as a fenced ```json``` payload,
so load()->upsert()->render() is lossless (escaping is JSON's job). Mirrors QI_REGISTER.md
so it reads familiar, but is a SEPARATE store from System 1 (no ReviewFinding/graph/AGE).

Finding record:
  {id, class, title, why, how_to_apply, tier in {automatic,agent-reviewed,human-reviewed},
   first_seen, last_seen (ISO-8601 UTC DATETIME — auto-stamped at write time on creation / a new
   occurrence; finer than a bare date), occurrences:[{date, session_id, goal_id, goal_prompt,
   roadmap, compact_event_id}], status in {open,closed,misfiled}, evidence}
   (status "misfiled" = noise / goal-specific confirmation that was never a real finding; rendered under
    ## Misfiled, excluded from the active-issues view like closed. The HARVEST never writes misfiled —
    it drops noise instead; misfiled is `/debrief`'s human sweep bucket. Wins (status "win") are NOT
    injected — they reach the loop via /debrief -> human-reviewed -> harness integration. Tier is clamped
    to <= agent-reviewed on every write except /debrief's --promote: see _clamp_tier.)

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


def _clamp_tier(tier, allow_human):
    """Harvest-origin writes are capped at <= agent-reviewed — the DETERMINISTIC block on the
    tier-as-visibility-lever self-promotion vector (an agent must not self-promote a finding to
    human-reviewed to improve its odds of surviving the post-compact active-issues cut). Only
    `/debrief` (the human governor, via the --promote flag -> allow_human=True) may set
    human-reviewed. The never-downgrade safeguard for a GENUINE human-reviewed finding is kept
    separately in upsert/group."""
    if not allow_human and TIER_ORDER.get(tier, 0) > TIER_ORDER["agent-reviewed"]:
        return "agent-reviewed"
    return tier


def _now_iso():
    """UTC datetime at second precision — datetime-granular first/last_seen (vs a bare date), stamped
    deterministically at write time on finding-creation / a new occurrence (no LLM dependency)."""
    import datetime

    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


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


def upsert(path, finding, allow_human=False):
    """Insert or merge `finding` into the register at `path`. Returns True if written,
    False if dropped by the public leak-scrub. Dedups by id; merges occurrences
    idempotently; widens first/last_seen; raises tier monotonically (never downgrades).
    Tier is CLAMPED to <= agent-reviewed unless `allow_human` (only `/debrief`'s --promote) —
    the deterministic block on harvest self-promotion to human-reviewed; the never-downgrade of
    a GENUINE human-reviewed finding is preserved below (clamped nt never lowers an existing et)."""
    if _should_drop(path, finding):
        return False
    finding = dict(finding)
    fid = finding.get("id") or slug(finding)
    finding["id"] = fid
    finding.setdefault("status", "open")
    finding.setdefault("occurrences", [])
    finding["tier"] = _clamp_tier(finding.get("tier", "automatic"), allow_human)
    findings = load(path)
    idx = next((i for i, x in enumerate(findings) if x.get("id") == fid), None)
    if idx is None:
        # F30: datetime-granular seen-stamps — auto-stamp at write time when not supplied.
        finding["first_seen"] = finding.get("first_seen") or _now_iso()
        finding["last_seen"] = finding.get("last_seen") or _now_iso()
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
        existing_occ = existing.get("occurrences", [])
        merged["occurrences"] = _merge_occurrences(existing_occ, finding.get("occurrences", []))
        # status: a new explicit status wins (e.g. /debrief closing a finding)
        merged["status"] = finding.get("status") or existing.get("status", "open")
        # F30: datetime-granular seen-stamps. first_seen preserved; last_seen bumped to NOW only on a
        # genuinely-new occurrence (the harvest re-observing it) — NOT on a status/evidence-only edit
        # (e.g. /debrief closing), so a close never masquerades as a fresh sighting.
        merged["first_seen"] = existing.get("first_seen") or finding.get("first_seen") or _now_iso()
        if len(merged["occurrences"]) > len(existing_occ):
            merged["last_seen"] = _now_iso()
        else:
            merged["last_seen"] = existing.get("last_seen") or finding.get("last_seen") or merged["first_seen"]
        findings[idx] = merged
    render(path, findings)
    return True


def group(path, absorb_ids, into, allow_human=False):
    """Combine the findings whose ids are in `absorb_ids` into the single `into` record, REMOVING the
    originals — the 'combine' op that upsert (add/merge-by-id) lacks, so the register-aware consolidator
    (and `/debrief`) can collapse semi-related findings into one. GUARDRAIL: a `human-reviewed` finding
    is NEVER absorbed (human curation is not dissolved unattended — relate / stack / re-open those
    instead); such ids are skipped and returned. Absorbed occurrences are merged into `into` so the
    tally/dates survive. The public leak-scrub still applies to `into`. Returns (absorbed, skipped, dropped)."""
    findings = load(path)
    by = {f.get("id"): f for f in findings}
    skipped = [i for i in absorb_ids if i in by and by[i].get("tier") == "human-reviewed"]
    absorb = {i for i in absorb_ids if i in by and i not in skipped}
    into = dict(into)
    into["id"] = into.get("id") or slug(into)
    into.setdefault("status", "closed")
    into["tier"] = _clamp_tier(into.get("tier", "automatic"), allow_human)
    occ = list(into.get("occurrences", []))
    for i in absorb:
        occ = _merge_occurrences(occ, by[i].get("occurrences", []))
    into["occurrences"] = occ
    dates = [d for d in _occ_dates(into) if d]
    into.setdefault("first_seen", min(dates) if dates else None)
    into.setdefault("last_seen", max(dates) if dates else None)
    kept = [f for f in findings if f.get("id") not in absorb and f.get("id") != into["id"]]
    if _should_drop(path, into):
        render(path, kept)
        return len(absorb), skipped, True
    kept.append(into)
    render(path, kept)
    return len(absorb), skipped, False


def render(path, findings=None):
    """Write the register: ## Open / ## Process Wins / ## Closed / ## Misfiled sections of `### <id>`
    blocks, each carrying the full record as a fenced ```json```. Idempotent + round-trip-safe.

    `## Process Wins` (status == "win") holds notable, reusable best practices (the "extremely well"
    side) — preserved + separated from open issues, and (like open issues) surfaced in active-issues.
    `## Misfiled` (status == "misfiled") is the quarantine bucket for harvest entries that are
    tactic-level noise or goal-specific single-occurrence confirmations — true but never standing
    findings. NOT "closed" (those were resolved); "misfiled" = should not have been a finding.
    A small number of broad catch-all misfiled records absorb the pattern; future repeats append
    to one rather than opening new findings. write_active_issues() filters open-only, so misfiled
    (like closed) is excluded from the SessionStart re-injection."""
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

    for status, header in (("open", "## Open"), ("win", "## Process Wins"),
                           ("closed", "## Closed"), ("misfiled", "## Misfiled")):
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
    """Refresh the REGISTER-WIDE active-issues view (spec 6.3/A.4): every OPEN finding (NOT scoped to
    any session/goal/loop), bounded to the top-ACTIVE_ISSUES_MAX by tier desc then tally desc. Shape:
    {generated, issues:[{title, tier, tally, kind="issue"}]}. Process wins are NOT included (ruling
    2026-06-20: a win reaches the loop via /debrief -> human-reviewed -> harness integration
    (CLAUDE.md / skill / bootstrap), never the injection payload). The gitignored cache Plan 1's
    SessionStart re-inject + AskUserQuestion redirect read."""
    findings = load(reg_path)
    # "Active" = OPEN issues ONLY. Process wins are NOT injected (ruling 2026-06-20): a win's route
    # to in-loop visibility is /debrief -> human-reviewed -> INTEGRATION into the harness (CLAUDE.md /
    # the relevant skill / context bootstrap), not the re-injection payload. Injecting wins bloated the
    # <9000-char payload, was self-congratulatory, and created the tier-as-visibility gaming incentive
    # (see _clamp_tier). win/closed/misfiled are all excluded here.
    active = [f for f in findings if f.get("status", "open") == "open"]
    active.sort(key=lambda f: (TIER_PRIORITY.get(f.get("tier", "automatic"), 3),
                               -len(f.get("occurrences", []))))
    issues = [{"title": f.get("title", ""), "tier": f.get("tier", "automatic"),
               "tally": len(f.get("occurrences", [])), "kind": "issue"}
              for f in active[:ACTIVE_ISSUES_MAX]]
    if out_path is None:
        # Repo-relative (system2_register.py lives at <repo>/scripts/), so this needs no
        # find_workspace AND ports VERBATIM to the private sibling repo's copy without
        # hardcoding any repo name — <repo>/.claude/dev-harness/active_issues.json is exactly
        # what Plan 1's harness_common.active_issues_path(repo_root) reads on each side.
        out_path = Path(__file__).resolve().parent.parent / ".claude" / "dev-harness" / "active_issues.json"
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"generated": time.time(), "issues": issues}, indent=2))
    return out_path


def _default_register():
    """The tracked public register path (<repo>/docs/dev-loops/SYSTEM2_REGISTER.md)."""
    return Path(__file__).resolve().parent.parent / "docs" / "dev-loops" / "SYSTEM2_REGISTER.md"


def _default_proposals_dir():
    return Path(__file__).resolve().parent.parent / "docs" / "dev-loops" / "proposals"


def _distinct_compact_events(finding):
    return {o.get("compact_event_id") for o in finding.get("occurrences", []) if o.get("compact_event_id")}


def _proposal_text(finding, distinct):
    return (
        "# GAP-A proposal: structural prevention for `{id}`\n\n".format(id=finding.get("id", "?"))
        + "> **Draft for HUMAN SIGN-OFF (spec 13 / ADR-004 pathway-2). NOT auto-applied.**\n\n"
        + "**Finding:** {0}\n\n".format(finding.get("title", ""))
        + "**Class:** `{0}`  ·  **Tier:** `{1}`\n\n".format(finding.get("class", ""), finding.get("tier", ""))
        + "**Why it matters:** {0}\n\n".format(finding.get("why", "") or "(see register)")
        + "**Recurrence:** {0} distinct compact-events: {1}\n\n".format(
            len(distinct), ", ".join(sorted(str(d) for d in distinct)))
        + "**Proposed structural prevention** (the recurring discipline mechanized into a gate — "
        + "fill in + sign off before adding):\n"
        + "- For a goal-authoring pattern: a `goal-prompt` reference / authoring-checklist tweak.\n"
        + "- For a harness-component pattern: a new deterministic `validate.py` check (or harness assert).\n"
        + "- For a tactical-friction pattern: a `/sync`-style automation or a docs fix.\n\n"
        + "**Suggested how-to-apply (from the finding):** {0}\n\n".format(
            finding.get("how_to_apply", "") or "(none recorded)")
        + "_Promote via `/skeft-qa:debrief` (human judgment); never auto-add a hard gate._\n"
    )


def propose_gate(finding, proposals_dir=None):
    """GAP-A graduation (spec 13): when a finding has recurred across >= 3 DISTINCT compact-events,
    write a draft proposed-structural-prevention spec to proposals/<id>.md FOR HUMAN SIGN-OFF
    (never auto-add a gate). Idempotent — one proposal per id. Returns True iff a NEW proposal was
    written, False otherwise (< 3 distinct events, or already proposed). The threshold counts
    DISTINCT compact_event_ids (occurrences are idempotent by (session_id, compact_event_id) in
    upsert), so a pre-vs-post-compact delta counts as one event like any other (counting is
    decoupled from extraction granularity, spec 13 v4.0 relaxation)."""
    distinct = _distinct_compact_events(finding)
    if len(distinct) < 3:
        return False
    pdir = Path(proposals_dir) if proposals_dir else _default_proposals_dir()
    fid = finding.get("id") or slug(finding)
    out = pdir / (fid + ".md")
    if out.exists():
        return False   # idempotent — one proposal per id
    pdir.mkdir(parents=True, exist_ok=True)
    out.write_text(_proposal_text(finding, distinct))
    return True


def main(argv=None):
    ap = argparse.ArgumentParser(description="System-2 dev-process findings register.")
    ap.add_argument("--register", default=str(_default_register()),
                    help="register path (default: <repo>/docs/dev-loops/SYSTEM2_REGISTER.md)")
    ap.add_argument("--upsert", action="store_true", help="read one finding as JSON from stdin and upsert")
    ap.add_argument("--group", action="store_true",
                    help='combine findings: stdin JSON {"absorb":[ids],"into":{record}} -> remove the '
                         'originals, write the grouped record (human-reviewed ids are never absorbed)')
    ap.add_argument("--promote", action="store_true",
                    help="permit setting human-reviewed (DEBRIEF ONLY — the human governor). Without it, "
                         "--upsert/--group clamp tier to <= agent-reviewed (harvest must NOT self-promote).")
    ap.add_argument("--render", action="store_true", help="rewrite the register from its own contents")
    ap.add_argument("--write-active-issues", action="store_true", help="refresh active_issues.json")
    ap.add_argument("--out", default=None, help="active_issues.json path (with --write-active-issues)")
    ap.add_argument("--propose-gate", action="store_true",
                    help="draft GAP-A gate proposals for findings recurred across >=3 distinct compact-events")
    a = ap.parse_args(argv)
    if a.upsert:
        try:
            finding = json.load(sys.stdin)
        except Exception as e:
            print("ERROR: --upsert expects one finding as JSON on stdin: " + str(e), file=sys.stderr)
            return 2
        ok = upsert(a.register, finding, allow_human=a.promote)
        print("upserted" if ok else "dropped (leak-scrub)")
        return 0 if ok else 1
    if a.group:
        try:
            payload = json.load(sys.stdin)
            absorb_ids, into = payload["absorb"], payload["into"]
        except Exception as e:
            print('ERROR: --group expects {"absorb":[ids],"into":{record}} on stdin: ' + str(e), file=sys.stderr)
            return 2
        n, skipped, dropped = group(a.register, absorb_ids, into, allow_human=a.promote)
        if dropped:
            print("grouped: removed {0} originals but target DROPPED by leak-scrub".format(n))
            return 1
        msg = "grouped {0} finding(s) -> 1".format(n)
        if skipped:
            msg += "; skipped {0} human-reviewed (not absorbed): {1}".format(len(skipped), ", ".join(skipped))
        print(msg)
        return 0
    if a.render:
        render(a.register)
        print("rendered " + a.register)
        return 0
    if getattr(a, "write_active_issues"):
        out = write_active_issues(a.register, a.out)
        print("active-issues -> " + str(out))
        return 0
    if getattr(a, "propose_gate"):
        n = sum(1 for f in load(a.register) if propose_gate(f))
        print("proposed {0} new GAP-A gate draft(s)".format(n))
        return 0
    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
