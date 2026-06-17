# SK_EFT_Hawking/scripts/tests/test_system2.py
import importlib.util
import sys
from pathlib import Path
SCRIPTS = Path(__file__).resolve().parent.parent


def _load(m):
    s = importlib.util.spec_from_file_location(m, SCRIPTS / f"{m}.py")
    mod = importlib.util.module_from_spec(s)
    sys.modules[m] = mod            # register before exec (canonical importlib pattern)
    s.loader.exec_module(mod)
    return mod


def test_upsert_dedups_and_increments(tmp_path):
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    f = {"class": "friction", "title": "re-derived the clean-build incantation",
         "why": "wasted cycles", "how_to_apply": "use /skeft-qa:sync", "tier": "agent-reviewed",
         "occurrences": [{"date": "2026-06-16", "session_id": "a", "roadmap": "R", "compact_event_id": "a:100"}]}
    s2.upsert(reg, dict(f))
    s2.upsert(reg, {**f, "occurrences": [{"date": "2026-06-16", "session_id": "a", "roadmap": "R", "compact_event_id": "a:200"}]})
    same = [i for i in s2.load(reg) if i["title"] == f["title"]]
    assert len(same) == 1                      # deduped by id
    assert len(same[0]["occurrences"]) == 2    # both DISTINCT compact-events recorded


def test_upsert_idempotent_on_same_compact_event(tmp_path):
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    f = {"class": "friction", "title": "x", "why": "", "how_to_apply": "", "tier": "agent-reviewed",
         "occurrences": [{"date": "2026-06-16", "session_id": "a", "roadmap": "R", "compact_event_id": "a:1"}]}
    s2.upsert(reg, dict(f)); s2.upsert(reg, dict(f))            # same (session, compact_event) twice
    same = [i for i in s2.load(reg) if i["title"] == "x"]
    assert len(same) == 1 and len(same[0]["occurrences"]) == 1  # NOT double-counted


def test_upsert_never_downgrades_human_reviewed(tmp_path):
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    base = {"class": "friction", "title": "x", "why": "", "how_to_apply": "",
            "occurrences": [{"date": "2026-06-16", "session_id": "a", "roadmap": "R", "compact_event_id": "a:1"}]}
    s2.upsert(reg, {**base, "tier": "human-reviewed"})
    s2.upsert(reg, {**base, "tier": "agent-reviewed",
                    "occurrences": [{"date": "2026-06-17", "session_id": "b", "roadmap": "R", "compact_event_id": "b:1"}]})
    same = [i for i in s2.load(reg) if i["title"] == "x"][0]
    assert same["tier"] == "human-reviewed"    # never knocked back down by a re-harvest


def test_round_trip_preserves_special_chars_and_goal_pointer(tmp_path):
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    f = {"class": "friction", "title": 'weird `backticks`, ## hashes and "quotes"',
         "why": "a\nmultiline\nwhy", "how_to_apply": "use `/skeft-qa:sync`", "tier": "agent-reviewed",
         "occurrences": [{"date": "2026-06-16", "session_id": "a", "goal_id": "20260616T142231",
                          "goal_prompt": "docs/dev-loops/R/goal_prompt_20260616T142231.md", "roadmap": "R",
                          "compact_event_id": "a:1"}]}
    s2.upsert(reg, dict(f))
    got = [i for i in s2.load(reg) if i["class"] == "friction"][0]
    assert got["title"] == f["title"] and got["why"] == f["why"]   # lossless markdown<->JSON
    occ = got["occurrences"][0]                                    # the goal pointer (spec A.4/A.5) round-trips too
    assert occ["goal_id"] == "20260616T142231"
    assert occ["goal_prompt"] == "docs/dev-loops/R/goal_prompt_20260616T142231.md"


def test_upsert_public_leak_scrub_drops_private_token(tmp_path, monkeypatch):
    """Deterministic public-only leak-scrub at the write choke point: a finding naming the private repo is
    DROPPED, with the private token discovered at RUNTIME (no hardcoded private name in the public source)."""
    s2 = _load("system2_register")
    ws = tmp_path / "ws"
    (ws / "SK_EFT_Hawking" / ".git").mkdir(parents=True)
    (ws / "PrivThing" / ".git").mkdir(parents=True)
    (ws / ".mcp.json").write_text("{}")
    monkeypatch.setattr(s2, "find_workspace", lambda *a, **k: ws)
    reg = ws / "SK_EFT_Hawking" / "docs" / "dev-loops" / "SYSTEM2_REGISTER.md"
    reg.parent.mkdir(parents=True)
    clean = {"class": "friction", "title": "re-derived sync", "why": "", "how_to_apply": "", "tier": "agent-reviewed",
             "occurrences": [{"date": "2026-06-16", "session_id": "a", "roadmap": "R", "compact_event_id": "a:1"}]}
    leaky = {**clean, "class": "leak", "title": "touched PrivThing internals"}
    assert s2.upsert(reg, dict(clean)) is True     # kept
    assert s2.upsert(reg, dict(leaky)) is False    # DROPPED by the runtime-discovered public scrub
    titles = {i["title"] for i in s2.load(reg)}
    assert "re-derived sync" in titles and "touched PrivThing internals" not in titles


def test_write_active_issues_is_register_wide_not_session_scoped(tmp_path):
    """The consolidator must refresh a compact `active System-2 issues` view (spec 6.3 / A.4) that Plan 1's
    SessionStart re-injection + AskUserQuestion redirect read. "Active" = REGISTER-WIDE: every open/unresolved
    finding in the register, NOT filtered to the current session/loop/goal — a lesson from a *prior* loop is
    exactly what a *new* loop should re-ground on. A finding is active until RESOLVED (closed by the user,
    superseded, or promoted to a System-1 gate). The view pulls open findings register-wide; closed excluded;
    no session_id/goal_id filter is applied. (Open/recurring only.)"""
    import json
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    # An open finding from a PRIOR loop (session "a", goal "g-prior") must still surface for a NEW loop.
    s2.upsert(reg, {"class": "friction", "title": "open one", "why": "", "how_to_apply": "", "tier": "agent-reviewed",
                    "status": "open",
                    "occurrences": [{"date": "2026-06-16", "session_id": "a", "goal_id": "g-prior",
                                     "goal_prompt": "docs/dev-loops/R/goal_prompt_g-prior.md", "roadmap": "R",
                                     "compact_event_id": "a:1"}]})
    # A DIFFERENT session/goal — register-wide means this is NOT filtered out by a session/goal scope.
    s2.upsert(reg, {"class": "friction", "title": "other-loop one", "why": "", "how_to_apply": "", "tier": "agent-reviewed",
                    "status": "open",
                    "occurrences": [{"date": "2026-06-17", "session_id": "b", "goal_id": "g-other",
                                     "goal_prompt": "docs/dev-loops/R/goal_prompt_g-other.md", "roadmap": "R",
                                     "compact_event_id": "b:1"}]})
    s2.upsert(reg, {"class": "friction", "title": "closed one", "why": "", "how_to_apply": "", "tier": "human-reviewed",
                    "status": "closed",
                    "occurrences": [{"date": "2026-06-16", "session_id": "a", "goal_id": "g-prior", "roadmap": "R",
                                     "compact_event_id": "a:2"}]})
    out = tmp_path / "active_issues.json"
    s2.write_active_issues(reg, out)              # derived from the tracked register, register-wide (no session/goal filter)
    view = json.loads(out.read_text())
    titles = {i["title"] for i in view["issues"]}
    assert "open one" in titles and "other-loop one" in titles          # register-wide: both open findings, any session/goal
    assert "closed one" not in titles                                   # resolved (closed) excluded
    row = [i for i in view["issues"] if i["title"] == "open one"][0]
    assert row["tier"] == "agent-reviewed" and row["tally"] == 1        # {title, tier, tally} shape


def test_write_active_issues_caps_at_top_8_sorted_by_tier_then_tally(tmp_path):
    """[BLOCKER C1] The view is BOUNDED so Plan 1's `build_reorientation_payload` (which caps the assembled
    payload < 9000 chars to stay under the 10k `additionalContext` limit, spec 4) has a bounded input: AT MOST
    the top 8 open/recurring findings, sorted by tier (human-reviewed > agent-reviewed > automatic) desc, then
    tally desc. (These numbers MUST match Plan 1: 9000-char payload cap, top-8 active issues.)"""
    import json
    s2 = _load("system2_register")
    reg = tmp_path / "SYSTEM2_REGISTER.md"
    # 12 open findings: mixed tiers + tallies, so both sort keys are exercised.
    def occ(n):  # n distinct compact-events -> tally n
        return [{"date": "2026-06-16", "session_id": "s", "goal_id": "g", "goal_prompt": "docs/dev-loops/R/goal_prompt_g.md",
                 "roadmap": "R", "compact_event_id": "s:%d" % i}
                for i in range(n)]
    rows = [
        ("automatic", 9, "auto-hi"), ("automatic", 1, "auto-lo"),
        ("agent-reviewed", 7, "agent-mid"), ("agent-reviewed", 2, "agent-lo"),
        ("human-reviewed", 1, "human-lo"), ("human-reviewed", 5, "human-hi"),
        ("agent-reviewed", 8, "agent-hi"), ("agent-reviewed", 3, "agent-3"),
        ("automatic", 4, "auto-mid"), ("human-reviewed", 2, "human-2"),
        ("agent-reviewed", 6, "agent-6"), ("agent-reviewed", 4, "agent-4"),
    ]
    for tier, n, title in rows:
        s2.upsert(reg, {"class": "friction", "title": title, "why": "", "how_to_apply": "", "tier": tier,
                        "status": "open", "occurrences": occ(n)})
    out = tmp_path / "active_issues.json"
    s2.write_active_issues(reg, out)
    issues = json.loads(out.read_text())["issues"]
    assert len(issues) <= 8                                  # bounded source for Plan 1's bounded payload
    # human-reviewed rows (2 of them) sort first regardless of tally; within a tier, tally desc.
    assert [i["title"] for i in issues[:2]] == ["human-hi", "human-2"]   # tier desc dominates
    tiers = ["human-reviewed", "agent-reviewed", "automatic"]
    keys = [(tiers.index(i["tier"]), -i["tally"]) for i in issues]
    assert keys == sorted(keys)                              # tier desc, then tally desc


def test_propose_gate_fires_at_three_distinct_compact_events(tmp_path):
    """GAP-A (spec 13): >=3 DISTINCT compact-events -> draft proposal; 2 do not; idempotent.
    Counting is decoupled from extraction granularity — a compact-delta counts as one event."""
    s2 = _load("system2_register")
    proposals = tmp_path / "proposals"

    def occ(ids):
        return [{"date": "2026-06-16", "session_id": "s", "compact_event_id": c} for c in ids]

    f2 = {"id": "friction-two", "class": "friction", "title": "two", "why": "", "how_to_apply": "",
          "tier": "agent-reviewed", "occurrences": occ(["s:1", "s:2"])}
    f3 = {"id": "friction-three", "class": "friction", "title": "three", "why": "", "how_to_apply": "",
          "tier": "agent-reviewed", "occurrences": occ(["s:1", "s:2", "s:3"])}
    assert s2.propose_gate(f2, proposals) is False     # 2 distinct events -> no proposal
    assert not (proposals / "friction-two.md").exists()
    assert s2.propose_gate(f3, proposals) is True      # 3 distinct events -> proposal drafted
    assert (proposals / "friction-three.md").exists()
    assert s2.propose_gate(f3, proposals) is False     # idempotent: already proposed -> no-op
