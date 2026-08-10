"""D5 both-directions tests for `validation/checks/bundles_readiness.py` — audit QI-27.

Five checks: `bundle_figure_integrity`, `bundle_metadata_matches_graph`,
`readiness_verdicts_agree`, `bundle_consistency`, `bundle_registry_consistency`.
(`readiness_submission_gate` was mutation-verified under ADR-009 §Deferred item 2 in
`test_readiness_submission_gate.py`.)

THIS MODULE IS WHERE FALSE GREEN LIVES. Its comment history records the same shape
five separate times: a readiness guard that cannot load its dependency, cannot build
its graph, or finds no gate nodes reports *"no disagreement found"* — which is
indistinguishable from agreement. The round-8 reviewer demonstrated it end-to-end:
renaming `evaluate_all_gates` makes `build_graph` emit ZERO ReadinessGate nodes, at
which point **every readiness check passed green with nothing to check**.

Each of those handlers has since been converted from fail-open to fail-closed, and
every one is a leg below. They are the cheapest thing in the suite to regress, because
reverting one restores a check that still *looks* like it is working.

`bundle_registry_consistency` is the H2 roster gate — the roster was hardcoded in
SEVEN places before 2026-07-30, and every omission failed silently and differently.
Its leg C (an AST scan for re-hardcoded rosters) is the structural guard, and the
audit's own QI-01 lesson says to test the scan, not just the count.

MUTATION-VERIFIED 2026-08-04 — 12 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import build_graph  # noqa: E402
import bundle_readiness as br  # noqa: E402
import validate_helpers as _H  # noqa: E402
from validation.checks import bundles_readiness as bru  # noqa: E402


def _agg(blockers=0, advisories=0, readiness=None):
    """The heatmap aggregate shape the checks actually read: `readiness`
    ('RED'/'GREEN'), `blocker_count`, and `severity_mix` (from which the
    advisory count is summed)."""
    return {"blocker_count": blockers,
            "severity_mix": {"minor": advisories},
            "readiness": readiness or ("RED" if blockers else "GREEN")}


def _patch_readiness(monkeypatch, by_bundle, *, gates=(), raise_aggregate=False):
    monkeypatch.setattr(br, "parse_mapping", lambda t: {})
    monkeypatch.setattr(br, "load_findings_by_paper", lambda: {})
    monkeypatch.setattr(br, "resolve_stage13_reviews", lambda backfill=False: {})

    def _agg_fn(*a, **k):
        if raise_aggregate:
            raise RuntimeError("graph build failed")
        return by_bundle
    monkeypatch.setattr(br, "aggregate_by_bundle", _agg_fn)
    monkeypatch.setattr(build_graph, "build_graph_json",
                        lambda: {"nodes": list(gates), "edges": []})


def _gate(bundle: str, state: str, name: str = "FixPropagation"):
    return {"id": f"gate:{bundle}:{name}", "type": "ReadinessGate",
            "meta": {"paper": bundle, "gate": name, "state": state},
            "label": name}


class TestBundleMetadataMatchesGraph:
    """The per-bundle metadata blob must not assert stale finding counts — and must
    not claim `stage13_status: green` while blockers are open."""

    def _meta(self, tmp_path, monkeypatch, bundle, blob):
        """⚠️ The blob path comes from `bundle_readiness._bundle_metadata_path`, NOT
        from `_H.PAPERS_DIR` — the readiness layer owns its own anchor. Patching only
        `_H.PAPERS_DIR` reads the REAL `papers/D1/bundle_metadata.json` and the test
        silently measures the live tree (observed: live blockers_open=37).
        """
        papers = tmp_path / "papers"
        (papers / bundle).mkdir(parents=True, exist_ok=True)
        if blob is not None:
            (papers / bundle / "bundle_metadata.json").write_text(json.dumps(blob))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(br, "_bundle_metadata_path",
                            lambda b: papers / b / "bundle_metadata.json")

    def test_agreeing_metadata_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=0, advisories=3)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 0, "advisories_open": 3, "readiness": "GREEN",
                    "stage13_status": "pending"})
        r = bru.check_bundle_metadata_matches_graph()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_stale_count_ALONE_fails(self, tmp_path, monkeypatch):
        """The count comparison, carrying the verdict alone. Before the 2026-08-07
        split (TODO-D23) the green rule lived in this check and a fixture that set BOTH
        a stale count and `stage13_status: green` let the green rule carry the verdict,
        so the count comparison was never load-bearing — measured: mutating it away was
        MISSED. After the split this check has no other leg, which is the structural
        version of the same guarantee."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2, advisories=5)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 99, "advisories_open": 5, "readiness": "RED",
                    "stage13_status": "pending"})
        r = bru.check_bundle_metadata_matches_graph()
        assert r.passed is False, (
            "a metadata blob asserting 99 open blockers against a live count of 2 "
            "passed — the count comparison no longer reaches the verdict")
        assert any("blockers_open=99 live=2" in (d.message or "") for d in r.details)

    def test_a_missing_metadata_blob_fails_rather_than_skips(self, tmp_path, monkeypatch):
        """D12 round-8: a bundle with no metadata has nothing to disagree with the
        graph, which is not the same as agreeing with it."""
        _patch_readiness(monkeypatch, {"D1": _agg()})
        self._meta(tmp_path, monkeypatch, "D1", None)
        r = bru.check_bundle_metadata_matches_graph()
        assert r.passed is False
        # The dedicated branch is REDUNDANT for the verdict — falling through raises
        # FileNotFoundError, which the unreadable-metadata handler also counts as
        # drift (measured: removing the branch was MISSED). What it uniquely provides
        # is the message: "no bundle_metadata.json at <path>" tells the author what to
        # create, where "metadata unreadable: [Errno 2]" tells them something broke.
        assert any("no bundle_metadata.json at" in (d.message or "") for d in r.details), (
            "the missing-blob case degraded to a generic unreadable-file error — the "
            "message no longer says what to do")

    def test_an_uncomputable_aggregate_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """FAIL, not pass: an uncomputable live verdict is not agreement."""
        _patch_readiness(monkeypatch, {}, raise_aggregate=True)
        self._meta(tmp_path, monkeypatch, "D1", {"blockers_open": 0})
        r = bru.check_bundle_metadata_matches_graph()
        assert r.passed is False
        assert any("UNVERIFIED" in (d.message or "") for d in r.details)


class TestBundleStage13ClaimConsistent:
    """`bundle_stage13_claim_consistent` — split out of `bundle_metadata_matches_graph`
    on 2026-08-07 (TODO-D23, operator authorized). The ASSERTION is unchanged and its
    history is why it exists: its own committed mutation record
    (`2026-08-01-0009-internal-adversarial/D11.md:179`) reads `PASS <-- missed` — the
    TEST existed, the GUARD did not. What changed is that a failure is now reported
    under a name that describes it."""

    _meta = TestBundleMetadataMatchesGraph._meta

    def test_a_pending_status_with_blockers_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. Open blockers are fine; CLAIMING a green review
        against them is not."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=7, advisories=2)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 7, "advisories_open": 2, "readiness": "RED",
                    "stage13_status": "pending"})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_green_with_zero_blockers_passes(self, tmp_path, monkeypatch):
        """The rule is green-WITH-BLOCKERS, not green-is-forbidden. A bundle that
        genuinely cleared Stage 13 must not be flagged here."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=0, advisories=0)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 0, "advisories_open": 0, "readiness": "GREEN",
                    "stage13_status": "green"})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_green_with_open_blockers_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the state 14 of 21 bundles were in until the
        operator's 2026-08-07 demotion."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2, advisories=5)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 2, "advisories_open": 5, "readiness": "RED",
                    "stage13_status": "green"})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False, (
            "stage13_status='green' with 2 open blockers passed — this is the guard "
            "whose absence let 14 bundles sit GREEN with blockers open")

    def test_it_reads_the_LIVE_count_not_the_metadata_claim(self, tmp_path, monkeypatch):
        """CROSS-BRACING, and the reason the split kept the two checks adjacent.
        Hand-editing `blockers_open` to 0 must NOT silence this check — it reads the
        graph. (Doing so trips `bundle_metadata_matches_graph` as well, so both have to
        be defeated rather than one.)"""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2, advisories=5)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 0, "advisories_open": 5, "readiness": "RED",
                    "stage13_status": "green"})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False, (
            "zeroing blockers_open by hand silenced the Stage-13 guard — it must read "
            "the live count, not the metadata's own claim")
        assert bru.check_bundle_metadata_matches_graph().passed is False, (
            "the cross-brace is gone: the hand-edited count no longer trips the "
            "counts check either")

    def test_case_and_whitespace_do_not_evade_it(self, tmp_path, monkeypatch):
        """`'  GREEN '` is the same claim as `'green'`."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=3)})
        self._meta(tmp_path, monkeypatch, "D1",
                   {"blockers_open": 3, "advisories_open": 0, "readiness": "RED",
                    "stage13_status": "  GREEN "})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False

    def test_a_missing_metadata_blob_fails_rather_than_skips(self, tmp_path, monkeypatch):
        """A bundle with no metadata makes no Stage-13 claim, which is not the same as
        making a consistent one."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=1)})
        self._meta(tmp_path, monkeypatch, "D1", None)
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False
        assert any("unverified rather than consistent" in (d.message or "")
                   for d in r.details)

    def test_an_empty_population_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        """SEAM GUARD (authoring guide §2.5). An empty roster is the round-8 state:
        every readiness check green with nothing to check."""
        _patch_readiness(monkeypatch, {})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False, "a check that inspected nothing reported agreement"
        assert r.measured is False
        assert any("UNVERIFIED" in (d.message or "") for d in r.details)

    def test_an_uncomputable_aggregate_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """FAIL, not pass: an uncomputable live verdict is not agreement."""
        _patch_readiness(monkeypatch, {}, raise_aggregate=True)
        self._meta(tmp_path, monkeypatch, "D1", {"stage13_status": "green"})
        r = bru.check_bundle_stage13_claim_consistent()
        assert r.passed is False
        assert any("UNVERIFIED" in (d.message or "") for d in r.details)


class TestReadinessVerdictsAgree:
    """Cross-validate two INDEPENDENT readiness verdicts. The whole value is that
    they are computed by different code, so this check is the one that notices when
    one of them stops computing anything at all."""

    def test_agreement_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — heatmap RED and a blocked gate agree."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2)},
                         gates=[_gate("D1", "blocked")])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_heatmap_red_with_no_blocked_gate_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the submission gate would report this bundle
        as passing while the heatmap shows open blockers."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2)},
                         gates=[_gate("D1", "passed")])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False
        assert any("DISAGREE" in (d.message or "") for d in r.details)

    def test_heatmap_red_with_NO_gate_nodes_fails(self, tmp_path, monkeypatch):
        """D12 round-7 finding 8.2 — the strongest form of the defect: the gate
        cannot report the bundle as blocked because it has nothing to report at all.
        Warning-and-passing here reproduced the original 8.1 failure exactly."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2)},
                         gates=[_gate("D2", "passed")])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False
        assert any("NO ReadinessGate nodes exist for" in (d.message or "")
                   for d in r.details)

    def test_zero_gate_nodes_anywhere_fails(self, tmp_path, monkeypatch):
        """The round-8 demonstration verbatim: renaming `evaluate_all_gates` makes
        build_graph emit ZERO ReadinessGate nodes, at which point every readiness
        check passed green with nothing to check."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=2)}, gates=[])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False, (
            "an empty ReadinessGate population passed — this is the round-8 8.2 "
            "false-green, reopened")

    def test_heatmap_GREEN_while_a_p1_gate_is_blocked_fails(self, tmp_path, monkeypatch):
        """THE REVERSE DIRECTION, and it was LIVE. The first version opened with
        `if readiness != 'RED': continue`, so it was blind BY CONSTRUCTION to a bundle
        the heatmap renders GREEN while a P1 gate is blocked — the same false-green
        shape as the defect it was written for, one layer over. D6 rendered GREEN in
        BUNDLE_READINESS_HEATMAP.md with NarrativeGrounding blocked.

        GREEN is what a reader takes as "ready", and the heatmap counts findings only,
        so it cannot see the gates it does not model.
        """
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=0)},
                         gates=[_gate("D1", "blocked", "NarrativeGrounding")])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False, (
            "a heatmap-GREEN bundle with a BLOCKED P1 gate passed — the reverse "
            "direction is blind again, and it was live on D6")
        assert any("reverse" in (d.message or "").lower() for d in r.details)

    def test_zero_gate_nodes_with_no_RED_bundle_still_fails(self, tmp_path, monkeypatch):
        """The GLOBAL zero-gates guard, isolated. With a RED bundle the per-bundle
        `bundle not in seen_papers` branch also fires, so the global guard is not
        load-bearing there — measured: removing it was MISSED. With every bundle GREEN
        nothing else looks at the gate population at all, and an empty one would sail
        through as 'nothing to cross-check'. That is exactly the round-8 state:
        `evaluate_all_gates` renamed, ZERO gate nodes, every readiness check green."""
        _patch_readiness(monkeypatch, {"D1": _agg(blockers=0)}, gates=[])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False, (
            "an EMPTY ReadinessGate population passed because no bundle happened to be "
            "RED — the global guard is gone, and this is the round-8 8.2 false-green")

    def test_an_uncomputable_heatmap_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """D12 round-7 finding 8.3. An exception inside the heatmap computation must
        not be indistinguishable from 'the two verdicts agree'."""
        _patch_readiness(monkeypatch, {}, raise_aggregate=True,
                         gates=[_gate("D1", "blocked")])
        r = bru.check_readiness_verdicts_agree()
        assert r.passed is False
        assert any("UNVERIFIED" in (d.message or "") for d in r.details)


class TestBundleConsistency:
    """Cross-bundle clusters must agree on numerical content across bundle
    boundaries. Advisory on mismatch; the INPUT being absent is not."""

    def _index(self, tmp_path, monkeypatch, blob):
        papers = tmp_path / "papers"
        papers.mkdir(parents=True, exist_ok=True)
        if blob is not None:
            (papers / "cluster_bundle_index.json").write_text(
                blob if isinstance(blob, str) else json.dumps(blob))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        return bru.check_bundle_consistency()

    def test_no_cross_bundle_clusters_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._index(tmp_path, monkeypatch,
                        {"cluster_count": 3, "clusters": [{"id": "c1"}]})
        assert r.passed is True
        assert any(d.name == "no_cross_bundle_clusters" for d in r.details)

    def test_a_missing_index_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. Cannot-measure is not success: with no index
        the check has verified nothing about cross-bundle agreement."""
        r = self._index(tmp_path, monkeypatch, None)
        assert r.passed is False
        assert "bundle_clusters.py" in (r.error or ""), (
            "the failure must name the command that produces the index")

    def test_an_unreadable_index_fails(self, tmp_path, monkeypatch):
        r = self._index(tmp_path, monkeypatch, "{not json")
        assert r.passed is False

    def test_an_exact_cluster_is_consistent_by_construction(self, tmp_path, monkeypatch):
        """`match_kind: exact` means the members share a normalized hash, so prose
        content agrees by construction — flagging it would manufacture work."""
        r = self._index(tmp_path, monkeypatch, {
            "cluster_count": 1,
            "clusters": [{"id": "c1", "cross_bundle": True, "match_kind": "exact",
                          "bundle_destinations_excluding_flagship": ["D1", "D2"]}]})
        assert r.passed is True
        assert any(d.name.startswith("exact_cluster:") for d in r.details)


class TestBundleRegistryConsistency:
    """The H2 roster gate. Before 2026-07-30 the roster was hardcoded in SEVEN
    places and every omission failed silently and differently."""

    def test_the_live_roster_is_consistent(self):
        """SILENT ON CORRECT DATA — and this one legitimately runs against the real
        tree, because the thing under test IS the repo's own consistency."""
        r = bru.check_bundle_registry_consistency()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_consumer_disagreeing_with_the_registry_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT (leg B) — `bundle_readiness._BUNDLE_ORDER`
        losing a code is exactly how 19 of 21 bundles rendered while looking
        complete."""
        short = {k: v for k, v in list(br._BUNDLE_ORDER.items())[:-1]} \
            if isinstance(br._BUNDLE_ORDER, dict) else list(br._BUNDLE_ORDER)[:-1]
        monkeypatch.setattr(br, "_BUNDLE_ORDER", short)
        r = bru.check_bundle_registry_consistency()
        assert r.passed is False, (
            "a consumer roster missing a bundle passed — leg B is inert, and this is "
            "the silent-omission class the gate exists for")
        assert any("disagrees with bundle_registry" in (d.message or "")
                   for d in r.details)

    def test_a_missing_consumer_attribute_fails(self, monkeypatch):
        """A renamed attribute must fail loudly rather than silently drop a consumer
        out of the gate's scope."""
        monkeypatch.delattr(br, "_BUNDLE_ORDER")
        r = bru.check_bundle_registry_consistency()
        assert r.passed is False
        assert any("update _ROSTER_CONSUMERS" in (d.message or "") for d in r.details)

    def test_a_rehardcoded_roster_literal_is_detected(self, tmp_path, monkeypatch):
        """LEG C, the STRUCTURAL guard. 'They all import the registry' is only true
        until someone writes a new dict — so the scan is what actually holds, and per
        the audit's QI-01 lesson a scan protects the NEXT offender, not just today's.
        """
        import bundle_registry
        codes = sorted(bundle_registry.VALID_BUNDLE_TARGETS)[:bru._ROSTER_LITERAL_THRESHOLD]
        assert len(codes) >= bru._ROSTER_LITERAL_THRESHOLD
        scripts = tmp_path / "scripts"
        scripts.mkdir(parents=True)
        (scripts / "offender.py").write_text(f"ROSTER = {codes!r}\n")
        monkeypatch.setattr(_H, "SCRIPT_DIR", scripts)
        r = bru.check_bundle_registry_consistency()
        assert r.passed is False, (
            f"a literal roster of {len(codes)} bundle codes in a new scripts/*.py was "
            f"not detected — leg C is the only thing preventing re-fragmentation")
        assert any("literal bundle rosters found" in (d.message or "")
                   for d in r.details)

    def test_a_small_incidental_group_is_not_a_roster(self, tmp_path, monkeypatch):
        """The threshold exists so a legitimate grouping — a tier slice, a pair of
        related bundles — is not reported. A guard that fires on correct code gets
        turned off."""
        import bundle_registry
        codes = sorted(bundle_registry.VALID_BUNDLE_TARGETS)[:bru._ROSTER_LITERAL_THRESHOLD - 1]
        scripts = tmp_path / "scripts"
        scripts.mkdir(parents=True)
        (scripts / "innocent.py").write_text(f"PAIR = {codes!r}\n")
        monkeypatch.setattr(_H, "SCRIPT_DIR", scripts)
        r = bru.check_bundle_registry_consistency()
        assert not any("literal bundle rosters found" in (d.message or "")
                       for d in r.details)

    def test_the_registry_itself_is_allowlisted(self, tmp_path, monkeypatch):
        """`bundle_registry.py` is the ONE legitimate home for the literal."""
        assert "bundle_registry.py" in bru._ROSTER_LITERAL_ALLOWLIST

    def test_validate_is_a_declared_roster_consumer(self):
        """⚠️ ADR-009 H2. `_ROSTER_CONSUMERS` contains `("validate", ("BUNDLE_CODES",))`,
        and REMOVING that entry is PROHIBITED — it would drop `validate` from the
        single-source-of-truth gate that exists because the roster was once hardcoded
        in seven places. The Phase-2 package split had to keep `BUNDLE_CODES` reachable
        as `validate.BUNDLE_CODES` precisely for this leg.
        """
        assert ("validate", ("BUNDLE_CODES",)) in bru._ROSTER_CONSUMERS, (
            "the `validate` roster-consumer entry was removed — H2 prohibits this")


class TestBundleFigureIntegrity:
    """Figures must be legible at typeset size. Stage-9 round 3 found figures printing
    at 2–3 pt against 10 pt body text while looking fine as PNGs; round 5 then found
    the checker had ZERO consumers repo-wide — honest but not binding.

    ⚠️ **The first version of this class did not test that.** It patched
    `bundle_figure_typeset_pt` and then pointed `PAPERS_DIR` at an empty tmp tree — so
    every PNG was absent, the check took its `missing_png` branch and `continue`d, and
    the patched function was never called. It asserted `passed is False` and passed,
    for a reason unrelated to its name, while `if pt < FLOOR_PT:` had no coverage at
    all. Found by review, 2026-08-04.

    The fixture below builds a COMPLETE bundle — a real PNG on disk and a stub figure
    function reachable through the derived spec roster — so the legibility branch is
    actually reached. `_typeset_calls` proves it: a test that does not invoke the stub
    is not testing the floor.
    """

    def _bundle(self, tmp_path, monkeypatch, *, pt, with_png=True):
        """Build papers/D11/figures/<name>.png + a spec roster + a stub renderer."""
        import src.core.visualizations as viz

        calls = []

        def _typeset(fig):
            calls.append(fig)
            return pt
        monkeypatch.setattr(viz, "bundle_figure_typeset_pt", _typeset)

        class _Fig:
            def write_image(self, path, scale=1):
                Path(path).write_bytes(b"\x89PNG-fresh")
        monkeypatch.setattr(viz, "fig_d11_stub", lambda: _Fig(), raising=False)

        # The check derives its roster from scripts/review_figures.py's FIGURE_REGISTRY,
        # loading it BY PATH from _H.SCRIPT_DIR — so a stand-in there controls the specs
        # without touching the real registry.
        scripts = tmp_path / "scripts"
        scripts.mkdir(parents=True, exist_ok=True)
        (scripts / "review_figures.py").write_text(
            "from types import SimpleNamespace\n"
            "FIGURE_REGISTRY = [SimpleNamespace(name='d11_stub', function='fig_d11_stub')]\n")
        monkeypatch.setattr(_H, "SCRIPT_DIR", scripts)

        papers = tmp_path / "papers"
        figs = papers / "D11" / "figures"
        figs.mkdir(parents=True, exist_ok=True)
        if with_png:
            (figs / "d11_stub.png").write_bytes(b"\x89PNG-shipped")
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        return calls

    def test_an_illegible_figure_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — 3 pt against a 10 pt body, the Stage-9 round-3
        condition. This is the leg that gives `if pt < FLOOR_PT:` its coverage."""
        calls = self._bundle(tmp_path, monkeypatch, pt=3.0)
        r = bru.check_bundle_figure_integrity()
        assert calls, (
            "bundle_figure_typeset_pt was never called — the check short-circuited "
            "before the legibility branch, so this test is not testing the floor")
        assert r.passed is False, "a 3pt figure passed the legibility floor"
        assert any(d.name.startswith("illegible:") for d in r.details), \
            [d.name for d in r.details]

    def test_a_legible_figure_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — and the other side of the floor, so the comparison
        is pinned by BEHAVIOUR rather than by asserting the constant's value."""
        calls = self._bundle(tmp_path, monkeypatch, pt=9.0)
        r = bru.check_bundle_figure_integrity()
        assert calls, "the legibility branch was not reached"
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert any(d.name.startswith("legible:") for d in r.details)
        assert not any(d.name.startswith("illegible:") for d in r.details)

    def test_the_floor_sits_between_those_two_values(self, tmp_path, monkeypatch):
        """Replaces an AST assertion that `FLOOR_PT == 8.0`, which was a pure
        change-detector: raising the floor to 9 pt is an IMPROVEMENT and would have
        broken it while catching no defect.

        The property that actually matters is that the floor lies in the band where
        3 pt fails and 9 pt passes — which survives a deliberate tightening to 8.5,
        and fails if someone quietly drops it to 2.
        """
        assert self._bundle(tmp_path, monkeypatch, pt=3.0) is not None
        assert bru.check_bundle_figure_integrity().passed is False
        monkeypatch.undo()
        self._bundle(tmp_path, monkeypatch, pt=9.0)
        assert bru.check_bundle_figure_integrity().passed is True

    def test_a_missing_shipped_png_fails(self, tmp_path, monkeypatch):
        """A bundle figure that does not exist on disk cannot have been reviewed, and
        the bundle ships it. Skipping would make absence indistinguishable from
        agreement — this module's recurring defect."""
        self._bundle(tmp_path, monkeypatch, pt=9.0, with_png=False)
        r = bru.check_bundle_figure_integrity()
        assert r.passed is False
        assert any(d.name.startswith("missing_png:") for d in r.details)

    def test_a_missing_render_function_fails(self, tmp_path, monkeypatch):
        """A spec naming a function `visualizations.py` does not export is a broken
        roster, not a clean run."""
        import src.core.visualizations as viz
        self._bundle(tmp_path, monkeypatch, pt=9.0)
        monkeypatch.delattr(viz, "fig_d11_stub")
        r = bru.check_bundle_figure_integrity()
        assert r.passed is False
        assert any(d.name.startswith("missing_fn:") for d in r.details)

    def test_it_skips_cleanly_when_the_helper_is_absent(self, monkeypatch):
        """Optional-toolchain absence is a deliberate PASS (ADR-009 item 4) — but only
        because the helper genuinely may not exist, not as a way of not measuring."""
        import src.core.visualizations as viz
        monkeypatch.delattr(viz, "bundle_figure_typeset_pt")
        r = bru.check_bundle_figure_integrity()
        assert r.passed is True
        assert any(d.name == "skipped" and d.warning for d in r.details)


class TestFigureRegistryIsActuallyDerived:
    """⚠️ PR-review pass 2, R4-MAJ3. `bundle_figure_integrity` derives its figure
    roster from `review_figures.FIGURE_REGISTRY` *"rather than hand-maintained"*,
    with a hardcoded 7-figure literal as the fallback if the registry is
    unreadable.

    The derivation raised on EVERY run, so the fallback always fired: production
    used the hand-maintained list the block exists to replace, and — because the
    derived list happens to equal the fallback today — nothing looked wrong. The
    guarantee that a NEW d11_/d12_ figure gets picked up automatically was dead,
    and would have been discovered only when a new figure shipped unguarded.

    Cause: `importlib.util.module_from_spec` does not register the module in
    `sys.modules`, and Python 3.12+ `@dataclass` dereferences
    `sys.modules.get(cls.__module__).__dict__` while probing for `KW_ONLY`.
    `review_figures.FigureSpec` is a dataclass, so out-of-band execution could
    never succeed.

    A `try/except Exception` around an import is invisible by construction — the
    only way to see it is to perform the load and assert it works.
    """

    def _load_review_figures(self):
        import importlib.util as ilu
        import sys as _sys
        import validate_helpers as _H
        spec = ilu.spec_from_file_location(
            "_review_figures_probe", _H.SCRIPT_DIR / "review_figures.py")
        mod = ilu.module_from_spec(spec)
        _sys.modules[spec.name] = mod          # the line whose absence was the bug
        try:
            spec.loader.exec_module(mod)
        finally:
            _sys.modules.pop(spec.name, None)
        return mod

    def test_review_figures_loads_out_of_band(self):
        """FIRES ON THE SEEDED DEFECT: drop the `sys.modules` registration in
        `bundles_readiness.py` and the check silently reverts to its literal."""
        mod = self._load_review_figures()
        assert hasattr(mod, "FIGURE_REGISTRY"), (
            "review_figures.py executed but exposes no FIGURE_REGISTRY — the "
            "derivation in bundle_figure_integrity would fall back silently")
        assert len(mod.FIGURE_REGISTRY) > 100, (
            f"FIGURE_REGISTRY has only {len(mod.FIGURE_REGISTRY)} specs; the "
            f"registry is the population the roster is derived FROM, so a "
            f"collapsed one makes the derivation vacuous")

    def test_the_check_source_registers_the_module_before_exec(self):
        """Structural backstop. The behavioural test above loads the module
        ITSELF, so it stays green even if `bundles_readiness.py` loses the line —
        a test one level away from the artifact, which is this audit's own
        recurring defect. This asserts against the production source."""
        import validate_helpers as _H
        src = (_H.SCRIPT_DIR / "validation" / "checks" / "bundles_readiness.py").read_text()
        block = src.split("spec_from_file_location", 1)[1].split("exec_module", 1)[0]
        assert "sys.modules[" in block.replace("_sys", "sys"), (
            "bundle_figure_integrity execs review_figures.py without registering "
            "it in sys.modules first — @dataclass will raise AttributeError and "
            "the check will silently use its hardcoded 7-figure fallback (R4-MAJ3)")

    def test_the_derived_roster_matches_what_production_uses(self):
        """The derived roster must be non-empty and consist of real registry
        names — otherwise `if _derived:` falls through to the literal."""
        mod = self._load_review_figures()
        derived = {}
        for fs in mod.FIGURE_REGISTRY:
            if fs.name.startswith(("d11_", "d12_")):
                derived.setdefault(fs.name.split("_")[0].upper(), []).append(fs.name)
        assert derived, ("no d11_/d12_ specs in FIGURE_REGISTRY — the derivation "
                         "raises RuntimeError and falls back to the literal")
        assert set(derived) == {"D11", "D12"}


class TestProducerDemotesGreenOnBlockedP1:
    """⚠️ PR-review pass 2, R4-I8 — the invariant that makes
    `readiness_verdicts_agree`'s reverse branch unreachable, asserted where it
    lives instead of being relied on implicitly.

    The chronology matters:

      2026-07-31  the reverse leg was added to `readiness_verdicts_agree` because
                  `aggregate_by_bundle` was GATE-BLIND — D6 rendered GREEN in the
                  heatmap while `NarrativeGrounding` was blocked.
      2026-08-04  `5228ed6d` made the producer gate-AWARE, demoting GREEN whenever
                  a P1 gate blocks.

    A fix to the producer silently removed a consumer guard's ability to fire, and
    nobody noticed. The guard is retained (it protects against a regression this
    codebase has actually occupied), but relying on a slow graph-building
    cross-check to notice a producer regression is the wrong layer. This asserts it
    directly, in milliseconds.

    ⚠️ Note what R4 filed and I initially repeated: "dead by construction". Measured,
    the leg RUNS — 1 GREEN bundle cross-checked on the live tree. Only its
    disagreement branch is unreachable. "Dead code" and "reachable code with an
    unreachable branch" are different findings with different fixes.
    """

    def test_the_producer_consults_blocked_P1_gates(self):
        """FIRES ON A SEEDED DEFECT: delete the `_blocked_p1_gates_by_paper()` call
        from `aggregate_by_bundle` and the heatmap can issue GREEN over a blocked
        P1 gate again — the exact D6 defect."""
        import ast
        import validate_helpers as _H
        src = (_H.SCRIPT_DIR / "bundle_readiness.py").read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "aggregate_by_bundle")
        # ⚠️ AST, NOT a substring scan. My first version tested
        # `"_blocked_p1_gates_by_paper" in body` and PASSED against a seeded
        # regression, because the function body carries the name in a COMMENT:
        #     # by default (2026-08-04; see `_blocked_p1_gates_by_paper`).
        # That is "seam guard defeatable by prose" — pass 1's R3-C1 — reproduced in
        # a guard written to prevent a different defect. Assert the CALL.
        calls = {getattr(c.func, "id", "") for c in ast.walk(fn) if isinstance(c, ast.Call)}
        assert "_blocked_p1_gates_by_paper" in calls, (
            "aggregate_by_bundle no longer consults blocked P1 gates — the heatmap "
            "can render GREEN for a bundle whose P1 gate is blocked (the 2026-07-31 "
            "D6 defect). readiness_verdicts_agree's reverse branch is the backstop, "
            "but it needs a full graph build to notice; this is the fast layer.")

    def test_the_helper_exists_and_returns_a_mapping(self):
        """Guard the seam: the assertion above is a source scan, so it stays green
        if the function is renamed to a stub. Check the real callable."""
        import bundle_readiness as br
        fn = getattr(br, "_blocked_p1_gates_by_paper", None)
        assert callable(fn), "_blocked_p1_gates_by_paper is gone or not callable"
        out = fn()
        assert isinstance(out, dict), (
            f"_blocked_p1_gates_by_paper returned {type(out).__name__}; "
            f"aggregate_by_bundle indexes it by paper key")


# ═══════════════════════════════════════════════════════════════════════════
# ADR-011 Phase 1 — `bundle_manuscript_length` (Gate 12)
# ═══════════════════════════════════════════════════════════════════════════

class TestBundleManuscriptLength:
    """The compiled article must be the size its declared venue requires.

    Two distinct concerns are tested separately, because they fail differently:
    the POLICY (is this value inside the declared band?) with the measurer stubbed,
    and the MEASURER (may this PDF be trusted at all?) against real files. A single
    end-to-end test of both would pass while either half was wrong.
    """

    def _setup(self, tmp_path, monkeypatch, blobs, measured=None):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, blob in blobs.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            if blob is not None:
                (papers / code / "bundle_metadata.json").write_text(json.dumps(blob))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(blobs))
        if measured is not None:
            monkeypatch.setattr(bru, "_measure_manuscript",
                                lambda code: measured.get(code, (None, None, "stub")))
        return papers

    @staticmethod
    def _blob(floor=24, ceiling=60, unit="pages", **kw):
        t = {"unit": unit, "ceiling": ceiling, "source": "test"}
        if floor is not None:
            t["floor"] = floor
        return {"bundle_target": "D1", "length_target": t,
                "target_journal": "PRD", **kw}

    # ── policy ────────────────────────────────────────────────────────────
    def test_a_manuscript_inside_its_band_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the case the gate must never fire on."""
        self._setup(tmp_path, monkeypatch, {"D1": self._blob()},
                    measured={"D1": (40, "pages", None)})
        r = bru.check_bundle_manuscript_length()
        assert r.passed and r.measured

    def test_over_ceiling_fails(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": self._blob(ceiling=60)},
                    measured={"D1": (61, "pages", None)})
        r = bru.check_bundle_manuscript_length()
        assert not r.passed
        assert any("over_ceiling" == d.name for d in r.details)

    def test_under_floor_is_REPORTED_but_does_not_gate(self, tmp_path, monkeypatch):
        """The live D7 case: 3 pp declared as a ~40 pp article.

        ⚠️ **OPERATOR DECISION 2026-08-09** — verbatim: *"if length of paper is not
        sufficient, it's ok to skip. I don't think it's realistic to write that
        length in many areas."* Under-floor became ADVISORY. This test previously
        asserted `not r.passed`.

        What the decision did NOT authorise, and what this test still pins: the
        finding must still be REPORTED, with its magnitude. Silencing it — or
        lowering the declared floor to match the page count — would erase the
        measurement, and the operator asked to stop blocking, not to stop knowing.
        A ceiling-only gate that emitted NOTHING is how D7 and D10 were closed GREEN
        (audit 2026-08-01 §5.4 Gate 12); that failure mode is still guarded."""
        self._setup(tmp_path, monkeypatch, {"D7": self._blob(floor=24)},
                    measured={"D7": (3, "pages", None)})
        r = bru.check_bundle_manuscript_length()
        assert r.passed, "under-floor is advisory by operator decision"
        under = [d for d in r.details if d.name == "under_floor"]
        assert under, "the gap must still be reported"
        assert under[0].warning is True, "reported as an advisory, visibly"
        assert "24" in under[0].message and "3" in under[0].message, (
            "the magnitude must survive: floor and actual both stated")

    def test_over_ceiling_still_FAILS(self, tmp_path, monkeypatch):
        """The half the operator decision did NOT touch, and the reason it did not:
        a journal rejects an over-length manuscript outright, so this is a real
        submission blocker rather than an aspiration."""
        self._setup(tmp_path, monkeypatch, {"D7": self._blob(floor=24, ceiling=40)},
                    measured={"D7": (99, "pages", None)})
        r = bru.check_bundle_manuscript_length()
        assert not r.passed, "over-ceiling must still gate"
        assert any(d.name == "over_ceiling" and not d.passed for d in r.details)

    def test_a_boundary_value_is_inside_the_band(self, tmp_path, monkeypatch):
        """Inclusive bounds, asserted in both directions so an off-by-one shows up."""
        self._setup(tmp_path, monkeypatch,
                    {"A": self._blob(), "B": self._blob()},
                    measured={"A": (24, "pages", None), "B": (60, "pages", None)})
        assert bru.check_bundle_manuscript_length().passed

    def test_a_letter_with_no_floor_is_never_under(self, tmp_path, monkeypatch):
        """A letter has no floor; `floor: None` must not read as `floor: 0`-and-fail."""
        self._setup(tmp_path, monkeypatch,
                    {"L1": self._blob(floor=None, ceiling=3750,
                                      unit="word_equivalents")},
                    measured={"L1": (12, "word_equivalents", None)})
        assert bru.check_bundle_manuscript_length().passed

    # ── UNMEASURED is not PASS ────────────────────────────────────────────
    def test_no_declared_target_is_unmeasured_not_passing(self, tmp_path, monkeypatch):
        """`length_target: null` is the honest record for an undecided venue.

        It must be VISIBLE and must not count as a sized manuscript — otherwise
        deleting the field is a way to make the gate green.
        """
        self._setup(tmp_path, monkeypatch,
                    {"D1": {"bundle_target": "D1", "length_target": None}},
                    measured={"D1": (999, "pages", None)})
        r = bru.check_bundle_manuscript_length()
        assert not r.passed and not r.measured, "nothing sizable ⇒ UNVERIFIED"
        assert any(d.name == "unmeasured" for d in r.details)

    def test_an_all_unmeasured_population_is_UNVERIFIED_not_passing(
            self, tmp_path, monkeypatch):
        """SEAM GUARD. Zero sizable manuscripts must fail closed.

        The failure this prevents is Stage 9's, exactly: its criterion is "ALL
        figures PASS", which over an empty set is `True`, and that is how a
        zero-figure bundle holds `stage9_status: green`.
        """
        self._setup(tmp_path, monkeypatch, {"D1": self._blob()},
                    measured={"D1": (None, "pages", "no compiled PDF")})
        r = bru.check_bundle_manuscript_length()
        assert not r.passed and not r.measured
        assert any(d.name == "population" for d in r.details)

    def test_one_sizable_bundle_still_judges_that_one(self, tmp_path, monkeypatch):
        """A mixed population is measured on what it can measure, not abandoned."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": self._blob(), "D2": self._blob()},
                    measured={"D1": (3, "pages", None),
                              "D2": (None, "pages", "no compiled PDF")})
        r = bru.check_bundle_manuscript_length()
        assert any(d.name == "under_floor" for d in r.details), (
            "the sized bundle must still be judged and its gap reported")
        assert any(d.name == "unmeasured" for d in r.details), (
            "and the one it could not size must be named, not dropped")
        # ⚠️ `measured=False` on a MIXED population, and that is the point of the
        # fold added 2026-08-09. The check judges what it can size — the assertion
        # above — but it must not report a full measurement over a population it
        # only partly reached: a bundle that goes UNMEASURED also escapes the
        # OVER-CEILING leg, the one that still gates, so staleness was a way to
        # skip the only blocking check here. Without the fold this gate degraded
        # silently from 11 reported gaps to 1 and stayed green.
        assert not r.measured, (
            "a partly-unsizable population is not a full measurement")

    # ── the measurer's trust conditions ───────────────────────────────────
    def test_a_pdf_older_than_the_draft_is_not_trusted(self, tmp_path, monkeypatch):
        """A stale PDF's page count is a previous draft's size.

        Reported UNMEASURED rather than measured, because a number carried over
        from an earlier draft is indistinguishable from this draft's — which is
        also why the check does not read `compiled_pages` from the metadata.
        """
        papers = self._setup(tmp_path, monkeypatch, {"D1": self._blob()})
        tex = papers / "D1" / "paper_draft.tex"
        pdf = papers / "D1" / "paper_draft.pdf"
        pdf.write_bytes(b"%PDF-1.4")
        import os, time
        tex.write_text(r"\documentclass{article}\begin{document}x\end{document}")
        os.utime(pdf, (time.time() - 500, time.time() - 500))
        value, _unit, note = bru._measure_manuscript("D1")
        assert value is None and "older" in note

    def test_a_missing_pdf_names_the_command_that_fixes_it(self, tmp_path, monkeypatch):
        papers = self._setup(tmp_path, monkeypatch, {"D1": self._blob()})
        (papers / "D1" / "paper_draft.tex").write_text("x")
        value, _unit, note = bru._measure_manuscript("D1")
        assert value is None and "compile_bundle_pdf.py D1" in note


class TestBundleReviewerStageOrdering:
    """Stage 13 may not be recorded before Stages 9 and 10 are green.

    `BUNDLE_LIFT_PROCEDURE.md:9` states this as a hard gate and nothing read the
    fields until ADR-011 Phase 2 (= TODO-D24 = the 2026-08-01 audit's Gate 16 #2).
    """

    def _setup(self, tmp_path, monkeypatch, blobs):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, blob in blobs.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            if blob is not None:
                (papers / code / "bundle_metadata.json").write_text(json.dumps(blob))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(blobs))

    @staticmethod
    def _b(s9="green", s10="green", s13="green"):
        return {"stage9_status": s9, "stage10_status": s10, "stage13_status": s13}

    def test_green_after_both_prerequisites_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the whole point is to allow a legitimate green."""
        self._setup(tmp_path, monkeypatch, {"D1": self._b()})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert r.passed and r.measured

    def test_the_live_D6_state_fires(self, tmp_path, monkeypatch):
        """The exact configuration measured on 2026-08-07: a Stage-13 green with
        figure review never started."""
        self._setup(tmp_path, monkeypatch,
                    {"D6": self._b(s9="not_started", s10="skeleton", s13="green")})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert not r.passed
        assert any("not_started" in d.message for d in r.details if d.name == "D6")

    def test_either_prerequisite_alone_is_enough_to_fire(self, tmp_path, monkeypatch):
        """Both directions — a check asserting only one conjunct would pass half of
        the five bundles this was written for (D7 failed on 9, D9 on 10)."""
        self._setup(tmp_path, monkeypatch,
                    {"D7": self._b(s9="not_started"), "D9": self._b(s10="pending")})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert not r.passed
        named = {d.name for d in r.details if not d.passed}
        assert {"D7", "D9"} <= named, f"only {named} reported"

    def test_a_non_green_stage13_asserts_nothing(self, tmp_path, monkeypatch):
        """The antecedent is false, so the implication holds — a bundle mid-cycle
        with unfinished prerequisites is the NORMAL state, not a violation."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": self._b(s9="pending", s10="pending", s13="pending")})
        assert bru.check_bundle_reviewer_stage_ordering().passed

    def test_case_and_whitespace_do_not_evade_it(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": self._b(s9=" NOT_STARTED ", s13="  GREEN ")})
        assert not bru.check_bundle_reviewer_stage_ordering().passed

    def test_an_undeclared_status_value_is_a_finding(self, tmp_path, monkeypatch):
        """A typo must not read as "not green, therefore safe".

        `greeen` is not in the declared set, and silently treating an unknown string
        as non-green is how a status enum rots: the roadmap declares three values,
        the corpus uses seven.
        """
        self._setup(tmp_path, monkeypatch, {"D1": self._b(s9="greeen")})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert not r.passed
        assert any("not a declared status" in d.message for d in r.details)

    def test_a_missing_blob_fails_rather_than_skips(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": None})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert not r.passed
        assert any("unverified rather than correct" in d.message for d in r.details)

    def test_an_empty_roster_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        """SEAM GUARD, and it is load-bearing HERE more than anywhere.

        Every assertion in this check is an implication, and today NO bundle has a
        Stage-13 green — so violations are zero on correct data and on an empty tree
        alike. The guard is on the population read, not on violations found.
        """
        self._setup(tmp_path, monkeypatch, {})
        r = bru.check_bundle_reviewer_stage_ordering()
        assert not r.passed and not r.measured
        assert any(d.name == "population" for d in r.details)

    def test_it_is_silent_where_the_sibling_check_fires(self, tmp_path, monkeypatch):
        """DISJOINTNESS, asserted rather than assumed.

        `bundle_stage13_claim_consistent` catches a green invalidated LATER by
        findings; this catches one invalid WHEN WRITTEN. A bundle whose stages are
        correctly ordered but whose blockers are open is the sibling's business, and
        this check must not double-report it.
        """
        self._setup(tmp_path, monkeypatch, {"D1": self._b()})   # ordering fine
        assert bru.check_bundle_reviewer_stage_ordering().passed


class TestBundleProseEmDashFree:
    """Zero em-dashes in prose a reader will see (ADR-011 Phase 3).

    A trust signal rather than a style rate — one em-dash is as disqualifying as
    forty — so the target is zero and there is no ratchet.

    The tests are weighted toward what this check must NOT do. Flagging an en-dash
    would be far worse than missing an em-dash: `--` is mandatory typography, the
    corpus carries 1,121 of them, and "fixing" those would corrupt every compound
    eponym in the program.
    """

    def _setup(self, tmp_path, monkeypatch, drafts):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, text in drafts.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            if text is not None:
                (papers / code / "paper_draft.tex").write_text(text)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(drafts))

    def test_an_em_dash_inside_an_INPUTED_file_is_flagged(self, tmp_path, monkeypatch):
        r"""⚠️ THE GATE'S BLIND SPOT, found by the closure reviewer and not by the gate.

        It scanned `paper_draft.tex` alone, so `papers/I1/tables/table1_stages.tex`
        carried two reader-visible em-dashes inside a live `\input`ed table and I1
        reported CLEAN. A reader does not know which file a sentence was typed in,
        and a check whose subject is *what a reader sees* cannot stop at a file
        boundary the reader cannot perceive."""
        papers = tmp_path / "papers"
        (papers / "D1" / "tables").mkdir(parents=True)
        (papers / "D1" / "paper_draft.tex").write_text(
            "Clean prose here.\n\\input{tables/t.tex}\n")
        (papers / "D1" / "tables" / "t.tex").write_text(
            "a & Lean --- interactive loop \\\\\n")
        import bundle_registry as registry
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D1",))
        r = bru.check_bundle_prose_em_dash_free()
        assert not r.passed, "an em-dash a reader sees through \\input must be flagged"
        assert "tables/t.tex" in " ".join(d.message for d in r.details), \
            "the finding must name the file the em-dash is actually IN"

    def test_a_bib_entry_in_the_closure_is_NOT_scanned(self, tmp_path, monkeypatch):
        """Discrimination: the closure also carries `.bib` and image paths, and a
        bibliography entry is not manuscript prose. Only `.tex` is scanned."""
        papers = tmp_path / "papers"
        (papers / "D1").mkdir(parents=True)
        (papers / "D1" / "paper_draft.tex").write_text(
            "Clean prose.\n\\bibliography{refs}\n")
        (papers / "D1" / "refs.bib").write_text("@article{x, title={A --- B}}\n")
        import bundle_registry as registry
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D1",))
        assert bru.check_bundle_prose_em_dash_free().passed

    # ── what it must NOT flag ────────────────────────────────────────────
    def test_an_EN_dash_is_never_flagged(self, tmp_path, monkeypatch):
        """THE LOAD-BEARING TEST. Every one of these is correct typography."""
        self._setup(tmp_path, monkeypatch, {"D1":
            "Bose--Einstein and Bekenstein--Hawking, SK--EFT, Kaul--Majumdar, pp. 10--15.\n"})
        r = bru.check_bundle_prose_em_dash_free()
        assert r.passed, [d.message for d in r.details]

    def test_both_dashes_on_ONE_line_are_told_apart(self, tmp_path, monkeypatch):
        """Taken from the live corpus: `observables---also drives the SK--EFT`.
        The em-dash must be caught and the en-dash left alone."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": "observables---also drives the SK--EFT bound.\n"})
        r = bru.check_bundle_prose_em_dash_free()
        assert not r.passed
        assert "1 em-dash" in r.details[0].message

    def test_a_hyphen_is_never_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "A well-known kernel-pure large-N limit.\n"})
        assert bru.check_bundle_prose_em_dash_free().passed

    def test_four_hyphens_are_not_an_em_dash(self, tmp_path, monkeypatch):
        """`----` is a rule or ASCII art, not punctuation. The right-lookahead
        exists for this; without it a decorative separator reads as an em-dash."""
        self._setup(tmp_path, monkeypatch, {"D1": "A table rule ---- here.\n"})
        assert bru.check_bundle_prose_em_dash_free().passed

    def test_an_em_dash_inside_a_COMMENT_is_not_flagged(self, tmp_path, monkeypatch):
        """Comments never reach a reader, so they carry no authorship signal.
        The sweep deliberately left several in place."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": "%% Section 3 --- lifted from phase6v\nClean prose here.\n"})
        assert bru.check_bundle_prose_em_dash_free().passed

    def test_an_ESCAPED_percent_is_not_a_comment(self, tmp_path, monkeypatch):
        r"""`\%` is a literal percent sign in rendered text, so an em-dash after it
        IS visible. Treating it as a comment would blind the check to real prose."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": r"A 50\% improvement --- and it renders." + "\n"})
        assert not bru.check_bundle_prose_em_dash_free().passed

    # ── what it must flag ────────────────────────────────────────────────
    def test_the_ligature_form_is_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": "The result --- surprisingly --- holds.\n"})
        r = bru.check_bundle_prose_em_dash_free()
        assert not r.passed and "2 em-dash" in r.details[0].message

    def test_the_UNICODE_form_is_flagged(self, tmp_path, monkeypatch):
        """120 of the corpus's 741 were literal characters, not ligatures — a check
        matching only `---` would have missed one in six."""
        self._setup(tmp_path, monkeypatch, {"D1": "The result — surprisingly — holds.\n"})
        assert not bru.check_bundle_prose_em_dash_free().passed

    def test_the_report_names_a_findable_location(self, tmp_path, monkeypatch):
        """A count alone is not actionable across a 2,500-line draft."""
        self._setup(tmp_path, monkeypatch, {"D1": "clean\nclean\nhere --- it is\n"})
        r = bru.check_bundle_prose_em_dash_free()
        assert ":3" in r.details[1].message

    # ── population ───────────────────────────────────────────────────────
    def test_an_empty_population_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        """SEAM GUARD — zero em-dashes found across zero drafts is not cleanliness."""
        self._setup(tmp_path, monkeypatch, {})
        r = bru.check_bundle_prose_em_dash_free()
        assert not r.passed and not r.measured
        assert any(d.name == "population" for d in r.details)


class TestBundleReaderFacingVoice:
    """A fix may not narrate itself (ADR-011 Phase 3, F-05).

    The design decision under test is that these patterns match the ACT of
    self-narration, not the vocabulary around it. The audit's proposed word denylist
    (`Stage 13`, `reviewer`, `adversarial review`) scores 90 on this corpus with I1
    holding 48 of them legitimately, because I1's subject matter IS the pipeline.
    Matching the act scores 13 with I1 at zero, so no exemption exists to drift.
    """

    def _setup(self, tmp_path, monkeypatch, drafts):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, text in drafts.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            (papers / code / "paper_draft.tex").write_text(text)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(drafts))

    # ── the four acts ────────────────────────────────────────────────────
    def test_a_dated_correction_is_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "The claim holds (corrected 2026-08-01).\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    def test_an_account_of_an_earlier_draft_is_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "Three earlier drafts of this paragraph said otherwise.\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    def test_a_first_person_superseded_claim_is_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "We previously shipped a theorem asserting X.\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    def test_an_internal_review_reference_is_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "As noted (D11 Stage-13 round-14 finding 6.2) the split holds.\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    # ── what it must NOT flag: the reason the vocabulary version was rejected ──
    def test_the_methodology_paper_describing_the_pipeline_is_CLEAN(
            self, tmp_path, monkeypatch):
        """THE DESIGN TEST. I1 documents the review pipeline; that is its subject.
        A vocabulary denylist scores 48 here. Matching the ACT scores zero."""
        self._setup(tmp_path, monkeypatch, {"I1":
            "Stage 13 is the fresh-context adversarial-reviewer pattern. "
            "Stage~9 runs a figure-reviewer agent, and a BLOCKER finding reopens "
            "the gate. Reviewers cannot run the computations themselves.\n"})
        r = bru.check_bundle_reader_facing_voice()
        assert r.passed, [d.message for d in r.details]

    def test_addressing_the_papers_own_referees_is_CLEAN(self, tmp_path, monkeypatch):
        """I2/I3's live usage: `reviewer` meaning this paper's actual audience."""
        self._setup(tmp_path, monkeypatch, {"I3":
            "The disclosure protocol lets Mathlib4 reviewers calibrate expectations.\n"})
        assert bru.check_bundle_reader_facing_voice().passed

    def test_a_correction_by_OTHERS_is_CLEAN(self, tmp_path, monkeypatch):
        """Reporting that the literature corrected something is ordinary scholarship;
        only the paper narrating its OWN edit history is the defect."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": "Smith corrected this coefficient in 2019.\n"})
        assert bru.check_bundle_reader_facing_voice().passed

    def test_a_lift_banner_in_a_COMMENT_is_not_flagged(self, tmp_path, monkeypatch):
        """The provenance banners live in `%` comments and belong there."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": "%% Lifted from phase6n — corrected 2026-07-31\nClean prose.\n"})
        assert bru.check_bundle_reader_facing_voice().passed

    # ── reporting + population ───────────────────────────────────────────
    def test_the_report_names_the_act_and_a_findable_line(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": "clean\nThe claim holds (corrected 2026-08-01).\n"})
        msg = bru.check_bundle_reader_facing_voice().details[1].message
        assert ":2" in msg and "stamped with its date" in msg

    def test_an_empty_population_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {})
        r = bru.check_bundle_reader_facing_voice()
        assert not r.passed and not r.measured

    # ── the coverage gap a subagent found, and its guard ──────────────────
    def test_internal_planning_documents_are_flagged(self, tmp_path, monkeypatch):
        """A gap the four original patterns missed, reported by the de-scarring agent
        rather than by me. Verified corpus-wide before being added: 4 hits, all
        genuine, zero false positives."""
        self._setup(tmp_path, monkeypatch, {"D1":
            "Our earlier planning documents described this thread as including X.\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    def test_review_rounds_cast_as_actors_are_flagged(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1":
            "Rounds 7 and 10 both rated this cosmetic, and round 12 supplied it.\n"})
        assert not bru.check_bundle_reader_facing_voice().passed

    def test_a_round_NUMBER_alone_is_not_enough(self, tmp_path, monkeypatch):
        """`round 3` needs a review VERB beside it. A bare ordinal is legitimate in
        numerical work (`round 3 of the iteration`), and banning it would be the
        vocabulary mistake this check exists to avoid."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": "Convergence is reached at round 3 of the iteration.\n"})
        assert bru.check_bundle_reader_facing_voice().passed


class TestBundleFigureAdequacy:
    """A bundle carries at least the figures its tier owes a reader (ADR-011 Phase 4).

    Nine of 21 bundles ship zero figures, the flagship among them, because
    `BUNDLE_LIFT_PROCEDURE` §6 only ever MIGRATED figures that already existed in the
    sources. No step planned one.
    """

    def _setup(self, tmp_path, monkeypatch, bundles):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, (tier, body) in bundles.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            (papers / code / "paper_draft.tex").write_text(body)
            (papers / code / "bundle_metadata.json").write_text(
                json.dumps({"bundle_target": code, "tier": tier}))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(bundles))

    @staticmethod
    def _figs(n):
        return "".join("\\begin{figure}x\\end{figure}\n" for _ in range(n))

    def test_a_bundle_meeting_its_floor_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        self._setup(tmp_path, monkeypatch, {"D1": (1, self._figs(4))})
        assert bru.check_bundle_figure_adequacy().passed

    def test_zero_figures_fails_and_says_why(self, tmp_path, monkeypatch):
        """The live case for 9 of 21 bundles, F included."""
        self._setup(tmp_path, monkeypatch, {"F": (0, "no figures here\n")})
        r = bru.check_bundle_figure_adequacy()
        assert not r.passed
        assert "charter defect" in r.details[1].message

    def test_the_floor_is_TIER_dependent(self, tmp_path, monkeypatch):
        """A four-page letter and a review article do not owe the same count. One
        figure passes at tier 2 and fails at tier 0, asserted together so a flat
        floor cannot satisfy this test."""
        self._setup(tmp_path, monkeypatch,
                    {"L1": (2, self._figs(1)), "F": (0, self._figs(1))})
        r = bru.check_bundle_figure_adequacy()
        assert not r.passed
        named = {d.name for d in r.details if not d.passed}
        assert "F" in named and "L1" not in named

    def test_a_declared_deferral_counts_toward_the_floor(self, tmp_path, monkeypatch):
        r"""`\figuredeferred{id}{reason}` is an explicit, reviewable statement that a
        planned figure is not yet drawn. That is categorically different from a
        bundle that never planned one, and must not be punished identically."""
        self._setup(tmp_path, monkeypatch,
                    {"L1": (2, "\\figuredeferred{f1}{awaiting the L=8 run}\n")})
        assert bru.check_bundle_figure_adequacy().passed

    def test_an_unknown_tier_is_UNMEASURED_not_passing_silently(
            self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"X1": (99, "nothing\n")})
        r = bru.check_bundle_figure_adequacy()
        assert any("UNMEASURED" in d.message for d in r.details)

    def test_a_green_cannot_hide_an_ALL_DEFERRED_corpus(self, tmp_path, monkeypatch):
        r"""⚠️ THE GUARD ON THE GREEN (2026-08-09, coach ruling on goal item 6).

        `\figuredeferred` legitimately satisfies the floor — it is the pipeline
        law's mandated disclosure form. But a bundle that has PLANNED four figures
        and a bundle that has DRAWN four are different states, and a summary
        reporting only "0 short" renders them identically. That is the vacuous
        Stage-9 failure ("ALL figures PASS" over an empty set) rebuilt one layer
        up. The split must ride on the SUMMARY, which is the line a reader of a
        passing run actually sees."""
        self._setup(tmp_path, monkeypatch, {
            "D1": (1, "".join("\\figuredeferred{f%d}{blocked on the X run}\n" % i
                              for i in range(4))),
        })
        r = bru.check_bundle_figure_adequacy()
        assert r.passed, "a fully-planned bundle still meets its floor"
        summary = r.details[0].message
        assert "0 drawn" in summary and "4 declared-deferred" in summary
        assert "1 bundle(s) with zero drawn figures" in summary

    def test_the_summary_counts_drawn_and_deferred_separately(
            self, tmp_path, monkeypatch):
        """Discrimination: the two numbers must not be one number wearing two
        labels. Four drawn and four deferred report as 4 and 4, not 8 and 0."""
        self._setup(tmp_path, monkeypatch, {
            "D1": (1, self._figs(4)),
            "D2": (1, "".join("\\figuredeferred{g%d}{blocked on the Y sweep}\n" % i
                              for i in range(4))),
        })
        r = bru.check_bundle_figure_adequacy()
        summary = r.details[0].message
        assert "4 drawn" in summary and "4 declared-deferred" in summary
        assert "1 bundle(s) with zero drawn figures" in summary

    def test_figures_in_a_COMMENT_do_not_count(self, tmp_path, monkeypatch):
        """A commented-out figure is not in the document a reader receives."""
        self._setup(tmp_path, monkeypatch,
                    {"L1": (2, "% \\begin{figure}old\\end{figure}\n")})
        assert not bru.check_bundle_figure_adequacy().passed

    def test_an_empty_population_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {})
        r = bru.check_bundle_figure_adequacy()
        assert not r.passed and not r.measured


class TestBundleStructuralCoherence:
    """A structural floor plus a section ceiling (ADR-011 Phase 4, Gate 14).

    Deliberately much narrower than the audit specified, because two of its four legs
    did not survive measurement. Both rejections are pinned by tests below, so a later
    author cannot reinstate them without a failing test explaining why they were dropped.
    """

    def _setup(self, tmp_path, monkeypatch, bundles):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, (tier, body) in bundles.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            (papers / code / "paper_draft.tex").write_text(body)
            (papers / code / "bundle_metadata.json").write_text(
                json.dumps({"bundle_target": code, "tier": tier}))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(bundles))

    _OK = ("\\begin{abstract}x\\end{abstract}\n\\section{Introduction}\n"
           "\\section{Conclusions}\n\\bibitem{a}x\n")

    def test_a_well_formed_draft_passes(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": (1, self._OK)})
        assert bru.check_bundle_structural_coherence().passed

    def test_a_missing_abstract_fails(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch,
                    {"D1": (1, "\\section{Introduction}\n\\section{Conclusions}\n\\bibitem{a}x\n")})
        assert not bru.check_bundle_structural_coherence().passed

    def test_a_closing_section_may_sit_BEFORE_a_methods_section(
            self, tmp_path, monkeypatch):
        """MY OWN FALSE POSITIVE, pinned. Testing only the LAST section reported 10 of
        21 bundles as having no conclusion when every one of them has one: papers end
        with `Methods and tools disclosure`, `Verification status`, `Code Availability`.
        """
        self._setup(tmp_path, monkeypatch, {"D1": (1,
            "\\begin{abstract}x\\end{abstract}\n\\section{Introduction}\n"
            "\\section{Synthesis and outlook}\n\\section{Methods and tools disclosure}\n"
            "\\bibitem{a}x\n")})
        assert bru.check_bundle_structural_coherence().passed

    def test_no_closing_section_anywhere_fails(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": (1,
            "\\begin{abstract}x\\end{abstract}\n\\section{Introduction}\n"
            "\\section{Results}\n\\section{Tables}\n\\bibitem{a}x\n")})
        assert not bru.check_bundle_structural_coherence().passed

    def test_EITHER_bibliography_mechanism_is_accepted(self, tmp_path, monkeypatch):
        r"""THE AUDIT LEG THIS REPLACES. Its spec — "bibliography with `\bibitem` count
        > 0 … alone catches D8 and D10" — would flag two bundles that are correct: both
        use `\bibliography{}` + a real `.bib`."""
        self._setup(tmp_path, monkeypatch, {"D8": (1,
            "\\begin{abstract}x\\end{abstract}\n\\section{Introduction}\n"
            "\\section{Conclusions}\n\\cite{a}\n\\bibliography{bibliography}\n")})
        assert bru.check_bundle_structural_coherence().passed

    def test_citing_with_NO_bibliography_at_all_fails(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": (1,
            "\\begin{abstract}x\\end{abstract}\n\\section{Introduction}\n"
            "\\section{Conclusions}\n\\cite{a}\n")})
        assert not bru.check_bundle_structural_coherence().passed

    def test_the_section_ceiling_fires(self, tmp_path, monkeypatch):
        """D3's live state: 31 top-level sections in a 30-50pp article."""
        body = ("\\begin{abstract}x\\end{abstract}\n"
                + "".join(f"\\section{{S{i}}}\n" for i in range(30))
                + "\\section{Conclusions}\n\\bibitem{a}x\n")
        self._setup(tmp_path, monkeypatch, {"D3": (1, body)})
        r = bru.check_bundle_structural_coherence()
        assert not r.passed and "table of contents" in r.details[1].message

    def test_a_review_article_is_EXEMPT_from_the_section_ceiling(
            self, tmp_path, monkeypatch):
        """Tier 0 is a review; a long section list is its correct shape."""
        body = ("\\begin{abstract}x\\end{abstract}\n"
                + "".join(f"\\section{{S{i}}}\n" for i in range(30))
                + "\\section{Conclusions}\n\\bibitem{a}x\n")
        self._setup(tmp_path, monkeypatch, {"F": (0, body)})
        assert bru.check_bundle_structural_coherence().passed

    def test_an_empty_population_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {})
        r = bru.check_bundle_structural_coherence()
        assert not r.passed and not r.measured


class TestBundleLeanModuleCoverage:
    """Declared substrate reaches the published claim (ADR-011 Phase 6, F-10)."""

    def _setup(self, tmp_path, monkeypatch, bundles):
        import bundle_registry as registry
        papers = tmp_path / "papers"
        for code, (mods, body) in bundles.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            (papers / code / "paper_draft.tex").write_text(body)
            (papers / code / "append_log.json").write_text(json.dumps(
                {"bundle_target": code,
                 "events": [{"lean_modules_referenced": mods}]}))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", tuple(bundles))

    def test_a_cited_module_is_not_absent(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": (["ADWMechanism"], "see ADWMechanism\n")})
        monkeypatch.setattr(bru, "LEAN_MODULE_ABSENT_CEILING", 0)
        assert bru.check_bundle_lean_module_coverage().passed

    def test_an_uncited_module_counts_against_the_ratchet(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, {"D1": (["ADWMechanism"], "no mention\n")})
        monkeypatch.setattr(bru, "LEAN_MODULE_ABSENT_CEILING", 0)
        r = bru.check_bundle_lean_module_coverage()
        assert not r.passed and "drifted further" in r.details[0].message.lower()

    def test_an_ESCAPED_underscore_still_matches(self, tmp_path, monkeypatch):
        r"""Drafts write `Foo\_Bar` inside `\thm{}`/`\texttt{}`. A bare substring test
        misses it and reports a cited module as absent — the trap the goal brief names.
        """
        self._setup(tmp_path, monkeypatch,
                    {"D1": (["Foo_Bar"], r"\texttt{Foo\_Bar} is used" + "\n")})
        monkeypatch.setattr(bru, "LEAN_MODULE_ABSENT_CEILING", 0)
        assert bru.check_bundle_lean_module_coverage().passed

    def test_a_DOTTED_module_may_be_cited_by_its_leaf(self, tmp_path, monkeypatch):
        """`APSEta.He3A` is normally written `He3A` in prose."""
        self._setup(tmp_path, monkeypatch,
                    {"D1": (["APSEta.He3A"], "the He3A construction\n")})
        monkeypatch.setattr(bru, "LEAN_MODULE_ABSENT_CEILING", 0)
        assert bru.check_bundle_lean_module_coverage().passed

    def test_an_ambiguous_basename_is_skipped(self, tmp_path, monkeypatch):
        """A substring hit on `Basic` proves nothing, so it is excluded rather than
        counted as satisfied — and excluded rather than counted as ABSENT."""
        self._setup(tmp_path, monkeypatch, {"D1": (["Foo.Basic"], "no mention\n")})
        monkeypatch.setattr(bru, "LEAN_MODULE_ABSENT_CEILING", 0)
        assert bru.check_bundle_lean_module_coverage().passed

    def test_the_ratchet_has_zero_headroom(self):
        """The live value IS the ceiling, so any regression fails immediately."""
        r = bru.check_bundle_lean_module_coverage()
        n = int(re.search(r"(\d+) registered-but-absent", r.details[0].message).group(1))
        assert n == bru.LEAN_MODULE_ABSENT_CEILING, (
            f"ceiling {bru.LEAN_MODULE_ABSENT_CEILING} but live count {n} — "
            f"a ratchet with headroom silently permits drift")

    def test_the_WRONG_field_name_reports_a_false_absence(self, tmp_path, monkeypatch):
        """PINS THE TRAP. The field is `lean_modules_referenced`; probing
        `lean_modules` reports 0 of 21 bundles declaring anything, which reads as
        'the data does not exist' and would retire this check as unbuildable."""
        papers = tmp_path / "papers"
        (papers / "D1").mkdir(parents=True)
        (papers / "D1" / "paper_draft.tex").write_text("no mention\n")
        (papers / "D1" / "append_log.json").write_text(json.dumps(
            {"events": [{"lean_modules": ["ADWMechanism"]}]}))   # wrong key
        import bundle_registry as registry
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D1",))
        r = bru.check_bundle_lean_module_coverage()
        assert not r.passed and not r.measured, "an empty population must be UNVERIFIED"


class TestBundleNativeDecideDebt:
    """`bundle_native_decide_debt` — the per-bundle ADR-002 ratchet (2026-08-08).

    Both directions: the debt cannot grow past its ceiling, an undisclosed use fails,
    and an unmeasurable substrate is UNVERIFIED rather than clean.
    """

    def test_live_state_passes(self):
        assert bru.check_bundle_native_decide_debt().passed

    def test_every_ceiling_has_zero_headroom(self):
        """A ratchet with slack permits silent drift. Each declared entry must equal
        the live measurement, so the next added use fails immediately."""
        from src.core.constants import NATIVE_DECIDE_BUNDLE_DEBT as DEBT
        hits, err = bru._bundle_native_decide_hits()
        assert not err, err
        for code, ceil in DEBT.items():
            assert len(hits.get(code, ())) == ceil, (
                f"{code}: ceiling {ceil} but live {len(hits.get(code, ()))} — "
                f"headroom in a ratchet is silent permission to regress")

    def test_a_bundle_absent_from_the_map_is_asserted_zero(self):
        """Absence must mean 'proven zero', not 'unchecked'."""
        from src.core.constants import NATIVE_DECIDE_BUNDLE_DEBT as DEBT
        hits, err = bru._bundle_native_decide_hits()
        assert not err, err
        for code, names in hits.items():
            if code not in DEBT:
                assert not names, f"{code} carries {len(names)} uses but declares no debt"

    def test_growth_past_the_ceiling_fails(self, monkeypatch):
        """MUTATION. Lowering D4's ceiling by one must fail — the live-tree proof
        that the ratchet leg is reachable."""
        import src.core.constants as C
        mutated = dict(C.NATIVE_DECIDE_BUNDLE_DEBT)
        mutated["D4"] = mutated["D4"] - 1
        monkeypatch.setattr(C, "NATIVE_DECIDE_BUNDLE_DEBT", mutated)
        r = bru.check_bundle_native_decide_debt()
        assert not r.passed
        assert any("ratchet:D4" in d.name for d in r.details)

    def test_an_undisclosed_use_fails(self, tmp_path, monkeypatch):
        """A bundle whose closure carries debt and whose draft never names the tactic."""
        papers = tmp_path / "papers"
        (papers / "D4").mkdir(parents=True)
        (papers / "D4" / "paper_draft.tex").write_text("Nothing about tactics here.\n")
        monkeypatch.setattr(_H, "PAPERS_DIR_ORIG", getattr(_H, "PAPERS_DIR", None), raising=False)
        real_papers = _H.PAPERS_DIR
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        # closures still derive from the REAL papers dir inside the helper, so point
        # only the draft read at the stub by restoring for the closure call.
        orig = bru._bundle_native_decide_hits
        monkeypatch.setattr(bru, "_bundle_native_decide_hits",
                            lambda: ({"D4": {"a", "b"}}, None))
        import src.core.constants as C
        monkeypatch.setattr(C, "NATIVE_DECIDE_BUNDLE_DEBT", {"D4": 2})
        import bundle_registry as registry
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D4",))
        r = bru.check_bundle_native_decide_debt()
        assert not r.passed
        assert any(d.name == "disclose:D4" for d in r.details)
        monkeypatch.setattr(bru, "_bundle_native_decide_hits", orig)
        monkeypatch.setattr(_H, "PAPERS_DIR", real_papers)

    def test_an_unmeasurable_substrate_is_UNVERIFIED_not_clean(self, monkeypatch):
        """The failure this suite exists to prevent: no measurement scoring green."""
        monkeypatch.setattr(bru, "_bundle_native_decide_hits", lambda: ({}, "no lean_deps"))
        r = bru.check_bundle_native_decide_debt()
        assert not r.passed and not r.measured


class TestBundleTodoFreeBeforeGreen:
    """`bundle_todo_free_before_green` — operator ruling 2026-08-08: drafts may carry
    TODOs, greens may not."""

    def _bundle(self, tmp_path, monkeypatch, body: str, status: str):
        papers = tmp_path / "papers"
        (papers / "D1").mkdir(parents=True)
        (papers / "D1" / "paper_draft.tex").write_text(body)
        (papers / "D1" / "bundle_metadata.json").write_text(
            json.dumps({"bundle": "D1", "stage13_status": status}))
        import bundle_registry as registry
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D1",))

    def test_live_state_passes(self):
        assert bru.check_bundle_todo_free_before_green().passed

    def test_a_todo_in_a_pending_draft_is_allowed(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch, "%% TODO: lift content\ntext\n", "pending")
        assert bru.check_bundle_todo_free_before_green().passed

    def test_a_todo_with_a_green_fails(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch, "%% TODO: lift content\ntext\n", "green")
        r = bru.check_bundle_todo_free_before_green()
        assert not r.passed
        assert any(d.name == "green_with_todo:D1" for d in r.details)

    def test_a_clean_green_passes(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch, "finished prose\n", "green")
        assert bru.check_bundle_todo_free_before_green().passed

    def test_the_word_placeholder_in_PROSE_is_not_a_marker(self, tmp_path, monkeypatch):
        """PINS THE FALSE POSITIVE that a first, broader predicate produced. A
        `True := trivial` Lean stub is a DISCLOSED concept here and drafts are required
        to name it; gating on the word would penalize the mandated honesty."""
        self._bundle(tmp_path, monkeypatch,
                     "The theorem ships as a placeholder pending Mathlib.\n", "green")
        assert bru.check_bundle_todo_free_before_green().passed

    def test_a_TODO_described_in_PROSE_is_not_a_marker(self, tmp_path, monkeypatch):
        """D11 §1 factually describes an in-source TODO in *Mathlib*. That is a
        statement about a dependency, not unfinished work of its own."""
        self._bundle(tmp_path, monkeypatch,
                     "Mathlib carries the manifold version as an explicit in-source TODO.\n",
                     "green")
        assert bru.check_bundle_todo_free_before_green().passed

    def test_an_escaped_percent_is_not_a_comment(self, tmp_path, monkeypatch):
        r"""`\%` prints a percent sign; only a real `%` opens a LaTeX comment."""
        self._bundle(tmp_path, monkeypatch,
                     "A 40\\% TODO-free reduction was measured.\n", "green")
        assert bru.check_bundle_todo_free_before_green().passed


class TestNativeDecideSeamGuard:
    """Authoring-guide §2.5 on `bundle_native_decide_debt`: an empty population must be
    UNVERIFIED, because "no bundle carries debt" and "I measured nothing" print the same."""

    def test_an_empty_native_decide_set_is_UNVERIFIED_not_clean(self, monkeypatch):
        import update_counts
        monkeypatch.setattr(update_counts, "native_decide_decls", lambda _raw: [])
        hits, err = bru._bundle_native_decide_hits()
        assert hits == {} and err and "EMPTY" in err
        monkeypatch.setattr(bru, "_bundle_native_decide_hits", lambda: ({}, err))
        r = bru.check_bundle_native_decide_debt()
        assert not r.passed and not r.measured

    def test_no_measurable_closure_is_UNVERIFIED_not_clean(self, monkeypatch):
        import bundle_closure as bc
        monkeypatch.setattr(bc, "build_closures", lambda *a, **k: {})
        hits, err = bru._bundle_native_decide_hits()
        assert hits == {} and err and "measurable apex closure" in err

    def test_the_live_population_is_plausible(self):
        """The guard is only meaningful if the real set is non-trivial."""
        hits, err = bru._bundle_native_decide_hits()
        assert not err, err
        assert len(hits) >= 20, "every declared bundle should appear"
        assert sum(len(v) for v in hits.values()) > 0, "the corpus does carry debt"


# ── TODO-D5: UNMEASURED is not YELLOW ─────────────────────────────────────

class TestUnmeasuredIsDistinctFromYellow:
    """The bundle layer had no equivalent of `CheckResult.measured`. A bundle whose
    Stage-10 artifact does not exist, or whose Stage-13 evidence is of the wrong
    kind, was rendered YELLOW — "measured, has issues" — when the truth is "the
    evidence to judge does not exist". D9 reached the portfolio's only GREEN that
    way, with its Stage 10 never run.

    ⚠️ Five of D5's six sub-claims were already closed by ADR-011 Phase 2 and were
    re-measured before any code changed: record_review.py IS the stage-status
    writer, bundle_reviewer_stage_ordering IS the ordering gate,
    _KINDS_SUFFICIENT_FOR_GREEN DOES discriminate review kind, _blocked_p1_gates
    returns None rather than {} on failure, and the missing-claims_review case was
    already handled. What remained was the STATE, and the unguarded stage9/10 enum."""

    def test_unmeasured_is_a_state_the_module_can_return(self):
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        import bundle_readiness as br
        src = pathlib.Path(br.__file__).read_text()
        assert '"UNMEASURED"' in src
        # and it must be reachable from BOTH withholding paths
        assert src.count('readiness = "UNMEASURED"') >= 2

    def test_icon_map_covers_unmeasured(self):
        """A consumer that KeyErrors on the new state would push it back to '?'."""
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from datastar_bundles import _VERDICT_ICON
        assert "UNMEASURED" in _VERDICT_ICON
        assert _VERDICT_ICON["UNMEASURED"] != _VERDICT_ICON["YELLOW"]

    def test_stage_status_enum_covers_the_live_vocabulary(self):
        """Measured live: not_started, skeleton and pending-redo were all in the
        corpus and all undeclared, on stages that had no enum guard at all."""
        import sys, pathlib, json
        root = pathlib.Path(__file__).resolve().parents[1]
        sys.path.insert(0, str(root / "scripts"))
        from bundle_readiness import _STAGE_STATUS_ENUM, _GUARDED_STAGE_FIELDS
        for f in ("not_started", "skeleton", "pending-redo"):
            assert f in _STAGE_STATUS_ENUM, f
        assert set(_GUARDED_STAGE_FIELDS) == {
            "stage9_status", "stage10_status", "stage13_status"}
        undeclared = []
        for md in sorted(root.glob("papers/*/bundle_metadata.json")):
            m = json.loads(md.read_text(encoding="utf-8"))
            for fld in _GUARDED_STAGE_FIELDS:
                if str(m.get(fld) or "") not in _STAGE_STATUS_ENUM:
                    undeclared.append(f"{md.parent.name}.{fld}={m.get(fld)!r}")
        assert undeclared == [], undeclared


# ── TODO-D7 readability half: the sentence-length ratchet ─────────────────

class TestSentenceLengthRatchet:
    """TODO-D7 measured "171 sentences over 60 words … 7 bundles contain a
    sentence over 100 words (max 179)" and nothing gated it. Re-measured
    2026-08-09: 199 over 60, and 22 over 100 across 14 bundles, max 235. The
    problem had GROWN, partly from this branch's own additions.

    ⚠️ The prose was deliberately not rewritten to lower the number in the change
    that introduced the check. TODO-D7's own constraint is that "the decider must
    not be the generator"; a metric shipped together with the edits that satisfy
    it has measured nothing."""

    def _run(self):
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from validation.checks.bundles_readiness import check_bundle_sentence_length
        return check_bundle_sentence_length()

    def test_gate_is_green_at_the_frozen_ratchet(self):
        res = self._run()
        assert res.passed, [d.message for d in res.details]

    def test_over_100_is_gated_and_over_60_is_not(self):
        """Both thresholds are reported; only the indefensible one gates.
        Gating >60 would fire on correct methods prose (GATE_TOPOLOGY §3)."""
        res = self._run()
        by = {d.name: d for d in res.details}
        assert "over_100_words" in by and "over_60_words" in by
        # ⚠️ The advisory leg's `passed` is a LITERAL `True` in the check body, so
        # asserting it is vacuous — it cannot fail, and the assertion that used to
        # live here reported coverage it did not have. The leg's real signal is its
        # WARNING flag; that is what the two tests below pin, in both directions.
        assert by["over_60_words"].passed, "the advisory leg must never fail the check"

    def test_the_advisory_WARNS_when_the_baseline_is_exceeded(self, monkeypatch):
        """The direction that carries the signal. Drop the baseline below the live
        count and the warning must appear."""
        from validation.checks import bundles_readiness as br
        import src.core.constants as C
        monkeypatch.setattr(C, "SENTENCE_OVER_60_ADVISORY", 0)
        by = {d.name: d for d in br.check_bundle_sentence_length().details}
        assert by["over_60_words"].warning is True
        assert by["over_60_words"].passed is True, "advisory must still never gate"

    def test_the_advisory_is_SILENT_under_the_baseline(self, monkeypatch):
        """The silent direction — otherwise a leg that always warns would pass the
        test above while carrying no information."""
        from validation.checks import bundles_readiness as br
        import src.core.constants as C
        monkeypatch.setattr(C, "SENTENCE_OVER_60_ADVISORY", 10_000)
        by = {d.name: d for d in br.check_bundle_sentence_length().details}
        assert by["over_60_words"].warning is False

    def test_ratchet_is_sensitive_to_a_seeded_regression(self, monkeypatch):
        """Lower the population by raising nothing: drop the ceiling below the
        live count and the gate must fail. Proves it is not vacuous."""
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from src.core import constants
        monkeypatch.setattr(constants, "SENTENCE_OVER_100_CEILING", 0)
        res = self._run()
        assert not res.passed, "ceiling 0 must fail — the gate would otherwise be inert"

    def test_ceiling_matches_the_live_measurement(self):
        """A ratchet frozen above the live value is slack that hides a
        regression; frozen below it is a permanently red gate."""
        from src.core.constants import SENTENCE_OVER_100_CEILING
        res = self._run()
        msg = next(d.message for d in res.details if d.name == "over_100_words")
        live = int(msg.split()[0])
        assert live == SENTENCE_OVER_100_CEILING, (live, SENTENCE_OVER_100_CEILING)
