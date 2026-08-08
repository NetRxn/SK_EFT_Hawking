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
