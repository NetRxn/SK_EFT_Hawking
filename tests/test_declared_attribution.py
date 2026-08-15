"""A review document's DECLARED target is what attributes its findings.

⚠️ **The defect these tests pin is a FALSE GREEN, not a miscount.** Until 2026-08-15 the
per-bundle aggregation resolved a finding's bundle from two regexes over text — a literal
`paper<digit>` somewhere in the heading/body/filename, and the filename stem matched
against the bundle roster — and opened the review document's frontmatter for nothing. A
document stating `paper: note_rt_ch_bounds`, `paper: paper17_dark_sector` or
`bundle_target: D11` was parsed by neither channel, so the convention every recent review
writes had no reader anywhere in `scripts/`. Eleven open blocking findings whose own
documents name a target that resolves through `PAPER_DRAFT_MAPPING` reached no bundle, and
nine bundles rendered YELLOW while carrying open blockers.

The tests below bind the mechanism in **both** directions, plus the seam between them:

* a finding that DECLARES a target reaches that bundle;
* a finding that declares NOTHING still lands in the unattributed leg, which is what
  bounds it;
* a finding whose declared target does NOT resolve is **reported as unresolved**, never
  silently merged into the undeclared population — losing that distinction is exactly how
  a convention rots while still reading as attribution to every human who opens the file.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))


@pytest.fixture(scope="module")
def mapping_keys():
    from bundle_readiness import _mapping_keys
    keys = _mapping_keys()
    assert keys, "PAPER_DRAFT_MAPPING parsed to nothing — every assertion below would be vacuous"
    return keys


def _meta(**kw):
    """A ReviewFinding meta with only the attribution-relevant fields set."""
    base = {"declared_paper": None, "declared_bundle": None,
            "inferred_paper": None, "inferred_bundle": None, "review_file": ""}
    base.update(kw)
    return base


class TestFrontmatterIsReadFromTheFrontmatter:
    """The declaration is a fenced block at the top of the file, or it is absent."""

    def test_a_leading_block_is_read(self):
        from build_graph import _parse_frontmatter
        fm = _parse_frontmatter(
            "---\npaper: note_rt_ch_bounds\nbundle_target: D4\nkind: targeted\n---\n\n# Title\n")
        assert fm["paper"] == "note_rt_ch_bounds"
        assert fm["bundle_target"] == "D4"

    def test_a_BODY_line_that_looks_like_a_declaration_is_NOT_read(self):
        """⚠️ SEEDED FROM THE LIVE CORPUS. A finding's prose contains the line
        ``paper: `AdmissibleBandFrame.overlap_ne` at `:164-169`, with the …`` — a sentence
        that happens to start with the word. A `MULTILINE` search would read that as an
        attribution and hand a bundle to whatever the sentence began with, which is the
        same infer-don't-read failure this whole fix removes, pointed the other way.
        """
        from build_graph import _parse_frontmatter
        body = ("# A review with no frontmatter\n\n"
                "paper: `AdmissibleBandFrame.overlap_ne` at `:164-169`\n"
                "bundle_target: D12\n")
        assert _parse_frontmatter(body) == {}

    def test_a_list_value_is_not_mistaken_for_a_scalar_declaration(self):
        from build_graph import _parse_frontmatter
        fm = _parse_frontmatter(
            "---\npaper: infra\nsources_of_truth:\n  - papers/D1/paper_draft.tex\n---\n")
        assert fm["paper"] == "infra"
        assert fm.get("sources_of_truth") == ""


class TestADeclarationReachesItsBundle:
    """Direction 1: a document that states its target attributes by that statement."""

    def test_a_declared_mapping_key_partitions_on_that_key(self, mapping_keys):
        from bundle_readiness import resolve_attribution
        key, channel = resolve_attribution(
            _meta(declared_paper="note_rt_ch_bounds"), mapping_keys)
        assert (key, channel) == ("note_rt_ch_bounds", "declared-paper-key")

    def test_a_declared_key_OUTRANKS_the_filename_and_the_text_inference(self, mapping_keys):
        """`paper20_scalar_rung_REINVOCATION.md` declares `paper: paper20_scalar_rung`.
        The filename stem is not a mapping key and the text inference yields the
        unmappable `paper20_scalar_rung_reinvocation`, so precedence is the whole
        mechanism here — the same precedence the extractor already applies to severity,
        where a declared `- **Severity:**` line beats glyph inference.
        """
        from bundle_readiness import resolve_attribution
        key, channel = resolve_attribution(
            _meta(declared_paper="paper20_scalar_rung",
                  inferred_paper="paper20_scalar_rung_reinvocation",
                  review_file="papers/AutomatedReviews/x/paper20_scalar_rung_REINVOCATION.md"),
            mapping_keys)
        assert (key, channel) == ("paper20_scalar_rung", "declared-paper-key")

    def test_a_declared_bundle_code_resolves_to_that_bundle(self, mapping_keys):
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(_meta(declared_bundle="D11"), mapping_keys) == (
            "D11", "declared-bundle-code")

    def test_a_declared_paper_that_IS_a_bundle_code_resolves(self, mapping_keys):
        """The corpus writes both `paper: D12` and `paper: D4_topological_qc_foundations`;
        both are the bundle, spelled through the same roster-validated token reader the
        filename stem goes through."""
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(_meta(declared_paper="D12"), mapping_keys)[0] == "D12"
        assert resolve_attribution(
            _meta(declared_paper="D4_topological_qc_foundations"), mapping_keys)[0] == "D4"

    def test_a_declared_finding_REACHES_its_bundles_in_the_live_aggregation(self):
        """⚠️ THE DECIDER, NOT A PROXY. Asserted against `aggregate_by_bundle`'s
        `open_finding_ids` — the field the ratchet's coverage complement is computed from
        — not against `meta`. `note_rt_ch_bounds` maps to D4 and F; before this fix its
        findings appeared in neither.
        """
        from bundle_readiness import (MAPPING_DOC, parse_mapping,
                                      load_findings_by_paper,
                                      resolve_stage13_reviews, aggregate_by_bundle)
        by_bundle = aggregate_by_bundle(parse_mapping(MAPPING_DOC.read_text()),
                                        load_findings_by_paper(),
                                        resolve_stage13_reviews(backfill=False))
        from build_graph import extract_review_finding_nodes
        declared = {n["id"] for n in extract_review_finding_nodes()
                    if (n["meta"].get("declared_paper") == "note_rt_ch_bounds"
                        and n["meta"].get("status") == "open")}
        assert declared, ("no open finding declares `paper: note_rt_ch_bounds` — the "
                          "corpus changed and this test is measuring nothing")
        for bundle in ("D4", "F"):
            reached = set(by_bundle[bundle]["open_finding_ids"])
            assert declared <= reached, (
                f"{bundle} does not carry {sorted(declared - reached)} — the declaration "
                f"is inert again, which is the defect this test exists for")


class TestNoDeclarationStillLandsInTheUnattributedLeg:
    """Direction 2: honouring declarations must not let anything escape the ratchet."""

    def test_a_finding_that_declares_nothing_reports_undeclared(self, mapping_keys):
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(_meta(), mapping_keys) == (None, "undeclared")

    def test_the_legacy_inference_still_runs_when_nothing_is_declared(self, mapping_keys):
        """The bundle-era fallback (`inferred_bundle`, D11 round-5 BLOCKER 4.1) is the
        last step, not a deleted one."""
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(_meta(inferred_bundle="D11"), mapping_keys) == (
            "D11", "inferred")

    def test_the_two_ratchet_legs_still_partition_the_open_blocking_population(self):
        """Coverage is true by construction: leg 1 counts the ids the aggregation named,
        leg 2 counts every open blocking finding whose id is not among them. A resolver
        that attributed a finding twice, or lost one, would break the partition here."""
        from build_graph import extract_review_finding_nodes
        from readiness_gates import BLOCKING_SEVERITIES
        from validation.checks.bundles_readiness import _readiness_aggregate
        by_bundle, _, failure = _readiness_aggregate()
        assert failure is None, f"aggregation failed: {failure}"
        covered = {i for d in by_bundle.values()
                   for i in (d.get("open_finding_ids") or ())}
        open_blocking = [n for n in extract_review_finding_nodes()
                         if n["meta"].get("status") == "open"
                         and n["meta"].get("severity") in BLOCKING_SEVERITIES]
        in_leg1 = {n["id"] for n in open_blocking if n["id"] in covered}
        in_leg2 = {n["id"] for n in open_blocking if n["id"] not in covered}
        assert len(in_leg1) + len(in_leg2) == len(open_blocking)
        assert not (in_leg1 & in_leg2)


class TestAnUnresolvableDeclarationIsReportedNotDropped:
    """⚠️ THE SEAM. `declared a target that does not resolve` and `declared nothing` are
    different facts about a document. Rendering them identically is how the original
    defect stayed invisible: the frontmatter kept reading as attribution to every human
    who opened the file while no consumer could act on it.
    """

    def test_a_declaration_outside_the_mapping_reports_declared_unresolved(self, mapping_keys):
        """`phase6EE_control` is neither a `PAPER_DRAFT_MAPPING` key nor a bundle code."""
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(
            _meta(declared_paper="phase6EE_control"), mapping_keys) == (
                None, "declared-unresolved")

    def test_a_TYPO_cannot_invent_a_bundle(self, mapping_keys):
        """Exactly-one match or nothing. `D99` is outside the roster and
        `note_rt_ch_boundz` is outside the mapping; both must resolve to nothing rather
        than to whatever is nearest."""
        from bundle_readiness import resolve_attribution
        assert resolve_attribution(_meta(declared_bundle="D99"), mapping_keys)[0] is None
        assert resolve_attribution(
            _meta(declared_paper="note_rt_ch_boundz"), mapping_keys)[0] is None

    def test_an_infra_declaration_attributes_to_no_bundle_and_stays_ratcheted(self, mapping_keys):
        """⚠️ NOT A GAP TO CLOSE. A defect in `formulas.py` or `update_counts.py` belongs
        to no publication bundle. It resolves to nothing BY CONSTRUCTION and the
        unattributed leg is what bounds it; narrowing that leg to exclude infra findings
        would be reclassification standing in for remediation."""
        from bundle_readiness import resolve_attribution
        for value in ("infra", "process"):
            assert resolve_attribution(_meta(declared_paper=value), mapping_keys) == (
                None, "declared-unresolved")

    def test_the_check_REPORTS_the_unresolved_count(self):
        """The distinction has to reach the surface, or it is not a distinction."""
        from validation.checks.bundles_readiness import (
            check_bundle_stage13_claim_consistent)
        res = check_bundle_stage13_claim_consistent()
        leg2 = [d for d in res.details if d.name == "unattributed_population"]
        assert len(leg2) == 1
        assert "DECLARE a target that resolves to no bundle" in leg2[0].message


class TestOneUniquePrefixResolver:
    """The two layers used to disagree about the same finding: `extract_flags_edges`
    normalised `paper10` -> `paper10_modular_generation` against Paper NODE IDs, and
    `load_findings_by_paper` partitioned on the raw `paper10`, which is not a mapping
    key. Same finding, correct FLAGS edge, no bundle. There is now ONE resolver,
    parameterised by the universe — the only thing that legitimately differs.
    """

    def test_a_short_key_normalises_against_the_mapping(self, mapping_keys):
        from build_graph import resolve_unique_prefix
        assert resolve_unique_prefix("paper10", mapping_keys) == "paper10_modular_generation"

    def test_an_ambiguous_short_key_resolves_to_NOTHING(self):
        from build_graph import resolve_unique_prefix
        assert resolve_unique_prefix(
            "paper16", {"paper16_graphene_sk_eft", "paper16_wrt_tqft"}) is None

    def test_an_exact_key_is_returned_unchanged(self):
        from build_graph import resolve_unique_prefix
        assert resolve_unique_prefix("paper1_first_order",
                                     {"paper1_first_order", "paper1_x"}) == "paper1_first_order"

    def test_the_flags_layer_and_the_aggregation_layer_call_the_SAME_resolver(self):
        """Pinned by identity, not by behaviour: two implementations that agree today can
        drift apart tomorrow, which is precisely what happened."""
        import inspect
        import build_graph
        import bundle_readiness
        src = inspect.getsource(build_graph.extract_flags_edges)
        assert "resolve_unique_prefix(" in src, (
            "extract_flags_edges no longer calls the shared resolver — the second "
            "implementation is back")
        assert "resolve_unique_prefix" in inspect.getsource(
            bundle_readiness.resolve_attribution)

    def test_the_short_key_reaches_a_bundle_in_the_live_aggregation(self):
        """`CitationReview-01` §9 infers `paper10`, which maps through
        `paper10_modular_generation` to L2/D2/F. Before the reconciliation it reached
        none of them."""
        from bundle_readiness import (MAPPING_DOC, parse_mapping,
                                      load_findings_by_paper,
                                      resolve_stage13_reviews, aggregate_by_bundle)
        by_paper = load_findings_by_paper()
        assert "paper10" not in by_paper, (
            "the aggregation is partitioning on the raw short key again")
        by_bundle = aggregate_by_bundle(parse_mapping(MAPPING_DOC.read_text()), by_paper,
                                        resolve_stage13_reviews(backfill=False))
        ids = {f["id"] for f in by_paper.get("paper10_modular_generation", [])
               if f["status"] == "open"}
        assert ids, "no open finding normalises onto paper10_modular_generation"
        for bundle in ("L2", "D2", "F"):
            assert ids <= set(by_bundle[bundle]["open_finding_ids"])
