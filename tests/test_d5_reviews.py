"""D5 both-directions tests for `validation/checks/reviews.py` — audit QI-27.

Four checks, none of which had a test that could fail on a seeded defect:
`recurrence_reopens_closures`, `review_severity_declared`, `review_docs_mint_findings`,
`accepted_findings_carry_rationale`.

WHY SYNTHETIC INPUTS AND NOT THE LIVE CORPUS
--------------------------------------------
Every one of these reads a **self-remediating corpus** — review documents and a ledger
that the project actively repairs. `reviews.py`'s own comments record the cost of
forgetting that: `recurrence_reopens_closures` had its threshold calibrated three times
against the live sweep, and each time *"a constant was set just under the live corpus
maximum by the same commit that repaired the pair producing that maximum, so it was
unreachable on arrival."*

A test asserting `check_x().passed is True` on the live tree inherits that defect exactly
— it passes whether the check works or not, and it breaks when the corpus is legitimately
remediated. So every test here drives the REAL check function over a synthetic corpus
built in `tmp_path`, with the path anchor monkeypatched by attribute (ADR-009 H1/H5).

MUTATION-VERIFIED 2026-08-04 — 8 mutations, all CAUGHT, clean negative control.
Each was scoped to the target function's AST span and restored by writing back the saved
bytes (ADR-009 §Deferred item 2's harness rule, plus the audit §4b rule that a mutation
is NEVER undone with `git checkout <file>`):

  | mutation                                                    | caught by |
  |---|---|
  | `recurrence`: `hits += 1` -> `hits += 0`                     | the whole class |
  | `recurrence`: drop the `odate <= cdate` guard                | `…earlier_open_finding…` |
  | `recurrence`: drop the same-bundle guard                     | `…different_bundle…` |
  | `recurrence`: drop the section-number tie-breaker            | `…marginal_score…` |
  | `review_severity_declared`: `n_sev < n_head` -> `n_sev < 0`  | `…missing_severity…` |
  | `review_docs_mint_findings`: `n == 0` -> `n < 0`             | `…mints_nothing…` |
  | `review_docs_mint_findings`: `_carries_findings` -> `True`   | `…resolved_note…` |
  | `accepted_findings…`: `len(why) < MIN_CHARS` -> `False`      | `…bare_acceptance…` |

The last four rows are the point: three of them mutate a FILTER rather than the verdict,
and a suite that only asserted `passed is False` on one dirty fixture would miss all
three. A guard is load-bearing in both directions or it is decoration.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import build_graph  # noqa: E402
import validate_helpers as _H  # noqa: E402
from validation.checks import reviews as rv  # noqa: E402


def _reviews_tree(tmp_path: Path, docs: dict[str, str]) -> Path:
    """Build `papers/AutomatedReviews/<dated-dir>/<file>.md` under a fake PROJECT_ROOT.

    Keys are `"<dated-dir>/<file>.md"`; the check derives the document's date from the
    PARENT directory name (`md.parent.name[:10]`), which is why the date lives there and
    not in the filename.
    """
    root = tmp_path / "root"
    for rel, body in docs.items():
        p = root / "papers" / "AutomatedReviews" / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body, encoding="utf-8")
    return root


def _patch_roots(monkeypatch, root):
    """Both anchors. `reviews_dir` derives from `_H.PAPERS_DIR` (one owner, QI-11) while
    the reported paths are relative to `_H.PROJECT_ROOT`, so a test patching only one
    reads the REAL corpus through the other — the by-value hazard, one level out."""
    monkeypatch.setattr(_H, "PROJECT_ROOT", root)
    monkeypatch.setattr(_H, "PAPERS_DIR", root / "papers")
    return root


def _finding(fid: str, label: str, *, date: str, status: str, severity: str = "critical",
             bundle: str | None = "D11", review_file: str | None = None,
             name: str | None = None) -> dict:
    """A ReviewFinding node in the shape `build_graph` actually emits.

    ⚠️ `name` was absent here until 2026-08-05 (audit QI-34). Production nodes carry
    BOTH `label` (`f'{section} {heading[:50]}'`) and `name` (`heading[:200]`), and the
    check matched on the truncated one — a defect this fixture could not have shown,
    because it modelled a node that has only one of the two. `name` defaults to
    `label` so the existing cases are unchanged; the cases that turn on the
    distinction pass it explicitly.
    """
    return {
        "id": fid,
        "label": label,
        "name": label if name is None else name,
        "meta": {
            "review_date": date,
            "status": status,
            "severity": severity,
            "inferred_bundle": bundle,
            "review_file": review_file,
        },
    }


class TestRecurrenceReopensClosures:
    """A finding closed in the ledger must not recur in a LATER review of the SAME bundle.

    The hit is reported against the CLOSURE, not the new finding — the new finding is
    correct and it is the closure that is now false. These tests assert that direction
    too, because reporting the wrong side would still produce `passed is False`.
    """

    #: Identical text on both sides scores Jaccard 1.0, clearing `_MIN_OVERLAP` (0.40)
    #: AND the `+0.10` marginal band, so the section-number tie-breaker never engages.
    #: Deliberate: this class tests the recurrence rule, and a separate test below
    #: covers the tie-breaker.
    LABEL = "PAPER_DRAFT_MAPPING row is stale for this bundle and misstates the lift"
    OTHER = "healing length constant disagrees with the transonic background module"

    def _run(self, monkeypatch, findings):
        monkeypatch.setattr(build_graph, "extract_review_finding_nodes", lambda: findings)
        return rv.check_recurrence_reopens_closures()

    def test_a_later_open_finding_contradicts_the_closure(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the whole point of the check."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed"),
            _finding("rev:D11:4.1", self.LABEL, date="2026-07-15", status="open"),
        ])
        assert r.passed is False, (
            "a closure contradicted by a later same-bundle finding reported PASS — "
            "the recurrence guard is inert again (it has been three times before)")
        assert any(d.name == "led:D11:4.1" and not d.passed for d in r.details), (
            "the hit must be reported against the CLOSURE, not the open finding: the "
            "later review is the evidence and the closure is what is now false")

    def test_no_recurrence_is_silent(self, monkeypatch):
        """SILENT ON CORRECT DATA — two unrelated findings in the same bundle."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed"),
            _finding("rev:D11:9.9", self.OTHER, date="2026-07-15", status="open"),
        ])
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_earlier_open_finding_is_not_a_recurrence(self, monkeypatch):
        """The date rule. An open finding PREDATING the closure is what the closure
        closed — counting it would make every correct closure a violation."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-15", status="fixed"),
            _finding("rev:D11:4.1", self.LABEL, date="2026-07-01", status="open"),
        ])
        assert r.passed is True

    def test_a_different_bundle_is_a_template_collision_not_a_recurrence(self, monkeypatch):
        """Reviews share heading boilerplate across bundles. The check's own comment
        records that the two hits before this constraint were exactly that."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed"),
            _finding("rev:I2:4.1", self.LABEL, date="2026-07-15", status="open",
                     bundle="I2"),
        ])
        assert r.passed is True

    def test_a_non_blocking_closure_is_out_of_scope(self, monkeypatch):
        """Only `critical`/`major` closures are compared — and the summary must SAY so
        rather than counting them as covered."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed",
                     severity="minor"),
            _finding("rev:D11:4.1", self.LABEL, date="2026-07-15", status="open"),
        ])
        assert r.passed is True
        summary = next(d for d in r.details if d.name == "summary")
        assert "1 non-blocking closure(s)" in summary.message, (
            "the summary must report what was NOT compared; overstating coverage is the "
            "defect this check's own history records nine times")

    def test_a_marginal_score_needs_the_section_number_to_agree(self, monkeypatch):
        """The tie-breaker (round-14 finding 14.4). Its first live effect was a FALSE
        positive: two different guards that both 'failed open', matched at exactly 0.400
        on that shared phrase. A marginal score under a different section number is not
        a recurrence."""
        # MEASURED, not chosen: Jaccard 0.5000, inside the marginal band
        # [_MIN_OVERLAP, _MIN_OVERLAP + 0.10) where the tie-breaker engages. Picking
        # these by eye is how this check's threshold was mis-set three times.
        # (Re-measured 2026-08-05 for the 0.40 -> 0.45 move under QI-34: the previous
        # pair scored 0.4444, which the new threshold excludes outright, so BOTH legs
        # passed and the tie-breaker was no longer exercised at all. A band-anchored
        # fixture must move when the band moves — this one silently went vacuous.)
        a = "readiness gate reports green stale roster"
        b = "readiness gate reports green stale blocked bundle metadata drift"
        marginal = [
            _finding("led:D11:8.2", a, date="2026-07-01", status="fixed"),
            _finding("rev:D11:8.4", b, date="2026-07-15", status="open"),
        ]
        assert self._run(monkeypatch, marginal).passed is True

        # ...and the SAME pair under the same section number is held. This leg is what
        # stops the test above being satisfied by a tie-breaker that rejects everything.
        same_number = [
            _finding("led:D11:8.2", a, date="2026-07-01", status="fixed"),
            _finding("rev:D11:8.2", b, date="2026-07-15", status="open"),
        ]
        assert self._run(monkeypatch, same_number).passed is False

    def test_the_matcher_reads_name_NOT_the_truncated_label(self, monkeypatch):
        """QI-34's substrate fix, pinned. `label` is `heading[:50]`, and 50 characters
        cut mid-word: `falsifier` becomes `falsifie`, `the` becomes `t`, and those
        fragments count as tokens. Two headings differing in ONE word therefore scored
        0.500 on `label` against 0.900 on `name` — and `name` was on the node all along.

        The two sides here are IDENTICAL for the first 50 characters and diverge after,
        so a matcher still reading `label` sees 1.0 and fires. Reading `name`, they are
        different findings and it must stay silent."""
        head = "the readiness gate reports a bundle green while its "
        assert len(head) >= 50
        a = head + "roster is stale and its blockers are open"
        b = head + "companion notebook stores outputs from before the fix"
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", a[:50], date="2026-07-01", status="fixed", name=a),
            _finding("rev:D11:4.2", b[:50], date="2026-07-15", status="open", name=b),
        ])
        assert r.passed is True, (
            "two findings sharing only a 50-character opening were reported as a "
            "recurrence — the matcher is reading the truncated `label` again (QI-34)")

    def test_a_later_RESOLUTION_NOTICE_does_not_contradict_the_closure(self, monkeypatch):
        """The false-positive class QI-34 removed, and it was the corpus's LOUDEST
        signal: every finding is born `open`, including the "✅ FIXED — <restated
        finding>" entries a later round writes to record a remediation. Those are
        near-verbatim by construction, so on the live corpus the top three scores
        (0.643 / 0.500 / 0.438) were all a closure matched against its own resolution
        notice. Firing there would have made the guard's first three hits all wrong."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed"),
            _finding("rev:D11:4.1", self.LABEL, date="2026-07-15", status="open",
                     name="✅ FIXED — " + self.LABEL),
        ])
        assert r.passed is True, (
            "a later review CONFIRMING the fix was counted as contradicting it")
        assert "resolution notice" in \
            next(d for d in r.details if d.name == "summary").message

    def test_the_resolution_exemption_does_not_swallow_a_real_recurrence(self, monkeypatch):
        """The other direction, and the reason the exemption is scoped to the heading:
        a later finding that restates the defect WITHOUT announcing a fix must still
        fire. Otherwise the exemption is a blanket amnesty rather than a semantic one."""
        r = self._run(monkeypatch, [
            _finding("led:D11:4.1", self.LABEL, date="2026-07-01", status="fixed"),
            _finding("rev:D11:4.1", self.LABEL, date="2026-07-15", status="open",
                     name="🔴 BLOCKER — still open: " + self.LABEL),
        ])
        assert r.passed is False, (
            "a genuine restatement was excused by the resolution-notice exemption")

    def test_a_short_title_is_reported_as_a_coverage_limit(self, monkeypatch):
        """Labels are truncated to `heading[:50]` upstream, so titles under
        `_MIN_TITLE` chars are a real coverage hole. The check must count them out
        loud rather than let them vanish into a clean verdict."""
        r = self._run(monkeypatch, [
            _finding("led:D11:1.1", "typo", date="2026-07-01", status="fixed"),
        ])
        assert r.passed is True
        assert "1 finding(s) whose normalised title is under" in \
            next(d for d in r.details if d.name == "summary").message

    def test_an_unavailable_extractor_fails_rather_than_passes(self, monkeypatch):
        """Cannot-measure is not success — the systemic finding this whole audit exists
        for. `reviews.py` already gets this right; the test pins it."""
        monkeypatch.delattr(build_graph, "extract_review_finding_nodes")
        r = rv.check_recurrence_reopens_closures()
        assert r.passed is False


class TestReviewSeverityDeclared:
    """From the cutoff forward, severity must be a declared field rather than a glyph
    inferred from a heading — glyphs are editable without leaving a trace."""

    CUTOFF_DIR = "2026-08-15-stage13"     # on/after the 2026-08-01 cutoff
    LEGACY_DIR = "2026-07-01-stage13"     # before it; glyph inference still allowed

    DECLARED = ("### 1.1 — the mapping row is stale\n"
                "- **Severity:** critical\n\nbody\n")
    UNDECLARED = "### 1.1 — 🔴 the mapping row is stale\n\nbody\n"

    def test_a_missing_severity_line_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/D11.md": self.UNDECLARED}))
        r = rv.check_review_severity_declared()
        assert r.passed is False, (
            "a post-cutoff review whose finding declares no severity reported PASS — "
            "severity drives the blocking-closure bar and this is the guard on it")

    def test_a_declared_severity_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/D11.md": self.DECLARED}))
        r = rv.check_review_severity_declared()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_documents_before_the_cutoff_keep_glyph_inference(self, tmp_path, monkeypatch):
        """~1400 findings predate the convention. The cutoff is the honest boundary;
        a blanket rule would be churn with no provenance value."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.LEGACY_DIR}/D11.md": self.UNDECLARED}))
        assert rv.check_review_severity_declared().passed is True

    def test_a_document_with_no_findings_is_not_penalised(self, tmp_path, monkeypatch):
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/notes.md": "# Notes\n\nprose only\n"}))
        r = rv.check_review_severity_declared()
        assert r.passed is True
        assert "0 review document(s)" in \
            next(d for d in r.details if d.name == "summary").message

    #: A well-formed LINE carrying a token `build_graph` cannot map. Satisfies the
    #: line-count leg completely.
    MISTYPED = ("### 1.1 — the mapping row is stale\n"
                "- **Severity:** blockr\n\nbody\n")

    def test_a_MISTYPED_severity_value_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — added 2026-08-05 (PR-review reviewer 6).

        This check counted `**Severity:**` LINES and never read what they said, so
        `blockr` satisfied it fully — while `build_graph._SEVERITY_DECL_MAP.get()`
        returned `None`, the finding fell back to `advisory`, the paper read YELLOW and
        `readiness_submission_gate` passed. The line count is the weaker half of the
        obligation; the vocabulary is the other half and this check owns both."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/D11.md": self.MISTYPED}))
        r = rv.check_review_severity_declared()
        assert r.passed is False, (
            "a severity token `build_graph` cannot map passed the declaration check — "
            "a mistyped BLOCKER lands advisory and nothing says so")
        assert any("vocabulary" in d.name for d in r.details)

    def test_the_accepted_vocabulary_is_DERIVED_from_build_graph(self, tmp_path,
                                                                 monkeypatch):
        """The vocabulary must come from the mapping that consumes it, not a copy.
        Every token `build_graph` maps must pass here — otherwise this check and the
        extractor disagree about what a valid declaration is, which is how the
        hand-listed severity set in `test_build_graph.py` sat RED for weeks."""
        from build_graph import _SEVERITY_DECL_MAP
        doc = "".join(
            f"### {i}.1 — finding\n- **Severity:** {tok}\n\nbody\n\n"
            for i, tok in enumerate(sorted(_SEVERITY_DECL_MAP), start=1))
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/D11.md": doc}))
        r = rv.check_review_severity_declared()
        assert r.passed is True, (
            "a token build_graph maps was rejected here: "
            f"{[(d.name, d.message) for d in r.details if not d.passed]}")


class TestReviewDocsMintFindings:
    """A review producing zero graph nodes is a parser failure — never evidence of a
    clean review. This is the fail-open path that survived every previous repair."""

    WITH_FINDING = "### 1.1 — BLOCKER — the mapping row is stale\n\nbody\n"
    #: A severity WORD inside a resolution note is not a severity LABEL. A clean figure
    #: review reads "`fig5.png` (P2) — **PASS** (round-2 BLOCKER resolved)" and correctly
    #: mints nothing.
    RESOLVED_NOTE = "### `fig5.png` (P2) — **PASS** (round-2 BLOCKER resolved)\n\nbody\n"

    REL = "papers/AutomatedReviews/2026-08-15-stage13/D11.md"

    def _run(self, tmp_path, monkeypatch, docs, findings):
        _patch_roots(monkeypatch, _reviews_tree(tmp_path, docs))
        monkeypatch.setattr(build_graph, "extract_review_finding_nodes", lambda: findings)
        return rv.check_review_docs_mint_findings()

    def test_a_findings_document_that_mints_nothing_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the round-9 case verbatim: a review declaring
        BLOCKERs whose headings drifted, minting zero nodes and reading as a clean round."""
        r = self._run(tmp_path, monkeypatch,
                      {"2026-08-15-stage13/D11.md": self.WITH_FINDING}, [])
        assert r.passed is False, (
            "a review carrying an unresolved BLOCKER heading minted zero nodes and the "
            "check passed — this is the fail-open path, reopened")

    def test_a_findings_document_that_mints_is_silent(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      {"2026-08-15-stage13/D11.md": self.WITH_FINDING},
                      [_finding("rev:D11:1.1", "the mapping row is stale",
                                date="2026-08-15", status="open", review_file=self.REL)])
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_resolved_note_is_not_a_finding(self, tmp_path, monkeypatch):
        """Scope is by CONTENT, not filename. A generated aggregation mints zero BY
        DESIGN and must be skipped — but because it never claimed to carry findings,
        not because of where it lives. Two earlier scopings were wrong in opposite
        directions; this leg pins the discriminator."""
        r = self._run(tmp_path, monkeypatch,
                      {"2026-08-15-stage13/figures.md": self.RESOLVED_NOTE}, [])
        assert r.passed is True
        assert "0 document(s) carrying" in \
            next(d for d in r.details if d.name == "summary").message

    def test_a_failing_extractor_fails_rather_than_passes(self, tmp_path, monkeypatch):
        def _boom():
            raise RuntimeError("graph build failed")
        _patch_roots(monkeypatch, _reviews_tree(tmp_path, {}))
        monkeypatch.setattr(build_graph, "extract_review_finding_nodes", _boom)
        r = rv.check_review_docs_mint_findings()
        assert r.passed is False
        assert any("unverified" in (d.message or "") for d in r.details)


class TestAcceptedFindingsCarryRationale:
    """`accepted` removes a finding from Gate 11's blocking set, so it must record a
    DECISION — why acceptance rather than a fix — not merely assert one."""

    SUBSTANTIVE = ("Accepted because the cited bound is a projection, not a measurement, "
                   "and the paper says so in the caption.")

    def _ledger(self, tmp_path, monkeypatch, entries):
        docs = tmp_path / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "review_finding_supersessions.json").write_text(
            json.dumps({"supersessions": entries}), encoding="utf-8")
        monkeypatch.setattr(_H, "DOCS_DIR", docs)
        return rv.check_accepted_findings_carry_rationale()

    def test_a_bare_acceptance_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        r = self._ledger(tmp_path, monkeypatch, [
            {"finding_id": "D11:4.1", "status": "accepted", "evidence": "accepted"}])
        assert r.passed is False, (
            "an `accepted` record with a one-word rationale passed — `accepted` is the "
            "cheapest way to make a blocking finding disappear from Gate 11")
        assert any(d.name == "D11:4.1" and not d.passed for d in r.details)

    def test_a_substantive_rationale_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. The round-8 reviewer measured 138 of 140 accepted
        records already carrying substantive rationale — this check pins the practice,
        it does not fix a live defect."""
        r = self._ledger(tmp_path, monkeypatch, [
            {"finding_id": "D11:4.1", "status": "accepted", "evidence": self.SUBSTANTIVE}])
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_all_three_historical_field_names_are_read(self, tmp_path, monkeypatch):
        """The ledger spells this field three ways across its history — `evidence`
        (recent), `rationale`, and `note` (the 2026-05 records). Reading only the first
        two produced two false positives on well-justified records."""
        for field in ("evidence", "rationale", "note"):
            r = self._ledger(tmp_path, monkeypatch, [
                {"finding_id": f"D11:{field}", "status": "accepted",
                 field: self.SUBSTANTIVE}])
            assert r.passed is True, f"a rationale spelled `{field}` was not read"

    def test_non_accepted_records_are_out_of_scope(self, tmp_path, monkeypatch):
        r = self._ledger(tmp_path, monkeypatch, [
            {"finding_id": "D11:4.1", "status": "fixed", "evidence": "x"}])
        assert r.passed is True
        assert "0 accepted record(s)" in \
            next(d for d in r.details if d.name == "summary").message

    def test_an_unreadable_ledger_fails_rather_than_passes(self, tmp_path, monkeypatch):
        docs = tmp_path / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "review_finding_supersessions.json").write_text("{not json", encoding="utf-8")
        monkeypatch.setattr(_H, "DOCS_DIR", docs)
        assert rv.check_accepted_findings_carry_rationale().passed is False

    def test_a_missing_ledger_is_the_annotated_h1_silent_site(self, tmp_path, monkeypatch):
        """⚠️ This asserts a KNOWN WEAKNESS, not a desired property. A missing ledger
        returns PASS, so a retargeted `_H.DOCS_DIR` makes this check report success
        having examined nothing — one of the two sites ADR-009 H1 annotates as SILENT,
        and one of the 22 pairs frozen in `test_cannot_measure_baseline.py`.

        Pinned here so that converting it to FAIL is a deliberate act that updates this
        test and the baseline together, rather than a drive-by change.
        """
        monkeypatch.setattr(_H, "DOCS_DIR", tmp_path / "nonexistent")
        r = rv.check_accepted_findings_carry_rationale()
        assert r.passed is True
        assert any(d.warning for d in r.details), (
            "if this site stops passing on a missing ledger, that is an improvement — "
            "update this test and tests/test_cannot_measure_baseline.py together")


class TestChainBackingTargetsResolve:
    """`chain_backing_targets_resolve` — the audit trail must point at Lean names that exist.

    ⚠️ **This class deliberately departs from this module's synthetic-input policy above,
    and the reason is specific.** That policy exists because the other four checks read a
    self-remediating corpus, where `assert check().passed is True` passes whether the check
    works or not. This check is a RATCHET, so the live corpus is not incidental to it — the
    measured population IS the subject. A synthetic corpus would prove the resolver parses
    JSON and nothing about whether 156 is the true figure or whether the ceiling can fire.

    So: the mutation is seeded into the REAL `papers/D3/claims_review.json` and written back
    from saved bytes (never `git checkout`), and the ceiling is asserted against the LIVE
    measured value rather than its own definition. When the backlog is legitimately
    remediated this class fails — that is the ratchet working, and the fix is to lower
    `UNRESOLVED_CHAIN_LINK_CEILING` in the same commit that does the remediation.
    """

    def test_a_dangling_link_seeded_into_the_real_corpus_fails(self):
        target = _H.PAPERS_DIR / "D3" / "claims_review.json"
        original = target.read_text(encoding="utf-8")
        assert rv.check_chain_backing_targets_resolve().passed is True, (
            "baseline must be green, or this mutation proves nothing")
        try:
            doc = json.loads(original)
            doc["sentences"][0].setdefault("chain_proposed", {}).setdefault("links", []).append(
                {"kind": "theorem",
                 "target": "SKEFTHawking.ThisDeclarationDoesNotExist.seeded_defect"})
            target.write_text(json.dumps(doc, indent=2), encoding="utf-8")
            r = rv.check_chain_backing_targets_resolve()
            assert r.passed is False, "one dangling link past the ceiling must fail the check"
            assert any("seeded_defect" not in d.message for d in r.details)
        finally:
            target.write_text(original, encoding="utf-8")
        assert rv.check_chain_backing_targets_resolve().passed is True, "restore failed"

    def test_the_ceiling_carries_no_headroom(self):
        """A ratchet above the population cannot fire. Assert against the LIVE measured
        value, never against the constant's own definition (guide §2.3)."""
        r = rv.check_chain_backing_targets_resolve()
        detail = next(d for d in r.details if d.name == "unresolvable")
        live = int(detail.message.split()[0])
        assert live == rv.UNRESOLVED_CHAIN_LINK_CEILING, (
            f"live unresolved count {live} != ceiling {rv.UNRESOLVED_CHAIN_LINK_CEILING}; "
            f"if the backlog shrank, LOWER the ceiling — headroom makes it unfireable")

    def test_an_unbuildable_graph_is_unverified_not_passing(self, monkeypatch):
        """The check's only heavy dependency is chain_canonicalize's GraphIndex. If it cannot
        be built, the verdict is UNVERIFIED — never a pass."""
        import chain_canonicalize as _cc

        def _boom():
            raise RuntimeError("seeded: graph unavailable")

        monkeypatch.setattr(_cc, "GraphIndex", _boom)
        r = rv.check_chain_backing_targets_resolve()
        assert r.passed is False and r.measured is False

    def test_an_empty_corpus_fails_rather_than_passing_vacuously(self, monkeypatch):
        """The seam guard (§2.5): a scan that matches nothing must not report health.

        Seeded at `_iter_links`, which is the check's population source now that resolution
        is delegated — patching a path anchor would no longer reach it."""
        import chain_canonicalize as _cc

        monkeypatch.setattr(_cc, "_iter_links", lambda: iter(()))
        r = rv.check_chain_backing_targets_resolve()
        assert r.passed is False, "zero links reached is a resolver/path defect, not a clean corpus"

    def test_this_check_owns_no_resolver(self):
        """The reconciliation guard. An earlier draft carried its own normalizer and membership
        test beside `chain_canonicalize`'s — a second resolver for one population, disagreeing
        with the real one (156 vs 121). Assert the duplication cannot return."""
        import ast
        src = (SK_ROOT / "scripts" / "validation" / "checks" / "reviews.py").read_text()
        tree = ast.parse(src)
        local = [n.name for n in ast.walk(tree)
                 if isinstance(n, ast.FunctionDef)
                 and ("resolve" in n.name or "normalize" in n.name)
                 and n.name != "check_chain_backing_targets_resolve"]
        assert local == [], (
            f"reviews.py defines its own resolution helpers {local} — resolution belongs to "
            f"chain_canonicalize.canonicalize_link, and a second resolver will disagree with it")
        assert "canonicalize_link" in src, "the check must call the shared resolver"
