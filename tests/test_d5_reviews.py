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
import re
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

    #: Two findings; the FIRST carries two `- **Severity:**` lines and the SECOND carries
    #: none. Totals reach parity (2 headings, 2 severity lines), so the old `n_sev <
    #: n_head` predicate passed this document completely — one finding paid for its
    #: neighbour and 1.2's severity silently fell back to glyph inference.
    PADDED = ("### 1.1 — the mapping row is stale\n"
              "- **Severity:** critical\n"
              "- **Severity:** critical\n\nbody\n"
              "### 1.2 — 🔴 the second row is stale too\n\nbody\n")

    def test_padding_cannot_pay_for_a_missing_declaration(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — D12 round-11 8.4.

        ⚠️ This is the mutation the old predicate could not catch, and it needed no
        adversary: comparing `len(severity lines)` to `len(headings)` asks whether the
        document has ENOUGH declarations, not whether each finding HAS one. Totals are not
        an association. Severity drives the blocking-closure bar, so the finding whose
        declaration went missing is exactly the one that must not be inferable.
        """
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {f"{self.CUTOFF_DIR}/D11.md": self.PADDED}))
        r = rv.check_review_severity_declared()
        assert r.passed is False, (
            "two headings and two severity lines reported PASS while finding 1.2 declares "
            "none — the count reached parity and the association did not")
        assert any("1.2" in (d.message or "") for d in r.details if not d.passed), \
            "the failure must NAME the finding that is missing its declaration"

    def test_a_non_iso_directory_name_fails_rather_than_skipping(
            self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the cutoff used to be OPT-OUT.

        Scope was decided by `parent.name[:10] < "2026-08-01"`, a string compare against a
        directory name. A review filed in a folder not named for a date was skipped in
        silence, so a reviewer chose whether to be checked by choosing a folder name.
        Undecidable scope is a failure: the check cannot know whether the document is in
        scope, and a check that cannot know must not answer "fine".
        """
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {"stage13-latest/D11.md": self.UNDECLARED}))
        r = rv.check_review_severity_declared()
        assert r.passed is False, (
            "a review in a non-date directory reported PASS — that is the cutoff working "
            "as an opt-out rather than as a boundary")
        assert any("scope" in d.name for d in r.details if not d.passed)

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


class TestReviewVerifyIsOneCommand:
    """Rule 4 of the review-document marker contract, stated in two docstrings and
    enforced nowhere until 2026-08-15.

    `close_finding.py` reads the `Verify:` line, takes it as ONE command and runs it under
    a shell — so trailing prose is argv, not commentary. A finding whose Verify line
    cannot run can be neither verified nor closed, because `close_finding` refuses a
    `--verify` that differs from the declared command.
    """

    GOOD = ("### 1.1 — the row is stale\n"
            "- **Severity:** major\n"
            "- **Verify:** `uv run python scripts/validate.py --check tables_fresh`\n"
            "  *What it asserts:* that the shipped scalars match a fresh render.\n")
    TRAILING_PROSE = ("### 1.1 — the row is stale\n"
                      "- **Severity:** major\n"
                      "- **Verify:** `uv run python -c \"pass\"` — exits 1 at HEAD\n")
    TWO_COMMANDS = ("### 1.1 — the row is stale\n"
                    "- **Severity:** major\n"
                    "- **Verify:** `first --thing` and then `second --thing`\n")

    def test_trailing_prose_after_the_command_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. This is the exact shape that strands a finding:
        `— exits 1 at HEAD` reads as commentary and runs as arguments."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {"2026-08-15-stage13/D11.md": self.TRAILING_PROSE}))
        r = rv.check_review_verify_is_one_command()
        assert r.passed is False
        assert any("not a single command" in (d.message or "")
                   for d in r.details if not d.passed)

    def test_two_commands_on_one_line_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a distinct shape from trailing prose."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {"2026-08-15-stage13/D11.md": self.TWO_COMMANDS}))
        assert rv.check_review_verify_is_one_command().passed is False

    def test_a_single_command_with_a_following_gloss_line_passes(
            self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. The explanation belongs on the NEXT line, and the
        contract's own house style puts it there — the check must not punish that."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {"2026-08-15-stage13/D11.md": self.GOOD}))
        r = rv.check_review_verify_is_one_command()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_EMPTY_WALK_fails_rather_than_passing_vacuously(
            self, tmp_path, monkeypatch):
        """⚠️ THE MUTATION THAT MATTERS. Every other leg is a zero-violation assertion,
        which a corpus containing no `Verify:` lines at all satisfies perfectly — so a
        broken walk or a drifted pattern would read exactly like a clean corpus. `checked
        > 0` is part of the verdict."""
        _patch_roots(monkeypatch, _reviews_tree(
            tmp_path, {"2026-08-15-stage13/D11.md": "### 1.1 — no verify here\n"}))
        r = rv.check_review_verify_is_one_command()
        assert r.passed is False
        assert "asserted nothing this run" in \
            next(d for d in r.details if d.name == "summary").message

    def test_the_live_corpus_is_clean(self):
        """PRODUCTION. Measured 2026-08-15: 129 Verify lines, 0 violating — which is why
        the bar is a hard zero. If this fails, a new document broke rule 4; fix the
        document, never the bar."""
        r = rv.check_review_verify_is_one_command()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    #: A review document this test OWNS. Chosen deliberately: seeding a document another
    #: worker may be editing risks a lost restore, and the whole point of restoring from
    #: saved bytes is that the corpus comes back byte-identical.
    _SEED_TARGET = ("papers/AutomatedReviews/"
                    "2026-08-15-closure-write-lost-under-concurrency/infra.md")

    def test_PRODUCTION_SEEDED_a_broken_verify_line_turns_it_red(self):
        """⚠️ PRODUCTION-SEEDED, per CHECK_AUTHORING_GUIDE §2.4. The fixture mutations
        above prove the TEST works; only this proves the CHECK can fire against the real
        corpus — the walk, the glob and the pattern all exercised end to end.

        The defect is written into a real review document and restored from saved bytes,
        never with `git checkout` (ADR-009 §Deferred item 2).
        """
        target = SK_ROOT / self._SEED_TARGET
        original = target.read_bytes()
        try:
            text = original.decode("utf-8")
            seeded = text.replace(
                "- **Verify:** `cd \"$REPO\" && uv run python -m pytest "
                "tests/test_close_finding.py -q -k \"readback or concurren\"`",
                "- **Verify:** `cd \"$REPO\" && uv run python -m pytest "
                "tests/test_close_finding.py -q -k \"readback or concurren\"` "
                "— exits 1 at HEAD", 1)
            assert seeded != text, (
                f"the seed did not apply to {self._SEED_TARGET}; its Verify line changed, "
                f"so this test is no longer seeding anything")
            target.write_bytes(seeded.encode("utf-8"))
            r = rv.check_review_verify_is_one_command()
            assert r.passed is False, (
                "a real review document carrying trailing prose on its Verify line "
                "reported PASS — the check cannot fire in production")
            assert any(self._SEED_TARGET in d.name for d in r.details if not d.passed)
        finally:
            target.write_bytes(original)
        assert target.read_bytes() == original, "the corpus was not restored byte-identically"


class TestAcceptedByRatchet:
    """D12 rounds 8/9/10 finding 8.5, second half. The rationale floor enforces that a
    decision was WRITTEN; this enforces that it is ATTRIBUTED. For a critical or major a
    bundle will ship carrying, an unattributed decision is one nobody can be asked about.
    """

    def test_the_blocking_set_matches_the_gate_evaluator(self):
        """SEAM GUARD. Two modules must not disagree about what 'blocking' means — the
        ratchet would then count a different population from the gate it exists to
        supplement, and both would look right."""
        from readiness_gates import BLOCKING_SEVERITIES
        assert rv._BLOCKING_SEVERITIES == BLOCKING_SEVERITIES

    def test_the_ceiling_carries_no_headroom(self):
        """PRODUCTION-SEEDED, and the reason this lives here rather than in the check:
        every fixture in `TestAcceptedFindingsCarryRationale` builds a synthetic ledger
        whose ids resolve to no severity, so a below-ceiling leg inside the check would
        fire on all of them and the ratchet would be measuring the fixtures.

        A ceiling left standing above an improved corpus stops ratcheting silently.
        """
        r = rv.check_accepted_findings_carry_rationale()
        d = next(x for x in r.details if x.name == "accepted_by")
        n = int(re.match(r"(\d+) blocking-severity", d.message).group(1))
        assert n == rv.ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING, (
            f"{n} unattributed blocking acceptances against a ceiling of "
            f"{rv.ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING}. Lower "
            f"ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING to {n} in the same commit. "
            f"⚠️ If it rose, do NOT raise the ceiling — the new acceptance owes an "
            f"`accepted_by`.")

    def test_an_unattributed_acceptance_past_the_ceiling_FAILS(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the ceiling dropped by one, so the live corpus is
        one over. Seeds the CEILING rather than the ledger, which leaves the 645 KB
        production file untouched while still exercising it as the input."""
        monkeypatch.setattr(
            rv, "ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING",
            rv.ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING - 1)
        r = rv.check_accepted_findings_carry_rationale()
        assert r.passed is False
        d = next(x for x in r.details if x.name == "accepted_by")
        assert "ABOVE the ceiling" in d.message and "review:" in d.message, (
            "the failure must NAME the records that owe an accepted_by")

    def test_an_unavailable_extractor_is_UNMEASURED_not_passing(self, monkeypatch):
        """Cannot-measure is not success. Without severities the leg cannot tell a
        blocking acceptance from an advisory one, so its silence is not evidence."""
        monkeypatch.delattr(build_graph, "extract_review_finding_nodes")
        r = rv.check_accepted_findings_carry_rationale()
        assert r.measured is False
        assert any(d.name == "accepted_by" and not d.passed for d in r.details)


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

    def test_a_dangling_link_seeded_past_the_ceiling_fails(
            self, monkeypatch, chain_backing_result):
        """⚠️ Seeded at the SEAM, not into the tracked corpus.

        This test used to append a dangling link to the real
        `papers/D3/claims_review.json` and restore it in a `finally`. Inside that
        window every concurrent reader — `validate.py`, the dashboard, a parallel
        pytest worker, even this class's own sibling `test_the_ceiling_carries_no_
        headroom` — measured one more unresolved link than the commit contains,
        and a kill or timeout mid-window left the corpus permanently +1. Against a
        ZERO-HEADROOM ratchet that makes the suite's colour depend on timing.

        The class docstring's argument that the *ceiling* must be measured live
        does not extend to the *seeding* test: this one only has to prove the
        ceiling can fire, which the seam shows without touching a tracked file."""
        import chain_canonicalize as _cc

        assert chain_backing_result.passed is True, (
            "baseline must be green, or this mutation proves nothing")

        real = list(_cc._iter_links())
        seeded = real + [("D3", "seeded-sentence", "theorem",
                          "SKEFTHawking.ThisDeclarationDoesNotExist.seeded_defect")]
        monkeypatch.setattr(_cc, "_iter_links", lambda: iter(seeded))

        r = rv.check_chain_backing_targets_resolve()
        assert r.passed is False, "one dangling link past the ceiling must fail the check"
        detail = next(d for d in r.details if d.name == "unresolvable")
        assert int(detail.message.split()[0]) == rv.UNRESOLVED_CHAIN_LINK_CEILING + 1

    def test_the_seeding_test_leaves_the_corpus_byte_identical(self):
        """The reason the rewrite above exists. Reading the tracked file after the
        seam-seeded run must show no trace of the mutation."""
        target = _H.PAPERS_DIR / "D3" / "claims_review.json"
        assert "seeded_defect" not in target.read_text(encoding="utf-8")

    def test_the_ceiling_carries_no_headroom(self, chain_backing_result):
        """A ratchet above the population cannot fire. Assert against the LIVE measured
        value, never against the constant's own definition (guide §2.3).

        Session-shared: this call is unpatched, so it is the same result the seeded
        test takes its baseline from."""
        r = chain_backing_result
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
        # ⚠️ Exempt REGISTERED CHECKS structurally, not by a hand-list that grows every
        # time a check's NAME happens to contain "resolve". The guard's subject is a
        # resolution HELPER living beside the shared resolver; a `check_*` entry point is
        # not one. `check_ledger_ids_resolve` (promoted here 2026-08-12) tripped the
        # name heuristic while resolving nothing — it tests ledger-id membership.
        local = [n.name for n in ast.walk(tree)
                 if isinstance(n, ast.FunctionDef)
                 and ("resolve" in n.name or "normalize" in n.name)
                 and not n.name.startswith("check_")]
        assert local == [], (
            f"reviews.py defines its own resolution helpers {local} — resolution belongs to "
            f"chain_canonicalize.canonicalize_link, and a second resolver will disagree with it")
        assert "canonicalize_link" in src, "the check must call the shared resolver"


class TestLaneEnforcementExtendsSeverityDeclared:
    """ADR-012 D1/D2 — the lane leg rides the SAME document walk as the severity leg.

    ⚠️ This file's discipline (see its header): drive the REAL check over a synthetic
    corpus in `tmp_path` with the anchors monkeypatched. A `check_x().passed is True`
    assertion against the live tree passes whether the check works or not.
    """

    def test_a_mappable_lane_passes(self, tmp_path, monkeypatch):
        root = _reviews_tree(tmp_path, {"2026-08-12-x/A.md":
            "### 1.1 — 🔴 CRITICAL — x\n\n"
            "- **Severity:** critical\n- **Lane:** substrate\n"})
        _patch_roots(monkeypatch, root)
        assert rv.check_review_severity_declared().passed is True

    def test_an_omitted_lane_is_NOT_a_failure(self, tmp_path, monkeypatch):
        """`lane` is forward-only. Absent reads `unclassified`; the historical corpus of
        1,596 findings must not go red on arrival."""
        root = _reviews_tree(tmp_path, {"2026-08-12-x/A.md":
            "### 1.1 — 🔴 CRITICAL — x\n\n- **Severity:** critical\n"})
        _patch_roots(monkeypatch, root)
        assert rv.check_review_severity_declared().passed is True

    def test_an_unmappable_lane_turns_the_check_red(self, tmp_path, monkeypatch):
        """Non-vacuity (ADR-012 D8): seed the defect, observe red. A lane build_graph
        cannot map routes the finding NOWHERE — no worker, no gate set, no fan-out key."""
        root = _reviews_tree(tmp_path, {"2026-08-12-x/A.md":
            "### 1.1 — 🔴 CRITICAL — x\n\n"
            "- **Severity:** critical\n- **Lane:** wizardry\n"})
        _patch_roots(monkeypatch, root)
        res = rv.check_review_severity_declared()
        assert res.passed is False
        assert any('wizardry' in d.message for d in res.details)


class TestBlockedByResolvesLeg:
    """ADR-012 D10. ⚠️ This leg REPLACES a raise in `_blocked_by_edges`, which propagated
    out of `build_graph_json()` — one hand-typed id in reviewer markdown would have taken
    down the graph, the atlas, `graph_integrity`, gate extraction and the dashboard at once,
    including the checks that would diagnose it. Detection had to survive the move, so this
    seeds the defect in a REAL review document and observes red end-to-end."""

    #: A live review document inside the check's date window that mints findings.
    DOC = ("papers/AutomatedReviews/2026-08-12-0200-citation-integrity/D10.md")

    def test_a_dangling_blocked_by_in_a_REAL_document_turns_the_check_red(self):
        """PRODUCTION-SEEDED (guide §2.4): the line goes into the tracked corpus and the
        real extractor parses it. A fixture tree cannot reach this leg — it reads
        `extract_review_finding_nodes()`, not the walked document text."""
        import validate_helpers as _H
        doc = _H.PROJECT_ROOT / self.DOC
        assert doc.is_file(), f"{self.DOC} moved — re-point this mutation, do not delete it"
        original = doc.read_text(encoding="utf-8")
        try:
            doc.write_text(
                original + "\n- **Blocked-by:** review:no-such-date:NOPE:9.9\n",
                encoding="utf-8")
            res = rv.check_review_severity_declared()
            assert res.passed is False, "a dangling Blocked-by did not turn the check red"
            assert any("review:no-such-date:NOPE:9.9" in (d.message or "")
                       for d in res.details)
        finally:
            doc.write_text(original, encoding="utf-8")
        # and the corpus is clean again, byte for byte
        assert doc.read_text(encoding="utf-8") == original
        assert rv.check_review_severity_declared().passed is True

    def test_the_live_corpus_carries_no_unresolvable_blocker(self):
        """Zero, not a ratcheted baseline: unlike the ledger's historical debt this
        population starts empty, so every entry in it is new."""
        import sys
        sys.path.insert(0, 'scripts')
        from build_graph import blocked_by_unresolved, extract_review_finding_nodes
        assert blocked_by_unresolved(extract_review_finding_nodes()) == {}


def _live_dangling_baseline() -> int:
    """The production `LEDGER_DANGLING_BASELINE`, imported — it is module scope now."""
    from validation.checks.reviews import LEDGER_DANGLING_BASELINE
    return LEDGER_DANGLING_BASELINE


class TestLedgerIdsResolveIsOneCheckNotTwo:
    """ADR-012 D13. ⚠️ This check was PROMOTED out of `check_graph_integrity`, not built.
    An earlier draft proposed building it at a ceiling of 247 — the aggregate over three id
    schemes — which would have been a second mechanism beside a working one AND weaker:
    one ratchet over 190 permanently-inert legacy records plus the live ones lets deleting a
    legacy record silently buy headroom for a real dangler."""

    def _ledger(self, tmp_path, monkeypatch, records):
        root = tmp_path / "root"
        (root / "docs").mkdir(parents=True, exist_ok=True)
        (root / "docs" / "review_finding_supersessions.json").write_text(
            json.dumps({"supersessions": records}, indent=2))
        monkeypatch.setattr(_H, "PROJECT_ROOT", root)
        monkeypatch.setattr(_H, "DOCS_DIR", root / "docs")
        return root

    def test_the_leg_is_gone_from_graph_integrity(self):
        """One mechanism, not two (CLAUDE.md rule 1). ⚠️ Asserts on the Detail
        CONSTRUCTION, not a bare substring: a pointer comment naming the destination is
        deliberately left behind."""
        import inspect
        from validation.checks import graph_atlas
        src = inspect.getsource(graph_atlas)
        assert 'Detail(\n            "ledger_ids_resolve"' not in src
        assert 'Detail("ledger_ids_resolve"' not in src

    def test_the_live_baseline_has_zero_headroom(self):
        import sys
        sys.path.insert(0, 'scripts')
        from build_graph import extract_review_finding_nodes
        known = {n["id"] for n in extract_review_finding_nodes()}
        led = json.loads(
            (_H.DOCS_DIR / "review_finding_supersessions.json").read_text())["supersessions"]
        live = len({e["finding_id"] for e in led
                    if e["finding_id"].startswith("review:") and e["finding_id"] not in known})
        assert live == _live_dangling_baseline(), (
            f"live {live} != baseline {_live_dangling_baseline()}; if the backlog shrank, "
            "LOWER the baseline in the commit that shrank it — headroom makes it unfireable")

    def test_a_dangling_closure_above_the_baseline_fails(self, tmp_path, monkeypatch):
        base = _live_dangling_baseline()
        self._ledger(tmp_path, monkeypatch,
                     [{"finding_id": f"review:r:ghost:{i}"} for i in range(base + 1)])
        assert rv.check_ledger_ids_resolve().passed is False

    def test_at_the_baseline_it_passes_with_a_warning(self, tmp_path, monkeypatch):
        base = _live_dangling_baseline()
        self._ledger(tmp_path, monkeypatch,
                     [{"finding_id": f"review:r:ghost:{i}"} for i in range(base)])
        res = rv.check_ledger_ids_resolve()
        assert res.passed is True
        assert any(d.warning for d in res.details)

    def test_legacy_scheme_ids_are_out_of_scope(self, tmp_path, monkeypatch):
        """Only `review:`-scheme ids ever minted nodes. Flagging the 190 legacy
        `bundle-stage10:` records would be noise, not signal — and folding them into one
        ratchet is what made the proposed replacement weaker."""
        self._ledger(tmp_path, monkeypatch,
                     [{"finding_id": f"bundle-stage10:x:{i}"} for i in range(300)])
        assert rv.check_ledger_ids_resolve().passed is True

    def test_an_unreadable_ledger_fails_rather_than_passes(self, tmp_path, monkeypatch):
        root = tmp_path / "root"
        (root / "docs").mkdir(parents=True, exist_ok=True)
        (root / "docs" / "review_finding_supersessions.json").write_text("{not json")
        monkeypatch.setattr(_H, "PROJECT_ROOT", root)
        monkeypatch.setattr(_H, "DOCS_DIR", root / "docs")
        res = rv.check_ledger_ids_resolve()
        assert res.passed is False and res.measured is False
