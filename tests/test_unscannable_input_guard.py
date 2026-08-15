"""An `\\input` that resolves to nothing must FAIL all three reader-visible checks.

⚠️ **This file exists because two commit messages said "(seeded, proven)" and
nothing in the repo pinned it.** The behaviour was real — it was verified
interactively — but a verification that lives in a transcript is not a guard, and
the closure reviewer was right to refuse the claim. `git grep unscannable -- tests/`
returned nothing.

The property: `draft_input_closure` deliberately keeps an unresolvable `\\input`
target ("an unresolvable reference is still recorded as a path"), and the
`.is_file()` filter that builds the scan population drops exactly those. Silently.
A draft with `\\input{tables/gone}` scanned clean and reported "0 em-dashes" over a
file it never opened.

`bundle_sentence_length` is the one that bites hardest: it is a DOWN-ONLY RATCHET
(`SENTENCE_OVER_100_CEILING`, lowered 22 → 20 in this same branch), so a renamed
`\\input` silently shrinks the population the floor is frozen against, and the
ratchet then locks in a floor derived from prose it never read.
"""
from __future__ import annotations

import pathlib
import sys

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO))

from validation.checks import bundles_readiness as br  # noqa: E402

#: All three checks that consume `_reader_visible_sources`. A new consumer that
#: takes the population without the gaps should be added here and will fail.
GAP_SENSITIVE_CHECKS = [
    "check_bundle_prose_em_dash_free",
    "check_bundle_sentence_length",
    "check_bundle_reader_facing_voice",
]

SEED_HOST = "D1"          # any real bundle draft; D1 is the largest
SEED = "\\input{tables/__unscannable_regression_probe}\n"


@pytest.fixture
def seeded_unresolvable_input():
    """Put an unresolvable `\\input` into a real draft, then restore it exactly.

    Restores from SAVED BYTES, never `git checkout` — a checkout would also discard
    concurrent edits, which is how a sibling test lost work.

    ⚠️ SINCE 2026-08-15 THE SAVED BYTES ARE DURABLE. `seeded_mutation` writes them, and
    the draft's mtime, to `.seed-journal/` before the draft is touched, so a run killed
    mid-test leaves a repairable record rather than an unresolvable `\\input` in a
    tracked bundle draft. The restore below is unchanged in what it does; it has simply
    stopped being the only copy of the information needed to do it.
    """
    import validate_helpers as _H
    from seed_journal import seeded_mutation
    draft = _H.PAPERS_DIR / SEED_HOST / "paper_draft.tex"
    original = draft.read_text(encoding="utf-8")
    original_stat = draft.stat()
    assert "\\begin{document}" in original, "fixture host lost its document body"
    # ⚠️ `preserve_mtime=True` (the default) IS LOAD-BEARING, not tidiness. This fixture
    # edits a TRACKED draft, and `bundle_manuscript_length` refuses to size a PDF older
    # than its draft's `\input` closure — so a byte-perfect restore with a fresh mtime
    # silently took D1 UNMEASURED and the length gate went from reporting 11 gaps to 10,
    # while still passing. Measured: the "0 UNMEASURED" state was invalidated by THIS
    # FIXTURE eight minutes before the commit claiming it was written. A test must not
    # change what a production check measures.
    with seeded_mutation(
            draft,
            original.replace("\\begin{document}", SEED + "\\begin{document}", 1),
            reason="an unresolvable \\input in a real draft must FAIL every "
                   "gap-sensitive check rather than be silently skipped"):
        yield

    # ⚠️ THE FIXTURE ASSERTS ITS OWN CONTRACT, HERE, IN TEARDOWN.
    # A separate test asserting this cannot work: an earlier version inlined the
    # write/restore cycle and asserted on its own two preceding lines, so deleting
    # the mtime restore left it GREEN — mutation-proven by a reviewer. Teardown
    # is the only place the real fixture's restoration can be observed, and every
    # test that uses the fixture now inherits the guard for free. It is kept even
    # though `seeded_mutation` makes the same assertion internally: this one holds
    # the MECHANISM to the contract, and a guard that trusts the thing it guards is
    # the proxy failure CHECK_AUTHORING_GUIDE §4.5 names.
    after = draft.stat()
    assert draft.read_text(encoding="utf-8") == original, (
        "the fixture did not restore the draft's BYTES")
    assert after.st_mtime_ns == original_stat.st_mtime_ns, (
        "the fixture restored bytes but MOVED THE MTIME. "
        "`bundle_manuscript_length` refuses to size a PDF older than its draft's "
        "`\\input` closure, so this silently takes the bundle UNMEASURED and "
        "shrinks that gate's reported population while it keeps passing.")


class TestAnUnreadFileIsNotACleanFile:
    @pytest.mark.parametrize("check", GAP_SENSITIVE_CHECKS)
    def test_an_unresolvable_input_FAILS_the_check(
            self, check, seeded_unresolvable_input):
        r = getattr(br, check)()
        assert r.passed is False, (
            f"{check} reported PASS over a draft whose `\\input` target does not "
            f"exist — it never opened the file and called it clean")
        assert r.measured is False, (
            f"{check} reported a MEASUREMENT over a population it could not read")

    @pytest.mark.parametrize("check", GAP_SENSITIVE_CHECKS)
    def test_the_clean_tree_reports_no_GAP(self, check):
        """The silent direction. A check wired to fail unconditionally would satisfy
        the test above while carrying no information.

        ⚠️ **It asserts the GAP mechanism, not a green corpus, and that is a
        correction (2026-08-15).** It read `passed is True`, which is a PROXY: it
        holds only while every one of these checks is green on production content,
        so any legitimate red anywhere in the corpus fails a test about `\\input`
        resolution. `bundle_reader_facing_voice` is deliberately RED — D12 discloses
        that it cites sources it has not read, and per ADR-014 that stays red until
        the sources are acquired, because deleting the disclosure while keeping the
        citation is the walk-back rather than the repair. Asserting `measured is
        True` and an empty gap set discriminates seeded from unseeded exactly, which
        is what this file owns; the seeded leg above asserts `measured is False`.
        """
        r = getattr(br, check)()
        gaps = [d.message for d in r.details if "unscannable" in d.name]
        assert not gaps, (
            f"{check} reported an unresolvable `\\input` on the UNSEEDED tree: {gaps}")
        assert r.measured is True, (
            f"{check} declined to measure the UNSEEDED tree: "
            f"{[d.message for d in r.details[:2]]}")

    def test_the_fixture_restores_the_draft_byte_for_byte(
            self, seeded_unresolvable_input):
        """Guard the guard: a seeding fixture that leaks corrupts every later run,
        and this one edits a tracked file."""
        import validate_helpers as _H
        assert SEED.strip() in (
            _H.PAPERS_DIR / SEED_HOST / "paper_draft.tex").read_text(encoding="utf-8")


# ⚠️ REMOVED: `test_the_fixture_restores_the_drafts_MTIME_not_just_its_bytes`
# re-implemented the fixture's cycle inline and asserted on that, never invoking the
# fixture — so deleting `os.utime` from the real one left it green. Its contract now
# lives in the fixture's own teardown above, where it cannot be bypassed.


def test_no_probe_survives_the_module():
    """The tracked corpus must carry no trace of the seed."""
    import validate_helpers as _H
    body = (_H.PAPERS_DIR / SEED_HOST / "paper_draft.tex").read_text(encoding="utf-8")
    assert "__unscannable_regression_probe" not in body, (
        "the seeding fixture leaked into the tracked corpus")
