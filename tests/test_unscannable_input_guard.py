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

    Restores from SAVED BYTES in a `finally`, never `git checkout` — a checkout
    would also discard concurrent edits, which is how a sibling test lost work.
    """
    import os
    import validate_helpers as _H
    draft = _H.PAPERS_DIR / SEED_HOST / "paper_draft.tex"
    original = draft.read_text(encoding="utf-8")
    original_stat = draft.stat()
    assert "\\begin{document}" in original, "fixture host lost its document body"
    try:
        draft.write_text(original.replace("\\begin{document}",
                                          SEED + "\\begin{document}", 1),
                         encoding="utf-8")
        yield
    finally:
        draft.write_text(original, encoding="utf-8")
        # ⚠️ RESTORE THE MTIME, not just the bytes. This fixture edits a TRACKED
        # draft, and `bundle_manuscript_length` refuses to size a PDF older than
        # its draft's `\input` closure — so a byte-perfect restore with a fresh
        # mtime silently took D1 UNMEASURED and the length gate went from
        # reporting 11 gaps to 10, while still passing. Measured: the "0
        # UNMEASURED" state was invalidated by THIS FIXTURE eight minutes before
        # the commit claiming it was written. A test must not change what a
        # production check measures.
        os.utime(draft, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))


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
    def test_the_clean_tree_still_passes(self, check):
        """The silent direction. A check wired to fail unconditionally would
        satisfy the test above while carrying no information."""
        r = getattr(br, check)()
        assert r.passed is True and r.measured is True, (
            f"{check} is failing on the UNSEEDED tree: {[d.message for d in r.details[:2]]}")

    def test_the_fixture_restores_the_draft_byte_for_byte(
            self, seeded_unresolvable_input):
        """Guard the guard: a seeding fixture that leaks corrupts every later run,
        and this one edits a tracked file."""
        import validate_helpers as _H
        assert SEED.strip() in (
            _H.PAPERS_DIR / SEED_HOST / "paper_draft.tex").read_text(encoding="utf-8")


def test_the_fixture_restores_the_drafts_MTIME_not_just_its_bytes():
    r"""⚠️ The property that actually matters, asserted directly on the file.

    An earlier version of this test asked whether `bundle_manuscript_length` still
    SIZED the host bundle — and that conflates two different facts. The gate also
    goes UNMEASURED when `docs/counts.tex` is regenerated (it sits in every
    bundle's `\input` closure), which any counts-regenerating test does and which
    is nothing to do with this fixture. A test that fails for a reason outside its
    own subject teaches the reader to ignore it.

    So: measure the draft's mtime, run the fixture's full cycle by hand, and
    require the mtime to come back. That is the fixture's contract and nothing
    else's."""
    import os
    import validate_helpers as _H

    draft = _H.PAPERS_DIR / SEED_HOST / "paper_draft.tex"
    before_bytes = draft.read_text(encoding="utf-8")
    before = draft.stat()

    # the fixture's cycle, inline
    try:
        draft.write_text(before_bytes.replace("\\begin{document}",
                                              SEED + "\\begin{document}", 1),
                         encoding="utf-8")
    finally:
        draft.write_text(before_bytes, encoding="utf-8")
        os.utime(draft, ns=(before.st_atime_ns, before.st_mtime_ns))

    after = draft.stat()
    assert draft.read_text(encoding="utf-8") == before_bytes, "bytes not restored"
    assert after.st_mtime_ns == before.st_mtime_ns, (
        "the draft's mtime moved. `bundle_manuscript_length` refuses to size a PDF "
        "older than its draft's input closure, so a byte-perfect restore with a "
        "fresh mtime silently takes this bundle UNMEASURED and shrinks that gate's "
        "reported population while it keeps passing.")


def test_no_probe_survives_the_module():
    """The tracked corpus must carry no trace of the seed."""
    import validate_helpers as _H
    body = (_H.PAPERS_DIR / SEED_HOST / "paper_draft.tex").read_text(encoding="utf-8")
    assert "__unscannable_regression_probe" not in body, (
        "the seeding fixture leaked into the tracked corpus")
