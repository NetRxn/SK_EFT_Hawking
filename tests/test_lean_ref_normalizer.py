"""One normalizer for `Lean:` docstring references — audit finding QI-03.

WHAT WENT WRONG
---------------
Three parsers existed for "turn a `Lean:` docstring token into a declaration name":

  1. ``build_graph._clean_lean_ref``                    — the graph's formula label
  2. ``build_graph.extract_verified_by_edges``, INLINE  — ``split('(')[0].split(' ')[0]``
  3. ``lean_statements._parse_formula_lean_refs``       — the `formula_grounding` gate

(2) had **no rejection step at all**. Measured 2026-08-04: it fed **33 junk tokens**
to ``_resolve_lean_short`` — ``'N/A'``, ``'K0E0'``, ``'2'``, ``'16}_num'``,
``'…falsifier_*'``. An unguarded short-name resolver fed unfiltered tokens is the
exact mechanism of ADR-009 §Deferred item 7, where tail-resolution manufactured 144
phantom Lean VERIFIES edges.

AND MY OWN FIRST DIAGNOSIS WAS WRONG — WHICH IS WHY THIS FILE EXISTS
--------------------------------------------------------------------
The finding was filed as "unify on the good parser". **Measured, that is a
regression**: ``_clean_lean_ref`` rejected a **leading-dot** ref
(``.dean_adiabatic`` → ``QuasiOneDReduction.dean_adiabatic``) and every **Lean
prime name** (``haldaneD_diracK'``), because its class ``[\\w.]`` has no apostrophe
and it never stripped the leading dot. Switching (2) to it would have **lost 5
genuine VERIFIED_BY edges** to gain 4.

A second draft then spelled the class out as ``[A-Za-z0-9_.']`` and **dropped
``γ_immirzi`` and ``c₄_pos``** — Lean identifiers are Unicode and ``\\w`` already
matches them. Both errors were caught by measuring the candidate against the live
refs rather than by reading it.

So the tests below pin all three lessons: reject the junk, keep the primes and
leading dots, and **never narrow the class to ASCII**.

MEASURED AT THE FIX
-------------------
  refs accepted        509 -> 514   (+5, every one resolves in lean_deps.json)
  refs newly rejected  0
  dangling refs        4 -> 4       (unchanged, so no `formula_grounding` movement)
  VERIFIED_BY edges    529 -> 533   (+4 net: keeps the 5 genuine, drops the junk)

MUTATION-VERIFIED, each scoped to the target function's AST span:
  * drop ``.lstrip('.')``            -> test_leading_dot_is_the_suffix_idiom FAILS
  * narrow the class to ASCII        -> test_unicode_identifiers_survive FAILS
  * drop ``'`` from the class        -> test_lean_prime_names_survive FAILS
  * restore the inline parser in (2) -> test_verified_by_uses_the_shared_normalizer FAILS
Clean negative control: unmutated tree, all pass.

⚠️ A FIFTH mutation is recorded because it was NOT caught, and that is the point.
The first draft of the fix carried a separate ``any(c in tok for c in "{}*/\\\\")``
rejection. Mutating it to ``if False:`` changed no verdict and failed no test — the
``\\w``-based ``fullmatch`` below it already rejects every one of those characters,
so the guard could never be the sole reason a token was rejected. It was deleted
rather than kept as belt-and-suspenders: a guard that cannot fire is exactly what
this audit exists to remove, and shipping one inside the fix would have reproduced
the defect one layer down. The junk-rejection tests below therefore pin the
BEHAVIOUR (these tokens are rejected), not the mechanism.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))


@pytest.fixture(scope="module")
def clean():
    from build_graph import _clean_lean_ref
    return _clean_lean_ref


class TestGenuineFormsSurvive:
    """Every one of these is a real declaration form that appeared in a live
    `Lean:` docstring. Rejecting any of them silently drops real coverage."""

    def test_plain_and_dotted_names(self, clean):
        assert clean("dampingRate_eq_zero_iff") == "dampingRate_eq_zero_iff"
        assert clean("QuasiOneDReduction.dean_adiabatic") == "QuasiOneDReduction.dean_adiabatic"

    def test_leading_dot_is_the_suffix_idiom(self, clean):
        """`.foo` means "the `foo` in the module just named" — a suffix form, not
        a malformed token. Three real refs used it and were being discarded."""
        assert clean(".dean_adiabatic") == "dean_adiabatic"
        assert clean(".greybody_zero_freq_le_one") == "greybody_zero_freq_le_one"
        assert clean(".quasi1D_validity_bound") == "quasi1D_validity_bound"

    def test_lean_prime_names_survive(self, clean):
        """A trailing prime is ordinary Lean. The old class had no apostrophe, so
        every primed declaration was dropped."""
        assert clean("haldaneD_diracK'") == "haldaneD_diracK'"
        assert clean("haldaneNNN_diracK'") == "haldaneNNN_diracK'"

    def test_unicode_identifiers_survive(self, clean):
        """Lean identifiers are Unicode. A `[A-Za-z0-9_]` class silently drops
        them — the bug in my own second draft of this fix."""
        assert clean("c₄_pos") == "c₄_pos"
        assert clean("BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi") == \
            "BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi"

    def test_trailing_annotations_are_stripped_not_fatal(self, clean):
        assert clean("effective_temp_zeroth_order (WKBAnalysis.lean)") == \
            "effective_temp_zeroth_order"
        assert clean("secondOrder_count — counts the coefficients") == "secondOrder_count"
        assert clean("dispersive_correction_bound - the bound") == "dispersive_correction_bound"


class TestStructuralJunkIsRejected:
    """The 33 tokens the inline parser used to hand to `_resolve_lean_short`."""

    @pytest.mark.parametrize("junk", [
        "N/A",            # authors' "nothing to cite"
        "pending",        # the project's own placeholder
        "K0E0", "K1E1",   # matrix-element labels
        "2", "3", "8",    # bare numerals
        "16}_num",        # brace fragment from a broken split
        "BHEntropyMicroscopic.H_HorizonBoundaryCondition.falsifier_*",  # wildcard
        "TetradGapEquation.lean",   # a FILE, not a declaration
        "_private_helper",          # underscore-prefixed
        "ab",                       # too short to be a name
    ])
    def test_structural_junk_is_rejected(self, clean, junk):
        assert clean(junk) is None, (
            f"{junk!r} is not a declaration name, but the normalizer accepted it. "
            f"It would be handed to `_resolve_lean_short`, whose tail-matching "
            f"fabricated 144 phantom edges the last time it was fed unfiltered "
            f"tokens (ADR-009 §Deferred item 7)."
        )


class TestSingleOwner:
    """`extract_verified_by_edges` must not grow its own parser again."""

    def test_verified_by_uses_the_shared_normalizer(self):
        # AST, not raw text — the same reason `bundle_registry_consistency`'s leg C
        # is an AST walk: this function's body documents the removed parser
        # verbatim in a comment, and a text scan trips on its own explanation.
        # `ast.unparse` yields CODE only, so prose can never fail the guard.
        import ast

        tree = ast.parse((SK_ROOT / "scripts" / "build_graph.py").read_text())
        fn = next(
            n for n in ast.walk(tree)
            if isinstance(n, ast.FunctionDef) and n.name == "extract_verified_by_edges"
        )
        body = "\n".join(ast.unparse(stmt) for stmt in fn.body)

        assert "_clean_lean_ref(" in body, (
            "extract_verified_by_edges no longer calls `_clean_lean_ref`. It had "
            "its own inline parser with no rejection step, which fed 33 junk "
            "tokens to the short-name resolver (audit QI-03)."
        )
        assert ".split('(')[0]" not in body and '.split("(")[0]' not in body, (
            "the inline ad-hoc parser is back in extract_verified_by_edges. There "
            "is one normalizer, `_clean_lean_ref`; a second one diverges from it "
            "the moment either is tuned."
        )

    def test_every_accepted_ref_is_a_plausible_identifier(self, clean):
        """Whole-corpus property: nothing the normalizer accepts off the live
        docstrings may contain a character a Lean name cannot hold."""
        from build_graph import extract_formula_nodes

        bad = []
        for node in extract_formula_nodes():
            for ref in node.get("meta", {}).get("lean_refs", []):
                tok = clean(ref)
                if tok and re.search(r"[{}*/\\\s]", tok):
                    bad.append((node["name"], ref, tok))
        assert not bad, (
            f"{len(bad)} accepted ref(s) carry a character no Lean declaration "
            f"name can contain, e.g. {bad[:3]}"
        )
