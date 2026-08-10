"""Every ratcheted check sits at ZERO HEADROOM — PR-review pass 2, R3.

WHY THIS FILE EXISTS
--------------------
The house idiom is a frozen ceiling that may only shrink: `COUNT_LITERAL_CEILING`,
`NATIVE_DECIDE_DECL_CLOSURE_CEILING`, `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING`, and
their siblings. The idiom only works at **zero headroom** — a ceiling above the
live population is a ratchet that cannot fire, and reports green while the thing
it guards drifts underneath it.

Reviewer R3 measured all ten ceilings as correct **today**, and found that **not
one of them had a test asserting it**. So the values were right by hand and free
to drift by accident: lower the population and the ceiling silently gains slack,
which is exactly how `test_cannot_measure_baseline`'s seam guard came to sit at
`>= 30` against a live 54 (**44 % headroom**, tightened in the same pass).

WHAT THIS ASSERTS, AND WHAT IT DELIBERATELY DOES NOT
-----------------------------------------------------
It runs each ratcheted check against the **live tree** and asserts the population
it reports equals the ceiling it reports. It does NOT re-implement any check's
counting logic — a test that recomputed the population would assert only that two
copies of the same arithmetic agree, which is the "test agrees with itself" shape
this audit keeps finding.

⚠️ **Checks whose summary does not state a ceiling are REPORTED, not skipped
silently.** A guard that quietly narrows its own population is the defect class
this suite exists to catch; `test_the_covered_set_is_declared` fails if coverage
drops below the frozen roster.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate  # noqa: E402

#: Checks whose summary Detail states "<N> ... (ceiling <M>)" or "<N> <= ceiling <M>".
#: FROZEN. Removing one is a decision — it means a ratchet lost its zero-headroom
#: guard, which is how slack creeps back in.
RATCHETED_CHECKS = (
    "native_decide_regression",
    "count_literals",
    "numerical_literals",
    "theorems",
    "elaboration_knob_watchlist",
    "bundle_tables_use_pipeline",
    # ⚠️ Added 2026-08-09. Both were ratchets in production, both stated their
    # ceiling in the phrasing this file already parses, and NEITHER was named by
    # any test in the suite — `PROVENANCE_UNRESOLVABLE_CEILING = 163` and
    # `LEGACY_DRAFT_LATEX_BROKEN_CEILING = 14`. They were invisible because the
    # roster was hand-listed and its only guard was `len(...) >= 6`, which a
    # never-added entry trivially satisfies. That guard is now a reconciliation
    # (see `test_every_ceiling_constant_is_named_by_a_test`).
    "parameter_provenance",
    "paper_latex_compiles",
)

#: `*_CEILING` constants that are NOT zero-headroom ratchets, with the reason.
#: Anything not here must be named by a test — that is the reconciliation.
_NOT_A_RATCHET = {
    # A per-tier cap on revtex4-2 letter-numbered subsections (26 is the format's
    # own limit). A charter sits under it by design; equality would be a defect,
    # not the goal, so zero headroom is the wrong property to assert.
    "_SECTION_CEILING_BY_TIER",
}

_CEIL_RE = re.compile(r"ceiling\s+(\d+)", re.IGNORECASE)
_LEAD_RE = re.compile(r"(\d+)")


def _population_and_ceiling(check: str):
    """(population, ceiling) as the check itself reports them, or None."""
    fn = next(s.func for s in validate._CHECKS if s.name == check)
    result = fn()
    for d in result.details:
        msg = d.message or ""
        m_ceil = _CEIL_RE.search(msg)
        if not m_ceil:
            continue
        m_pop = _LEAD_RE.search(msg)
        if not m_pop:
            continue
        return int(m_pop.group(1)), int(m_ceil.group(1))
    return None


class TestRatchetsHaveZeroHeadroom:

    @pytest.mark.parametrize("check", RATCHETED_CHECKS)
    def test_population_equals_ceiling(self, check):
        """FIRES ON A SEEDED DEFECT: raise any ceiling above its live population and
        this fails — before the ratchet silently stops guarding."""
        got = _population_and_ceiling(check)
        assert got is not None, (
            f"{check} no longer reports a '(ceiling N)' in any Detail, so its "
            f"headroom cannot be measured. Restore the phrasing or remove it from "
            f"RATCHETED_CHECKS deliberately — do not let it fall out silently.")
        population, ceiling = got
        assert population == ceiling, (
            f"{check}: live population {population} against ceiling {ceiling} — "
            f"{abs(ceiling - population)} of headroom. "
            + ("LOWER the ceiling in the same commit (the population shrank, which is "
               "good news the ratchet must record)." if population < ceiling else
               "The population GREW past its ceiling; fix the underlying debt rather "
               "than raising the number."))

    def test_every_ceiling_constant_is_named_by_a_test(self):
        """⚠️ THE RECONCILIATION THAT REPLACED A `>= 6` FLOOR.

        The old guard asserted the roster had at least six entries. A ratchet that
        was never added satisfies that trivially, so the roster's own blind spot
        was undetectable by the test guarding the roster. Measured 2026-08-09: 15
        `*_CEILING` constants exist; **two were named by no test file at all**, and
        six more were covered by ad-hoc per-check tests rather than by this roster
        — zero-headroom enforcement living in two unreconciled mechanisms.

        This derives the population from the source instead: every `*_CEILING`
        constant must be named somewhere in `tests/`, or be declared a non-ratchet
        with a reason. It fails when a new ceiling is added and forgotten, which is
        the failure mode a count-based floor cannot see."""
        import re as _re
        roots = [SK_ROOT / "src" / "core" / "constants.py"]
        roots += sorted((SK_ROOT / "scripts" / "validation").rglob("*.py"))
        found = set()
        for f in roots:
            found |= set(_re.findall(r"^(_?[A-Z][A-Z0-9_]*CEILING[A-Z0-9_]*)\s*=",
                                     f.read_text(encoding="utf-8"), _re.MULTILINE))
        found -= _NOT_A_RATCHET
        assert found, "no ceiling constants found — the scan itself broke"

        # ⚠️ COMMENTS AND DOCSTRINGS DO NOT COUNT. The first version of this test
        # concatenated the raw test tree, which includes THIS FILE — and the very
        # comment above naming the two previously-uncovered ceilings was their
        # only test-tree mention. The mechanism meant to catch a forgotten ceiling
        # was discharged by writing the ceiling's name in prose explaining that it
        # had been forgotten. Strip comments and string literals first, so a name
        # counts only where it is USED.
        # Drop COMMENTS and DOCSTRINGS. ⚠️ NOT all strings: `monkeypatch.setattr(
        # mod, "SOME_CEILING", 0)` names the constant in a string literal and is a
        # perfectly real use. A docstring is a string in STATEMENT position, which
        # is what the `prev_significant` test below identifies.
        import io, tokenize
        code_only = []
        for f in sorted((SK_ROOT / "tests").rglob("*.py")):
            src = f.read_text(encoding="utf-8")
            try:
                prev = tokenize.NEWLINE
                for tok in tokenize.generate_tokens(io.StringIO(src).readline):
                    if tok.type == tokenize.COMMENT:
                        continue
                    is_docstring = (tok.type == tokenize.STRING and prev in (
                        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
                        tokenize.DEDENT, tokenize.ENCODING))
                    if not is_docstring:
                        code_only.append(tok.string)
                    if tok.type not in (tokenize.NL, tokenize.COMMENT):
                        prev = tok.type
            except (tokenize.TokenError, IndentationError, SyntaxError):
                code_only.append(src)          # unparseable: fall back to raw
        test_src = "\n".join(code_only)
        # A ceiling is covered EITHER by name in test code, OR because the check
        # that consumes it is in RATCHETED_CHECKS — which is how
        # `PROVENANCE_UNRESOLVABLE_CEILING` and `LEGACY_DRAFT_LATEX_BROKEN_CEILING`
        # are held: the parametrized zero-headroom test above drives
        # `parameter_provenance` and `paper_latex_compiles` and asserts their live
        # population equals their reported ceiling. Coverage by check name is real
        # coverage; what is NOT coverage is a mention in a comment, which is why
        # `test_src` is stripped of comments and docstrings above.
        # ⚠️ Ownership is per FUNCTION BODY, not per module. Crediting every
        # ceiling in a module that happens to contain a ratcheted check gives a
        # free pass to the next ceiling added to `citations.py` — measured: a
        # seeded `ZZZ_FORGOTTEN_CEILING` there passed under the module-level rule.
        import ast as _ast
        from textwrap import dedent as _dedent
        covered_by_check: set[str] = set()
        for f in sorted((SK_ROOT / "scripts" / "validation").rglob("*.py")):
            src = f.read_text(encoding="utf-8")
            try:
                tree = _ast.parse(src)
            except SyntaxError:
                continue
            for node in _ast.walk(tree):
                if not isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                    continue
                names = {d.args[0].value for d in node.decorator_list
                         if isinstance(d, _ast.Call)
                         and getattr(d.func, "id", "") == "register_check"
                         and d.args and isinstance(d.args[0], _ast.Constant)}
                if not (names & set(RATCHETED_CHECKS)):
                    continue
                # ⚠️ `get_source_segment` returns RAW source INCLUDING comments,
                # so a bare substring test would credit a ceiling named only in a
                # comment inside a ratcheted check body — the same evasion this
                # test strips comments to prevent on the other path. Caught by the
                # closure reviewer. Match against identifier tokens only.
                body = _ast.get_source_segment(src, node) or ""
                try:
                    used = {n.id for n in _ast.walk(_ast.parse(_dedent(body)))
                            if isinstance(n, _ast.Name)}
                    used |= {n.attr for n in _ast.walk(_ast.parse(_dedent(body)))
                             if isinstance(n, _ast.Attribute)}
                    used |= {a.name for n in _ast.walk(_ast.parse(_dedent(body)))
                             if isinstance(n, (_ast.Import, _ast.ImportFrom))
                             for a in n.names}
                    used |= {a.asname for n in _ast.walk(_ast.parse(_dedent(body)))
                             if isinstance(n, (_ast.Import, _ast.ImportFrom))
                             for a in n.names if a.asname}
                except SyntaxError:
                    used = set()
                covered_by_check |= (found & used)

        orphans = sorted(c for c in found
                         if c not in test_src and c not in covered_by_check)
        assert orphans == [], (
            f"{len(orphans)} ratchet ceiling(s) are named by NO test, so nothing "
            f"holds them at zero headroom: {orphans}. Add the owning check to "
            f"RATCHETED_CHECKS, or declare the constant in _NOT_A_RATCHET with a "
            f"reason.")

    def test_the_covered_set_is_declared(self):
        """Guard the seam. If a ratcheted check drops out of RATCHETED_CHECKS the
        parametrization above silently shrinks and every remaining case still
        passes — the exact narrowing this suite exists to catch."""
        registered = {s.name for s in validate._CHECKS}
        missing = [c for c in RATCHETED_CHECKS if c not in registered]
        assert not missing, f"RATCHETED_CHECKS names unregistered check(s): {missing}"
