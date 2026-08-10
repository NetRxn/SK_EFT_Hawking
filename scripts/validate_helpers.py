"""Shared helpers for the validation suite — ADR-009 Phase 1.

WHAT THIS IS FOR
----------------
`scripts/validate.py` had grown 8 independent `lean_deps.json` load sites, 3
mutually inconsistent paper-draft scoping idioms, and 13 redundant `sys.path`
mutations. Each duplicate was individually reasonable and collectively a defect:
the 8 loaders disagree about what a MISSING `lean_deps.json` means (five treat it
as PASS, two as FAIL, one as a warning, one is unguarded and raises), and no
reader of any single check can see that.

This module owns **where things are and how they are read**. It deliberately does
NOT own **what their absence means** — see the policy note below.

THE POLICY LINE (ADR-009 H4) — READ BEFORE EXTENDING
----------------------------------------------------
A single `load_lean_deps()` that also decided the missing-file verdict would
silently unify eight checks' behaviour in one commit. That is a semantic change
wearing a mechanical disguise, and it is how a cleanup turns five live gates into
no-ops.

So the split is:

* **Here**: path resolution and parsing. `load_lean_deps()` RAISES on absence.
* **At each call site**: the guard, unchanged, returning that check's own
  `CheckResult` exactly as it did before.

Every call site therefore still reads `if not lean_deps_present(): return <its own
verdict>`. The divergence stays visible and is marked for the Phase-3 semantic
review, rather than being erased by a refactor nobody reviewed as a behaviour
change.

NO MEMOIZATION — still true, but NOT for the reason first written here
----------------------------------------------------------------------
`load_lean_deps()` re-reads and re-parses the 70 MB file on every call, and it
stays that way. It reads the file DIRECTLY rather than through
`extract_lean_deps.load_lean_deps()`, so it never triggers that function's
hash-guarded refresh — deliberate, and preserved.

⚠️ **This section described the pre-fix world as current until 2026-08-04 (audit
finding QI-18).** It said the readers at ~55/56/58 "currently observe the
regenerated file" while those at ~5/7/8/9 "observed the pre-regeneration one", and
concluded that caching was a Phase-3 candidate. That divergence was CLOSED by
ADR-009 §Deferred item 0: `validate.main()` now calls
:func:`ensure_lean_deps_fresh` once, before any check runs, so all eight readers
observe one snapshot. The exact positions are measured in that function's own
docstring, sixty lines below — and this section contradicted it inside the same
file, which is precisely the shape a reader cannot resolve without going to the
code.

What remains true: a cache here would still be a behaviour change rather than an
optimisation, because `counts_fresh` shells out to `update_counts.py`, which *can*
rewrite `lean/lean_deps.json` mid-run. With the up-front refresh in place the hash
guard makes that a no-op in practice, but the ordering hazard is structural and the
cache would freeze whichever state was read first. The remaining performance item
is the shared GRAPH handle, which ADR-009 §Deferred item 0 **DECLINED** on
measurement (8% of one command's runtime against a three-module signature change).
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# ── The single path anchor (ADR-009 H1) ──────────────────────────────────
# Every path in the suite derives from these two. When `validate.py` becomes
# `scripts/validate/` in Phase 2, `Path(__file__).parent` shifts by one level and
# a per-module anchor would silently retarget PROJECT_ROOT into `scripts/` —
# where every artifact lookup misses and every check takes its "absent" branch,
# turning the whole suite green while measuring nothing. Anchoring once, here,
# means that failure has exactly one place to be fixed.
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent

SRC_DIR = PROJECT_ROOT / "src"
LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
LEAN_DEPS_PATH = PROJECT_ROOT / "lean" / "lean_deps.json"
NOTEBOOKS_DIR = PROJECT_ROOT / "notebooks"
PAPERS_DIR = PROJECT_ROOT / "papers"
DOCS_DIR = PROJECT_ROOT / "docs"
COUNTS_JSON_PATH = DOCS_DIR / "counts.json"
COUNTS_TEX_PATH = DOCS_DIR / "counts.tex"


# ── lean_deps.json ───────────────────────────────────────────────────────

def lean_deps_present() -> bool:
    """True if `lean/lean_deps.json` exists. Call sites use this to keep their
    OWN missing-file verdict (see the policy note in the module docstring)."""
    return LEAN_DEPS_PATH.exists()


def load_lean_deps() -> list[dict]:
    """Parse `lean/lean_deps.json` and return its declaration records.

    RAISES `FileNotFoundError` if absent — deliberately. Deciding what absence
    means belongs to the caller; see the module docstring. Reads the file
    directly, without the hash-guarded refresh in
    `extract_lean_deps.load_lean_deps()`, matching what the inline sites did.

    Whole-run freshness is the job of :func:`ensure_lean_deps_fresh`, called once
    by `validate.main()` for a FULL run. Doing it per-call here would fire an
    ExtractDeps inside `--check native_decide_regression`, which the commit gate
    forbids (see that function's docstring).
    """
    return json.loads(LEAN_DEPS_PATH.read_text())


def ensure_lean_deps_fresh() -> tuple[bool, str]:
    """Hash-guarded refresh of `lean/lean_deps.json`. Returns `(refreshed, note)`.

    WHY THIS EXISTS — the readers disagreed with each other
    -------------------------------------------------------
    ⚠️ DO NOT WRITE ORDINALS HERE. This paragraph used to argue from fixed registry
    positions ("`counts_fresh` sits at position 29 ... five readers before it, three
    after"). `counts_fresh` was moved to the FRONT of `_CANONICAL_ORDER` on
    2026-08-07, which refuted every number in the sentence and, read literally,
    refuted the function's own reason for existing. Derive the ordering instead:

        uv run python scripts/validate.py --list        # order is the run order

    THE DEFECT, stated without ordinals: several checks read `lean/lean_deps.json`,
    `load_lean_deps()` reads it directly with NO hash guard, and the check that
    regenerates it sits somewhere in the same ordered run. On exactly the runs where
    Lean changed — a wave close — every reader scheduled BEFORE the regeneration
    validated the PREVIOUS extraction while every reader after it validated the fresh
    one, inside a single run. Among the early readers is the
    `native_decide_regression` ratchet: a ratchet measuring the previous wave's
    substrate cannot see the trust surface the current wave added, which is the one
    thing it exists to catch.

    That the regenerating check now happens to run first does NOT retire this
    function: the guarantee must not depend on registry order, which has already
    moved once. Refreshing here, before the loop starts, is order-independent.

    A cache would not have fixed that — it would have frozen one of the two states.
    Refreshing once, up front, makes all eight observe the same snapshot.

    SCOPE IS DELIBERATELY "FULL RUN ONLY"
    -------------------------------------
    `validate.main()` calls this only when no `--check` filter is given.
    `scripts/pre-commit-sync.sh` runs `--check native_decide_regression` in the commit
    gate and states plainly that it must NEVER run the heavy ExtractDeps pass
    (`:72-74`, and the file header: *"INCREMENTAL lean guard — never the 30-min clean
    ExtractDeps"*). Refreshing inside `load_lean_deps()` would have violated that.

    COST IS ZERO WHEN NOTHING CHANGED, AND NOT NEW WHEN IT DID
    ----------------------------------------------------------
    The guard is a SHA-256 over every `.lean` source: **46 ms** measured, against
    **150 ms** for one parse of the 70 MB artifact. When a refresh IS needed, a full
    run already pays for that same extraction at position 29 via `counts_fresh` →
    `update_counts.py`; this moves the cost earlier, it does not add it.

    Degrades to a no-op (never raises) if `extract_lean_deps` is unavailable, so a
    partial checkout behaves exactly as before.
    """
    try:
        import extract_lean_deps
    except ImportError as exc:  # pragma: no cover - partial checkout
        return False, f"skipped — extract_lean_deps unavailable ({exc})"
    try:
        if not extract_lean_deps._needs_refresh():
            return False, "lean_deps.json already fresh (hash matches .lean sources)"
        extract_lean_deps._run_extraction()
        # ⚠️ VERIFY the refresh actually took. This returned True unconditionally
        # after calling `_run_extraction()`, so any run that completed without
        # regenerating the artifact still reported "refreshed before any check read
        # it". That report is worse than no report: the checks downstream then read
        # a STALE artifact under a fresh-looking banner, and the resulting pass is
        # memoized under the NEW source key, so it replays instead of re-running.
        # Re-asking the same hash guard is the only claim we can actually back.
        if extract_lean_deps._needs_refresh():
            return False, ("refresh RAN but lean_deps.json is still stale by its own "
                           "hash guard — downstream checks are reading an out-of-date "
                           "artifact; do NOT trust counts from this run")
        return True, "lean_deps.json refreshed before any check read it"
    except Exception as exc:  # noqa: BLE001
        # NEVER fail the run here. Each check keeps its own missing/stale verdict
        # (H4); this is a best-effort freshening, not a gate.
        return False, f"refresh attempted and failed ({type(exc).__name__}: {exc})"


# ── counts.json ──────────────────────────────────────────────────────────

def counts_present() -> bool:
    return COUNTS_JSON_PATH.exists()


def load_counts() -> dict:
    """Parse `docs/counts.json`. Raises on absence / malformed JSON."""
    return json.loads(COUNTS_JSON_PATH.read_text())


# ── paper drafts ─────────────────────────────────────────────────────────
# TWO functions, never one with a flag. The scopes differ by design and the
# difference is load-bearing: `prose_theorem_reference_coverage` is deliberately
# bundle-only (documented in its own docstring), while the prose-hygiene checks
# cover every draft on disk. A single `paper_drafts(bundles_only=False)` would
# make that distinction an argument someone can get wrong, which is exactly how
# D10 shipped for a month outside the one gate that catches Lean-name drift.

def all_paper_drafts() -> list[Path]:
    """Every `papers/*/paper_draft.tex` on disk — bundles AND legacy per-paper
    drafts (64 today). Sorted for stable iteration order."""
    if not PAPERS_DIR.exists():
        return []
    return sorted(PAPERS_DIR.glob("*/paper_draft.tex"))


def bundle_drafts(bundle_codes) -> list[tuple[str, Path]]:
    """`(code, path)` for each publication-bundle draft that exists on disk.

    Scope is the 21 roster codes only. `bundle_codes` is passed in rather than
    imported so this module stays independent of `bundle_registry` — the roster's
    single source of truth is gated separately by
    `check_bundle_registry_consistency`, and importing it here would add a second
    consumer that gate would then have to know about.
    """
    out: list[tuple[str, Path]] = []
    for code in bundle_codes:
        tex = PAPERS_DIR / code / "paper_draft.tex"
        if tex.exists():
            out.append((code, tex))
    return out


def unresolved_aristotle_keys() -> list[str]:
    """`ARISTOTLE_THEOREMS` keys that name NO declaration in `lean_deps.json`.

    ONE OWNER, deliberately (added 2026-08-05, PR-review R4-I3). Two checks need
    this set and they need the SAME set:

    * `lean_toolchain.check_theorem_count` ratchets its size, so a new stale key
      fails; and
    * `lean_substrate.check_formulas_to_theorems` must SUBTRACT it, because that
      check unions the registry's keys into `all_lean_names` — the set it resolves
      formula references against. A key naming nothing therefore launders a
      nonexistent theorem into the valid-name set, and a formula grounded on it
      passes. Ratcheting the count closed the generator; it did not close the hole.

    A second copy of this resolver in the second call site is exactly the shape the
    audit keeps finding (`_recurrence_norm`, `_SEVERITY_DECL_MAP`, the duplicated
    `NUMERICAL_LITERAL_RE`), so it lives here — `validate_helpers` is the
    shared-helper home and is outside the check package, so neither module imports
    a sibling.

    RAISES `FileNotFoundError` via :func:`load_lean_deps` when the substrate is
    absent. Callers decide what absence means; both current callers treat it as
    UNVERIFIED rather than clean.
    """
    from src.core.constants import ARISTOTLE_THEOREMS

    full = {d.get("name", "") for d in load_lean_deps()}
    short = {n.rsplit(".", 1)[-1] for n in full if n}
    return sorted(k for k in ARISTOTLE_THEOREMS if k not in short and k not in full)


# ═══════════════════════════════════════════════════════════════════════
# Compiler-generated vs author-written declarations
# ═══════════════════════════════════════════════════════════════════════

#: Suffixes Lean reserves for declarations it generates alongside an inductive or
#: structure. Lean's own `isReservedName` is `private opaque`, so it cannot be called
#: from `ExtractDeps`; these are the residue its three PUBLIC predicates
#: (`Name.isInternalDetail`, `isAuxRecursor`, `isNoConfusion`) do not reach.
#:
#: ⚠️ Never matched on the name alone — `_autogen_supplement` requires the PARENT to be
#: an `inductive` or `structure`, which is read from `lean_deps.json`'s `kind`. A bare
#: suffix match would classify an author-written `Foo.injEq` as generated.
#: The first group is the residue Lean's public predicates do NOT reach. The second is
#: redundant with them in production (verified: `casesOn` 580/580, `recOn` 577/577,
#: `noConfusion` 923/923 all carry `autogen`) and is listed anyway so this lookup is
#: SELF-SUFFICIENT — it then also classifies correctly against a `lean_deps.json` that
#: predates the `autogen` field, rather than silently returning "author-written" for
#: every eliminator in the tree.
_RESERVED_GENERATED_SUFFIXES = (
    # not reached by isInternalDetail / isAuxRecursor / isNoConfusion
    "noConfusionType", "ctorIdx", "toCtorIdx", "sizeOf_spec", "eq_def", "injEq",
    "inj", "ctorElim", "ctorElimType", "ofNat",
    # reached by Lean in production; kept for self-sufficiency
    "casesOn", "recOn", "brecOn", "below", "ibelow", "binductionOn", "noConfusion",
)

#: `deriving`-generated INSTANCE FIELDS — `instReprFoo.repr`, `instDecidableEqFoo.decEq`.
#: Their parent is the derived `instance`, not the type, so the inductive/structure guard
#: above cannot reach them; they get their own parent-kind branch rather than a bare
#: suffix match. Measured over the live corpus: every `.repr` (76) and `.decEq` (34) has
#: an `instance` parent, and no author-written declaration ends in either.
_DERIVED_INSTANCE_FIELD_SUFFIXES = ("repr", "decEq")


def _is_internal_detail(name: str) -> bool:
    """Faithful port of Lean's `Name.isInternalDetail` (Lean/Data/Name.lean:147).

    ⚠️ This is NOT a heuristic dressed as one. `isInternalDetail` is defined in Lean as a
    predicate ON THE NAME — `_`-prefixed, or `eq_` / `match_` / `proof_` / `omega_`
    followed only by digits and underscores, or a numeric component. Reproducing that
    definition is reproducing Lean, and it lets this lookup classify a record that has no
    `autogen` field. The parts of the classification that are NOT name-based
    (`isAuxRecursor`, `isNoConfusion`) are exactly the parts that require the field.
    """
    for comp in name.split("."):
        if comp.startswith("_") or comp.isdigit():
            return True
        for pre in ("eq_", "match_", "proof_", "omega_"):
            if comp.startswith(pre):
                rest = comp[len(pre):]
                if rest and all(c.isdigit() or c == "_" for c in rest):
                    return True
    return False


def autogen_index(records) -> dict:
    """`{declaration name: True/False}` — is it COMPILER-GENERATED?

    Primary source is the `autogen` field `ExtractDeps` emits, computed from Lean's own
    predicates. Measured against the name-pattern regex this replaces: the two agreed on
    barely half the population — the regex MISSED ~2 300 (mostly `X.eq_1`, whose name
    carries no leading underscore) and OVER-CLAIMED ~2 700. Every count that filtered on
    that regex inherited both errors.

    Adds the structurally-guarded suffix supplement described above (~2 300 more).
    Build it ONCE per `lean_deps` load and pass it around; it needs the whole record set
    to resolve parents.
    """
    kind = {r["name"]: r.get("kind") for r in records if r.get("name")}

    def supplement(name: str) -> bool:
        if _is_internal_detail(name):
            return True
        for suf in _RESERVED_GENERATED_SUFFIXES:
            if not name.endswith("." + suf):
                continue
            parent = name[: -(len(suf) + 1)]
            if kind.get(parent) in ("inductive", "structure"):
                return True
            # `X.mk.injEq`, `X.ctor.sizeOf_spec` — the TYPE is the grandparent.
            if kind.get(parent.rsplit(".", 1)[0]) in ("inductive", "structure"):
                return True
        for suf in _DERIVED_INSTANCE_FIELD_SUFFIXES:
            if name.endswith("." + suf) and kind.get(name[: -(len(suf) + 1)]) == "instance":
                return True
        return False

    out = {}
    for r in records:
        n = r.get("name")
        if n:
            out[n] = bool(r.get("autogen")) or supplement(n)
    return out


# ═══════════════════════════════════════════════════════════════════════
# LaTeX draft input closure — promoted here 2026-08-08 (ADR-011 Phase 2b)
# ═══════════════════════════════════════════════════════════════════════

#: `\input{...}` / `\include{...}` / `\includegraphics[...]{...}` — the three ways a
#: draft pulls in a file whose content can change whether, and how, it compiles.
TEX_INPUT_RE = re.compile(
    r"\\(?:input|include)\s*\{([^}]+)\}"
    r"|\\includegraphics\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}")


def draft_input_closure(tex: Path, _seen: set | None = None) -> list[Path]:
    """Every file whose content can change this draft's compile outcome.

    Resolves ``\\input``/``\\include`` recursively (LaTeX's own ``.tex``-extension
    default applied when the reference has no suffix) and ``\\includegraphics`` one
    level, plus any ``*.bib`` sitting beside the draft. Cycle-guarded via ``_seen``.

    Deliberately a SUPERSET where it is uncertain: an unresolvable reference is still
    recorded as a path, so the file appearing later moves the hash. Over-hashing costs
    a needless recompile; under-hashing skips a broken draft, and only one of those two
    failures is silent.

    **Lives here because three subsystems now ask the same question** — is this draft's
    compiled output still current? `paper_latex_compiles` hashes this closure for its
    per-draft cache, `bundle_manuscript_length` compares the PDF's mtime against it, and
    `compile_bundle_pdf.py` skips a recompile on it. Three copies of "which files change
    this draft" would disagree the first time someone added `\\includesvg`, and the
    disagreement would be invisible: each consumer would look right on its own.

    Consistent with this module's policy line — it resolves WHERE things are, and says
    nothing about what a stale or missing artifact MEANS. Each caller decides that.
    """
    seen = _seen if _seen is not None else set()
    if tex in seen:
        return []
    seen.add(tex)
    closure = [tex]
    try:
        body = tex.read_text(errors="replace")
    except OSError:
        return closure
    if _seen is None:  # top level only — siblings, not per-\input
        closure.extend(sorted(tex.parent.glob("*.bib")))
    for m in TEX_INPUT_RE.finditer(body):
        ref = (m.group(1) or m.group(2) or "").strip()
        if not ref:
            continue
        target = (tex.parent / ref).resolve()
        if m.group(1) and not target.suffix:
            target = target.with_suffix(".tex")
        if m.group(1) and target.suffix == ".tex":
            closure.extend(draft_input_closure(target, seen))
        else:
            closure.append(target)
    return closure


def bundle_codes_or_unmeasured() -> "tuple[list[str] | None, str | None]":
    """`(codes, None)`, or `(None, reason)` when the roster cannot be read.

    DRY: **ten** checks opened with a byte-identical seven-line try/except that
    imported `bundle_registry`, caught `Exception`, and returned
    `CheckResult(passed=False, measured=False, details=[Detail("roster", False, …)])`
    — in two message variants that had drifted apart (seven said ", not passing",
    three did not). One roster reader, one message, one place to change it.

    Lives here rather than in a check module so neither check package imports a
    sibling; `validate_helpers` is already the shared home and is outside both.
    """
    try:
        # From the roster's OWNER, not from `validate`'s re-export — the discipline
        # `bundle_registry_consistency` leg C exists to enforce. That comment used to
        # live at one of the ten call sites and applied to all of them.
        import bundle_registry as registry
        return list(registry.BUNDLE_CODES), None
    except Exception as exc:      # noqa: BLE001 — any import failure is unmeasured
        return None, (f"could not read the bundle roster ({exc}) — UNVERIFIED, "
                      f"not passing")
