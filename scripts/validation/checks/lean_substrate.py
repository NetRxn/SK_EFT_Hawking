"""Lean substrate-integrity checks — the SUBSTANCE gates (ADR-004 R1-R3).

Does a theorem actually prove something, and is every modelling assumption
disclosed? `formulas`, `placeholder_not_cited`, `disclosure_consistency`,
`proxy_body_audit`, `tracked_hypothesis_ledger`, `tracked_hypotheses_fresh`,
`formula_grounding`, `vacuous_statement_audit`, `nogo_substrate_integrity`.

Split from the BUILD/TRUST-SURFACE half, which lives in `checks/lean_toolchain.py`
— see that module's header for why (the combined module measured ~1,580 lines and
failed D1's readable-in-one-pass criterion; the two share no helpers).

WHAT THIS MODULE OWNS THAT OTHERS BORROW
-----------------------------------------
The **type-thinness classifier** — `_thin_type_label`, `_is_vacuous_identity_wrapper`,
`_top_tokens`, `_top_arrow_split`, `_strip_leading_binders`, `_THIN_HARD`,
`_is_autogen_decl` — operates on the ELABORATED type from `lean_deps.json`, so it is
name-agnostic and tactic-agnostic. That is deliberate: `proxy_body_audit` is
name-gated and excludes `norm_num`/`decide` bodies, so a theorem whose STATEMENT
proves nothing slips past it. The classifier is the companion that catches those,
and `nogo_substrate_integrity` reuses it to refuse a self-discharging no-go.

FIFTEEN OF THIS MODULE'S INTERNALS ARE IN THE FROZEN EXTERNAL SURFACE
----------------------------------------------------------------------
`tests/test_substrate_integrity_gates.py` imports the regexes and pure cores
directly — `_STRUCTURAL_NAME_RE`, `_TRIVIAL_BODY_RES`, `_NONTRIVIAL_MARKER_RE`,
`_VERIFY_CLAIM_RE`, `_HEDGE_CLAIM_RE`, `_OVERCLAIM_VERB_RE`, `_LEDGER_HEDGE_RE`,
`_TRACKED_PROP_NAME_RE`, `_THIN_HARD`, `_tex_name_pattern`, `_is_prop_codomain`,
`_is_autogen_decl`, `_thin_type_label`, `_is_vacuous_identity_wrapper`,
`_parse_formula_lean_refs` — plus five check functions. `validate` re-exports every
one (ADR-009 D2 item 8).

⚠️ That file was INVISIBLE to the first surface scan, which filtered on
`module == "validate"` while the file still said `scripts.validate`. Twenty names
were missing from the frozen list and fifteen of them were these. Had the omission
survived, this extraction is exactly where it would have detonated.

MOVED VERBATIM — extracted by script from AST-verified ranges. No body edited, no
policy unified, no threshold retuned (ADR-009 D4). Paths are `_H.<NAME>` at each
use, never module-level aliases and never from `__file__` (H1). No check here reads
a runtime flag.
"""
from __future__ import annotations

import ast
import json
import re
import tokenize
from typing import Dict, List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check
from validation._tex import tex_escaped_name_pattern


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1: Python formulas ↔ Lean theorems
# ═══════════════════════════════════════════════════════════════════════

@register_check("formulas", "Python formulas reference valid Lean theorems")
def check_formulas_to_theorems() -> CheckResult:
    from src.core import formulas
    from src.core.constants import ARISTOTLE_THEOREMS

    mapping = [
        ('count_coefficients', ['secondOrder_count', 'secondOrder_count_with_parity', 'thirdOrder_count']),
        ('enumerate_monomials', ['secondOrder_count_with_parity', 'secondOrder_requires_parity_breaking']),
        ('damping_rate', ['dampingRate_eq_zero_iff']),
        ('dispersive_correction', ['dispersive_correction_bound', 'bogoliubov_superluminal']),
        ('first_order_correction', ['firstOrder_correction_zero_iff']),
        ('effective_temperature_ratio', ['effective_temp_zeroth_order']),
        ('turning_point_shift', ['turning_point_shift_nonzero', 'turning_point_shift']),
    ]

    # Build set of all Lean theorem names (Aristotle-proved + manually proved)
    lean_dir = _H.LEAN_DIR          # was Path(__file__).parent.parent — ADR-009 H1
    #
    # ⚠️ SUBTRACT THE UNRESOLVED REGISTRY KEYS (2026-08-05, PR-review R4-I3).
    # `ARISTOTLE_THEOREMS` is hand-maintained and its keys are unioned into the set
    # this check resolves formula references against — so a key naming no Lean
    # declaration LAUNDERS a nonexistent theorem into the valid-name set, and a
    # formula grounded on it reports as grounded. QI-30 ratcheted the count of such
    # keys, which closed the generator; the existing 14 kept laundering.
    #
    # Measured 2026-08-05: 14 of 322 keys resolve to nothing, and **none of the 14 is
    # currently a mapping target**, so the exposure was LATENT, not live — the same
    # posture as QI-01, and filed the same way rather than downgraded for it.
    #
    # `_H.unresolved_aristotle_keys` is the single owner shared with
    # `check_theorem_count`'s ratchet; a second resolver here could disagree with the
    # ratchet about which keys are stale, which is the failure this fix exists to end.
    try:
        _stale_keys = set(_H.unresolved_aristotle_keys())
    except FileNotFoundError:
        # Absence is not evidence the registry is clean. Keep the STRICTER behaviour:
        # no subtraction means no laundering-suppression, so fall back to the full
        # key set rather than silently trusting it — and say so in the details below.
        _stale_keys = set()
    all_lean_names = set(ARISTOTLE_THEOREMS.keys()) - _stale_keys
    if lean_dir.exists():
        # ⚠️ rglob, NOT glob (fixed 2026-08-04, audit finding QI-01). `glob` read
        # 1,373 of ~2,040 files, so any mapped theorem that lives in a package
        # would be reported "Not in Lean source or ARISTOTLE_THEOREMS" while
        # existing. A false failure rather than a false pass, but the set this
        # check resolves against was two-thirds of the library.
        for lean_file in lean_dir.rglob('*.lean'):
            for line in lean_file.read_text().splitlines():
                if line.startswith('theorem '):
                    name = line.split()[1].split('(')[0].split(':')[0].strip()
                    all_lean_names.add(name)

    details = []
    all_pass = True

    for func_name, theorem_names in mapping:
        func = getattr(formulas, func_name, None)
        if not func or not func.__doc__:
            details.append(Detail(func_name, False, "Function not found or missing docstring"))
            all_pass = False
            continue

        doc = func.__doc__
        missing_from_doc = [t for t in theorem_names if t not in doc]
        missing_from_lean = [t for t in theorem_names if t not in all_lean_names]

        if not missing_from_doc and not missing_from_lean:
            details.append(Detail(func_name, True, f"Refs: {', '.join(theorem_names)}"))
        elif missing_from_doc:
            details.append(Detail(func_name, False, f"Missing from docstring: {missing_from_doc}"))
            all_pass = False
        else:
            details.append(Detail(func_name, False, f"Not in Lean source or ARISTOTLE_THEOREMS: {missing_from_lean}"))
            all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1b: Placeholder theorems are not cited as verified (Invariant #9, R5)
# ═══════════════════════════════════════════════════════════════════════

# Verification-claim phrasing that, in a window around a placeholder reference,
# indicates the paper presents a `True := trivial` placeholder as a real result.
_VERIFY_CLAIM_RE = re.compile(
    r"formally\s+verif|formal\s+verification|machine[-\s]check|"
    r"end[-\s]to[-\s]end\s+(formal\s+)?verif|kernel[-\s]verif|kernel[-\s]check|"
    r"proven\s+in\s+Lean|verified\s+(in|by)\s+Lean|rigorously\s+verif|"
    r"zero\s+\\?texttt\{?sorry",
    re.IGNORECASE,
)
# Hedge phrasing that, near a placeholder reference, means the claim is honestly
# disclosed (statement-level / concrete-instance-only / deferred) — not an
# overclaim. ADR-004 W7 finding H2: these are CLAIM-SPECIFIC MULTI-WORD phrases,
# NOT bare ambiguous single words (a stray "stub"/"modulo"/"deferred" in
# unrelated prose must not suppress a real overclaim). Each alternative is a
# phrase a careful author writes ABOUT this specific claim.
_HEDGE_CLAIM_RE = re.compile(
    r"statement[-\s]level|at\s+the\s+statement\s+level|formalized\s+at\s+the\s+statement|"
    r"_TODO|\\_TODO|not\s+yet\s+(proven|formal|verif)|conjectur|"
    r"deferred\s+to|abstract\s+(braided[-\s]monoidal\s+)?functor|"
    r"concrete(ly)?\s+(verif|for|instance)|verified\s+concretely|"
    r"general[-\s]?\$?G\$?\s+(statement|case|level)|matched\s+at\s+the\s+(level|anyon)|"
    r"only\s+(the\s+)?\$?\\?mathbb\{?Z\}?|for\s+\$?\\?mathbb",
    re.IGNORECASE,
)


def _tex_name_pattern(token: str) -> "re.Pattern":
    """Regex for a Lean decl name as it can appear in LaTeX — underscores may be
    backslash-escaped (`\\_`) inside `\\texttt{}` / prose.

    Delegates to the shared helper (TODO-D2). This module and `prose_lean_refs`
    had independently rediscovered the same trap; the handling now lives in one
    place so a third consumer inherits it instead of re-deriving it.
    """
    return tex_escaped_name_pattern(token)


@register_check(
    "placeholder_not_cited",
    "Placeholder (True := trivial) theorems are not cited as verified in any paper (Invariant #9)")
def check_placeholder_not_cited() -> CheckResult:
    """Enforces the paper-claim clause of Pipeline Invariant #9: a placeholder
    theorem (registered in ``PLACEHOLDER_THEOREMS``) must NOT be presented as a
    formally-verified result in any paper. Matches both (a) the actual Lean decl
    name / tracking key and (b) an optional ``tex_signature`` (the published math
    notation a paper cites the claim by, e.g. ``Z(Vec_G) ≅ Rep(D(G))``) within a
    window of a verification-claim phrase, unless a hedge phrase is also present.
    Substrate Integrity Gates W1 (2026-06-13); enforces audit finding #3.
    """
    from src.core.constants import PLACEHOLDER_THEOREMS

    if not _H.PAPERS_DIR.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "papers_dir", True, "no papers/ directory — UNMEASURED, not clean")])

    WINDOW = 320  # verification-claim + hedge search window each side of a match.
    #               ADR-004 W7 finding H2 is addressed by tightening the HEDGE
    #               REGEX to claim-specific multi-word phrases (above), NOT by a
    #               narrower window (which false-flags legitimately-hedged-but-
    #               spread-out prose, e.g. paper9).

    tokens: List[tuple] = []  # (compiled_regex, registry_key, kind)
    for key, meta in PLACEHOLDER_THEOREMS.items():
        lean_name = meta.get("lean_name", key)
        for tok in {lean_name, key}:
            tokens.append((_tex_name_pattern(tok), key, "name"))
        sig = meta.get("tex_signature")
        if sig:
            tokens.append((re.compile(sig, re.IGNORECASE), key, "signature"))

    details: List[Detail] = []
    any_fail = False
    n_drafts = 0

    for tex in _H.all_paper_drafts():          # ALL drafts (bundles + legacy), 64 today
        paper_dir = tex.parent
        n_drafts += 1
        try:
            text = tex.read_text()
        except (OSError, UnicodeDecodeError):
            continue

        offenders: Dict[str, str] = {}
        for tok_re, key, kind in tokens:
            for m in tok_re.finditer(text):
                win = text[max(0, m.start() - WINDOW): min(len(text), m.end() + WINDOW)]
                if _VERIFY_CLAIM_RE.search(win) and not _HEDGE_CLAIM_RE.search(win):
                    offenders.setdefault(key, kind)

        if offenders:
            any_fail = True
            msg = "; ".join(f"{k} ({kind})" for k, kind in sorted(offenders.items()))
            details.append(Detail(
                paper_dir.name, False,
                f"presents placeholder(s) as formally verified without a hedge: {msg} "
                f"(Invariant #9 — placeholders MUST NOT be cited as a paper claim)"))

    if not any_fail:
        details.append(Detail(
            "all_papers", True,
            f"no placeholder cited as a verified result across {n_drafts} paper draft(s)"))
    return CheckResult(passed=not any_fail, details=details)


# Strong "this proves the scientific result" verbs (the theorem as SUBJECT).
# Deliberately EXCLUDES `proven`/`proved` — "the theorem is proven (zero sorry)"
# is a legitimate statement about the theorem EXISTING, not an overclaim that it
# establishes the physics.
_OVERCLAIM_VERB_RE = re.compile(
    r"\b(establish(es|ed)?|demonstrat(es|ed)?|guarante(es|ed)|confirm(s|ed))\b",
    re.IGNORECASE)
# Honest framings for a bookkeeping / definitional theorem near its name.
#
# ⚠️ FIVE OF NINE ALTERNATIVES COULD NOT MATCH ANYTHING (fixed 2026-08-04, audit
# QI-28). The pattern was `\b(record(s|ed)?|tabulat|aggregat|enumerat|bookkeep|
# tallies|classification\s+ledger|summari[sz])\b` — stems written for prefix
# matching, but closed with `\b`. A trailing word boundary after `tabulat`
# requires the next character to be a non-word one, so `tabulated`, `tabulates`,
# `aggregates`, `enumerates`, `bookkeeping` and `summarizes` all FAILED to match
# while the bare stems (which never occur in prose) were the only accepted forms.
# Measured: 6 of the 9 alternatives matched no inflected form at all.
#
# Direction of the defect: a hedge SUPPRESSES a flag, so a dead alternative means
# prose that should be exempt gets FLAGGED — a guard firing on correct data, which
# this project holds to be worse than no guard. Measured on the live corpus at the
# fix: 0 overclaim-verb windows, so 0 flags before and 0 after. The hole was
# LATENT, and this closes it rather than moving a verdict (same posture as QI-01).
#
# Found by mutation, not by reading: dropping the `_LEDGER_HEDGE_RE` conjunct
# failed no test, because the hedge test used "records" — which fails the
# OVERCLAIM conjunct first, so the hedge was never exercised.
_LEDGER_HEDGE_RE = re.compile(
    r"\b(record|tabulat|aggregat|enumerat|bookkeep|tall(y|ies)|"
    r"classification\s+ledger|summari[sz])", re.IGNORECASE)


@register_check(
    "disclosure_consistency",
    "No paper presents a disclosed definitional/vacuous_proxy theorem as 'establishing' a result (#9)")
def check_disclosure_consistency() -> CheckResult:
    """ADR-004 reconcile #9: a theorem disclosed in ``MODELING_ASSUMPTION_THEOREMS``
    as ``definitional`` / ``vacuous_proxy`` (NOT carrying the substantive proof
    load — bookkeeping / a self-disclosed marker) must NOT be presented in any
    paper as ESTABLISHING / DEMONSTRATING / GUARANTEEING a scientific result.
    Nothing previously checked that paper prose matched a theorem's disclosure
    tier: D5 prose-claimed the disclosed-bookkeeping aggregator
    ``r_d_independent_count_eight`` 'establishes the 8/8 closure', contradicting
    its own constants.py disclosure. Mirrors ``placeholder_not_cited`` (R5) for the
    modeling-assumption disclosure tier (paper-prose ↔ disclosure-category)."""
    from src.core.constants import MODELING_ASSUMPTION_THEOREMS as M
    if not _H.PAPERS_DIR.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "papers_dir", True, "no papers/ directory — UNMEASURED, not clean")])

    disclosed = []  # (regex, lean_name)
    for k, v in M.items():
        if v.get("category") in ("definitional", "vacuous_proxy"):
            ln = v.get("lean_name", k)
            disclosed.append((_tex_name_pattern(ln), ln))

    AFTER = 60  # the disclosed theorem is the SUBJECT; the claim verb follows it.
    details: List[Detail] = []
    any_fail = False
    n_drafts = 0
    for tex in _H.all_paper_drafts():          # ALL drafts (bundles + legacy)
        paper_dir = tex.parent
        n_drafts += 1
        try:
            text = tex.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        offenders: set = set()
        for rx, ln in disclosed:
            for m in rx.finditer(text):
                win = text[m.end(): min(len(text), m.end() + AFTER)]
                if _OVERCLAIM_VERB_RE.search(win) and not _LEDGER_HEDGE_RE.search(win):
                    offenders.add(ln)
        if offenders:
            any_fail = True
            details.append(Detail(
                paper_dir.name, False,
                f"presents disclosed definitional/vacuous_proxy theorem(s) as establishing a result: "
                f"{', '.join(sorted(offenders))} — reframe (the substantive proof load is in the "
                f"per-item theorems; these are bookkeeping/markers per MODELING_ASSUMPTION_THEOREMS)"))
    if not any_fail:
        details.append(Detail(
            "all_papers", True,
            f"no disclosed-definitional theorem prose-claimed to 'establish' a result "
            f"across {n_drafts} paper draft(s)"))
    return CheckResult(passed=not any_fail, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1c: Proxy-body audit — structurally-named theorems not trivially closed
#           (R2; mechanizes Stage-3a checklist item 5 "defining-the-conclusion")
# ═══════════════════════════════════════════════════════════════════════

# Theorem NAME claims a structural / quantitative result.
_STRUCTURAL_NAME_RE = re.compile(
    r"(_dim$|_dim_|_dims_|rank|finrank|Ext|classification|_no_go$|_nogo$|"
    r"sixteen_|_unanimous$|_equivalence$|_corresponds$|_correspondence$|_combined$|"
    r"_iso$|_well_defined$|_count$|_matches|_preserved$|_bijection$|_holds$)",
    re.IGNORECASE,  # ADR-004 W7 finding M3: added correspondence/matches/preserved/bijection/holds
)
# A body that is ESSENTIALLY a trivial closer (after whitespace normalization).
# Deliberately EXCLUDES decide / native_decide / norm_num / ring / simp etc. —
# the compiler-trust surface is ADR-002's P4 gate, and the decide/norm_num
# arithmetic-proxy class is Phase-5q.T's T5 detector.
_TRIVIAL_BODY_RES = [
    (re.compile(r"^(by\s+)?(exact\s+)?rfl$"), "rfl"),
    (re.compile(r"^(by\s+)?(exact\s+)?trivial$"), "trivial"),
    (re.compile(r"^by\s+(intro\s+[\w\s]+?)?cases\s+\w+\s*<;>\s*rfl$"), "cases <;> rfl"),
    (re.compile(r"^(by\s+exact\s+)?h[\w']*$"), "identity-return (hypothesis)"),
    (re.compile(r"^(by\s+exact\s+)?Equiv\.refl[\w\s.]*$"), "Equiv.refl"),
    # ADR-004 W7 adversarial finding C2 — UNAMBIGUOUSLY-trivial forms only.
    # (Deliberately NOT a bare `⟨…⟩` matcher: an anonymous constructor of REAL
    # proven lemmas — e.g. `full_correspondence := ⟨left_inverse, right_inverse,
    # …⟩` — is substantive, so only all-rfl/all-trivial constructors are flagged.)
    (re.compile(r"^(by\s+exact\s+)?Iff\.rfl$"), "Iff.rfl"),
    (re.compile(r"^(by\s+exact\s+)?⟨\s*(rfl|trivial)(\s*,\s*(rfl|trivial))*\s*⟩$"), "⟨rfl,…⟩"),
    (re.compile(r"^(by\s+exact\s+)?And\.intro\s+(rfl|trivial)\s+(rfl|trivial)$"), "And.intro rfl rfl"),
    (re.compile(r"^fun\s+\w+\s*=>\s*\w+\.\w+$"), "struct-field projection (fun _ => _.field)"),
    # ADR-004 reconcile #23 — a self-discharging existential witnessed ENTIRELY by
    # `Equiv.refl` / `rfl` / `trivial` (+ a `.bijective`/`.symm` projection of one):
    # `∃ φ, Bijective φ := ⟨Equiv.refl _, (Equiv.refl _).bijective⟩`. This is a
    # TARGETED anon-ctor matcher (every component is itself trivial), NOT a bare
    # `⟨…⟩` matcher — a constructor of REAL lemmas (`⟨left_inv, right_inv⟩`) has a
    # component that is not Equiv.refl/rfl/trivial, so it does not match (preserves
    # the deliberate non-flagging of substantive constructors at finding C2).
    (re.compile(
        r"^(by\s+exact\s+)?⟨\s*"
        r"(\(?\s*Equiv\.refl[\s\w]*+\)?(\.\w+)?|rfl|trivial)"
        r"(\s*,\s*(\(?\s*Equiv\.refl[\s\w]*+\)?(\.\w+)?|rfl|trivial))*\s*⟩$"),
     "⟨Equiv.refl,…⟩ (self-discharging existential)"),
]
# Substantive-tactic markers: if the body contains any of these it is NOT a
# trivial closer (belt-and-suspenders with the anchored patterns above).
_NONTRIVIAL_MARKER_RE = re.compile(
    r"\b(decide|native_decide|norm_num|simp|ring|omega|linarith|nlinarith|"
    r"aesop|positivity|induction|refine|constructor|calc|apply)\b")


@register_check(
    "proxy_body_audit",
    "Structurally-named theorems are not proved by a trivial 'defining-the-conclusion' body (R2)")
def check_proxy_body_audit() -> CheckResult:
    """Flags any theorem whose NAME claims a structural / quantitative result
    but whose PROOF is a trivial closer (rfl / trivial / cases<;>rfl /
    identity-return / Equiv.refl) — the defining-the-conclusion anti-pattern
    where the real content lives in a definition / struct field / registry, not
    the proof. A flagged decl is COMPLIANT iff registered in
    ``MODELING_ASSUMPTION_THEOREMS`` (with a reason + disclosure pointer) or
    already a ``PLACEHOLDER_THEOREMS`` stub. Substrate Integrity Gates W2."""
    from build_graph import _scan_lean_theorem_bodies
    from src.core.constants import PLACEHOLDER_LEAN_NAMES
    try:
        from src.core.constants import MODELING_ASSUMPTION_THEOREMS
    except ImportError:
        MODELING_ASSUMPTION_THEOREMS = {}
    try:
        from src.core.constants import VACUOUS_STATEMENT_BASELINE as BASELINE
        from src.core.constants import SIMP_PROJECTION_CEILING
        from src.core.constants import SIMP_PROJECTION_ALLOWLIST
    except ImportError:
        BASELINE = frozenset()

    lean_dir = _H.LEAN_DIR   # audit QI-11: one owner
    if not lean_dir.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "lean_dir", True, "no lean dir — UNMEASURED, not clean")])

    exempt = set(PLACEHOLDER_LEAN_NAMES.keys())
    # A whitelist entry is a valid disclosure ONLY if it carries `reason` AND
    # `discloses` — a bare entry is not a free pass.
    whitelisted: set = set()
    wl_incomplete: List[str] = []
    for k, v in MODELING_ASSUMPTION_THEOREMS.items():
        if v.get("reason") and v.get("discloses"):
            whitelisted.add(v.get("lean_name", k))
        else:
            wl_incomplete.append(k)

    new_flagged: List[tuple] = []
    grandfathered: List[str] = []
    simp_projections: List[str] = []
    scanned = 0
    for lean_file in sorted(lean_dir.rglob("*.lean")):
        try:
            source = lean_file.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        scanned += 1
        for thm_name, line_no, body, is_simp in _scan_lean_theorem_bodies(source):
            if thm_name in exempt or thm_name in whitelisted:
                continue
            if not _STRUCTURAL_NAME_RE.search(thm_name):
                continue
            # ── `@[simp]` PROJECTION LEMMAS ARE A DIFFERENT SPECIES ────────────
            # This check hunts a theorem NAMED like a claim that is `rfl`-provable
            # because its definition was rigged. A `@[simp]` lemma is not making a
            # claim — it is exposing a field to the simp set, and `rfl` is its ONLY
            # correct proof:
            #     instance : Add _ := ⟨fun x y => ⟨x.rank + y.rank⟩⟩
            #     @[simp] theorem add_rank … : (x + y).rank = x.rank + y.rank := rfl
            # Calling that "defining the conclusion" is a category error.
            #
            # ⚠️ THIS IS A CATEGORY CORRECTION, NOT A THRESHOLD MOVE. Until the
            # scanner was taught to tolerate attributes (it was anchored at column
            # 0 and missed 8.1% of the corpus), it had NEVER seen a `@[simp]`
            # declaration, so `VACUOUS_STATEMENT_BASELINE` was calibrated on a
            # population that structurally excluded them. Grandfathering the seven
            # it newly caught into that baseline would have been the real
            # loosening — using a just-repaired instrument to justify widening the
            # exemption it exists to shrink.
            #
            # It is RATCHETED, so the exemption cannot grow silently: an eighth
            # `@[simp]` structural `rfl` lemma fails this check loudly.
            if is_simp:
                norm_s = " ".join(body.split())
                if any(rx.match(norm_s) for rx, _ in _TRIVIAL_BODY_RES):
                    qual = f"{lean_file.stem}.{thm_name}"
                    simp_projections.append(qual)
                    # ⚠️ IDENTITY, not just count. An unknown `@[simp]` structural
                    # `rfl` lemma is flagged even if the TOTAL is unchanged — a
                    # count-only ratchet is defeated by swapping one out for a
                    # rigged one, which is exactly how a reviewer broke the first
                    # version of this leg.
                    if qual not in SIMP_PROJECTION_ALLOWLIST:
                        new_flagged.append((qual, line_no, "@[simp] rfl (not allow-listed)"))
                continue
            norm = " ".join(body.split())
            if _NONTRIVIAL_MARKER_RE.search(norm):
                continue
            label = next((lbl for rx, lbl in _TRIVIAL_BODY_RES if rx.match(norm)), None)
            if label is None:
                continue
            # Grandfather the pre-existing class un-hid by the scanner / anon-ctor
            # fixes (visible tracked debt). A NEW trivially-bodied structural
            # theorem (not in the baseline) is a HARD-FAIL — closes the generator.
            if thm_name in BASELINE:
                grandfathered.append(thm_name)
            else:
                new_flagged.append((f"{lean_file.stem}.{thm_name}", line_no, label))

    details: List[Detail] = []
    # Advisory: disclosed vacuous_proxy theorems are tracked debt (PASS, but visible).
    # SEAM GUARD (closure review 4). The directory-exists guard above is not enough:
    # an existing but EMPTY tree scans zero files and reports "no NEW trivially-closed
    # structural theorems" with passed=True, measured=True — a clean bill issued over a
    # population never read, counted toward the CI_MIN_CHECKS_RUN floor. Identical seam
    # to the one closed in `elaboration_knob_watchlist`; `test_cannot_measure_baseline`
    # covered only the ABSENT-dir path, not existing-but-empty.
    if scanned == 0:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "lean_src", False,
            f"SKIPPED — no readable .lean files under {lean_dir}; the proxy-body "
            f"audit is UNVERIFIED, not clean")])

    n_vac = sum(1 for v in MODELING_ASSUMPTION_THEOREMS.values()
                if v.get("category") == "vacuous_proxy")
    # `@[simp]` projection lemmas: exempt by CATEGORY, ratcheted so the exemption
    # cannot grow silently. Over ceiling is a HARD FAIL — a new one must be shown
    # to be a projection and not a claim wearing `@[simp]`.
    _simp_over = len(simp_projections) > SIMP_PROJECTION_CEILING
    details.append(Detail(
        "simp_projections", not _simp_over,
        f"{len(simp_projections)} `@[simp]` projection lemma(s) with a structural "
        f"name and a trivial body (ceiling {SIMP_PROJECTION_CEILING}) — rewrite "
        f"plumbing, where `rfl` is the only correct proof, NOT a "
        f"defining-the-conclusion claim"
        + ("" if not _simp_over else
           f"; OVER CEILING: {', '.join(sorted(simp_projections))}"),
        warning=bool(simp_projections) and not _simp_over))

    if n_vac:
        details.append(Detail(
            "tracked_vacuous_proxies", True,
            f"{n_vac} structurally-named theorem(s) disclosed as `vacuous_proxy` tracked debt "
            f"(see MODELING_ASSUMPTION_THEOREMS `discharge` pointers)", warning=True))
    if grandfathered:
        details.append(Detail(
            "baseline", True,
            f"{len(grandfathered)} grandfathered trivially-bodied theorem(s) in "
            f"VACUOUS_STATEMENT_BASELINE (visible tracked debt → Vacuous Statement Sweep)",
            warning=True))

    for k in wl_incomplete:
        details.append(Detail(
            k, False,
            "MODELING_ASSUMPTION_THEOREMS entry missing `reason`/`discloses` — not a valid disclosure"))
    for full, line_no, label in new_flagged:
        details.append(Detail(
            full, False,
            f"NEW structurally-named theorem closed by `{label}` at line {line_no} (not in baseline) — "
            f"register in MODELING_ASSUMPTION_THEOREMS (with reason+discloses) or strengthen"))

    # ⚠️ `_simp_over` FOLDS INTO THE VERDICT. Without it the check rendered a red
    # `✗ simp_projections` detail under a green `✓ PASS` header — a failing detail
    # on a passing check, which is the exact shape flagged elsewhere in this suite
    # (`elaboration_knob_watchlist` printing 22 ✗ lines under ✓ PASS). A ratchet
    # whose breach does not reach the verdict is not a ratchet.
    if new_flagged or wl_incomplete or _simp_over:
        return CheckResult(passed=False, details=details)
    details.append(Detail(
        "all_theorems", True,
        f"no NEW trivially-closed structural theorems ({len(grandfathered)} baselined, "
        f"{n_vac} disclosed vacuous_proxy, {len(simp_projections)} `@[simp]` projections)"))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1d: Tracked-hypothesis ledger coverage (R3, Invariant #16)
# ═══════════════════════════════════════════════════════════════════════

def _is_prop_codomain(type_str: str) -> bool:
    """True if a declaration's type has codomain `Prop` (a Prop-valued def /
    structure = a candidate tracked-hypothesis), excluding `Subgroup`/type
    defs that happen to be H_*-named."""
    if not type_str:
        return False
    return type_str.replace("\n", " ").rstrip().split("→")[-1].strip() == "Prop"


_TRACKED_PROP_NAME_RE = re.compile(r"^(H_[A-Za-z0-9_]+|[A-Za-z0-9_]+Conjecture|[A-Za-z0-9_]+Hypothesis)$")


@register_check(
    "tracked_hypothesis_ledger",
    "Every consumed tracked-hypothesis Prop is registered in HYPOTHESIS_REGISTRY (Invariant #16, R3)")
def check_tracked_hypothesis_ledger() -> CheckResult:
    """Single-source-of-truth enforcement for tracked hypotheses: every
    Prop-valued tracked hypothesis (`H_*` / `*Conjecture` / `*Hypothesis`) that
    is CONSUMED as a binder `(h : P …)` by some theorem must be registered in
    ``HYPOTHESIS_REGISTRY`` (the machine-readable source of truth) — or listed
    in ``TRACKED_HYPOTHESIS_NON_LOAD_BEARING`` with a reason. Substrate
    Integrity Gates W3. **Advisory until the registry backlog is cleared, then
    escalates to hard-fail (Invariant #16).**"""
    from src.core import constants as _c
    HYPOTHESIS_REGISTRY = getattr(_c, "HYPOTHESIS_REGISTRY", {})
    NON_LB = getattr(_c, "TRACKED_HYPOTHESIS_NON_LOAD_BEARING", {})

    # ⚠️ These were `TODO(semantic-review, ADR-009 Phase 3)` until 2026-08-04
    # (audit finding QI-15). Phase 3 is COMPLETE and its §Deferred item 4
    # explicitly DECLINED converting these sites wholesale: 5 are
    # optional-toolchain-absent, 3 advisory by design, 8 are this `lean_deps`
    # divergence kept VISIBLE on purpose, 2 are the annotated H1-silent sites.
    # A TODO pointing at a finished phase reads as unfinished work; the
    # population is frozen instead by `tests/test_cannot_measure_baseline.py`,
    # which fails both on a NEW silent PASS and on a converted site left stale
    # in the baseline.
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> PASS here, but -> FAIL in
    # prose_theorem_reference_coverage / theorem_name_embedded_citations. Five checks
    # pass on a missing lean_deps.json and two fail. Unify deliberately, not by refactor.
    if not _H.lean_deps_present():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "lean_deps", True, "no lean_deps.json — UNMEASURED, not clean")])
    deps = _H.load_lean_deps()

    # 1) Prop-valued tracked-hypothesis defs/structures (codomain Prop, tracked name)
    tracked: dict = {}  # short name -> module
    for d in deps:
        short = d.get("name", "").split(".")[-1]
        if _TRACKED_PROP_NAME_RE.match(short) and _is_prop_codomain(d.get("type", "")):
            tracked[short] = d.get("module", "")

    # 2) which are CONSUMED as a binder `( ident : Name` anywhere in the source
    lean_dir = _H.LEAN_DIR   # audit QI-11: one owner
    src = "\n".join(
        f.read_text(errors="ignore") for f in lean_dir.rglob("*.lean"))
    consumed = set()
    for name in tracked:
        if re.search(r"\(\s*_?[A-Za-z0-9_']*\s*:\s*" + re.escape(name) + r"\b", src):
            consumed.add(name)

    # 3) coverage: registry key OR a dependent_theorems back-reference OR non-LB list
    covered = set(HYPOTHESIS_REGISTRY.keys())
    gap = sorted(n for n in consumed if n not in covered and n not in NON_LB)

    details: List[Detail] = []
    details.append(Detail(
        "surface", not gap,
        f"{len(tracked)} tracked Prop-defs; {len(consumed)} consumed; "
        f"{len(consumed) - len(gap)} covered (registry {len(HYPOTHESIS_REGISTRY)} + non-LB {len(NON_LB)})"))
    for n in gap:
        details.append(Detail(
            n, False,
            f"consumed tracked Prop (def in {tracked[n]}) absent from HYPOTHESIS_REGISTRY "
            f"and TRACKED_HYPOTHESIS_NON_LOAD_BEARING — register or downgrade (Invariant #16)"))
    return CheckResult(passed=not gap, details=details)


@register_check(
    "tracked_hypotheses_fresh",
    "docs/PERMANENT_TRACKED_HYPOTHESES.md is up-to-date vs HYPOTHESIS_REGISTRY (auto-regen)")
def check_tracked_hypotheses_fresh() -> CheckResult:
    """The tracked-hypotheses doc is an auto-generated VIEW of HYPOTHESIS_REGISTRY
    (Substrate Integrity Gates W3). Same auto-regenerate-stale pattern as
    ``counts_fresh``/``tables_fresh``: if the on-disk markdown drifts from the
    registry render, regenerate it (so it can never silently diverge — the prior
    two-disjoint-ledgers failure)."""
    # ⚠️ FAILS CLOSED (changed 2026-08-05, PR-review R4-I4). This was
    # `except Exception: return CheckResult(passed=True, ...)`, so ANY breakage while
    # importing the renderer converted a drift gate into a silent green.
    #
    # `render_tracked_hypotheses` is a first-party module in `scripts/`, not an
    # optional dependency — the five deliberate `passed=True` skips ADR-009 §Deferred
    # item 4 preserves are all optional TOOLCHAIN absences (pdfminer, lake, nbclient),
    # which is a different thing. Its absence is a defect, not an environment.
    #
    # VALIDATED, not reasoned: `constants.py:1375` asserts the Aristotle count at
    # IMPORT time, so adding a registry entry without updating the count raises
    # `AssertionError` — not `ImportError` — while this module is being imported.
    # Measured before the fix: that returned `passed=True` with the detail
    # "renderer unavailable: Expected 322 Aristotle-proved theorems, got 323".
    # A registry edit that trips a real invariant greened the hypothesis-drift gate.
    try:
        import render_tracked_hypotheses as _r
    except Exception as e:
        return CheckResult(passed=False, details=[Detail(
            "import", False,
            f"render_tracked_hypotheses could not be imported ({type(e).__name__}: {e}) "
            f"— the tracked-hypotheses doc could not be compared against "
            f"HYPOTHESIS_REGISTRY, so this gate is UNVERIFIED, not passing. Note that "
            f"an import-time assert in src/core/constants.py surfaces here as an "
            f"AssertionError, not an ImportError.")])
    new = _r.render()
    doc = _r.DOC_PATH
    old = doc.read_text() if doc.exists() else ""
    if old == new:
        return CheckResult(passed=True, details=[Detail(
            "tracked_hypotheses", True, f"{new.count('### ')} entries; doc matches HYPOTHESIS_REGISTRY")])
    # HARD-FAIL on drift (do NOT silently rewrite a git-tracked file — ADR-004 W7
    # adversarial finding M1; cf. memory feedback_dont_discard_autogen_artifacts).
    # The maintainer regenerates + commits the result in the same wave.
    return CheckResult(passed=False, details=[Detail(
        "tracked_hypotheses", False,
        "docs/PERMANENT_TRACKED_HYPOTHESES.md is STALE vs HYPOTHESIS_REGISTRY — "
        "run `python scripts/render_tracked_hypotheses.py` and commit the regenerated doc")])


@register_check(
    "lean_zero_sorry",
    "Pipeline Invariant #4 — no declaration's axiom closure contains `sorryAx`")
def check_lean_zero_sorry() -> CheckResult:
    """Pipeline Invariant #4 — *"every Lean theorem has a proof (zero sorry)"* — asserted
    UNCONDITIONALLY and cheaply.

    ⚠️ **Read this before quoting the gap this check closes.** A first draft of this
    docstring claimed the invariant "had no `validate.py` gate" and that "nothing else
    covered it". **That was wrong**, and the error is instructive: it came from grepping
    the check modules for `sorry` (which finds nothing, because no check mentions the
    word) instead of asking which check would *detect* one.

    **`axiom_closure_allowlist` already detects it.** A `sorry` elaborates to `sorryAx`,
    which enters the transitive axiom closure of every dependent declaration; that check
    runs the `AxiomAudit` Lean executable over all `SKEFTHawking.*` declarations and flags
    any axiom outside `{propext, Classical.choice, Quot.sound} ∪ AXIOM_METADATA`. `sorryAx`
    is in neither set, so it is flagged.

    What this check adds is therefore **posture and cost**, not detection:

    * `axiom_closure_allowlist` is **WARN-first by design** — `passed=not strict`, so on a
      default run a `sorry` is an advisory warning and the suite stays green. It hard-fails
      only under `--strict` (the paper-submission gate). This check hard-fails always.
    * That check is the **most expensive in the suite at 145 s** and is skipped whenever
      `lake` is absent. This one reads `counts.json` and costs ~0 s, so the invariant is
      asserted on every run including environments with no Lean toolchain.

    The other two paths, verified rather than assumed:

    * `lake build` **exits 0 on a `sorry`** — measured, not relayed: a probe file
      containing `theorem t : 1 + 1 = 3 := by sorry` compiles with
      ``warning: declaration uses `sorry` `` and **exit code 0**. So `check_lean_build`,
      which tests only `returncode == 0`, cannot catch one.
    * `pre-commit-sync.sh`'s guard is sound in substance (it greps lake's own
      ``declaration uses `sorry` `` output, not the source), but it is **warn-only off
      `main`** by design, `.lean`-diff-scoped, and fail-open when `lake` is absent.

    So the honest statement is: the invariant was **detected but not enforced** on a
    default run. This check makes it enforced.

    **Source is Lean's own axiom closure, not a source scan.** `update_counts` counts
    declarations whose `axiom_deps_core` contains a `sorry` marker — a `sorry` elaborates
    to `sorryAx`, which propagates into the axiom closure of everything depending on it.
    A `grep` for `sorry` over `.lean` files is the wrong instrument and is known to be:
    tried on this project it returned **11 docstring false positives** ("Zero sorry. Zero
    axioms.") while missing nothing real — the reason the pre-commit guard reads lake's
    output instead.
    """
    details: List[Detail] = []
    counts_path = _H.COUNTS_JSON_PATH
    if not counts_path.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "counts_present", True,
            f"{counts_path} absent — run update_counts.py; nothing to measure",
            warning=True)])
    try:
        lean = json.loads(counts_path.read_text())["lean"]
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        return CheckResult(passed=True, measured=False, details=[Detail(
            "counts_parse", True, f"counts.json unreadable ({exc})", warning=True)])

    if "sorry_declarations" not in lean:
        # The field going missing must not read as zero — that is the same
        # absence-as-success shape this check exists to close.
        return CheckResult(passed=False, details=[Detail(
            "field_present", False,
            "counts.json has no `lean.sorry_declarations` field, so the invariant cannot "
            "be evaluated — regenerate with update_counts.py")])

    n_decl = int(lean.get("sorry_declarations") or 0)
    n_thm = int(lean.get("sorry_theorems") or 0)
    details.append(Detail(
        "zero_sorry", n_decl == 0,
        f"0 of {lean.get('total_declarations', '?')} declarations carry `sorryAx` in "
        f"their axiom closure"
        if n_decl == 0 else
        f"{n_decl} declaration(s) carry `sorryAx` in their axiom closure "
        f"({n_thm} of them theorems) — Pipeline Invariant #4 is violated"))
    return CheckResult(passed=n_decl == 0, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: one theorem census, enforced — the anti-whack-a-mole guard
# ═══════════════════════════════════════════════════════════════════════
#
# WHY THIS EXISTS. "Is this declaration compiler-generated?" was answered
# independently in SIX places, each found by a different reviewer, one at a time:
#   1. update_counts.py `count_lean`          (found by review 1)
#   2. update_counts.py per-module I1 macros  (found by review 2, F1)
#   3. render_bundle_counts.py                (found by review 2, F1)
#   4. paper_tables/sources.py                (found by review 3)
#   5. atlas_view.py                          (found by review 4)
#   6. bundle_closure.py apex classifier      (found by the guard itself)
# Five of them counted generated declarations as authored, so the PUBLISHED instruments
# agreed on an inflated figure on main. Agreement was never the property that needed
# checking. The sixth, `bundle_closure`'s apex classifier, publishes no count — it is on
# this list because it compares the same field, and it carries a `census-exempt` marker.
#
# Fixing site N and waiting for a reviewer to find site N+1 is not a process. This
# check makes the census self-enforcing in two independent ways:
#   LEG 2 (ownership) — every `kind == "theorem"` filter must carry an autogen guard
#                       or sit on a stated allow-list. THIS is the leg that would have
#                       caught the original defect: it fails on the CODE that produces
#                       a wrong number, before any number is published.
#   LEG 1 (agreement) — every PUBLISHED census must equal the one derivation. This
#                       catches a PARTIAL fix: correcting the six sites one at a time
#                       left `ATLAS_HEATMAP.md` at 26,398 against `counts.tex`'s 22,669
#                       across five commits.

# Sites that compare `kind == "theorem"` WITHOUT an autogen guard, deliberately.
# Each entry needs a reason. Adding one is a scope decision, not a formality.
#
# ⚠️ EXEMPTION IS SITE-LOCAL, enforced by a marker on the line itself:
#     ... d["kind"] == "theorem" ...  # census-exempt: <key>
# Keying on file, or on file:enclosing-def, both failed: a second bare census added
# beside an exempted one — inside the SAME 156-line `count_lean`, the function that
# carried two of the six historical defects — inherited the exemption and passed.
# A marker cannot be inherited by a neighbouring line.
THEOREM_FILTER_ALLOWLIST: Dict[str, str] = {
    "detector-self":
        "the comparison inside `_is_theorem` that FINDS census sites; it is the "
        "detector, not a census.",
    "sorry-theorems":
        "counts declarations with a `sorry` axiom dep; an autogen declaration cannot "
        "carry one, so the filter is a no-op here (sorry count is 0 and ratcheted).",
    "node-id-dispatch":
        "dispatches a node-ID prefix by kind; it is not a census and publishes no count.",
    "apex-kind":
        "classifies ONE declared apex (is the name a theorem?) rather than counting a "
        "population; the module already threads `autogen` into `compute_closure`, and a "
        "bundle never declares a compiler-generated name as an apex.",
    "reuse-scan":
        "a reuse/citation scan over proof bodies, not a published census (its docstring "
        "overclaims an exclusion it does not implement — tracked, not load-bearing).",
}

# Down-only ratchet on the SCANNED POPULATION, not only on violations, because a
# detector that stops SEEING a site cannot report it and the violation count never
# moves. Both earlier detectors shrank this silently — a regex that matched nothing
# across 131 files, then token adjacency that missed a swapped operand. `sites_found`
# is reported so a narrowing is visible. Lower only alongside a stated reason, exactly
# like every other ratchet here.
# RE-MEASURED 2026-08-11 against the AST detector: 12 sites, zero headroom. The two
# earlier values (13 regex, 11 tokens) were each the population of a DIFFERENT detector,
# and neither was re-derived when the technique changed — which left one slack site, so a
# real census could vanish silently. Re-measure this whenever the detector changes;
# `test_the_floor_equals_the_live_population` now fails if you do not.
THEOREM_FILTER_SITES_FLOOR = 12

#: Published censuses leg 1 must locate: counts.json, counts.tex, atlas_view.json,
#: ATLAS_HEATMAP.md. counts.tex was OUTSIDE this leg until 2026-08-11 — the artifact the
#: leg's own cited incident names, `\input` by ten-plus drafts and printed by I1 as
#: "machine-checked theorems", and reachable by no other content guard (`counts_fresh`
#: keys on its mtime and is CI_SKIP). Setting it to 99999 left this check green.
PUBLISHED_CENSUS_FLOOR = 4

_EXEMPT_RE = re.compile(r"#\s*census-exempt:\s*([a-z0-9-]+)")


def _census_sites(path) -> tuple:
    """Census comparison sites, and `# census-exempt:` markers. AST for code, tokens for
    comments — each tool used for what it can actually decide.

    DETECTED SHAPES, stated rather than implied:
      * `x == "theorem"` and `"theorem" == x`, plus the `!=` forms — EITHER operand order;
      * `x in ("theorem", ...)` and `not in`;
      * `case "theorem":` in a `match`.

    NOT DETECTED, a real limit rather than an oversight: a literal reached through a
    variable (`T = "theorem"; d["kind"] == T`) or built at runtime. Deciding that needs
    dataflow. The `agreement` leg is the backstop for whatever ownership cannot see.

    Two earlier implementations were narrower and BOTH shipped believing otherwise. A line
    regex missed the dominant `d.get('kind') == 'theorem'` form outright. Token adjacency
    then required the literal immediately right of the operator, so swapping the operands
    hid a site while DELETING its autogen guard — demonstrated green against a real census
    in `atlas_view.py`. Hence AST: operand order is not a property the node cares about.
    """
    tree = ast.parse(path.read_text(errors="replace"))

    marks: dict = {}
    with open(path, "rb") as fh:
        for tok in tokenize.tokenize(fh.readline):
            if tok.type == tokenize.COMMENT:
                m = _EXEMPT_RE.search(tok.string)
                if m:
                    marks[tok.start[0]] = m.group(1)

    def _is_theorem(node) -> bool:
        return isinstance(node, ast.Constant) and node.value == "theorem"  # census-exempt: detector-self

    def _guarded(stmt) -> bool:
        """Whether this statement carries an autogen reference.

        A NAME-SHAPED HEURISTIC, and its limits are real in both directions: a variable
        merely named `autogen_unused` forges a guard, and a guard applied in a PRECEDING
        statement (`if autogen.get(n): continue`) or through a differently-named helper is
        not seen. Fail-open on the first, fail-closed on the second. Stated because
        claiming completeness is what broke the two previous detectors.
        """
        for n in ast.walk(stmt):
            if isinstance(n, ast.Name) and "autogen" in n.id.lower():
                return True
            if isinstance(n, ast.Attribute) and "autogen" in n.attr.lower():
                return True
        return False

    seen: set = set()
    sites: set = set()
    for stmt in ast.walk(tree):
        if not isinstance(stmt, ast.stmt):
            continue
        guarded = _guarded(stmt)
        for n in ast.walk(stmt):
            hit = None
            if isinstance(n, ast.Compare):
                operands = [n.left] + list(n.comparators)
                if any(_is_theorem(o) for o in operands) and any(
                        isinstance(op, (ast.Eq, ast.NotEq)) for op in n.ops):
                    hit = n
                elif any(isinstance(op, (ast.In, ast.NotIn)) for op in n.ops) and any(
                        isinstance(c, (ast.Tuple, ast.List, ast.Set)) and len(c.elts) == 1
                        and _is_theorem(c.elts[0]) for c in n.comparators):
                    # SINGLE-element only. `kind in ("theorem", "axiom", ...)` is node-kind
                    # DISPATCH, not a census — you cannot count theorems by matching a set
                    # of several kinds — and all six live instances are exactly that. A
                    # one-element container IS census-shaped, so it stays detected.
                    hit = n
            elif isinstance(n, ast.MatchValue) and _is_theorem(n.value):
                hit = n
            if hit is not None:
                key = (hit.lineno, hit.col_offset)
                seen.add(key)
                if not guarded:
                    sites.add(key)
    return seen, sites, marks


@register_check(
    "theorem_census_agrees",
    "Every published theorem census equals the one derivation, and every "
    "`kind == \"theorem\"` filter goes through the single owner",
)
def check_theorem_census_agrees() -> CheckResult:
    """Two legs: published counts must AGREE; source filters must be OWNED."""
    details: List[Detail] = []

    # ---- LEG 1: every published census equals the canonical derivation ----------
    try:
        deps = _H.load_lean_deps()
    except Exception as exc:  # pragma: no cover - absent input
        return CheckResult(passed=False, measured=False, details=[
            Detail("population", False, f"SKIPPED — lean_deps unreadable ({exc}); "
                                        "the census is UNVERIFIED, not agreed")])
    if not deps:
        return CheckResult(passed=False, measured=False, details=[
            Detail("population", False,
                   "SKIPPED — lean_deps.json holds no declarations; UNVERIFIED")])

    autogen = _H.autogen_index(deps)
    canonical = sum(1 for d in deps
                    if d.get("kind") == "theorem" and not autogen.get(d.get("name", "")))
    details.append(Detail("canonical", True,
                          f"{canonical} author-written theorem(s) — the one derivation, "
                          f"from validate_helpers.autogen_index"))

    published: Dict[str, int] = {}
    counts_path = _H.COUNTS_JSON_PATH
    if counts_path.exists():
        try:
            published["docs/counts.json:lean.theorems_total"] = int(
                json.loads(counts_path.read_text())["lean"]["theorems_total"])
        except Exception:
            pass
    atlas_path = _H.PROJECT_ROOT / "lean" / "atlas_view.json"
    if atlas_path.exists():
        try:
            _a = json.loads(atlas_path.read_text())
            published["lean/atlas_view.json:nodes"] = len(_a.get("nodes", []))
        except Exception:
            pass
    tex_path = _H.COUNTS_TEX_PATH
    if tex_path.exists():
        # Strip LaTeX comments and take EVERY binding: a commented-out decoy with the right
        # value, or a later \renewcommand carrying a wrong one, both passed a first-match
        # search while the compiled document used something else.
        body = re.sub(r"(?<!\\)%.*", "", tex_path.read_text())
        vals = [int(v) for v in re.findall(r"\\totaltheorems\}\{([0-9]+)\}", body)]
        if len(set(vals)) > 1:
            details.append(Detail(
                "counts_tex", False,
                f"docs/counts.tex binds \\totaltheorems to {sorted(set(vals))} — the "
                f"compiled value is whichever comes last; make it single-valued"))
            return CheckResult(passed=False, details=details)
        if vals:
            published["docs/counts.tex:\\totaltheorems"] = vals[-1]

    heat_path = _H.DOCS_DIR / "ATLAS_HEATMAP.md"
    if heat_path.exists():
        m = re.search(r"([0-9][0-9,]*)\s+theorem nodes", heat_path.read_text())
        if m:
            published["docs/ATLAS_HEATMAP.md:theorem nodes"] = int(m.group(1).replace(",", ""))

    # Floor, not emptiness: `if not published` fires only when ALL THREE consumers
    # vanish, so renaming one artifact's phrasing dropped it from the comparison
    # silently and the leg passed over a document publishing the wrong number.
    if len(published) < PUBLISHED_CENSUS_FLOOR:
        details.append(Detail(
            "agreement", False,
            f"only {len(published)} of {PUBLISHED_CENSUS_FLOOR} published census(es) "
            f"located ({sorted(published) or 'none'}) — one is no longer being read; "
            f"UNVERIFIED, not agreed"))
        return CheckResult(passed=False, measured=False, details=details)

    disagreeing = {k: v for k, v in published.items() if v != canonical}
    details.append(Detail(
        "agreement", not disagreeing,
        f"{len(published)} published census(es) checked against {canonical}"
        + ("" if not disagreeing else
           " — DISAGREE: " + ", ".join(f"{k}={v}" for k, v in sorted(disagreeing.items())))))
    for k, v in sorted(disagreeing.items()):
        details.append(Detail(k, False,
                              f"publishes {v}, canonical is {canonical} "
                              f"(delta {v - canonical}); regenerate it through "
                              f"validate_helpers.autogen_index"))

    # ---- LEG 2: every kind == "theorem" filter is owned or allow-listed ---------
    unowned: List[str] = []
    used_sites: List[str] = []          # one entry PER SITE, not per key
    key_sites: Dict[str, List[str]] = {}   # key -> the sites claiming it
    used_keys: set = set()
    sites_found = 0
    scanned_files = 0
    for py in sorted(_H.PROJECT_ROOT.glob("scripts/**/*.py")):
        if "/.venv/" in str(py) or "__pycache__" in str(py):
            continue
        scanned_files += 1
        rel = py.relative_to(_H.PROJECT_ROOT).as_posix()
        try:
            seen, sites, marks = _census_sites(py)
        except (SyntaxError, UnicodeDecodeError, tokenize.TokenError):
            unowned.append(f"{rel}: UNPARSEABLE — cannot audit")
            continue
        sites_found += len(seen)
        for lineno, col in sorted(sites):
            key = marks.get(lineno)
            if key and key in THEOREM_FILTER_ALLOWLIST:
                used_sites.append(f"{rel}:{lineno}:{col}")
                key_sites.setdefault(key, []).append(f"{rel}:{lineno}:{col}")
                used_keys.add(key)
                continue
            unowned.append(f"{rel}:{lineno}:{col}")

    if sites_found < THEOREM_FILTER_SITES_FLOOR:
        # A scan that matches nothing is a broken pattern, not a clean codebase:
        # this project HAS `kind == "theorem"` filters by construction.
        details.append(Detail("ownership", False,
                              f"{scanned_files} script(s) scanned, only {sites_found} "
                              f"`kind == \"theorem\"` site(s) matched (floor "
                              f"{THEOREM_FILTER_SITES_FLOOR}) — the pattern NARROWED; the "
                              f"leg would pass over sites it can no longer see"))
        return CheckResult(passed=False, measured=False, details=details)

    # ONE KEY, ONE SITE. A key is a per-site exemption with a stated reason, so a second
    # site claiming the same key is a NEW unreviewed exemption wearing an approved name —
    # and the site count alone does not reveal it.
    for k, ss in sorted(key_sites.items()):
        if len(ss) > 1:
            unowned.append(f"key '{k}' claimed by {len(ss)} sites: {', '.join(sorted(ss))}")

    # F7: an entry nobody uses is a stale exemption widening the rule invisibly.
    unused = sorted(set(THEOREM_FILTER_ALLOWLIST) - used_keys)
    if unused:
        unowned.append(f"STALE allow-list entr(ies) matching no site: {', '.join(unused)}")

    details.append(Detail(
        "ownership", not unowned,
        f"{scanned_files} script(s) scanned, {sites_found} `kind == \"theorem\"` site(s); "
        + (f"{len(used_sites)} allow-listed site(s) under {len(used_keys)} key(s)"
           if not unowned else
           f"UNOWNED `kind == \"theorem\"` filter(s): {', '.join(unowned)} — route through "
           f"validate_helpers.autogen_index, or add to THEOREM_FILTER_ALLOWLIST with a reason")))

    return CheckResult(passed=not disagreeing and not unowned, details=details)
