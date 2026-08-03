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

import json
import re
from typing import Dict, List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check


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
    all_lean_names = set(ARISTOTLE_THEOREMS.keys())
    if lean_dir.exists():
        for lean_file in lean_dir.glob('*.lean'):
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
    backslash-escaped (`\\_`) inside `\\texttt{}` / prose."""
    return re.compile(re.escape(token).replace("_", r"(?:\\_|_)"))


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
        return CheckResult(passed=True, details=[Detail("papers_dir", True, "no papers/ directory")])

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
_LEDGER_HEDGE_RE = re.compile(
    r"\b(record(s|ed)?|tabulat|aggregat|enumerat|bookkeep|tallies|"
    r"classification\s+ledger|summari[sz])\b", re.IGNORECASE)


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
        return CheckResult(passed=True, details=[Detail("papers_dir", True, "no papers/ directory")])

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
    except ImportError:
        BASELINE = frozenset()

    lean_dir = _H.PROJECT_ROOT / "lean" / "SKEFTHawking"
    if not lean_dir.exists():
        return CheckResult(passed=True, details=[Detail("lean_dir", True, "no lean dir")])

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
    for lean_file in sorted(lean_dir.rglob("*.lean")):
        try:
            source = lean_file.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for thm_name, line_no, body in _scan_lean_theorem_bodies(source):
            if thm_name in exempt or thm_name in whitelisted:
                continue
            if not _STRUCTURAL_NAME_RE.search(thm_name):
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
    n_vac = sum(1 for v in MODELING_ASSUMPTION_THEOREMS.values()
                if v.get("category") == "vacuous_proxy")
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

    if new_flagged or wl_incomplete:
        return CheckResult(passed=False, details=details)
    details.append(Detail(
        "all_theorems", True,
        f"no NEW trivially-closed structural theorems ({len(grandfathered)} baselined, "
        f"{n_vac} disclosed vacuous_proxy)"))
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

    # TODO(semantic-review, ADR-009 Phase 3): absence -> PASS here, but -> FAIL in
    # prose_theorem_reference_coverage / theorem_name_embedded_citations. Five checks
    # pass on a missing lean_deps.json and two fail. Unify deliberately, not by refactor.
    if not _H.lean_deps_present():
        return CheckResult(passed=True, details=[Detail("lean_deps", True, "no lean_deps.json")])
    deps = _H.load_lean_deps()

    # 1) Prop-valued tracked-hypothesis defs/structures (codomain Prop, tracked name)
    tracked: dict = {}  # short name -> module
    for d in deps:
        short = d.get("name", "").split(".")[-1]
        if _TRACKED_PROP_NAME_RE.match(short) and _is_prop_codomain(d.get("type", "")):
            tracked[short] = d.get("module", "")

    # 2) which are CONSUMED as a binder `( ident : Name` anywhere in the source
    lean_dir = _H.PROJECT_ROOT / "lean" / "SKEFTHawking"
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
    try:
        import render_tracked_hypotheses as _r
    except Exception as e:  # pragma: no cover
        return CheckResult(passed=True, details=[Detail("import", True, f"renderer unavailable: {e}", warning=True)])
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


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1e: Formula content-grounding (R1, Invariant #4 with teeth)
# ═══════════════════════════════════════════════════════════════════════

# ═══════════════════════════════════════════════════════════════════════
# Type-thinness classifier (ADR-004 reconcile #45/#54/#25/#14) — shared by
# `vacuous_statement_audit` and the `formula_grounding` hardening. Operates on
# the ELABORATED type from lean_deps.json (name-agnostic, tactic-agnostic), so
# it catches statements that prove nothing regardless of the proof tactic or the
# theorem's name — the gap that let bare-arithmetic / reflexive theorems slip the
# name-gated, norm_num-excluding `proxy_body_audit`.
# ═══════════════════════════════════════════════════════════════════════

# Tokens that carry NO physics content (operators, relations, numeric base types,
# logical connectives). A statement whose ONLY identifiers are these (+ numeric
# literals) is a closed decidable fact — "ground arithmetic dressed as physics".
_ARITH_TOKENS = frozenset({
    "Eq", "Ne", "GT.gt", "LT.lt", "LE.le", "GE.ge",
    "HMul.hMul", "instHMul.hMul", "HAdd.hAdd", "instHAdd.hAdd",
    "HSub.hSub", "instHSub.hSub", "HDiv.hDiv", "instHDiv.hDiv",
    "HPow.hPow", "instHPow", "Neg.neg", "OfNat.ofNat", "OfScientific.ofScientific",
    "Nat", "Int", "Real", "Rat", "ℝ", "ℕ", "ℤ", "ℚ",
    "And", "Or", "Iff", "Not", "True", "False", "Prop",
})
_NUMLIT_RE = re.compile(r"^-?\d+(\.\d+)?(e-?\d+)?$", re.IGNORECASE)
_TYPE_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
# A "simple" Eq-argument = a single token with no internal structure (numeric
# literal or a bare identifier / bound variable). Reflexive `Eq X X` is reliable
# ONLY for simple args: a COMPOUND arg (`Eq (f a) (f a)`) may be a FALSE reflexive
# because lean_deps' pretty-printed type ELIDES implicit args — e.g.
# `sigPos_cast_pos : … sigPos (A.map (Int.cast:ℤ→ℝ)) → … sigPos (A.map (Int.cast:ℤ→ℚ))`
# prints both sides as `sigPos (A.map Int.cast)` (the ℝ/ℚ codomain is elided), so a
# genuine ℝ→ℚ transfer LOOKS reflexive. Restricting to simple args removes this
# whole elision false-positive class (reconcile 2026-06-13).
_SIMPLE_ARG_RE = re.compile(r"^-?[\w.]+'?$")
_THIN_HARD = {"True", "reflexive (X=X)"}


def _top_tokens(s: str) -> List[str]:
    """Split into top-level tokens (bracket-balanced groups or maximal
    non-space runs), respecting ()[]{}⟨⟩."""
    toks, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨":
            depth += 1; cur += ch
        elif ch in ")]}⟩":
            depth -= 1; cur += ch
        elif ch == " " and depth == 0:
            if cur:
                toks.append(cur); cur = ""
        else:
            cur += ch
    if cur:
        toks.append(cur)
    return toks


def _top_arrow_split(s: str) -> List[str]:
    """Split on top-level `→` (function arrows), respecting brackets."""
    parts, depth, last, i = [], 0, 0, 0
    while i < len(s):
        ch = s[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and ch == "→":
            parts.append(s[last:i].strip()); last = i + 1
        i += 1
    parts.append(s[last:].strip())
    return parts


def _strip_leading_binders(t: str) -> str:
    """Drop leading `∀ … ,` / `∃ … ,` binder groups to reach the proposition."""
    t = t.strip()
    while t.startswith("∀") or t.startswith("∃"):
        depth, ci = 0, None
        for i, ch in enumerate(t):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif ch == "," and depth == 0:
                ci = i; break
        if ci is None:
            break
        t = t[ci + 1:].strip()
    return t


# Lean/Mathlib compiler-EMITTED lemmas (congruence, constructor, recursor,
# equation lemmas) carry trivial/structural types by construction and are NOT
# authored claims — exclude them (e.g. `Padic.congr_simp`, `Foo.mk.congr_simp`).
_AUTOGEN_SHORT = frozenset({
    "congr_simp", "congr", "injEq", "mk", "rec", "recOn", "casesOn", "below",
    "brecOn", "ind", "binductionOn", "noConfusion", "noConfusionType",
    "sizeOf_spec", "eq_def", "eq_mp", "eq_mpr", "fst", "snd",
})
_AUTOGEN_RE = re.compile(r"^(eq|proof|match|fun)_\d+$")


def _is_autogen_decl(name: str) -> bool:
    short = name.split(".")[-1]
    return (short in _AUTOGEN_SHORT or bool(_AUTOGEN_RE.match(short))
            or ".mk." in name or name.endswith(".congr_simp"))


def _thin_type_label(type_str: str):
    """Classify a declaration's elaborated type as content-thin, or None.

    Returns a label string; `label in _THIN_HARD` ⇒ unambiguously vacuous
    (hard-fail). `'ground-arith'` ⇒ closed numeric fact (advisory — the class
    legitimately mixes vacuous physics-dressing with real counting identities
    like `4*5/2 = 10`, with no syntactic separator). Operates on the elaborated
    lean_deps type. Order: True ▸ reflexive ▸ ground-arith.

    NOTE type-based `P→P` (hypothesis-return) detection is DELIBERATELY omitted:
    lean_deps elides implicit args, so a genuine transfer `P_ℝ → P_ℚ` prints as
    `P → P` (e.g. `sigPos_cast_pos`). The genuine `P→P` tautologies are caught
    body-wise by `proxy_body_audit` (identity-return), which is elision-immune."""
    if not type_str:
        return None
    t = type_str.replace("\n", " ").strip()
    while "  " in t:
        t = t.replace("  ", " ")
    if t == "True":
        return "True"
    core = _strip_leading_binders(t)
    concl = _top_arrow_split(core)[-1].strip()
    # reflexive `Eq X X` (prefix) / `X = X` (infix) — SIMPLE args only (a compound
    # arg may be a pretty-print elision false-reflexive; see `_SIMPLE_ARG_RE`).
    toks = _top_tokens(concl)
    if len(toks) == 3 and toks[0] == "Eq" and toks[1] == toks[2] \
            and _SIMPLE_ARG_RE.match(toks[1]):
        return "reflexive (X=X)"
    if len(toks) == 3 and toks[1] == "=" and toks[0] == toks[2] \
            and _SIMPLE_ARG_RE.match(toks[0]):
        return "reflexive (X=X)"
    # ground arithmetic: conclusion's only identifiers are operators/literals
    leftover = [x for x in _TYPE_IDENT_RE.findall(concl)
                if x not in _ARITH_TOKENS and not _NUMLIT_RE.match(x)]
    has_rel = (any(r in concl for r in ("Eq", "GT.gt", "LT.lt", "LE.le", "GE.ge", "Ne"))
               or any(op in concl for op in ("=", "<", ">", "≤", "≥")))
    if has_rel and not leftover:
        return "ground-arith"
    return None


def _is_vacuous_identity_wrapper(type_str: str) -> bool:
    """True iff the elaborated type is a DOUBLY-vacuous identity wrapper: an
    implication `P → P` whose antecedent equals its consequent AND that shared
    `P` is itself a reflexive equality `Eq X X` / `X = X`. This is the
    `dd_simples_count` evidence-laundering shape (`… (h : Σ = Σ) : Σ = Σ := h`
    — returns its hypothesis, proves nothing).

    Requiring the reflexive body is what makes this false-positive-free: a
    genuine transfer `P_ℝ → P_ℚ` also prints `P → P` after implicit-arg elision
    (the reason `_thin_type_label` omits bare `P→P`), but there `P` is a
    substantive proposition, not `Eq X X`. Only the reflexive-body case is
    unambiguously content-free."""
    if not type_str:
        return False
    core = _strip_leading_binders(type_str.replace("\n", " ").strip())
    parts = _top_arrow_split(core)
    if len(parts) < 2 or parts[-1].strip() != parts[-2].strip():
        return False
    toks = _top_tokens(parts[-1].strip())
    return ((len(toks) == 3 and toks[0] == "Eq" and toks[1] == toks[2])
            or (len(toks) == 3 and toks[1] == "=" and toks[0] == toks[2]))


# Bare definitional closers: an `rfl`-family proof of an equality means the two
# sides are DEFINITIONALLY equal (the theorem unfolds a definition, deriving
# nothing). `simp`/`norm_num`/`decide` are deliberately NOT here — those can
# discharge substantive computations.
_BARE_RFL_RE = re.compile(r"^(by\s+)?(exact\s+)?(rfl|Iff\.rfl|Eq\.refl(\s+\S+)?)$")


def _lean_decl_proof_body(short_name: str, module: str):
    """Normalized proof body of ``short_name`` in its Lean ``module`` file, or
    None. ``module`` is the lean_deps form ``SKEFTHawking.<Path.To.Module>`` and
    maps to ``_H.LEAN_DIR/<Path>/<To>/<Module>.lean``. Reads a single file."""
    if not module:
        return None
    try:
        from build_graph import _scan_lean_theorem_bodies
    except Exception:  # pragma: no cover - import guard
        return None
    segs = str(module).split(".")
    if segs and segs[0] == "SKEFTHawking":
        segs = segs[1:]
    if not segs:
        return None
    f = _H.LEAN_DIR.joinpath(*segs).with_suffix(".lean")
    if not f.exists():
        return None
    try:
        source = f.read_text()
    except (OSError, UnicodeDecodeError):
        return None
    for name, _ln, body in _scan_lean_theorem_bodies(source):
        if name.split(".")[-1] == short_name:
            return " ".join(body.split())
    return None


def _grounding_is_definitional(decl: dict) -> bool:
    """A grounding theorem is a 'definitional record' iff its elaborated type is
    a vacuous identity wrapper OR its Lean proof body is a bare `rfl`-family
    closer (definitional equality). Used by `formula_grounding` to keep the
    `FORMULA_GROUNDING_KIND` declarations honest."""
    if _is_vacuous_identity_wrapper(decl.get("type", "")):
        return True
    body = _lean_decl_proof_body(decl.get("name", "").split(".")[-1], decl.get("module", ""))
    return bool(body and _BARE_RFL_RE.match(body))


def _parse_formula_lean_refs(src: str) -> set:
    """Extract Lean theorem-name tokens from `Lean: …` docstring lines in
    formulas.py, dropping non-decl artifacts (file names, `pending`, fragments,
    all-caps matrix labels)."""
    refs = set()
    for m in re.finditer(r"Lean:\s*(.+)", src):
        line = re.split(r"[—–]\s|\s-\s", m.group(1))[0]  # drop trailing description
        for tok in line.split(","):
            tok = re.sub(r"\(.*?\)", "", tok).strip().rstrip(".").strip()
            if not re.fullmatch(r"[A-Za-z_][\w.]*", tok) or len(tok) <= 2:
                continue
            if tok.endswith(".lean") or tok == "pending" or tok.startswith("_"):
                continue
            if re.fullmatch(r"[A-Z][A-Z0-9]{0,4}", tok):  # matrix-element labels (K0E0)
                continue
            refs.add(tok)
    return refs


@register_check(
    "formula_grounding",
    "Every formulas.py Lean reference resolves to a real, non-placeholder theorem (Invariant #4, R1)")
def check_formula_grounding() -> CheckResult:
    """Content-grounding for Pipeline Invariant #4: each `Lean:` reference in
    `formulas.py` must resolve to a real Lean declaration that is NOT a
    `True`/placeholder stub (a formula must not be 'grounded' on a theorem that
    proves nothing — the δ_diss-class hazard, audit 2026-06-13 #14). Extends the
    7-pair name-presence `formulas` check to ALL ~390 references.
    HARD-FAIL: placeholder-grounded refs. ADVISORY: dangling (unresolved) refs —
    a stale-name drift backlog the gate surfaces (FormulaRefSweep follow-up)."""
    from src.core.constants import PLACEHOLDER_LEAN_NAMES
    formulas_path = _H.SRC_DIR / "core" / "formulas.py"
    # TODO(semantic-review, ADR-009 Phase 3): absence -> PASS (see the note at
    # tracked_hypothesis_ledger; the eight loaders disagree).
    if not formulas_path.exists() or not _H.lean_deps_present():
        return CheckResult(passed=True, details=[Detail("inputs", True, "formulas.py / lean_deps.json absent")])

    deps = _H.load_lean_deps()
    names, dotted, shorts, by_short, by_full = set(), set(), set(), {}, {}
    for d in deps:
        n = d.get("name", "")
        if not n:
            continue
        names.add(n); by_full[n] = d
        segs = n.split("."); shorts.add(segs[-1]); by_short.setdefault(segs[-1], d)
        for i in range(1, len(segs)):
            dotted.add(".".join(segs[i:]))

    refs = _parse_formula_lean_refs(formulas_path.read_text())

    def resolves(t):
        return t in names or t in dotted or t in shorts

    def decl(t):
        return by_full.get(t) or by_short.get(t.split(".")[-1])

    placeholder_grounded, dangling, thin_grounded = [], [], []
    for t in sorted(refs):
        if not resolves(t):
            dangling.append(t)
            continue
        d = decl(t)
        if not d:
            continue
        if d.get("type") == "True" or d["name"].split(".")[-1] in PLACEHOLDER_LEAN_NAMES:
            placeholder_grounded.append(t)
            continue
        # ADR-004 reconcile #14 (the real Wave-21 semantic audit): a formula must
        # not be "grounded" on a theorem whose CONCLUSION proves nothing — a
        # reflexive `Eq N N` / `P→P` tautology (the δ_diss-class hazard, where the
        # cited theorem merely mentions the quantity instead of relating it). The
        # 7-9-order δ_diss units bug hid precisely because grounding meant "a named
        # theorem exists", not "the theorem's conclusion pertains to the formula".
        # NOTE this is STRUCTURAL substance (the statement is non-tautological),
        # not full semantic "conclusion ⟹ float-computation" (undecidable); it
        # catches the prove-nothing class. Ground-arith groundings are allowed —
        # a formula computing a count may legitimately ground on `… = N`.
        if _thin_type_label(d.get("type", "")) in _THIN_HARD:
            thin_grounded.append(t)

    # ── R-05: grounding-kind honesty (definitional-record vs derivation) ──
    # A formula must not present a DEFINITIONAL record (identity wrapper / rfl
    # equality) as an independent DERIVATION. FORMULA_GROUNDING_KIND is the
    # authoritative per-ref claim; this cross-checks it against the Lean.
    from src.core.constants import FORMULA_GROUNDING_KIND
    kind_violations: List[tuple] = []

    # Leg B (false-positive-free, ALL refs): a vacuous identity wrapper (`P → P`
    # with reflexive body — proves nothing) MUST be declared a definitional
    # record; grounding a formula on one as a derivation is forbidden.
    for t in sorted(refs):
        if not resolves(t):
            continue
        d = decl(t)
        if not d or not _is_vacuous_identity_wrapper(d.get("type", "")):
            continue
        meta = FORMULA_GROUNDING_KIND.get(t.split(".")[-1])
        if not meta or meta.get("kind") != "definitional-record":
            kind_violations.append((t,
                "vacuous identity wrapper (`P → P`, reflexive body — proves nothing) grounds "
                "a formula; declare grounding_kind='definitional-record' in FORMULA_GROUNDING_KIND "
                "or reground on a substantive theorem"))

    # Legs A/C (the declared entries): the declared kind must MATCH the Lean.
    # 'definitional-record' that is actually substantive → mislabel; 'derivation'
    # that is actually an identity wrapper / rfl-definitional equality → the R-05
    # relabel we forbid (a definitional record cannot be re-labeled a derivation).
    for short, meta in FORMULA_GROUNDING_KIND.items():
        d = by_short.get(short)
        if not d:
            kind_violations.append((short,
                "FORMULA_GROUNDING_KIND entry resolves to no Lean declaration"))
            continue
        kind = meta.get("kind")
        is_defl = _grounding_is_definitional(d)
        if kind == "definitional-record" and not is_defl:
            kind_violations.append((short,
                "declared grounding_kind='definitional-record' but the Lean is neither an identity "
                "wrapper nor an rfl-definitional equality — inaccurate label (do not hide a "
                "substantive or open theorem behind a definitional record)"))
        elif kind == "derivation" and is_defl:
            kind_violations.append((short,
                "declared grounding_kind='derivation' but the Lean IS an identity wrapper / "
                "rfl-definitional equality — a definitional record cannot be re-labeled a "
                "derivation (R-05 evidence-laundering)"))
        elif kind not in ("definitional-record", "derivation"):
            kind_violations.append((short,
                f"kind={kind!r} is not 'definitional-record' or 'derivation'"))

    ok = not (placeholder_grounded or dangling or thin_grounded or kind_violations)
    details: List[Detail] = []
    details.append(Detail(
        "coverage", ok,
        f"{len(refs)} Lean refs; {len(refs) - len(dangling)} resolve; "
        f"{len(placeholder_grounded)} placeholder-grounded; {len(thin_grounded)} thin-grounded; "
        f"{len(dangling)} dangling; {len(FORMULA_GROUNDING_KIND)} grounding-kind declared; "
        f"{len(kind_violations)} grounding-kind violation(s)"))
    for t, msg in kind_violations:
        details.append(Detail(t, False, msg))
    for t in placeholder_grounded:
        details.append(Detail(t, False, "formula grounded on a placeholder/True stub (Invariant #4)"))
    for t in thin_grounded:
        details.append(Detail(
            t, False,
            "formula grounded on a reflexive/tautological theorem (proves nothing; "
            "Invariant #4 content-grounding) — reground on a substantive theorem"))
    # Dangling refs are HARD-FAIL since the 2026-06-13 FormulaRefSweep drove the
    # count to 0 (ratchet — a NEW stale/renamed formula ref must be fixed, not
    # left to rot). Replace the dangling name with the current theorem, drop the
    # ref if no theorem grounds the formula, or (if it is a legitimate Mathlib /
    # external name) it should still resolve in lean_deps — if not, it is drift.
    for t in dangling:
        details.append(Detail(
            t, False,
            "formula Lean-ref does not resolve (stale/renamed) — fix the name or drop the ref"))
    return CheckResult(passed=ok, details=details)


@register_check(
    "vacuous_statement_audit",
    "No project theorem/lemma has a content-thin (reflexive / tautological) statement (R2 type-companion)")
def check_vacuous_statement_audit() -> CheckResult:
    """Type-based companion to `proxy_body_audit` (ADR-004 reconcile #45/#54/#25).
    `proxy_body_audit` is name-gated (`_STRUCTURAL_NAME_RE`) and excludes
    `norm_num`/`decide` bodies, so a theorem whose STATEMENT proves nothing slips
    if its name isn't structural or its proof is `by norm_num` (e.g.
    `tetrad_components : 4*4=16`, `hom_tensor_adjunction_dim : ∀ rank, rank=rank`).
    This check classifies the ELABORATED type (lean_deps.json), name- and
    tactic-agnostic.

    HARD-FAIL: reflexive `Eq X X` and `True` (the unambiguously-vacuous classes)
    NOT in `VACUOUS_STATEMENT_BASELINE`. ADVISORY: ground-arithmetic (closed
    numeric facts — the class legitimately mixes vacuous physics-dressing with
    real counting identities like `4*5/2=10`) AND the grandfathered baseline (the
    ~48 pre-existing content-thin theorems un-hid by the SIG-gate blind-spot fixes,
    visible tracked debt — a name leaves the set only by being dispositioned). A
    flagged decl is COMPLIANT iff registered in `PLACEHOLDER_THEOREMS` /
    `MODELING_ASSUMPTION_THEOREMS` (reason+discloses), self-disclosed via a
    `_DEFINITIONAL` name suffix, or in the baseline. NEW (non-baseline) thin
    statements HARD-FAIL — closing the generator (ADR-004 pathway #2)."""
    from src.core.constants import PLACEHOLDER_LEAN_NAMES
    try:
        from src.core.constants import MODELING_ASSUMPTION_THEOREMS
    except ImportError:
        MODELING_ASSUMPTION_THEOREMS = {}
    try:
        from src.core.constants import VACUOUS_STATEMENT_BASELINE as BASELINE
    except ImportError:
        BASELINE = frozenset()
    # TODO(semantic-review, ADR-009 Phase 3): absence -> PASS (loaders disagree).
    if not _H.lean_deps_present():
        return CheckResult(passed=True, details=[Detail("inputs", True, "lean_deps.json absent")])

    exempt = set(PLACEHOLDER_LEAN_NAMES.keys())
    for k, v in MODELING_ASSUMPTION_THEOREMS.items():
        if v.get("reason") and v.get("discloses"):
            exempt.add(v.get("lean_name", k))

    deps = _H.load_lean_deps()
    new_hard: List[tuple] = []
    grandfathered: List[str] = []
    advisory: List[tuple] = []
    for d in deps:
        if d.get("kind") not in ("theorem", "lemma"):
            continue
        name = d.get("name", "")
        if _is_autogen_decl(name):
            continue
        short = name.split(".")[-1]
        if short in exempt or short.endswith("_DEFINITIONAL"):
            continue
        label = _thin_type_label(d.get("type", ""))
        if label is None:
            continue
        if label not in _THIN_HARD:
            advisory.append((name, label))
        elif short in BASELINE:
            grandfathered.append(short)
        else:
            new_hard.append((name, label))

    details: List[Detail] = []
    if advisory:
        details.append(Detail(
            "ground_arithmetic", True,
            f"{len(advisory)} closed-arithmetic theorem(s) (verify load-bearing or delete/disclose) — "
            f"e.g. {', '.join(n.split('.')[-1] for n, _ in advisory[:5])}", warning=True))
    if grandfathered:
        details.append(Detail(
            "baseline", True,
            f"{len(grandfathered)} grandfathered content-thin theorem(s) in VACUOUS_STATEMENT_BASELINE "
            f"(visible tracked debt → Vacuous Statement Sweep)", warning=True))
    for name, label in new_hard:
        short = name.split(".")[-1]
        details.append(Detail(
            short, False,
            f"NEW content-thin statement `{short}` [{label}] not in baseline — strengthen, delete, "
            f"or register in MODELING_ASSUMPTION_THEOREMS (reason+discloses)"))
    if new_hard:
        return CheckResult(passed=False, details=details)
    details.append(Detail(
        "all_theorems", True,
        f"no NEW content-thin statements ({len(grandfathered)} baselined, "
        f"{len(advisory)} ground-arith advisory)"))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1e′: kernel no-go substrate integrity (ADR-007 N-C, Invariant #17)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "nogo_substrate_integrity",
    "Every provably-false no-go has a live, kernel-pure, non-vacuous backing theorem (Invariant #17, ADR-007 N-C)")
def check_nogo_substrate_integrity() -> CheckResult:
    """The negative-front mirror of ``tracked_hypothesis_ledger`` (ADR-007 N-C).
    For every ``KERNEL_NOGO_REGISTRY`` entry, each backing theorem must (1) EXIST
    in ``lean_deps.json``, (2) be KERNEL-PURE (core-axiom closure ⊆
    ``{propext, Classical.choice, Quot.sound}``, no ``sorryAx`` / genuine project
    axiom), and (3) be NON-VACUOUS (its elaborated type is not ``True`` / reflexive
    ``X=X`` — a self-discharging no-go blocks nothing; reuses
    ``vacuous_statement_audit``'s ``_thin_type_label``). Any failure = **BLOCKER**
    (this plugs the atlas ``"never touches OBSTRUCTION"`` hole — Hole A/B, ADR-007).
    ADVISORY: every ``SETTLED_FORKS`` fork field-authored ``kernel-no-go`` that has
    no registry entry — the *refutable-but-unencoded* one-time audit (ADR-007
    Costs/risks #1; encode per N-E). SCOPE: provably-false no-gos only; policy /
    route / preference bans are OUT of scope (N-B) and remain prose-only."""
    from src.core import constants as _c
    REG = getattr(_c, "KERNEL_NOGO_REGISTRY", {})
    KERNEL = {"propext", "Classical.choice", "Quot.sound"}
    _ND = re.compile(r"\._native\.native_decide")

    # TODO(semantic-review, ADR-009 Phase 3): absence -> PASS (loaders disagree).
    if not _H.lean_deps_present():
        return CheckResult(passed=True, details=[Detail("inputs", True, "lean_deps.json absent")])
    by_name = {d.get("name", ""): d for d in _H.load_lean_deps()}

    def _kernel_pure(rec: dict) -> bool:
        core = set(rec.get("axiom_deps_core", []))
        proj = [a for a in rec.get("axiom_deps_project", []) if not _ND.search(a)]
        return (core.issubset(KERNEL) and not proj
                and not any("sorryAx" in a for a in rec.get("axiom_deps_core", [])))

    details: List[Detail] = []
    hard = False
    for fork_id, e in sorted(REG.items()):
        bts = e.get("backing_theorems", []) or []
        if not bts:
            details.append(Detail(
                fork_id, True,
                "registry entry carries NO backing theorem (construction-level no-go?) — advisory",
                warning=True))
            continue
        for bt in bts:
            rec = by_name.get(bt)
            if rec is None:
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` ABSENT from lean_deps.json (renamed/deleted — the blocker rotted; Hole B)"))
                continue
            if not _kernel_pure(rec):
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` NOT kernel-pure (core={sorted(set(rec.get('axiom_deps_core', [])))}, "
                    f"proj={rec.get('axiom_deps_project', [])}) — a tainted refutation is not self-enforcing"))
                continue
            label = _thin_type_label(rec.get("type", ""))
            if label in _THIN_HARD:
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` is VACUOUS [{label}] — a self-discharging no-go blocks nothing (Hole A)"))
                continue
            details.append(Detail(
                fork_id, True,
                f"backing `{bt}` [{e.get('nogo_kind', '?')}] exists, kernel-pure, non-vacuous"))

    # Hole-B audit (advisory): field-authored `kernel-no-go` SETTLED_FORKS forks lacking a registry entry.
    forks_path = _H.PROJECT_ROOT / "docs" / "dev-loops" / "SETTLED_FORKS.md"
    if forks_path.exists():
        text = forks_path.read_text(errors="ignore")
        knogo = []
        for block in re.split(r"^## +", text, flags=re.M)[1:]:
            fid = block.splitlines()[0].strip()
            if re.search(r"authored_by:\s*kernel-no-go", block):
                knogo.append(fid)
        reg_forks = {e.get("fork_id") for e in REG.values()}
        unencoded = [f for f in knogo if f not in reg_forks]
        details.append(Detail(
            "audit", True,
            f"{len(REG)} registry entries; {len(knogo)} field-authored kernel-no-go forks; "
            f"{len(unencoded)} refutable-but-unencoded (advisory — encode per N-E): "
            f"{', '.join(unencoded) or 'none'}",
            warning=bool(unencoded)))

    return CheckResult(passed=not hard, details=details)
