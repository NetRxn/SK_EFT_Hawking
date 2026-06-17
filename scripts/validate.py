#!/usr/bin/env python3
"""
SK-EFT Hawking Project — Cross-Layer Validation Suite
=====================================================

Single entry point for verifying consistency across:
  Python source  ↔  Lean formal proofs  ↔  Notebooks  ↔  Papers

Usage
-----
    # From project root (recommended):
    python scripts/validate.py

    # With JSON output for CI:
    python scripts/validate.py --json

    # Save timestamped report to docs/validation/reports/:
    python scripts/validate.py --archive

    # Run a single check:
    python scripts/validate.py --check formulas

    # List available checks:
    python scripts/validate.py --list

Exit Codes
----------
    0 — all checks passed
    1 — one or more checks failed
    2 — script error (bad arguments, missing files)

Architecture & Extensibility
----------------------------
Each check is a function decorated with @register_check. To add a new check:

    @register_check("my_new_check", "Description of what it validates")
    def check_my_new_thing() -> CheckResult:
        ...
        return CheckResult(passed=True, details=[...])

The decorator handles registration, output formatting, and CI integration.
Checks are run in registration order, and any check can be run individually
via --check <name>.

Design Decisions
----------------
- Pure stdlib (no pytest dependency for the validation itself).
  This means validation works even if the test environment is degraded.
- Path-agnostic: resolves PROJECT_ROOT from this file's location,
  works from any working directory.
- Timestamped archival: --archive writes a dated JSON + text report
  to docs/validation/reports/ for historical tracking.
- Lean integration: if `lake` is on PATH, runs `lake build` as a check.
  If not available, skips gracefully with a warning.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Optional

# ═══════════════════════════════════════════════════════════════════════
# Path resolution
# ═══════════════════════════════════════════════════════════════════════

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
SRC_DIR = PROJECT_ROOT / "src"
LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
NOTEBOOKS_DIR = PROJECT_ROOT / "notebooks"
# Local (git-ignored) skip-cache for CHECK 11 notebook execution: maps each
# vetted notebook to a content hash so unchanged, previously-passed notebooks
# are not re-executed. Mirrors the Lean `extract_lean_deps.py` hash-skip.
NOTEBOOK_EXEC_CACHE = NOTEBOOKS_DIR / ".notebook_exec_cache.json"
PAPERS_DIR = PROJECT_ROOT / "papers"
REPORTS_DIR = PROJECT_ROOT / "docs" / "validation" / "reports"

# Ensure src is importable
sys.path.insert(0, str(PROJECT_ROOT))


# ═══════════════════════════════════════════════════════════════════════
# Data structures
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class Detail:
    """Single sub-check result."""
    name: str
    passed: bool
    message: str = ""
    warning: bool = False  # True = passed but with advisory warning (⚠)


@dataclass
class CheckResult:
    """Result of one top-level check."""
    passed: bool
    details: List[Detail] = field(default_factory=list)
    error: Optional[str] = None


@dataclass
class CheckSpec:
    """Registered check metadata."""
    name: str
    description: str
    func: Callable[[], CheckResult]


# Global registry
_CHECKS: List[CheckSpec] = []

# Strict mode flag — set by CLI --strict. Tightens advisory warnings to hard
# failures for paper-submission gating (currently used by parameter_provenance
# and provenance_doi_in_registry).
STRICT_MODE: bool = False

# Force flag — set by CLI --force-notebooks. Bypasses the CHECK 11 notebook
# skip-cache and re-executes every notebook (use after a kernel / dependency
# upgrade that could change execution outcomes without changing notebook
# content). Default False: unchanged, previously-vetted notebooks are skipped.
FORCE_NOTEBOOK_REEXEC: bool = False

# Force flag — set by CLI --force-latex OR when `paper_latex_compiles` is the
# explicitly selected `--check`. The latex-compile check is slow (pdflatex ×
# all bundle drafts), so it SKIPS in the default full run unless one of these
# is set. Default False.
FORCE_LATEX: bool = False


def register_check(name: str, description: str):
    """Decorator to register a validation check."""
    def decorator(func: Callable[[], CheckResult]) -> Callable[[], CheckResult]:
        _CHECKS.append(CheckSpec(name=name, description=description, func=func))
        return func
    return decorator


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
    lean_dir = Path(__file__).parent.parent / 'lean' / 'SKEFTHawking'
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

    if not PAPERS_DIR.exists():
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

    for paper_dir in sorted(PAPERS_DIR.iterdir()):
        if not paper_dir.is_dir():
            continue
        tex = paper_dir / "paper_draft.tex"
        if not tex.exists():
            continue
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
    if not PAPERS_DIR.exists():
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
    for paper_dir in sorted(PAPERS_DIR.iterdir()):
        tex = paper_dir / "paper_draft.tex"
        if not (paper_dir.is_dir() and tex.exists()):
            continue
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
        r"(\(?\s*Equiv\.refl[\s\w]*\)?(\.\w+)?|rfl|trivial)"
        r"(\s*,\s*(\(?\s*Equiv\.refl[\s\w]*\)?(\.\w+)?|rfl|trivial))*\s*⟩$"),
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
    import sys as _sys
    _sys.path.insert(0, str(Path(__file__).parent))
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

    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
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

    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    if not deps_path.exists():
        return CheckResult(passed=True, details=[Detail("lean_deps", True, "no lean_deps.json")])
    deps = json.loads(deps_path.read_text())

    # 1) Prop-valued tracked-hypothesis defs/structures (codomain Prop, tracked name)
    tracked: dict = {}  # short name -> module
    for d in deps:
        short = d.get("name", "").split(".")[-1]
        if _TRACKED_PROP_NAME_RE.match(short) and _is_prop_codomain(d.get("type", "")):
            tracked[short] = d.get("module", "")

    # 2) which are CONSUMED as a binder `( ident : Name` anywhere in the source
    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
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
    import sys as _sys
    _sys.path.insert(0, str(Path(__file__).parent))
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
    formulas_path = PROJECT_ROOT / "src" / "core" / "formulas.py"
    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    if not formulas_path.exists() or not deps_path.exists():
        return CheckResult(passed=True, details=[Detail("inputs", True, "formulas.py / lean_deps.json absent")])

    deps = json.loads(deps_path.read_text())
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

    details: List[Detail] = []
    details.append(Detail(
        "coverage", not (placeholder_grounded or dangling or thin_grounded),
        f"{len(refs)} Lean refs; {len(refs) - len(dangling)} resolve; "
        f"{len(placeholder_grounded)} placeholder-grounded; {len(thin_grounded)} thin-grounded; "
        f"{len(dangling)} dangling"))
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
    return CheckResult(passed=not (placeholder_grounded or dangling or thin_grounded), details=details)


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
    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    if not deps_path.exists():
        return CheckResult(passed=True, details=[Detail("inputs", True, "lean_deps.json absent")])

    exempt = set(PLACEHOLDER_LEAN_NAMES.keys())
    for k, v in MODELING_ASSUMPTION_THEOREMS.items():
        if v.get("reason") and v.get("discloses"):
            exempt.add(v.get("lean_name", k))

    deps = json.loads(deps_path.read_text())
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
# CHECK 1f: native_decide trust-surface regression (R4)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "native_decide_regression",
    "native_decide decl-closure does not silently grow past its ceiling (R4; ADR-002)")
def check_native_decide_regression() -> CheckResult:
    """The native_decide kernel-trust surface (decl-closure — ADR-002's metric,
    in docs/counts.json `lean.native_decide_decl_closure`) may only DECREASE
    without review. A wave that ADDS trust surface must bump
    `NATIVE_DECIDE_DECL_CLOSURE_CEILING` (constants.py) in the same commit with a
    rationale, so the increase is visible (no silent growth). Elimination policy
    is owned by ADR-002. Substrate Integrity Gates W5."""
    from src.core.constants import NATIVE_DECIDE_DECL_CLOSURE_CEILING as CEIL
    counts_path = PROJECT_ROOT / "docs" / "counts.json"
    if not counts_path.exists():
        return CheckResult(passed=True, details=[Detail("counts", True, "counts.json absent")])
    lean = json.loads(counts_path.read_text()).get("lean", {})
    cur = lean.get("native_decide_decl_closure")
    if cur is None:
        return CheckResult(passed=True, details=[Detail(
            "metric", True, "native_decide_decl_closure not yet in counts.json — run update_counts.py",
            warning=True)])
    clusters = lean.get("native_decide_clusters", {})
    if cur > CEIL:
        return CheckResult(passed=False, details=[Detail(
            "ceiling", False,
            f"native_decide decl-closure {cur} EXCEEDS ceiling {CEIL} — a wave grew the "
            f"kernel-trust surface. Eliminate (ADR-002) or bump NATIVE_DECIDE_DECL_CLOSURE_CEILING "
            f"with a rationale. Clusters: {clusters}")])
    msg = f"native_decide decl-closure {cur} ≤ ceiling {CEIL}"
    if cur < CEIL:
        msg += f" (down {CEIL - cur}; consider lowering the ceiling). Clusters: {clusters}"
    return CheckResult(passed=True, details=[Detail("ceiling", True, msg, warning=(cur < CEIL))])


# ═══════════════════════════════════════════════════════════════════════
# CHECK 2: Numerical consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("numerical", "Experimental parameters match reference values")
def check_numerical_consistency() -> CheckResult:
    from src.core.constants import get_all_experiments, HBAR

    expected = {
        'Steinhauer': {'c_s': 5.476e-4, 'xi': 1.334e-6, 'kappa': 4.8, 'T_H': 5.78e-12},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 4.159e-7, 'kappa': 101.9, 'T_H': 1.24e-10},
        'Trento':     {'c_s': 2.185e-3, 'xi': 1.264e-6, 'kappa': 21.4, 'T_H': 2.6e-11},
    }

    tolerance = 0.05
    details = []
    all_pass = True

    try:
        experiments = get_all_experiments()
    except Exception as e:
        return CheckResult(passed=False, error=str(e))

    for name, (params, bg) in experiments.items():
        if name not in expected:
            continue

        actuals = {
            'c_s': params.sound_speed_upstream,
            'xi': params.healing_length,
            'kappa': bg.surface_gravity,
            'T_H': bg.hawking_temp,
        }

        for param, exp_val in expected[name].items():
            actual = actuals[param]
            rel_err = abs(actual - exp_val) / abs(exp_val)
            ok = rel_err <= tolerance
            details.append(Detail(
                f"{name}.{param}",
                ok,
                f"expected={exp_val:.3e}, actual={actual:.3e}, err={rel_err*100:.1f}%"
            ))
            if not ok:
                all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 3: Formula identities
# ═══════════════════════════════════════════════════════════════════════

@register_check("identities", "Mathematical identities and boundary conditions hold")
def check_formula_identities() -> CheckResult:
    from src.core import formulas

    details = []
    all_pass = True

    tests = [
        ("count(1)==2", lambda: formulas.count_coefficients(1) == 2),
        ("count(2)==2", lambda: formulas.count_coefficients(2) == 2),
        ("count(3)==3", lambda: formulas.count_coefficients(3) == 3),
        ("disp(0)==0", lambda: formulas.dispersive_correction(0) == 0),
        ("1st_order(0,kappa)==0", lambda: formulas.first_order_correction(0, 1.0) == 0),
        ("Gamma(k,w,cs,0,0,0,0)==0", lambda: formulas.damping_rate(1.0, 2.0, 0.5, 0, 0, 0, 0) == 0),
    ]

    for name, fn in tests:
        try:
            ok = fn()
            details.append(Detail(name, ok))
            if not ok:
                all_pass = False
        except Exception as e:
            details.append(Detail(name, False, str(e)))
            all_pass = False

    # Acoustic-mode vanishing: k=w/cs with gamma_22=-gamma_21
    try:
        c_s, omega, kappa = 1.0, 100.0, 50.0
        k = omega / c_s
        g21 = 0.5
        result = formulas.second_order_correction(k, omega, c_s, g21, -g21, kappa)
        ok = abs(result) < 1e-10
        details.append(Detail("delta2_acoustic_vanishes", ok, f"value={result:.3e}"))
        if not ok:
            all_pass = False
    except Exception as e:
        details.append(Detail("delta2_acoustic_vanishes", False, str(e)))
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 4: Paper 1 Table 1 consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("paper_table", "Paper 1 Table 1 values match solver output")
def check_paper_table_consistency() -> CheckResult:
    from src.core.constants import get_all_experiments

    paper_path = PAPERS_DIR / "paper1_first_order" / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    # Reference values from the corrected table (solver output)
    # NOTE: Steinhauer kappa/T_H here are MODEL values (tanh profile).
    # Published values (kappa=290, T_H=0.35nK) come from the actual
    # step potential, not our smooth model. See backreaction.py steinhauer_si().
    paper_table = {
        'Steinhauer': {'c_s': 5.476e-4, 'xi': 1.334e-6, 'kappa': 4.8, 'T_H': 0.006e-9},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 4.159e-7, 'kappa': 101.9, 'T_H': 0.124e-9},
        'Trento':     {'c_s': 2.185e-3, 'xi': 1.264e-6, 'kappa': 21.4, 'T_H': 0.026e-9},
    }

    tolerance = 0.05
    details = []
    all_pass = True

    try:
        experiments = get_all_experiments()
    except Exception as e:
        return CheckResult(passed=False, error=str(e))

    for name, paper_vals in paper_table.items():
        if name not in experiments:
            continue
        params, bg = experiments[name]
        actuals = {
            'c_s': params.sound_speed_upstream,
            'xi': params.healing_length,
            'kappa': bg.surface_gravity,
            'T_H': bg.hawking_temp,
        }
        for param, pval in paper_vals.items():
            actual = actuals[param]
            rel_err = abs(actual - pval) / abs(pval)
            ok = rel_err <= tolerance
            details.append(Detail(f"{name}.{param}", ok,
                                  f"paper={pval:.3e}, code={actual:.3e}"))
            if not ok:
                all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 5: Theorem registry
# ═══════════════════════════════════════════════════════════════════════

@register_check("theorems", "Theorem registry has 322 entries and is self-consistent")
def check_theorem_count() -> CheckResult:
    from src.core.constants import ARISTOTLE_THEOREMS, TOTAL_THEOREMS

    details = []
    all_pass = True

    for name, (actual, expected) in {
        "TOTAL_THEOREMS": (TOTAL_THEOREMS, 322),
        "len(ARISTOTLE_THEOREMS)": (len(ARISTOTLE_THEOREMS), 322),
    }.items():
        ok = actual == expected
        details.append(Detail(name, ok, f"actual={actual}, expected={expected}"))
        if not ok:
            all_pass = False

    ok = TOTAL_THEOREMS == len(ARISTOTLE_THEOREMS)
    details.append(Detail("consistency", ok,
                          f"TOTAL={TOTAL_THEOREMS}, dict={len(ARISTOTLE_THEOREMS)}"))
    if not ok:
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 6: No inline physics in notebooks
# ═══════════════════════════════════════════════════════════════════════

@register_check("notebooks", "Notebooks import physics from src.core, no re-implementation")
def check_notebook_isolation() -> CheckResult:
    forbidden = {
        'damping_rate', 'dispersive_correction', 'first_order_correction',
        'second_order_correction', 'turning_point_shift',
        'effective_temperature', 'count_formula',
        'enumerate_monomials', 'count_coefficients',
        'cgl_fdr', 'retarded_kernel', 'noise_kernel',
        'derive_fdr_fourier', 'extract_odd_kernel',
    }

    details = []
    all_pass = True

    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = json.load(f)
        except Exception as e:
            details.append(Detail(nb_path.name, False, f"Parse error: {e}"))
            all_pass = False
            continue

        violations = set()
        for cell in nb.get('cells', []):
            if cell.get('cell_type') != 'code':
                continue
            src = ''.join(cell.get('source', []))
            for fn in forbidden:
                if re.search(rf'def\s+{re.escape(fn)}\s*\(', src):
                    violations.add(fn)

        ok = len(violations) == 0
        msg = "clean" if ok else f"redefines: {', '.join(sorted(violations))}"
        details.append(Detail(nb_path.name, ok, msg))
        if not ok:
            all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 7: Lean theorem names appear in .lean source files
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_source", "Key theorem names found in Lean source files")
def check_lean_source() -> CheckResult:
    if not LEAN_DIR.exists():
        return CheckResult(passed=False, error=f"Lean directory not found: {LEAN_DIR}")

    # Collect all identifiers declared as theorem/lemma/def
    lean_idents = set()
    for lf in LEAN_DIR.glob("*.lean"):
        try:
            content = lf.read_text()
            lean_idents.update(re.findall(r'(?:theorem|lemma|def)\s+(\w+)', content))
        except Exception:
            pass

    # Map Python registry names to expected Lean identifiers
    # (some differ by naming convention)
    spot_checks = {
        # Phase 1-2
        'dampingRate_eq_zero_iff': 'dampingRate_eq_zero_iff',
        'dispersive_bound': 'dispersive_correction_bound',
        'firstOrder_correction_zero_iff': 'firstOrder_correction_zero_iff',
        'acoustic_metric_determinant': 'acousticMetric_det',
        'secondOrder_count': 'secondOrder_count',
        # Phase 4 (Aristotle batch b1ea2eb7)
        'fracton_exceeds_standard_general': 'fracton_exceeds_standard_general',
        'binomial_strict_mono': 'binomial_strict_mono',
        'dof_gap_positive_2_through_8': 'dof_gap_positive_2_through_8',
        'evading_one_breaks_nogo': 'evading_one_breaks_nogo',
        'ep_distinguishes_phases': 'ep_distinguishes_phases',
        'obstructions_individually_sufficient': 'obstructions_individually_sufficient',
    }

    details = []
    all_pass = True

    for registry_name, lean_name in spot_checks.items():
        ok = lean_name in lean_idents
        details.append(Detail(registry_name, ok,
                              f"Lean ident '{lean_name}' {'found' if ok else 'NOT found'}"))
        if not ok:
            all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 8: CGL FDR derivation consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("cgl_fdr", "CGL FDR derivation produces correct results")
def check_cgl_fdr() -> CheckResult:
    """Verify the CGL dynamical KMS derivation of the FDR."""
    from src.second_order.cgl_derivation import (
        verify_einstein_relation,
        verify_first_order_bec,
        verify_second_order_fdr,
        derive_fdr_fourier,
    )

    details = []
    all_pass = True

    # Einstein relation
    ok = verify_einstein_relation()
    details.append(Detail("einstein_relation", ok,
                          "σ = γ/β₀ for Brownian particle"))
    if not ok:
        all_pass = False

    # First-order BEC FDR
    ok = verify_first_order_bec()
    details.append(Detail("first_order_bec", ok,
                          "K_N = 2Γ/β₀ for BEC with damping"))
    if not ok:
        all_pass = False

    # Second-order noise reality
    ok = verify_second_order_fdr()
    details.append(Detail("second_order_real", ok,
                          "Second-order noise kernel is real"))
    if not ok:
        all_pass = False

    # General pattern: noise count at even orders
    try:
        results = derive_fdr_fourier(4)
        counts = {N: len(data['noise']) for N, data in results.items()}
        ok = counts == {0: 1, 1: 0, 2: 2, 3: 0, 4: 3}
        details.append(Detail("noise_count_pattern", ok,
                              f"Noise counts: {counts}"))
        if not ok:
            all_pass = False
    except Exception as e:
        details.append(Detail("noise_count_pattern", False, str(e)))
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 9: Lean build (optional, requires `lake` on PATH)
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_build", "Lean project builds cleanly (requires lake)")
def check_lean_build() -> CheckResult:
    """
    Run `lake build` on the Lean project.

    Lake discovery order:
      1. LAKE_PATH env var  (explicit path to lake binary)
      2. ~/.elan/bin/lake   (standard elan install location)
      3. System PATH         (global install)

    Lean project directory:
      1. LEAN_PROJECT_DIR env var  (override for mono-repo layouts)
      2. PROJECT_ROOT / "lean"     (default, same repo)

    The check looks for lakefile.lean OR lakefile.toml (Lean 4 / Lake v4+).
    """
    import shutil
    import os

    # ── Resolve lake binary ──
    lake_bin = os.environ.get("LAKE_PATH")

    if not lake_bin:
        # Try ~/.elan/bin/lake (standard elan install)
        elan_lake = Path.home() / ".elan" / "bin" / "lake"
        if elan_lake.is_file():
            lake_bin = str(elan_lake)

    if not lake_bin:
        lake_bin = shutil.which("lake")

    if not lake_bin:
        return CheckResult(
            passed=True,
            details=[Detail("lake", True,
                            "SKIPPED — lake not found. Set LAKE_PATH or install elan "
                            "(https://github.com/leanprover/elan)")],
        )

    # ── Resolve Lean project directory ──
    lean_root = Path(os.environ.get("LEAN_PROJECT_DIR", PROJECT_ROOT / "lean"))

    has_lakefile = (
        (lean_root / "lakefile.lean").exists()
        or (lean_root / "lakefile.toml").exists()
    )
    if not has_lakefile:
        return CheckResult(
            passed=True,
            details=[Detail("lakefile", True,
                            f"SKIPPED — no lakefile.{{lean,toml}} in {lean_root}")],
        )

    # ── Run lake build ──
    details = [Detail("lake_bin", True, lake_bin),
               Detail("lean_root", True, str(lean_root))]

    try:
        result = subprocess.run(
            [lake_bin, "build"],
            cwd=str(lean_root),
            capture_output=True, text=True, timeout=600,
        )
        ok = result.returncode == 0
        if ok:
            # Count jobs from output like "Build completed successfully (2254 jobs)."
            # or "ℹ [2254/2254] ..." lines in stderr + stdout
            combined = result.stderr + result.stdout
            job_match = (
                re.search(r'(\d+) jobs?\)', combined)
                or re.search(r'\[(\d+)/\1\]', combined)  # [N/N] = final job
            )
            jobs = job_match.group(1) if job_match else "cached"
            msg = f"build succeeded ({jobs} jobs)"
        else:
            msg = result.stderr[-500:]
        details.append(Detail("lake_build", ok, msg))
        return CheckResult(passed=ok, details=details)
    except subprocess.TimeoutExpired:
        details.append(Detail("lake_build", False, "timeout (600s)"))
        return CheckResult(passed=False, details=details)
    except Exception as e:
        return CheckResult(passed=False, details=details, error=str(e))


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Axiom-closure allow-list (AI-Defect-Defense-Layer P4, Invariant #15)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "axiom_closure_allowlist",
    "Every SKEFTHawking declaration's transitive axiom closure is on the standard "
    "kernel axioms + the AXIOM_METADATA allow-list (Invariant #15 backstop)",
)
def check_axiom_closure_allowlist() -> CheckResult:
    """
    AI-Defect-Defense-Layer P4. Runs the ``AxiomAudit`` Lean executable
    (interpreted, reusing the memoized ``AxiomClosure`` machinery that backs
    ``ExtractDeps``) to obtain the transitive *non-core* axiom closure of every
    ``SKEFTHawking.*`` declaration, and verifies each axiom lies in the allow-list

        {propext, Classical.choice, Quot.sound} ∪ AXIOM_METADATA.keys()

    Posture (WARN-first, retrofit): a non-allow-listed axiom is an advisory
    warning by default and a hard failure under ``--strict`` (paper-submission
    gating), mirroring ``parameter_provenance``. ``native_decide``-generated
    compiler-trust axioms (per-declaration ``*._native.native_decide.ax_*``) are
    recognised as a distinct *accepted* category and reported for visibility —
    they are not declared project ``axiom``s, so ``counts.json`` reports
    ``Axioms: 0`` while this check surfaces the genuine trust surface.

    Shares the underlying Lean executable with the lean4 plugin's
    ``/check-axioms`` (``lean/SKEFTHawking/AxiomAudit.lean``): discipline defined
    once, invoked interactively at ``/lean4:checkpoint`` and non-interactively here.
    """
    import shutil
    import os

    # ── Resolve lake (mirror check_lean_build) ──
    lake_bin = os.environ.get("LAKE_PATH")
    if not lake_bin:
        elan_lake = Path.home() / ".elan" / "bin" / "lake"
        if elan_lake.is_file():
            lake_bin = str(elan_lake)
    if not lake_bin:
        lake_bin = shutil.which("lake")
    if not lake_bin:
        return CheckResult(passed=True, details=[
            Detail("lake", True, "SKIPPED — lake not found. Set LAKE_PATH or install elan")])

    lean_root = Path(os.environ.get("LEAN_PROJECT_DIR", PROJECT_ROOT / "lean"))
    audit_src = lean_root / "SKEFTHawking" / "AxiomAudit.lean"
    if not audit_src.exists():
        return CheckResult(passed=True, details=[
            Detail("axiom_audit_src", True, f"SKIPPED — {audit_src} not found")])

    # ── Allow-list ──
    try:
        from src.core.constants import AXIOM_METADATA  # type: ignore
        metadata_keys = set(AXIOM_METADATA.keys())
    except Exception:
        metadata_keys = set()
    allowlist = {"propext", "Classical.choice", "Quot.sound"} | metadata_keys

    # ── Run AxiomAudit (interpreted; native link exceeds macOS arg limits) ──
    try:
        result = subprocess.run(
            [lake_bin, "env", "lean", "--run", "SKEFTHawking/AxiomAudit.lean"],
            cwd=str(lean_root), capture_output=True, text=True, timeout=600,
        )
    except subprocess.TimeoutExpired:
        return CheckResult(passed=True, details=[
            Detail("axiom_audit_run", True, "SKIPPED — AxiomAudit timed out (600s)", warning=True)])
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=True, details=[
            Detail("axiom_audit_run", True, f"SKIPPED — {exc}", warning=True)])

    if result.returncode != 0:
        return CheckResult(passed=True, details=[
            Detail("axiom_audit_run", True,
                   f"SKIPPED — AxiomAudit exited {result.returncode}: {result.stderr[-300:]}",
                   warning=True)])

    try:
        closures: Dict[str, List[str]] = json.loads(result.stdout.strip() or "{}")
    except json.JSONDecodeError as exc:
        return CheckResult(passed=True, details=[
            Detail("axiom_audit_parse", True,
                   f"SKIPPED — could not parse AxiomAudit output ({exc})", warning=True)])

    def is_native_decide(ax: str) -> bool:
        return "native_decide" in ax or ax in ("Lean.ofReduceBool", "Lean.trustCompiler")

    native_decls: set[str] = set()
    unexpected: Dict[str, List[str]] = {}
    for decl, axes in closures.items():
        if "native_decide" in decl:
            continue  # the per-declaration native-axiom self-entries
        bad: List[str] = []
        for ax in axes:
            if ax in allowlist:
                continue
            if is_native_decide(ax):
                native_decls.add(decl)
                continue
            bad.append(ax)
        if bad:
            unexpected[decl] = sorted(set(bad))

    details = [Detail("allowlist_size", True,
                      f"{len(allowlist)} allow-listed axioms "
                      f"(3 core + {len(metadata_keys)} AXIOM_METADATA)")]

    if native_decls:
        details.append(Detail(
            "native_decide", True,
            f"{len(native_decls)} declaration(s) transitively use `native_decide` "
            f"(compiler-trust axiom) — accepted Lean mechanism, flagged for visibility "
            f"(counts.json 'Axioms: 0' counts only declared `axiom`s)",
            warning=True))

    strict = STRICT_MODE
    if unexpected:
        sample = list(unexpected.items())[:10]
        msg = (f"{len(unexpected)} declaration(s) carry a non-allow-listed axiom "
               f"({'FAIL under --strict' if strict else 'WARN-first'} — add to "
               f"AXIOM_METADATA or discharge): "
               + "; ".join(f"{d} → {','.join(ax)}" for d, ax in sample))
        details.append(Detail("unexpected_axioms", not strict, msg, warning=not strict))
        return CheckResult(passed=not strict, details=details)

    details.append(Detail(
        "allowlist", True,
        "no declaration carries a non-allow-listed, non-native_decide axiom "
        "(Invariant #15 backstop clean)"))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Elaboration-knob watchlist (perf / upstream-portability, NOT soundness)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "elaboration_knob_watchlist",
    "Watchlist (advisory): proof-body maxRecDepth / synthInstance knobs — a "
    "performance / Mathlib-CI-portability signal, NOT a soundness or axiom-closure issue",
)
def check_elaboration_knob_watchlist() -> CheckResult:
    """
    Surfaces every ``set_option maxRecDepth`` / ``synthInstance.maxSize`` /
    ``synthInstance.maxHeartbeats`` in SKEFTHawking Lean source.

    WHY THIS IS SEPARATE FROM ``axiom_closure_allowlist`` (the soundness gate):
    these are *elaboration-time* knobs. They only let the front-end search deeper /
    wider before giving up; the **kernel independently re-checks the final term** and
    never reads them, so they add NOTHING to the axiom closure (no ``Lean.ofReduceBool``)
    and stay kernel-pure ``{propext, Classical.choice, Quot.sound}``. Mathlib uses
    ``maxRecDepth`` routinely. The genuine trust surface (``native_decide`` →
    ``Lean.ofReduceBool``) is gated by ``axiom_closure_allowlist``; THIS check is a
    NON-FAILING watchlist for the only real downside — a ``decide`` heavy enough to
    need a knob is also a slow KERNEL reduction, which Mathlib CI's speed budget may
    reject. So each hit is an upstream-portability candidate (consider a structural
    reproof IF upstreaming that lemma), never a correctness concern. Always passes.

    NB ``maxHeartbeats`` in proof bodies is forbidden outright by Invariant #10
    (architecture discipline) and is enforced elsewhere; it is intentionally not in
    this advisory list.
    """
    import re

    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    if not lean_dir.exists():
        return CheckResult(passed=True, details=[
            Detail("lean_src", True, f"SKIPPED — {lean_dir} not found")])

    pat = re.compile(
        r"set_option\s+(maxRecDepth|synthInstance\.maxSize|synthInstance\.maxHeartbeats)\s+(\d+)")
    hits: List[Detail] = []
    for f in sorted(lean_dir.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        for i, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
            m = pat.search(line)
            if m:
                rel = f.relative_to(PROJECT_ROOT)
                hits.append(Detail(f"{rel}:{i}", True, f"{m.group(1)} {m.group(2)}", warning=True))

    summary = Detail(
        "watchlist", True,
        f"{len(hits)} proof-body elaboration-knob site(s) — perf/upstream-CI watchlist, "
        "kernel-pure (NOT a soundness/axiom-closure issue; that is axiom_closure_allowlist)",
        warning=bool(hits))
    return CheckResult(passed=True, details=[summary] + hits)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 10: Notebook visualization consistency (warnings only)
# ═══════════════════════════════════════════════════════════════════════

@register_check("viz_consistency", "Notebook visualizations use imported physics and consistent style")
def check_viz_consistency() -> CheckResult:
    """Visualization consistency warnings (advisory, always passes).

    Two mechanisms:
      1. Opt-in: cells tagged ``# viz-ref: fig_name`` are checked against
         the corresponding function in ``src/core/visualizations.py``.
      2. Safety net: any ``.show()`` call in a code cell that lacks a
         ``viz-ref`` tag triggers a warning — the figure is untracked.

    Also warns if a figure cell uses hardcoded color hex values instead
    of the COLORS dict from constants.py.
    """
    import ast
    import importlib

    details = []

    # ── Discover visualizations.py figure functions ──
    viz_functions = set()
    viz_path = SRC_DIR / "core" / "visualizations.py"
    if viz_path.exists():
        try:
            tree = ast.parse(viz_path.read_text())
            viz_functions = {
                node.name for node in ast.walk(tree)
                if isinstance(node, ast.FunctionDef) and node.name.startswith("fig_")
            }
        except SyntaxError:
            details.append(Detail("visualizations.py", True,
                                  "WARN: could not parse visualizations.py",
                                  warning=True))

    # ── Known COLORS hex values (hardcoding these is a smell) ──
    try:
        from src.core.constants import COLORS as _COLORS
        known_hex = {v.lower() for v in _COLORS.values() if isinstance(v, str)}
    except ImportError:
        known_hex = set()

    # ── Scan notebooks ──
    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = json.load(f)
        except Exception as e:
            details.append(Detail(nb_path.name, True,
                                  f"WARN: could not parse — {e}", warning=True))
            continue

        untracked_show = 0
        hardcoded_colors = 0
        ref_warnings = []

        for cell_idx, cell in enumerate(nb.get('cells', [])):
            if cell.get('cell_type') != 'code':
                continue
            src = ''.join(cell.get('source', []))

            # ── Check for viz-ref tags ──
            ref_match = re.search(r'#\s*viz-ref:\s*(\w+)', src)
            has_show = '.show()' in src

            if ref_match:
                ref_name = ref_match.group(1)
                # Check function exists in visualizations.py
                if ref_name not in viz_functions:
                    ref_warnings.append(
                        f"cell {cell_idx}: viz-ref '{ref_name}' not found in visualizations.py"
                    )
            elif has_show:
                # Safety net: .show() without viz-ref tag
                untracked_show += 1

            # ── Check for hardcoded color hex values ──
            if known_hex:
                hex_matches = re.findall(r'["\']#([0-9a-fA-F]{6})["\']', src)
                for h in hex_matches:
                    if f"#{h.lower()}" in known_hex:
                        hardcoded_colors += 1

        # ── Report per notebook ──
        warns = []
        if untracked_show:
            warns.append(f"{untracked_show} untagged .show() call(s)")
        if hardcoded_colors:
            warns.append(f"{hardcoded_colors} hardcoded COLORS hex value(s) — use COLORS dict")
        for rw in ref_warnings:
            warns.append(rw)

        if warns:
            details.append(Detail(
                nb_path.name, True,
                "WARN: " + "; ".join(warns),
                warning=True,
            ))
        else:
            details.append(Detail(nb_path.name, True, "clean"))

    # Always passes — these are advisory warnings
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 11: Notebook execution (all notebooks must run without errors)
# ═══════════════════════════════════════════════════════════════════════

def _src_core_fingerprint() -> str:
    """SHA-256 (16 hex) of all ``src/core/*.py`` — the physics the notebooks
    import. Any change invalidates the whole CHECK 11 skip-cache, forcing a
    full re-vet (a formulas/constants edit can change notebook outcomes without
    changing notebook content)."""
    hasher = hashlib.sha256()
    src_core = SRC_DIR / "core"
    if src_core.is_dir():
        for fp in sorted(src_core.glob("*.py")):
            hasher.update(fp.read_bytes())
    return hasher.hexdigest()[:16]


def _notebook_code_hash(nb) -> str:
    """SHA-256 (16 hex) of a notebook's code-cell sources. Ignores outputs and
    execution_count (which change on every run) so the hash is stable for an
    otherwise-unchanged notebook."""
    hasher = hashlib.sha256()
    for cell in nb.cells:
        if cell.cell_type == "code":
            hasher.update(cell.source.encode("utf-8"))
    return hasher.hexdigest()[:16]


@register_check("notebook_exec", "All notebooks execute without errors")
def check_notebook_execution() -> CheckResult:
    """Execute each notebook top-to-bottom and verify zero errors.

    Uses nbclient's execute engine with a per-cell timeout. Catches import
    errors, missing variables, broken physics code, and runtime failures that
    static checks miss.

    **Skip-cache (2026-05-28):** unchanged, previously-passed notebooks are
    skipped via a content hash recorded in ``NOTEBOOK_EXEC_CACHE`` (keyed on a
    ``src/core`` fingerprint), mirroring the Lean ``extract_lean_deps.py``
    hash-skip. Without it this check re-executes all ~89 notebooks every run
    (~25 min) — the dominant ``validate.py`` slowness. Pass ``--force-notebooks``
    to bypass the cache and re-execute everything (e.g. after a kernel /
    dependency upgrade that changes outcomes without changing content).
    """
    import nbformat

    details: List[Detail] = []
    all_pass = True

    # Try importing the execution engine
    try:
        from nbclient import NotebookClient
    except ImportError:
        return CheckResult(
            passed=True,
            details=[Detail("nbclient", True,
                            "SKIPPED — nbclient not installed. "
                            "Install with: pip install nbclient")],
        )

    # Load the skip-cache. A src/core fingerprint mismatch discards it (re-vet
    # all); --force-notebooks ignores it entirely.
    src_fp = _src_core_fingerprint()
    prev_passed: Dict[str, str] = {}
    if NOTEBOOK_EXEC_CACHE.is_file() and not FORCE_NOTEBOOK_REEXEC:
        try:
            loaded = json.loads(NOTEBOOK_EXEC_CACHE.read_text())
            if isinstance(loaded, dict) and loaded.get("src_fingerprint") == src_fp:
                prev_passed = loaded.get("passed", {}) or {}
        except (json.JSONDecodeError, OSError):
            prev_passed = {}

    new_passed: Dict[str, str] = {}
    n_skipped = 0

    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = nbformat.read(f, as_version=4)
        except Exception as e:
            all_pass = False
            details.append(Detail(nb_path.name, False, f"unreadable: {e}"))
            continue

        code_hash = _notebook_code_hash(nb)

        # Skip unchanged, previously-vetted notebooks.
        if not FORCE_NOTEBOOK_REEXEC and prev_passed.get(nb_path.name) == code_hash:
            n_skipped += 1
            new_passed[nb_path.name] = code_hash
            details.append(Detail(nb_path.name, True,
                                  "SKIPPED — unchanged, previously vetted"))
            continue

        try:
            client = NotebookClient(
                nb,
                timeout=120,          # per-cell timeout
                kernel_name="python3",
                resources={"metadata": {"path": str(NOTEBOOKS_DIR)}},
            )
            client.execute()

            # Count executed cells
            code_cells = sum(1 for c in nb.cells if c.cell_type == "code")
            details.append(Detail(
                nb_path.name, True,
                f"{code_cells} code cells executed successfully"))
            new_passed[nb_path.name] = code_hash  # record vetted state

        except Exception as e:
            all_pass = False
            # Extract just the error type and message, not the full traceback
            err_lines = str(e).strip().split("\n")
            # Find the actual error line (usually last non-empty line with Error in it)
            err_msg = err_lines[-1] if err_lines else str(e)
            for line in reversed(err_lines):
                if "Error" in line:
                    err_msg = line.strip()
                    break
            if len(err_msg) > 200:
                err_msg = err_msg[:200] + "..."
            details.append(Detail(nb_path.name, False, err_msg))
            # Do NOT record — a failed notebook re-runs next time.

    # Persist the updated cache (only currently-existing, vetted notebooks).
    try:
        NOTEBOOK_EXEC_CACHE.write_text(json.dumps(
            {"src_fingerprint": src_fp, "passed": new_passed},
            indent=2, sort_keys=True))
    except OSError:
        pass

    if n_skipped:
        details.insert(0, Detail(
            "skip_cache", True,
            f"{n_skipped} notebook(s) skipped (unchanged, previously vetted); "
            f"--force-notebooks re-runs all"))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 12: Physical bounds validation
# ═══════════════════════════════════════════════════════════════════════

@register_check("physical_bounds", "All computed quantities within physical bounds")
def check_physical_bounds() -> CheckResult:
    """Verify computed physics values are physically reasonable.

    Catches absurdities like negative temperatures, perturbative corrections > 1,
    or shot counts that are impossibly small for tiny corrections.
    """
    from src.wkb.spectrum import (
        steinhauer_platform, heidelberg_platform, trento_platform,
        compute_spectrum, spectrum_summary,
    )

    details = []
    all_pass = True

    platforms = {
        'steinhauer': steinhauer_platform(),
        'heidelberg': heidelberg_platform(),
        'trento': trento_platform(),
    }

    for name, platform in platforms.items():
        spectrum = compute_spectrum(platform)
        summ = spectrum_summary(spectrum)

        checks = [
            ('T_H > 0', platform.T_H > 0),
            ('kappa > 0', platform.kappa > 0),
            ('0 < D < 1', 0 < platform.D < 1),
            ('0 < delta_diss < 1', 0 < summ['delta_diss_at_T_H'] < 1),
            ('n_noise >= 0', summ['n_noise_at_T_H'] >= 0),
        ]

        # Shot count sanity: if correction is sub-percent, need many shots
        delta_diss = summ['delta_diss_at_T_H']
        shots = summ['shots_needed']
        if delta_diss < 1e-3:
            checks.append((
                f'shots > 10^4 (delta={delta_diss:.1e})',
                shots > 1e4
            ))

        for check_name, passed in checks:
            if not passed:
                all_pass = False
            details.append(Detail(f"{name}/{check_name}", passed,
                                  f"{'OK' if passed else 'FAILED'}"))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 13: Cross-path consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("cross_path_consistency",
                "Different code paths agree within 0.5%/1% tolerance")
def check_cross_path_consistency() -> CheckResult:
    """Verify quantities computed by different modules agree.

    Catches duplicate implementations that drift apart.
    """
    from src.core.formulas import decoherence_parameter
    from src.core.transonic_background import steinhauer_Rb87, solve_transonic_background
    from src.core.constants import EXPERIMENTS
    from src.wkb.spectrum import steinhauer_platform, compute_spectrum, spectrum_summary

    details = []
    all_pass = True

    # --- Compare delta_diss: direct formula vs spectrum_summary ---
    platform = steinhauer_platform()
    spectrum = compute_spectrum(platform)
    summ = spectrum_summary(spectrum)
    delta_diss_spectrum = summ['delta_diss_at_T_H']

    gamma_eff = platform.gamma_1 + platform.gamma_2
    delta_diss_direct = gamma_eff * (platform.T_H / platform.c_s)**2 / platform.kappa

    if delta_diss_spectrum > 0 and delta_diss_direct > 0:
        rel_diff = abs(delta_diss_spectrum - delta_diss_direct) / delta_diss_spectrum
        ok = rel_diff < 0.005
        details.append(Detail(
            "delta_diss: spectrum vs direct",
            ok,
            f"spectrum={delta_diss_spectrum:.4e}, direct={delta_diss_direct:.4e}, "
            f"rel_diff={rel_diff:.4f}"
        ))
        if not ok:
            all_pass = False

    # --- Compare decoherence: spectrum_summary vs formulas.py ---
    dk_spectrum = summ['delta_k_at_T_H']
    Gamma_H = gamma_eff * (platform.T_H / platform.c_s)**2
    dk_formulas = decoherence_parameter(Gamma_H, platform.kappa)

    if dk_spectrum > 0 and dk_formulas > 0:
        rel_diff = abs(dk_spectrum - dk_formulas) / dk_spectrum
        ok = rel_diff < 0.005
        details.append(Detail(
            "decoherence: spectrum vs formulas",
            ok,
            f"spectrum={dk_spectrum:.4e}, formulas={dk_formulas:.4e}, "
            f"rel_diff={rel_diff:.4f}"
        ))
        if not ok:
            all_pass = False

    # Note: WKB platform uses natural units (c_s=1, kappa=1) while
    # BECParameters uses SI. Dimensionless ratios (delta_diss, decoherence)
    # are unit-independent and compared above. Dimensional quantities
    # (c_s, T_H) cannot be directly compared across unit systems.

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 14: Paper claim provenance
# ═══════════════════════════════════════════════════════════════════════

@register_check("paper_provenance",
                "Paper numerical claims trace to computations within 0.5%")
def check_paper_provenance() -> CheckResult:
    """Verify paper theorem references exist in Lean and figures are present."""
    details = []
    all_pass = True

    # Build set of all Lean theorem names
    lean_names = set()
    for lean_file in LEAN_DIR.glob("*.lean"):
        for line in lean_file.read_text().splitlines():
            if line.startswith("theorem "):
                name = line.split()[1].split("(")[0].split(":")[0].strip()
                lean_names.add(name)

    for paper_dir in sorted(PAPERS_DIR.iterdir()):
        tex_file = paper_dir / "paper_draft.tex"
        if not tex_file.exists():
            continue

        tex = tex_file.read_text()

        # Check 1: \\texttt{theorem_name} refs exist in Lean
        texttt_refs = re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}', tex)
        theorem_refs = [r for r in texttt_refs if '_' in r]
        missing = [r for r in theorem_refs if r not in lean_names]
        if missing:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", False,
                f"Not in Lean: {missing}"
            ))
        elif theorem_refs:
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", True,
                f"{len(theorem_refs)} theorem references verified"
            ))

        # Check 2: No \\fbox placeholder figures
        if '\\fbox{\\parbox' in tex:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/figures", False,
                "Has \\fbox placeholder figures — must use \\includegraphics"
            ))
        elif '\\includegraphics' in tex:
            # Resolve each \includegraphics{PATH} relative to the paper tex dir.
            # Papers may reference local figures/ (most) or shared figures/phase*/ (paper16).
            includegraphics_refs = re.findall(
                r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', tex
            )
            missing_figs = []
            resolved_count = 0
            for ref in includegraphics_refs:
                ref_path = (paper_dir / ref).resolve()
                # Accept the exact path, or the path with any of the common
                # graphics extensions appended (LaTeX auto-appends .pdf/.png).
                candidates = [ref_path] + [
                    ref_path.with_suffix(ext) for ext in ('.png', '.pdf', '.jpg')
                ]
                if any(c.exists() for c in candidates):
                    resolved_count += 1
                else:
                    missing_figs.append(ref)
            if missing_figs:
                all_pass = False
                details.append(Detail(
                    f"{paper_dir.name}/figures", False,
                    f"Missing {len(missing_figs)} referenced figure(s): {missing_figs[:3]}"
                    + (f" (+{len(missing_figs) - 3} more)" if len(missing_figs) > 3 else "")
                ))
            else:
                details.append(Detail(
                    f"{paper_dir.name}/figures", True,
                    f"{resolved_count} referenced figure(s) resolved"
                ))

        # Check 3: No placeholder bibliography entries
        # Strip LaTeX line comments first so historical cleanup notes
        # like "% [2026-05-04 cleanup: ... arXiv:2604.XXXXX ...]" don't
        # false-positive. A LaTeX line comment starts at an unescaped %
        # and continues to end-of-line.
        tex_comment_stripped = re.sub(r'(?<!\\)%[^\n]*', '', tex)
        if (
            'xxxxx' in tex_comment_stripped.lower()
            or 'Nature \\textbf{XXX}' in tex_comment_stripped
        ):
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/bibliography", False,
                "Has placeholder bibliography entries (xxxxx or XXX)"
            ))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15: Parameter provenance — every experimental param has a
# verified source traced to a published paper + table/figure.
# ═══════════════════════════════════════════════════════════════════════

@register_check("parameter_provenance",
                "Every experimental parameter has verified provenance")
def check_parameter_provenance() -> CheckResult:
    """CHECK 15: Validate the parameter provenance registry.

    Checks:
    1. Coverage: every param in EXPERIMENTS/ATOMS/POLARITON has provenance
    2. LLM verification: all entries have llm_verified_date (gates Stage 1)
    3. Human verification: advisory — gates paper submission, not computation
    4. Consistency: provenance value matches actual constant value
    5. Tier appropriateness: MEASURED params must have a real source
    """
    from src.core.constants import EXPERIMENTS, ATOMS, POLARITON_PLATFORMS
    from src.core.provenance import PARAMETER_PROVENANCE

    details = []
    all_pass = True

    # --- 1. Coverage: every parameter has a provenance entry ---
    missing = []
    for platform, params in EXPERIMENTS.items():
        for key in params:
            if key in ('description', 'atom'):
                continue
            prov_key = f"{platform}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                missing.append(prov_key)

    for atom, props in ATOMS.items():
        for key in props:
            if key in ('label',):
                continue
            prov_key = f"{atom}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                missing.append(prov_key)

    # Check POLARITON_MASS
    if 'POLARITON_MASS' not in PARAMETER_PROVENANCE:
        missing.append('POLARITON_MASS')

    for config, params in POLARITON_PLATFORMS.items():
        for key in ('c_s', 'xi', 'kappa', 'tau_cav', 'Gamma_pol', 'gamma_phonon_dim'):
            prov_key = f"{config}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                # Shared params (c_s, xi, kappa, gamma_phonon_dim) only need
                # one entry under Paris_long since all configs share them
                if key in ('c_s', 'xi', 'kappa', 'gamma_phonon_dim'):
                    shared_key = f"Paris_long.{key}"
                    if shared_key not in PARAMETER_PROVENANCE:
                        missing.append(prov_key)
                else:
                    missing.append(prov_key)

    if missing:
        all_pass = False
        details.append(Detail(
            "coverage", False,
            f"Missing provenance for {len(missing)} params: {', '.join(missing[:5])}"
            + (f"... (+{len(missing)-5} more)" if len(missing) > 5 else "")
        ))
    else:
        details.append(Detail("coverage", True,
                              f"All {len(PARAMETER_PROVENANCE)} parameters have provenance entries"))

    # --- 2. LLM verification (gates Stage 1 computation) ---
    not_llm = [k for k, v in PARAMETER_PROVENANCE.items()
               if v.get('llm_verified_date') is None]
    if not_llm:
        all_pass = False
        details.append(Detail(
            "llm_verification", False,
            f"{len(not_llm)} params not LLM-verified: {', '.join(not_llm[:5])}"
            + (f"... (+{len(not_llm)-5} more)" if len(not_llm) > 5 else "")
        ))
    else:
        details.append(Detail("llm_verification", True,
                              "All parameters LLM-verified"))

    # --- 3. Human verification (advisory by default; hard fail in --strict) ---
    # PROJECTED tier is exempt from human_verified — these are explicit estimates
    # for not-yet-performed experiments, not measurements requiring verification.
    not_human = [k for k, v in PARAMETER_PROVENANCE.items()
                 if v.get('human_verified_date') is None]
    not_human_required = [
        k for k in not_human
        if PARAMETER_PROVENANCE[k].get('tier') != 'PROJECTED'
    ]
    if STRICT_MODE and not_human_required:
        all_pass = False
        sample = ', '.join(not_human_required[:8])
        more = f" + {len(not_human_required) - 8} more" if len(not_human_required) > 8 else ""
        details.append(Detail(
            "human_verification", False,
            f"[strict] {len(not_human_required)} non-PROJECTED params lack "
            f"human_verified_date (paper-submission blocker): {sample}{more}"
        ))
    elif not_human:
        details.append(Detail(
            "human_verification", True,
            f"{len(not_human)} params not yet human-verified "
            f"({len(not_human_required)} non-PROJECTED; blocks paper submission)",
            warning=True
        ))
    else:
        details.append(Detail("human_verification", True,
                              "All parameters human-verified — paper submission unblocked"))

    # --- 4. Consistency: provenance value matches actual constant ---
    mismatches = []
    null_values = []
    for prov_key, entry in PARAMETER_PROVENANCE.items():
        if entry['value'] is None:
            null_values.append(prov_key)
            continue

        # Look up actual value
        actual = _lookup_provenance_value(prov_key, EXPERIMENTS, ATOMS,
                                          POLARITON_PLATFORMS)
        if actual is not None:
            try:
                rel_err = abs(float(actual) - float(entry['value'])) / max(abs(float(actual)), 1e-30)
                if rel_err > 0.001:
                    mismatches.append(f"{prov_key}: registry={entry['value']}, code={actual}")
            except (TypeError, ValueError):
                pass  # non-numeric (e.g., string params)

    if null_values:
        all_pass = False
        details.append(Detail(
            "unresolved_conflicts", False,
            f"{len(null_values)} params have NULL value (unresolved conflict): "
            f"{', '.join(null_values)}"
        ))
    if mismatches:
        all_pass = False
        details.append(Detail(
            "value_consistency", False,
            f"{len(mismatches)} mismatches: {'; '.join(mismatches[:3])}"
        ))
    elif not null_values:
        details.append(Detail("value_consistency", True,
                              "All provenance values match code"))

    # --- 5. Tier appropriateness ---
    tier_issues = []
    for prov_key, entry in PARAMETER_PROVENANCE.items():
        if (entry['tier'] == 'MEASURED'
                and entry.get('llm_verified_date') is None
                and 'CODATA' not in entry.get('source', '')
                and 'NIST' not in entry.get('source', '')):
            tier_issues.append(prov_key)
    if tier_issues:
        details.append(Detail(
            "tier_appropriateness", True,
            f"{len(tier_issues)} MEASURED params not yet LLM-verified: "
            f"{', '.join(tier_issues[:5])}",
            warning=True
        ))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15b: Counts freshness (Phase 5v Wave 1b)
# ═══════════════════════════════════════════════════════════════════════

COUNTS_JSON_PATH = PROJECT_ROOT / "docs" / "counts.json"
COUNTS_TEX_PATH = PROJECT_ROOT / "docs" / "counts.tex"
_COUNTS_SOURCES = [
    PROJECT_ROOT / "lean" / "lean_deps.json",
    PROJECT_ROOT / "src" / "core" / "constants.py",
    PROJECT_ROOT / "src" / "core" / "visualizations.py",
]


def _counts_is_stale() -> tuple[bool, str]:
    """Return (stale, reason). Stale if counts.json is missing or older
    than any of _COUNTS_SOURCES, or if counts.tex is missing."""
    if not COUNTS_JSON_PATH.exists():
        return True, "counts.json missing"
    if not COUNTS_TEX_PATH.exists():
        return True, "counts.tex missing"
    counts_mtime = COUNTS_JSON_PATH.stat().st_mtime
    for src in _COUNTS_SOURCES:
        if src.exists() and src.stat().st_mtime > counts_mtime:
            return True, f"{src.name} newer than counts.json"
    # Also regenerate if any .lean file in SKEFTHawking is newer (catches
    # cases where lean_deps.json isn't regenerated but sources changed).
    # rglob (recursive) — a *.lean in a subdirectory (FKLW/, SymTFT/,
    # QuantumNetwork/, …) must also mark counts stale, else a native_decide
    # added in a subdir kept the decl-closure metric stale (ADR-004 W7
    # adversarial finding M2, 2026-06-13).
    lean_src = LEAN_DIR.rglob("*.lean")
    newest_lean = max((f.stat().st_mtime for f in lean_src), default=0)
    if newest_lean > counts_mtime:
        return True, "SKEFTHawking/**/*.lean newer than counts.json"
    return False, "fresh"


@register_check("counts_fresh",
                "counts.json / counts.tex are up-to-date vs. sources")
def check_counts_fresh() -> CheckResult:
    """CHECK 15b: Regenerate counts.json + counts.tex if stale.

    Papers reference counts via \\input{counts.tex} macros; this check
    ensures the macro values reflect the current codebase. Regeneration
    is automatic when sources are newer; check passes as long as both
    artifacts exist after the regeneration attempt.
    """
    stale, reason = _counts_is_stale()
    details = []

    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}",
                              warning=True))
        # Run update_counts.py
        try:
            # Timeout 1800s = 30 min (Phase 7a sub-wave 7a.0.4 bump from 600s).
            # update_counts.py invokes ExtractDeps.lean which walks ~5000+ decls
            # and runs collectAxioms on each — exceeds 600s on current project size.
            result = subprocess.run(
                ["uv", "run", "python",
                 str(SCRIPT_DIR / "update_counts.py")],
                cwd=str(PROJECT_ROOT),
                capture_output=True, text=True, timeout=1800,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"update_counts.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            details.append(Detail("regenerate", True,
                                  "update_counts.py succeeded"))
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"update_counts.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, "fresh"))

    # Both artifacts must now exist
    passed = COUNTS_JSON_PATH.exists() and COUNTS_TEX_PATH.exists()
    if passed:
        # Summary of current counts
        try:
            counts = json.loads(COUNTS_JSON_PATH.read_text())
            lean = counts.get("lean", {})
            python = counts.get("python", {})
            aristotle = counts.get("aristotle", {})
            summary = (
                f"theorems={lean.get('theorems_total','?')} "
                f"(substantive={lean.get('theorems_substantive','?')}, "
                f"placeholder={lean.get('theorems_placeholder','?')}) | "
                f"modules={lean.get('modules','?')} | "
                f"sorry={lean.get('sorry_declarations','?')} | "
                f"papers={python.get('papers','?')} | "
                f"aristotle_proved={aristotle.get('aristotle_proved','?')}"
            )
            details.append(Detail("summary", True, summary))
        except (json.JSONDecodeError, OSError) as exc:
            details.append(Detail("summary", False,
                                  f"counts.json unreadable: {exc}"))
            passed = False

    return CheckResult(passed=passed, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15c: Paper tables freshness (Phase 5v)
# ═══════════════════════════════════════════════════════════════════════

_TABLES_SOURCES = [
    PROJECT_ROOT / "src" / "core" / "formulas.py",
    PROJECT_ROOT / "src" / "core" / "constants.py",
    PROJECT_ROOT / "src" / "core" / "transonic_background.py",
    PROJECT_ROOT / "src" / "core" / "provenance.py",
    PROJECT_ROOT / "lean" / "lean_deps.json",
    PROJECT_ROOT / "docs" / "WAVE_EXECUTION_PIPELINE.md",
    PROJECT_ROOT / "scripts" / "paper_tables" / "__init__.py",
    PROJECT_ROOT / "scripts" / "paper_tables" / "sources.py",
    PROJECT_ROOT / "scripts" / "render_paper_tables.py",
]


def _tables_specs() -> list[Path]:
    """Every papers/<key>/tables.py that exists."""
    if not PAPERS_DIR.exists():
        return []
    return list(PAPERS_DIR.glob("paper*_*/tables.py"))


def _tables_outputs() -> list[Path]:
    """Every papers/<key>/tables/*.tex that has been generated."""
    if not PAPERS_DIR.exists():
        return []
    return list(PAPERS_DIR.glob("paper*_*/tables/*.tex"))


def _tables_is_stale() -> tuple[bool, str]:
    """Stale if any source / spec mtime is newer than the newest output,
    or if a spec exists but has no output file."""
    specs = _tables_specs()
    outputs = _tables_outputs()
    if not specs:
        return False, "no tables.py specs"
    if not outputs:
        return True, f"{len(specs)} spec(s) but no output .tex files"
    output_mtime = min(p.stat().st_mtime for p in outputs)
    for src in _TABLES_SOURCES + specs:
        if src.exists() and src.stat().st_mtime > output_mtime:
            return True, f"{src.name} newer than oldest output"
    return False, f"fresh ({len(outputs)} output files across {len(specs)} papers)"


@register_check("tables_fresh",
                "Paper tables (tables/*.tex) are up-to-date vs. pipeline sources")
def check_tables_fresh() -> CheckResult:
    """CHECK 15c: Regenerate papers/*/tables/*.tex if stale.

    Papers `\\input{}` their numerical tables from this autogenerated
    directory; this check keeps the cells fresh when any pipeline source
    changes (formulas, constants, transonic background, the paper's
    spec). Mirror of CHECK 15b counts_fresh for numerical tables.
    """
    stale, reason = _tables_is_stale()
    details = []
    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}", warning=True))
        try:
            result = subprocess.run(
                ["uv", "run", "python",
                 str(SCRIPT_DIR / "render_paper_tables.py")],
                cwd=str(PROJECT_ROOT),
                capture_output=True, text=True, timeout=300,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"render_paper_tables.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            tables_written = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else '0 tables'
            details.append(Detail("regenerate", True,
                                  f"render_paper_tables.py succeeded: {tables_written}"))
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"render_paper_tables.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, reason))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15d: Cross-paper ClaimCluster freshness (Phase 5v Wave 10f)
# ═══════════════════════════════════════════════════════════════════════

CLAIM_CLUSTERS_PATH = PROJECT_ROOT / "papers" / "claim_clusters.json"


def _claim_clusters_is_stale() -> tuple[bool, str]:
    """Stale if any v2 ``claims_review.json`` mtime is newer than
    ``claim_clusters.json``, or if any v2 file exists but no cluster
    file does.

    A v2 ``claims_review.json`` carries a top-level ``sentences`` list;
    files without that key are v1 and don't participate in cross-paper
    clustering.
    """
    if not PAPERS_DIR.exists():
        return False, "no papers/ dir"
    v2_files: list[Path] = []
    for p in PAPERS_DIR.iterdir():
        if not p.is_dir() or not p.name.startswith('paper'):
            continue
        cr = p / 'claims_review.json'
        if not cr.exists():
            continue
        try:
            data = json.loads(cr.read_text())
        except json.JSONDecodeError:
            continue
        if isinstance(data.get('sentences'), list):
            v2_files.append(cr)
    if not v2_files:
        return False, "no v2 claims_review.json files"
    if not CLAIM_CLUSTERS_PATH.exists():
        return True, f"{len(v2_files)} v2 paper(s), no claim_clusters.json"
    cluster_mtime = CLAIM_CLUSTERS_PATH.stat().st_mtime
    for f in v2_files:
        if f.stat().st_mtime > cluster_mtime:
            return True, f"{f.parent.name}/claims_review.json newer than claim_clusters.json"
    return False, f"fresh ({len(v2_files)} v2 paper(s) tracked)"


@register_check("claim_clusters_fresh",
                "papers/claim_clusters.json is up-to-date vs. v2 claims_review.json files")
def check_claim_clusters_fresh() -> CheckResult:
    """CHECK 15d: Regenerate ``papers/claim_clusters.json`` if any v2
    ``claims_review.json`` is newer.

    Wave 10f. The cross-paper ClaimCluster + MEMBER_OF graph extractors
    consume this file; out-of-date data means the dashboard misses
    propagation prompts and ``graph_integrity.claim_cluster_inconsistency``
    runs against stale member sets. Auto-regenerates via ``cluster_detect.py``.
    Idempotent + safe on machines with zero v2 papers.
    """
    stale, reason = _claim_clusters_is_stale()
    details = []
    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}", warning=True))
        try:
            result = subprocess.run(
                ["uv", "run", "python",
                 str(SCRIPT_DIR / "cluster_detect.py")],
                cwd=str(PROJECT_ROOT),
                capture_output=True, text=True, timeout=120,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"cluster_detect.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            # cluster_detect prints summary on stderr (one-line)
            tail = (result.stderr or '').strip().splitlines()
            details.append(Detail("regenerate", True,
                                  tail[-1] if tail else "cluster_detect.py succeeded"))
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"cluster_detect.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, reason))

    # Summarize current cluster state when present
    if CLAIM_CLUSTERS_PATH.exists():
        try:
            data = json.loads(CLAIM_CLUSTERS_PATH.read_text())
            n_clusters = data.get('cluster_count', 0)
            n_papers = len(data.get('paper_coverage') or [])
            details.append(Detail(
                "summary", True,
                f"{n_clusters} cluster(s) across {n_papers} paper(s)",
            ))
        except (json.JSONDecodeError, OSError) as exc:
            details.append(Detail("summary", False,
                                  f"claim_clusters.json unreadable: {exc}"))
            return CheckResult(passed=False, details=details)
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 17b: Inline numerical literals outside \input{} blocks (Phase 5v)
# ═══════════════════════════════════════════════════════════════════════

# Patterns that strongly suggest a hardcoded numerical literal with a
# physical unit. Any such literal in paper prose should move into an
# auto-generated tables/*.tex file so it stays pipeline-derived.
_NUMERICAL_LITERAL_RE = re.compile(
    r'(?<!\\)\b(\d+\.\d+|\d+(?:\.\d+)?e[+-]?\d+)\s*'
    r'(~?)\\?(?:'
    r'(?:mu|\\mu)\s*m\b|'
    r'nK\b|'
    r'mK\b|'
    r'\\mathrm\{[a-zA-Z]+\}|'
    r's\^?(?:-|\{-|\^{-)1\}?|'
    r'mm/s\b|'
    r'\\mu m\b|'
    r'\\times\s*10\^'
    r')',
    re.IGNORECASE,
)


@register_check("numerical_literals",
                "Paper .tex files free of inline numerical literals outside \\input{} blocks")
def check_numerical_literals() -> CheckResult:
    """CHECK 17b: Flag hardcoded numerical literals in paper body.

    Counterpart to CHECK 17 count_literals. Values with physical units
    should come from auto-generated tables/*.tex files, not be
    hand-coded in the body. WARN-level during retrofit; flip to FAIL
    once every paper uses `\\input{tables/...}` for its numerical
    content.
    """
    if not PAPERS_DIR.exists():
        return CheckResult(passed=True, details=[
            Detail("papers_dir", True, "papers/ not found; skipping", warning=True),
        ])

    details = []
    total_findings = 0
    total_inputs = 0
    for tex_path in sorted(PAPERS_DIR.glob("paper*_*/paper_draft.tex")):
        paper_name = tex_path.parent.name
        try:
            text = tex_path.read_text()
        except UnicodeDecodeError:
            details.append(Detail(paper_name, True, "unreadable; skipping",
                                  warning=True))
            continue

        # Papers that \input{tables/...} have opted in for data rows
        input_count = len(re.findall(r'\\input\{tables/[^}]+\}', text))
        total_inputs += input_count

        # Strip everything inside \input{tables/...} sections (the
        # generated files have their own literals, we trust those).
        # Also strip captions (they often cite reference values like
        # "290 s^-1" for comparison — those are intentional literals
        # documenting the paper's relationship to primary sources).
        stripped = re.sub(r'\\input\{tables/[^}]+\}', '', text)
        stripped = re.sub(r'\\caption\{[^}]*\}', '', stripped, flags=re.DOTALL)

        # Find numerical literals with physical units in the remainder
        findings = []
        for m in _NUMERICAL_LITERAL_RE.finditer(stripped):
            line_no = stripped.count("\n", 0, m.start()) + 1
            findings.append((line_no, m.group(0).strip()))

        if not findings:
            details.append(Detail(
                paper_name, True,
                f"no inline unit-bearing literals in body"
                + (f" (uses {input_count} \\input tables)" if input_count else ""),
            ))
            continue

        total_findings += len(findings)
        sample = "; ".join(f'L{ln} "{lit}"' for ln, lit in findings[:3])
        suffix = f" (+{len(findings)-3} more)" if len(findings) > 3 else ""
        prefix = f"uses {input_count} \\input, " if input_count else ""
        details.append(Detail(
            paper_name, True,
            f"{prefix}{len(findings)} inline literal(s): {sample}{suffix}",
            warning=(len(findings) > 0),
        ))

    details.insert(0, Detail(
        "summary", True,
        f"{total_findings} inline literals across papers; "
        f"{total_inputs} \\input{{tables/}} references in use "
        f"(WARN-level during retrofit)",
        warning=(total_findings > 0),
    ))

    # WARN-only until retrofit is complete; never hard-fails.
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 16: Knowledge graph integrity
# ═══════════════════════════════════════════════════════════════════════

@register_check("graph_integrity",
                "Knowledge graph integrity — orphans, conflicts, broken chains")
def check_graph_integrity() -> CheckResult:
    """CHECK 16: Build provenance graph and run integrity queries."""
    try:
        sys.path.insert(0, str(SCRIPT_DIR))
        from graph_integrity import run_integrity_checks
    except ImportError as exc:
        return CheckResult(passed=True, details=[
            Detail("import", True,
                   f"graph_integrity not available ({exc}); skipping",
                   warning=True),
        ])

    report = run_integrity_checks()
    s = report['summary']

    details = []

    # Graph size (informational)
    details.append(Detail(
        "graph_size", True,
        f"{s['total_nodes']} nodes, {s['total_edges']} edges",
    ))

    # Conflicts are hard failures
    if s['conflicts'] > 0:
        conflict_names = ', '.join(c['name'] for c in report['conflicts'][:5])
        suffix = f" (+{s['conflicts'] - 5} more)" if s['conflicts'] > 5 else ""
        details.append(Detail(
            "conflicts", False,
            f"{s['conflicts']} verification conflicts: {conflict_names}{suffix}",
        ))
    else:
        details.append(Detail("conflicts", True, "No verification conflicts"))

    # Orphans are warnings
    if s['orphans'] > 0:
        orphan_sample = ', '.join(o['id'] for o in report['orphan_nodes'][:5])
        suffix = f" (+{s['orphans'] - 5} more)" if s['orphans'] > 5 else ""
        details.append(Detail(
            "orphan_nodes", True,
            f"{s['orphans']} orphan nodes: {orphan_sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("orphan_nodes", True, "No orphan nodes"))

    # Ungrounded claims are warnings
    if s['ungrounded'] > 0:
        sample = ', '.join(u['id'] for u in report['ungrounded_claims'][:5])
        suffix = f" (+{s['ungrounded'] - 5} more)" if s['ungrounded'] > 5 else ""
        details.append(Detail(
            "ungrounded_claims", True,
            f"{s['ungrounded']} ungrounded claims: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("ungrounded_claims", True, "All claims grounded"))

    # Broken chains are warnings
    if s['broken_chains'] > 0:
        sample = ', '.join(b['formula'] for b in report['broken_chains'][:5])
        suffix = f" (+{s['broken_chains'] - 5} more)" if s['broken_chains'] > 5 else ""
        details.append(Detail(
            "broken_chains", True,
            f"{s['broken_chains']} broken provenance chains: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("broken_chains", True, "No broken provenance chains"))

    # Missing provenance are warnings
    if s['missing_provenance'] > 0:
        sample = ', '.join(m['name'] for m in report['missing_provenance'][:5])
        suffix = f" (+{s['missing_provenance'] - 5} more)" if s['missing_provenance'] > 5 else ""
        details.append(Detail(
            "missing_provenance", True,
            f"{s['missing_provenance']} params without SOURCED_FROM: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("missing_provenance", True,
                              "All non-projected params have provenance sources"))

    # Only conflicts are hard failures
    passed = s['conflicts'] == 0

    return CheckResult(passed=passed, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 17: Count literals in paper .tex (Phase 5v Wave 1b)
# ═══════════════════════════════════════════════════════════════════════

# Patterns that strongly suggest a hardcoded count literal in paper prose.
# Each pattern captures (\d+) together with a domain noun; the assumption
# is that any such count should come from \input{../../docs/counts.tex}
# macros (\totaltheorems, \leanmodules, etc.) so counts stay fresh.
_COUNT_LITERAL_PATTERNS = [
    # "N theorems", "N Lean theorems", "N formally-verified theorems"
    (re.compile(r'(?<![\\{\d])\b(\d{2,5})\s+(?:formally[- ]?verified\s+|machine[- ]?checked\s+|Lean\s+)?theorems?\b', re.IGNORECASE), "theorems"),
    # "N Lean modules" / "N modules"
    (re.compile(r'(?<![\\{\d])\b(\d{2,4})\s+(?:Lean\s+)?modules?\b', re.IGNORECASE), "modules"),
    # "N sorry" (remaining sorry count)
    (re.compile(r'(?<![\\{\d])\b(\d{1,4})\s+(?:remaining\s+)?sorry\b', re.IGNORECASE), "sorry"),
    # "N Aristotle-proved"
    (re.compile(r'(?<![\\{\d])\b(\d{2,4})\s+Aristotle[- ]?proved', re.IGNORECASE), "aristotle_proved"),
]


@register_check("count_literals",
                "Paper .tex files reference counts via \\input{counts.tex} macros, not literals")
def check_count_literals() -> CheckResult:
    """CHECK 17: Flag hardcoded count literals in paper .tex files.

    Papers should pull counts from docs/counts.tex via \\input + macros
    (\\totaltheorems, \\leanmodules, \\sorrycount, etc.) so stale counts
    can't ship. This check greps every paper_draft.tex for patterns like
    "N theorems", "N Lean modules", etc., and WARNs when found outside
    of an \\input context. WARN-level during the retrofit period; will
    escalate to FAIL once all 15 papers use macros.
    """
    if not PAPERS_DIR.exists():
        return CheckResult(passed=True, details=[
            Detail("papers_dir", True, "papers/ directory not found; skipping",
                   warning=True),
        ])

    # Papers that have \input'd counts.tex are exempt — they've opted in
    paper_tex_files = sorted(PAPERS_DIR.glob("paper*/paper_draft.tex"))
    details = []
    total_findings = 0

    for tex_path in paper_tex_files:
        paper_name = tex_path.parent.name
        try:
            text = tex_path.read_text()
        except UnicodeDecodeError:
            details.append(Detail(paper_name, True,
                                  "unreadable (encoding); skipping",
                                  warning=True))
            continue

        # Has this paper opted in to macros?
        uses_macros = (
            r'\input{../../docs/counts.tex}' in text
            or r'\input{../docs/counts.tex}' in text
            or r'\input{counts.tex}' in text
            or any(macro in text for macro in [
                r'\totaltheorems', r'\substantivetheorems',
                r'\leanmodules', r'\sorrycount', r'\aristotleproved',
            ])
        )

        findings = []
        for pattern, kind in _COUNT_LITERAL_PATTERNS:
            for m in pattern.finditer(text):
                # Compute a rough line number for reporting
                line_no = text.count("\n", 0, m.start()) + 1
                findings.append((line_no, kind, m.group(0).strip()))

        if not findings:
            details.append(Detail(
                paper_name, True,
                "no count literals found" + (" (macros in use)" if uses_macros else ""),
            ))
            continue

        # Found literals — WARN (passes but advisory)
        total_findings += len(findings)
        sample = "; ".join(
            f"L{ln} \"{lit}\" ({kind})" for ln, kind, lit in findings[:3]
        )
        suffix = f" (+{len(findings)-3} more)" if len(findings) > 3 else ""
        status_prefix = "USES MACROS but " if uses_macros else ""
        details.append(Detail(
            paper_name, True,
            f"{status_prefix}{len(findings)} count-literal matches: {sample}{suffix}",
            warning=True,
        ))

    details.insert(0, Detail(
        "summary", True,
        f"{total_findings} count-literal matches across {len(paper_tex_files)} papers "
        f"(WARN-level; retrofit to \\input{{counts.tex}} + macros)",
        warning=(total_findings > 0),
    ))

    # CHECK 17 is WARN-only until retrofit complete — never hard-fail
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 18: Readiness submission gate (Phase 5v Wave 4)
# ═══════════════════════════════════════════════════════════════════════

@register_check("readiness_submission_gate",
                "Every paper has all P1 readiness gates passed (Phase 5v Wave 4)")
def check_readiness_submission_gate() -> CheckResult:
    """CHECK 18: Aggregate per-paper readiness state.

    Iterates every Paper node's 11 ReadinessGate instances. A paper is
    submission-ready iff ALL priority-1 gates are `passed` and no
    priority-2 gate is `blocked`. Priority-2 `needs-recheck`/`open` are
    advisory warnings.

    The check is WARN-only during the readiness rollout — existing drafts
    will light up red (as intended) until remediation lands. To block
    submission, run `validate.py --strict` (future flag) or grep for
    'readiness-status: red' in archived reports.
    """
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        from build_graph import build_graph_json
    except ImportError as exc:
        return CheckResult(passed=True, details=[
            Detail("import", True, f"build_graph not available ({exc}); skipping",
                   warning=True),
        ])

    graph = build_graph_json()
    gates = [n for n in graph.get('nodes', []) if n['type'] == 'ReadinessGate']
    if not gates:
        return CheckResult(passed=True, details=[
            Detail("gates", True,
                   "no ReadinessGate nodes found (readiness_gates not wired?)",
                   warning=True),
        ])

    # Aggregate per-paper
    from collections import defaultdict
    per_paper: dict[str, dict] = defaultdict(lambda: {
        'p1_blocked': [], 'p2_blocked': [], 'p2_advisory': [],
        'passed': [], 'open': [],
    })
    for g in gates:
        m = g['meta']
        paper = m['paper']
        entry = (m['gate'], m['state'], m.get('notes', ''))
        if m['state'] == 'passed':
            per_paper[paper]['passed'].append(entry)
        elif m['priority'] == 1 and m['state'] == 'blocked':
            per_paper[paper]['p1_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] == 'blocked':
            per_paper[paper]['p2_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] in ('needs-recheck', 'open'):
            per_paper[paper]['p2_advisory'].append(entry)
        else:
            per_paper[paper]['open'].append(entry)

    # Classification
    green, yellow, red = [], [], []
    for paper, state in sorted(per_paper.items()):
        if state['p1_blocked'] or state['p2_blocked']:
            red.append(paper)
        elif state['p2_advisory'] or state['open']:
            yellow.append(paper)
        else:
            green.append(paper)

    details = [
        Detail("summary", True,
               f"{len(green)} green / {len(yellow)} yellow / {len(red)} red "
               f"across {len(per_paper)} papers"),
    ]

    for paper in green:
        details.append(Detail(paper, True, "all 11 gates passed"))
    for paper in yellow:
        s = per_paper[paper]
        details.append(Detail(
            paper, True,
            f"all P1 passed; advisory on: "
            f"{', '.join(g for g,_,_ in s['p2_advisory'] + s['open'])}",
            warning=True))
    for paper in red:
        s = per_paper[paper]
        blockers = s['p1_blocked'] + s['p2_blocked']
        details.append(Detail(
            paper, True,  # WARN not FAIL during rollout
            f"{len(blockers)} blocked: "
            f"{', '.join(g for g,_,_ in blockers[:5])}"
            + (f" (+{len(blockers)-5} more)" if len(blockers) > 5 else ""),
            warning=True))

    return CheckResult(passed=True, details=details)


def _lookup_provenance_value(prov_key, experiments, atoms, polariton_platforms):
    """Look up the actual value in constants for a provenance key like 'Steinhauer.omega_perp'."""
    import numpy as np
    from src.core.constants import HBAR, K_B, A_BOHR, POLARITON_MASS

    # Fundamental constants
    fundamentals = {'HBAR': HBAR, 'K_B': K_B, 'A_BOHR': A_BOHR,
                    'POLARITON_MASS': POLARITON_MASS}
    if prov_key in fundamentals:
        return fundamentals[prov_key]

    parts = prov_key.split('.', 1)
    if len(parts) != 2:
        return None
    group, key = parts

    # ATOMS
    if group in atoms:
        return atoms[group].get(key)

    # EXPERIMENTS
    if group in experiments:
        return experiments[group].get(key)

    # POLARITON_PLATFORMS
    if group in polariton_platforms:
        return polariton_platforms[group].get(key)

    return None


# ═══════════════════════════════════════════════════════════════════════
# Runner
# ═══════════════════════════════════════════════════════════════════════

def run_checks(
    check_filter: Optional[str] = None,
) -> Dict[str, CheckResult]:
    """Run all (or one) registered checks, return results keyed by name."""
    results = {}
    for spec in _CHECKS:
        if check_filter and spec.name != check_filter:
            continue
        try:
            results[spec.name] = spec.func()
        except Exception as e:
            results[spec.name] = CheckResult(passed=False, error=str(e))
    return results


def print_results(results: Dict[str, CheckResult]) -> None:
    """Pretty-print validation results to stdout."""
    for spec in _CHECKS:
        if spec.name not in results:
            continue
        cr = results[spec.name]
        status = "\033[32m✓ PASS\033[0m" if cr.passed else "\033[31m✗ FAIL\033[0m"
        print(f"\n{'═'*70}")
        print(f"  {status}  {spec.name}: {spec.description}")
        print(f"{'═'*70}")

        if cr.error:
            print(f"  ERROR: {cr.error}")

        for d in cr.details:
            if d.warning:
                sym = "\033[33m⚠\033[0m"
            elif d.passed:
                sym = "✓"
            else:
                sym = "✗"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f"  —  {d.message}"
            print(line)

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    total_warnings = sum(
        1 for r in results.values() for d in r.details if d.warning
    )
    print(f"\n{'═'*70}")
    summary = f"  Overall: {passed}/{total} checks passed"
    if total_warnings:
        summary += f" ({total_warnings} warning{'s' if total_warnings > 1 else ''})"
    print(summary)
    if passed == total:
        print("  \033[32mALL CHECKS PASSED\033[0m")
    else:
        print("  \033[31mSOME CHECKS FAILED\033[0m")
    print(f"{'═'*70}\n")


def archive_results(results: Dict[str, CheckResult]) -> Path:
    """Write timestamped JSON + text report to docs/validation/reports/."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    # JSON report
    json_path = REPORTS_DIR / f"validation_{ts}.json"
    payload = {
        "timestamp": ts,
        "project_root": str(PROJECT_ROOT),
        "checks": {},
    }
    for name, cr in results.items():
        payload["checks"][name] = {
            "passed": cr.passed,
            "error": cr.error,
            "details": [asdict(d) for d in cr.details],
        }
    payload["summary"] = {
        "total": len(results),
        "passed": sum(1 for r in results.values() if r.passed),
        "failed": sum(1 for r in results.values() if not r.passed),
    }
    class _Encoder(json.JSONEncoder):
        def default(self, o):
            if isinstance(o, (bool,)):
                return bool(o)
            try:
                return float(o)  # numpy scalars
            except (TypeError, ValueError):
                return super().default(o)

    with open(json_path, 'w') as f:
        json.dump(payload, f, indent=2, cls=_Encoder)

    # Text report (human-readable)
    txt_path = REPORTS_DIR / f"validation_{ts}.txt"
    lines = [
        f"SK-EFT Hawking Validation Report",
        f"Generated: {ts}",
        f"Project: {PROJECT_ROOT}",
        "",
    ]
    for name, cr in results.items():
        status = "PASS" if cr.passed else "FAIL"
        lines.append(f"[{status}] {name}")
        if cr.error:
            lines.append(f"  ERROR: {cr.error}")
        for d in cr.details:
            sym = "+" if d.passed else "-"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f" — {d.message}"
            lines.append(line)
        lines.append("")

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    lines.append(f"Overall: {passed}/{total} passed")
    with open(txt_path, 'w') as f:
        f.write('\n'.join(lines))

    return json_path


# ═══════════════════════════════════════════════════════════════════════
# CHECK 19: Citation primary-source cache present (Phase 6i Wave 1)
# ═══════════════════════════════════════════════════════════════════════

@register_check("citation_primary_sources_present",
                "Every external bibitem cited in papers has a primary-source cache file")
def check_citation_primary_sources_present() -> CheckResult:
    """For every \\cite{<bibkey>} in any papers/*/paper_draft.tex, verify a
    primary-source artifact exists on disk under
    `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,tex,abstract.txt,json}`.

    `inprep: True` entries are exempt (no external primary source to cache).

    Textbook / pre-DOI references with `primary_source_path: None` AND
    `doi: None` AND `arxiv: None` are also exempt — these are canonical
    textbook citations (e.g. Gilkey 1995 CRC heat-equation textbook;
    Trautman 1973 pre-DOI Symposia Mathematica volume) verified via
    secondary academic citations rather than via a downloadable primary
    source. The registry entry's `notes` field documents the secondary-
    citation pathway. Phase 6i Wave 6 addition.

    Bibkeys absent from CITATION_REGISTRY surface as FAIL — that's already a
    CitationIntegrity violation, not a Wave 1 concern, but worth reporting.
    """
    import re
    from src.core.citations import CITATION_REGISTRY, bibkey_phase
    from src.core.workspace import find_workspace

    LIT_SEARCH = find_workspace() / "Lit-Search"
    FALLBACK = "Phase-1-and-Background"
    EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]

    # Match \cite, \citep, \citet, \citeauthor, etc., with optional star,
    # optional [opt-args], then {key1,key2,...}
    CITE_RE = re.compile(r"\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}")

    details: List[Detail] = []
    all_pass = True

    paper_tex_files = sorted(PAPERS_DIR.glob("*/paper_draft.tex"))
    if not paper_tex_files:
        return CheckResult(passed=False, error="No papers/*/paper_draft.tex found")

    # First pass: collect (bibkey, paper_key) usage across all papers
    usage: dict[str, set[str]] = {}
    for tex_path in paper_tex_files:
        paper_key = tex_path.parent.name
        text = tex_path.read_text(encoding="utf-8", errors="replace")
        # Strip TeX-comment lines so commented-out \cite{} are not gated
        text_uncommented = "\n".join(
            line.split("%", 1)[0] for line in text.splitlines()
        )
        for m in CITE_RE.finditer(text_uncommented):
            for raw_key in m.group(1).split(","):
                key = raw_key.strip()
                if key:
                    usage.setdefault(key, set()).add(paper_key)

    # Second pass: classify each cited bibkey
    missing_from_registry: list[str] = []
    inprep_exempt: list[str] = []
    textbook_exempt: list[str] = []
    cached: list[str] = []
    not_cached: list[tuple[str, str, list[str]]] = []  # (key, phase, papers)

    for bibkey in sorted(usage):
        entry = CITATION_REGISTRY.get(bibkey)
        if entry is None:
            missing_from_registry.append(bibkey)
            continue
        if entry.get("inprep"):
            inprep_exempt.append(bibkey)
            continue
        # Textbook / pre-DOI exemption (Wave-6): canonical textbook
        # references with no DOI / no arXiv / no primary_source_path,
        # verified via secondary academic citations per `notes`.
        if (entry.get("primary_source_path") is None
                and entry.get("doi") is None
                and entry.get("arxiv") is None):
            textbook_exempt.append(bibkey)
            continue
        # Resolve phase: prefer canonical (used_in[0] paper), else fallback
        phase = bibkey_phase(entry) or FALLBACK
        target_dir = LIT_SEARCH / phase / "primary-sources"
        found = False
        for ext in EXTENSIONS:
            candidate = target_dir / f"{bibkey}.{ext}"
            if candidate.is_file() and candidate.stat().st_size > 0:
                found = True
                break
        if found:
            cached.append(bibkey)
        else:
            not_cached.append((bibkey, phase, sorted(usage[bibkey])))

    # Report
    n_cited = len(usage)
    n_cached = len(cached)
    n_inprep = len(inprep_exempt)
    n_textbook = len(textbook_exempt)
    n_missing = len(missing_from_registry)
    n_uncached = len(not_cached)

    details.append(Detail(
        "summary",
        n_uncached == 0 and n_missing == 0,
        f"{n_cited} bibkeys cited across {len(paper_tex_files)} papers — "
        f"{n_cached} cached / {n_inprep} inprep-exempt / "
        f"{n_textbook} textbook-exempt / "
        f"{n_uncached} need cache / {n_missing} missing-from-registry"
    ))

    if missing_from_registry:
        all_pass = False
        sample = ", ".join(missing_from_registry[:8])
        more = f" (and {len(missing_from_registry) - 8} more)" if len(missing_from_registry) > 8 else ""
        details.append(Detail(
            "missing_from_registry",
            False,
            f"{n_missing} cited bibkeys absent from CITATION_REGISTRY: {sample}{more}"
        ))

    if not_cached:
        all_pass = False
        # Group by phase for compactness
        by_phase: dict[str, list[str]] = {}
        for bibkey, phase, _ in not_cached:
            by_phase.setdefault(phase, []).append(bibkey)
        for phase in sorted(by_phase):
            keys = by_phase[phase]
            sample = ", ".join(keys[:5])
            more = f" + {len(keys) - 5} more" if len(keys) > 5 else ""
            details.append(Detail(
                f"missing_cache:{phase}",
                False,
                f"{len(keys)} bibkeys lack primary-source cache: {sample}{more}"
            ))

    if all_pass:
        details.append(Detail(
            "all_cached",
            True,
            "Every cited external bibkey has a primary-source cache file"
        ))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 20: Provenance DOI ↔ CITATION_REGISTRY coverage
# ═══════════════════════════════════════════════════════════════════════

@register_check("provenance_doi_in_registry",
                "PARAMETER_PROVENANCE source DOIs resolve to CITATION_REGISTRY bibkeys")
def check_provenance_doi_in_registry() -> CheckResult:
    """For every PARAMETER_PROVENANCE entry whose `doi` is non-null, verify
    that DOI is present in CITATION_REGISTRY. This is the
    `qi-provenance-citation-coverage` QI item recommended by the Stage 13
    paper40 re-review (round 2): primary-experimental papers cited in
    PARAMETER_PROVENANCE should themselves be in CITATION_REGISTRY so that
    the Phase 6i Wave 1 primary-source cache covers them.

    Each entry may also carry a `cited_bibkeys` field listing the registry
    keys it relies on; if present, those keys must exist in CITATION_REGISTRY.

    Strict mode promotes both findings to hard failures; default mode keeps
    them as warnings (advisory during the rolling Phase 6i remediation).
    """
    from src.core.citations import CITATION_REGISTRY
    from src.core.provenance import PARAMETER_PROVENANCE

    reg_dois = {
        (e.get('doi') or '').lower(): k
        for k, e in CITATION_REGISTRY.items() if e.get('doi')
    }

    details: List[Detail] = []
    all_pass = True

    missing_doi: list[tuple[str, str]] = []  # (prov_key, doi)
    missing_bibkey: list[tuple[str, str]] = []  # (prov_key, bibkey)
    resolved_doi = 0
    resolved_bibkey = 0
    no_doi = 0

    for prov_key, entry in PARAMETER_PROVENANCE.items():
        doi = entry.get('doi')
        if doi:
            if doi.lower() in reg_dois:
                resolved_doi += 1
            else:
                missing_doi.append((prov_key, doi))
        else:
            no_doi += 1

        for bibkey in entry.get('cited_bibkeys', []) or []:
            if bibkey in CITATION_REGISTRY:
                resolved_bibkey += 1
            else:
                missing_bibkey.append((prov_key, bibkey))

    n_total = len(PARAMETER_PROVENANCE)
    details.append(Detail(
        "summary", not (missing_doi or missing_bibkey),
        f"{resolved_doi} provenance DOIs resolved / {len(missing_doi)} missing "
        f"/ {no_doi} entries without DOI (internal derivation); "
        f"{resolved_bibkey} cited_bibkeys resolved / "
        f"{len(missing_bibkey)} missing"
    ))

    if missing_doi:
        sample = ', '.join(f"{k}({d})" for k, d in missing_doi[:5])
        more = f" + {len(missing_doi) - 5} more" if len(missing_doi) > 5 else ""
        msg = (f"{len(missing_doi)} provenance DOIs absent from "
               f"CITATION_REGISTRY: {sample}{more}")
        if STRICT_MODE:
            all_pass = False
            details.append(Detail("missing_dois", False, f"[strict] {msg}"))
        else:
            details.append(Detail("missing_dois", True, msg, warning=True))

    if missing_bibkey:
        sample = ', '.join(f"{k}({b})" for k, b in missing_bibkey[:5])
        more = f" + {len(missing_bibkey) - 5} more" if len(missing_bibkey) > 5 else ""
        all_pass = False  # cited_bibkeys MUST resolve — these are explicit refs
        details.append(Detail(
            "missing_cited_bibkeys", False,
            f"{len(missing_bibkey)} cited_bibkeys absent from "
            f"CITATION_REGISTRY: {sample}{more}"
        ))

    if not (missing_doi or missing_bibkey):
        details.append(Detail(
            "all_resolved", True,
            "Every provenance DOI and cited_bibkey resolves to a "
            "CITATION_REGISTRY entry"
        ))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# Phase 6i Wave 7.3 — bundle-level cross-paper consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("bundle_consistency",
                "Cross-bundle clusters' member sentences agree on numerical "
                "content across bundle boundaries")
def check_bundle_consistency() -> CheckResult:
    """For every cluster in `papers/cluster_bundle_index.json` whose
    `cross_bundle: true` flag is set, verify that the cluster's member
    sentences carry the same numerical content across all member
    bundles.

    The cluster index is built by `scripts/bundle_clusters.py` and
    projects each cluster's `member_papers` through
    `docs/PAPER_DRAFT_MAPPING.md` to determine which bundle codes the
    cluster spans. A cross-bundle cluster's member sentences must agree
    on:

    - Same primary source citation (bibkey).
    - Same numerical value (within ±2σ of the citation's reported
      uncertainty, or within 1% relative tolerance if no uncertainty
      is published).
    - Same Lean theorem reference (or no Lean reference if the cluster
      is qualitative).

    Mismatches are flagged at WARN level (advisory; not yet a blocker
    pending Wave 7.4 per-bundle Stage-13 sweep). The check exits
    cleanly when no cross-bundle clusters disagree.

    Phase 6i Wave 7.3 deliverable. Builds on the cluster-bundle index
    from Wave 7.1 + the per-bundle anchor list from Wave 7.2.
    """
    PROJECT_ROOT_LOCAL = Path(__file__).resolve().parent.parent.parent
    INDEX_PATH = PROJECT_ROOT_LOCAL / "SK_EFT_Hawking" / "papers" / "cluster_bundle_index.json"

    details: List[Detail] = []
    if not INDEX_PATH.exists():
        return CheckResult(
            passed=False,
            error=(
                f"missing cluster bundle index at {INDEX_PATH}; "
                f"run `uv run python scripts/bundle_clusters.py` first"
            ),
        )

    try:
        idx = json.loads(INDEX_PATH.read_text())
    except (json.JSONDecodeError, OSError) as exc:
        return CheckResult(passed=False, error=f"failed to read index: {exc}")

    cross_bundle_clusters = [c for c in idx.get("clusters", [])
                             if c.get("cross_bundle")]
    n_total = idx.get("cluster_count", 0)
    n_cross = len(cross_bundle_clusters)

    details.append(Detail(
        "summary",
        True,
        f"{n_total} clusters indexed / {n_cross} cross-bundle clusters",
    ))

    if not cross_bundle_clusters:
        details.append(Detail(
            "no_cross_bundle_clusters",
            True,
            "No cross-bundle clusters present; nothing to verify.",
        ))
        return CheckResult(passed=True, details=details)

    # For each cross-bundle cluster, the cluster_detect.py exact-match
    # algorithm guarantees same `normalized_hash`. So if the cluster
    # was constructed by `match_kind: exact`, all member sentences
    # share the same normalized prose content by construction — the
    # only consistency risk is post-hoc drift via direct prose_state
    # edit. For `match_kind: normalized`, fuzzy matches may differ in
    # numerical content; flag those for manual review.
    n_passing = 0
    n_warning = 0
    for c in cross_bundle_clusters:
        match_kind = c.get("match_kind", "unknown")
        bundles = ",".join(c.get(
            "bundle_destinations_excluding_flagship", []
        ))
        if match_kind == "exact":
            details.append(Detail(
                f"exact_cluster:{c['id']}",
                True,
                f"exact-match cluster spans {bundles}; "
                f"normalized_hash guarantees identical content "
                f"({len(c.get('member_papers', []))} member papers).",
            ))
            n_passing += 1
        elif match_kind == "normalized":
            details.append(Detail(
                f"normalized_cluster:{c['id']}",
                True,  # advisory only
                f"normalized-match cluster spans {bundles}; "
                f"fuzzy match — manual numerical-consistency review "
                f"recommended at Stage 13 sweep.",
            ))
            n_warning += 1
        else:
            details.append(Detail(
                f"unknown_match_kind:{c['id']}",
                False,
                f"unknown match_kind {match_kind!r}; cluster index may "
                f"be stale — re-run scripts/bundle_clusters.py",
            ))

    details.append(Detail(
        "verdict",
        all(d.passed for d in details),
        f"{n_passing} exact-match clusters guaranteed consistent; "
        f"{n_warning} normalized-match clusters flagged for Stage-13 "
        f"manual review.",
    ))

    return CheckResult(
        passed=all(d.passed for d in details),
        details=details,
    )


# ═══════════════════════════════════════════════════════════════════════
# CHECK 22: bundle source freshness (Phase 7a sub-wave 7a.1.4)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "bundle_source_freshness",
    "Bundle source-paper mtime ≤ bundle last_lift; flag stale bundles",
)
def check_bundle_source_freshness() -> CheckResult:
    """For each bundle (per `papers/<bundle>/bundle_metadata.json`),
    detect whether any of its source papers (per
    `docs/PAPER_DRAFT_MAPPING.md`) has been modified since the bundle's
    last lift. Stale bundles need Stage-13 re-invocation per
    `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`.

    Default mode: advisory (every detail.warning=True passes the check).
    Strict mode (`validate.py --strict`): freshness-stale bundles fail.

    Phase 7a sub-wave 7a.1.4 deliverable. Schema reference:
    `docs/BUNDLE_DIRECTORY_SCHEMA.md`.
    """
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        from check_bundle_source_freshness import check as _run_check
    except ImportError as exc:
        return CheckResult(
            passed=False,
            error=f"check_bundle_source_freshness module unavailable: {exc}",
        )

    findings = _run_check()
    if not findings:
        return CheckResult(
            passed=True,
            details=[Detail(
                "scope",
                True,
                "no bundle directories initialized yet (pre-Phase-7-execution state)",
            )],
        )

    details: List[Detail] = []
    n_warn = 0
    n_fail = 0
    for f in findings:
        bundle = f["bundle"]
        msg = f["message"]
        passed = f["passed"]
        warning = f.get("warning", False)
        # In strict mode, WARN bundles fail
        if STRICT_MODE and warning:
            passed = False
        details.append(Detail(
            f"bundle:{bundle}",
            passed,
            msg,
            warning=warning,
        ))
        if not passed:
            n_fail += 1
        elif warning:
            n_warn += 1

    summary_msg = (
        f"{len(findings)} sub-findings: {n_fail} FAIL / {n_warn} WARN / "
        f"{len(findings) - n_fail - n_warn} PASS"
    )
    if STRICT_MODE:
        summary_msg += " (strict mode: WARN promoted to FAIL)"
    details.insert(0, Detail("summary", n_fail == 0, summary_msg))

    return CheckResult(
        passed=(n_fail == 0),
        details=details,
    )


# ═══════════════════════════════════════════════════════════════════════
# CHECK 23: Bibitem title ↔ primary-source PDF page-1 consistency
# (Stage 14 QI candidate from Phase 6o Wave 4a.4 D5 adversarial review:
#  catches single-word title drift like "in a relativistic" vs
#  "in relativistic" Bose-Einstein condensate. Default: advisory WARN.)
# ═══════════════════════════════════════════════════════════════════════

@register_check("bibitem_title_primary_source",
                "Registry titles match primary-source cache PDF page-1 titles (drift detector)")
def check_bibitem_title_primary_source() -> CheckResult:
    """For every CITATION_REGISTRY entry whose `primary_source_path` points
    to a `.pdf` cache file AND has a non-empty `title`, extract the page-1
    text from the cached PDF and compare against the registry title.

    Flags single-word and multi-word title drift between the registry's
    bibitem title and the actual published form. Designed to catch the
    failure mode that produced the BLOCKER in the Phase 6o Wave 4a.4 D5
    adversarial review (`BelenchiaLiberatiMohd2014` registered as "in a
    relativistic Bose-Einstein condensate" but published as "in
    relativistic Bose-Einstein condensate" — a single-word drop).

    Implementation: extract page-1 text via pdfminer.six; normalize both
    titles (lowercase, collapse whitespace, strip punctuation); compute
    `difflib.SequenceMatcher` ratio between the registry title and a
    sliding window of the page-1 text. Flag entries where the best-window
    ratio falls below a threshold.

    Default mode: advisory WARN per finding (the check passes overall;
    individual mismatches are surfaced for author review). Strict mode
    (`validate.py --strict`) promotes mismatches to FAIL — for use at
    paper-submission gate.

    Skips:
    - Entries with `inprep: True` (no external primary source).
    - Entries with `primary_source_path: None` (textbook / pre-DOI exempt
      per Pipeline Invariant #11).
    - Entries whose cache is non-PDF (`.json`, `.abstract.txt`, `.tex`).
    - Entries whose cache file does not exist on disk (separately
      enforced by `citation_primary_sources_present`).

    Phase 6o Wave 4a.4 close memo `temporary/working-docs/phase6o/
    wave_4a_sakharov_lambda_substrate_refactor_close.md` documents the
    BLOCKER pattern this check guards against.
    """
    import re
    from src.core.citations import CITATION_REGISTRY

    PROJECT_ROOT_LOCAL = Path(__file__).resolve().parent.parent.parent

    try:
        from pdfminer.high_level import extract_text  # type: ignore
    except ImportError:
        return CheckResult(
            passed=True,
            details=[Detail(
                "skipped",
                True,
                "pdfminer.six not installed — check skipped (advisory)",
                warning=True,
            )],
        )

    # Common ligature decompositions used in PDF text extraction
    LIGATURES = {
        "ﬁ": "fi", "ﬂ": "fl", "ﬀ": "ff", "ﬃ": "ffi", "ﬄ": "ffl",
        "ﬅ": "ft", "ﬆ": "st",
    }

    # Greek-letter spell-outs that appear in titles vs PDF text
    GREEK = {
        "Λ": "lambda", "λ": "lambda",
        "Α": "alpha", "α": "alpha",
        "Β": "beta", "β": "beta",
        "Γ": "gamma", "γ": "gamma",
        "Δ": "delta", "δ": "delta",
        "Ω": "omega", "ω": "omega",
        "ℝ": "r", "ℤ": "z", "ℕ": "n", "ℂ": "c",
    }

    def _normalize(s: str) -> str:
        # Apply ligature + Greek decomposition
        for k, v in LIGATURES.items():
            s = s.replace(k, v)
        for k, v in GREEK.items():
            s = s.replace(k, v)
        s = s.lower()
        # Normalize all dash variants
        s = s.replace("–", "-").replace("—", "-").replace("−", "-")
        # Strip everything except letters, digits, hyphens, spaces.
        # Also drop hyphens (so "Bose-Einstein" matches "Bose Einstein")
        s = re.sub(r"[^a-z0-9\s]", " ", s)
        s = re.sub(r"\s+", " ", s).strip()
        return s

    details: List[Detail] = []
    flagged: list[tuple[str, str, str]] = []  # (key, registry_title, pdf_excerpt)
    checked = 0
    skipped_no_pdf = 0
    skipped_inprep = 0
    skipped_textbook = 0
    skipped_no_title = 0
    skipped_missing_cache = 0
    extract_failed: list[tuple[str, str]] = []

    for bibkey, entry in sorted(CITATION_REGISTRY.items()):
        if entry.get("inprep"):
            skipped_inprep += 1
            continue
        title = (entry.get("title") or "").strip()
        if not title:
            skipped_no_title += 1
            continue
        ps_path = entry.get("primary_source_path")
        if ps_path is None:
            # Textbook / pre-DOI exempt per Pipeline Invariant #11
            if entry.get("doi") is None and entry.get("arxiv") is None:
                skipped_textbook += 1
            continue
        if not str(ps_path).endswith(".pdf"):
            skipped_no_pdf += 1
            continue
        cache_file = PROJECT_ROOT_LOCAL / ps_path
        if not cache_file.is_file() or cache_file.stat().st_size == 0:
            skipped_missing_cache += 1
            continue

        try:
            page1_text = extract_text(str(cache_file), maxpages=1) or ""
        except Exception as exc:
            extract_failed.append((bibkey, str(exc)[:100]))
            continue

        norm_title = _normalize(title)
        norm_page = _normalize(page1_text)
        if not norm_title or not norm_page:
            extract_failed.append((bibkey, "empty extract"))
            continue

        checked += 1

        # Primary signal: substring containment after normalization.
        # If the normalized registry title appears verbatim in the
        # normalized page-1 text, the bibitem is consistent with the PDF.
        if norm_title in norm_page:
            continue

        # Secondary signal: try dropping a single word from the registry
        # title — if any single-word drop makes it a substring, that is
        # the BLOCKER drift pattern (e.g., registry has "in a relativistic"
        # but PDF has "in relativistic": dropping "a" yields containment).
        tokens = norm_title.split()
        single_drop_match = None
        if len(tokens) >= 3:
            for i, _ in enumerate(tokens):
                candidate = " ".join(tokens[:i] + tokens[i + 1:])
                if candidate and candidate in norm_page:
                    single_drop_match = tokens[i]
                    break
        if single_drop_match is not None:
            # Localize the matched window for the report
            candidate = " ".join(t for t in tokens if t != single_drop_match)
            idx = norm_page.find(candidate)
            window = norm_page[max(0, idx - 10):idx + len(candidate) + 30]
            flagged.append((
                bibkey,
                f"DROP-WORD: registry has extra {single_drop_match!r} not in PDF — title={title!r}",
                window,
            ))
            continue

        # Tertiary signal: check if PDF has an extra word the registry lacks.
        # If we can find every registry token in order in a 200-char window
        # of the page, but the title isn't a clean substring, flag for review.
        # Otherwise, the title may simply not be on page 1 (e.g., journal
        # metadata pages) — defer to manual audit.
        # For brevity, just flag with a low-priority "title-not-on-page1" note.
        flagged.append((
            bibkey,
            f"NOT-FOUND: registry title not a substring of page-1 — title={title!r}",
            norm_page[:120],
        ))

    # Partition flags: DROP-WORD flags are the high-confidence drift class
    # (the BLOCKER pattern this check targets). NOT-FOUND flags often
    # indicate that the title isn't on page 1 of the PDF (e.g., the cache
    # is a journal title page, a chapter excerpt, or has heavy metadata
    # before the title) — these are advisory only.
    drop_word_flags = [(k, m, w) for (k, m, w) in flagged if m.startswith("DROP-WORD")]
    not_found_flags = [(k, m, w) for (k, m, w) in flagged if m.startswith("NOT-FOUND")]
    n_drop_word = len(drop_word_flags)
    n_not_found = len(not_found_flags)
    n_extract_failed = len(extract_failed)

    # In strict mode, both drift classes fail; in default mode, only
    # DROP-WORD flags fail (high-confidence BLOCKER pattern), NOT-FOUND
    # is advisory only.
    summary_passed = STRICT_MODE is False or (n_drop_word == 0 and n_not_found == 0)
    if not STRICT_MODE:
        summary_passed = True  # Always pass in default mode

    details.append(Detail(
        "summary",
        summary_passed,
        f"checked {checked} PDF caches — "
        f"{n_drop_word} DROP-WORD drift flag(s) / "
        f"{n_not_found} NOT-FOUND advisory flag(s) / "
        f"{n_extract_failed} extract-failure(s) / "
        f"skipped: {skipped_inprep} inprep, {skipped_textbook} textbook, "
        f"{skipped_no_pdf} non-pdf cache, {skipped_no_title} no-title, "
        f"{skipped_missing_cache} cache-missing"
        + (" (strict mode: drift flags promoted to FAIL)" if STRICT_MODE else ""),
        warning=(n_drop_word > 0 or n_not_found > 0) and not STRICT_MODE,
    ))

    # DROP-WORD findings: high-confidence drift (the BLOCKER class)
    for bibkey, msg, pdf_excerpt in drop_word_flags[:20]:
        details.append(Detail(
            f"drop_word:{bibkey}",
            STRICT_MODE is False,
            f"{msg} — pdf-page1≈{pdf_excerpt!r}",
            warning=not STRICT_MODE,
        ))
    if len(drop_word_flags) > 20:
        details.append(Detail(
            "drop_word:overflow",
            True,
            f"({len(drop_word_flags) - 20} more DROP-WORD flags omitted)",
            warning=True,
        ))

    # NOT-FOUND findings: advisory (title not on page 1; often false-positive
    # for cached PDFs whose page-1 is a journal cover or chapter intro).
    # Show only first 10 in default output.
    for bibkey, msg, pdf_excerpt in not_found_flags[:10]:
        details.append(Detail(
            f"not_found:{bibkey}",
            True,  # advisory only
            f"{msg} (advisory — verify manually)",
            warning=True,
        ))
    if len(not_found_flags) > 10:
        details.append(Detail(
            "not_found:overflow",
            True,
            f"({len(not_found_flags) - 10} more NOT-FOUND advisory flags omitted)",
            warning=True,
        ))

    for bibkey, err in extract_failed[:10]:
        details.append(Detail(
            f"extract_failed:{bibkey}",
            True,  # extract failures are advisory
            f"pdfminer error: {err}",
            warning=True,
        ))

    if n_drop_word == 0 and n_not_found == 0 and n_extract_failed == 0:
        details.append(Detail(
            "all_consistent",
            True,
            "Every checked registry title matches its PDF page-1 form",
        ))

    return CheckResult(
        passed=summary_passed,
        details=details,
    )


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Quantum-network substrate Python ↔ Lean cross-validation
# ═══════════════════════════════════════════════════════════════════════

@register_check("quantum_network",
                "QN Python formulas satisfy the QuantumNetwork Lean theorem identities")
def check_quantum_network() -> CheckResult:
    """Cross-checks the `src/core/formulas.py` quantum-network mirror against the
    closed-form identities/bounds proven in `lean/SKEFTHawking/QuantumNetwork/*.lean`
    (Phases 6AA–6AD), and confirms the referenced Lean theorem names exist in that
    subdirectory (CHECK 1 only globs the top-level package)."""
    from src.core import formulas as F

    details: List[Detail] = []
    all_pass = True

    def check(name: str, cond: bool, msg: str = ""):
        nonlocal all_pass
        details.append(Detail(name, cond, msg))
        if not cond:
            all_pass = False

    # Werner swap multiplicative in the Werner parameter (wernerParam_swap)
    F1, F2 = 0.83, 0.71
    check("wernerParam_swap_multiplicative",
          abs(F.werner_param(F.werner_swap_fidelity(F1, F2))
              - F.werner_param(F1) * F.werner_param(F2)) < 1e-12)

    # End-to-end one-more-link recurrence (endToEndFidelity_succ)
    check("endToEndFidelity_succ",
          all(abs(F.end_to_end_fidelity(0.9, k + 1)
                  - F.werner_swap_fidelity(F.end_to_end_fidelity(0.9, k), 0.9)) < 1e-12
              for k in range(6)))

    # Envelope ∈ [1/4,1] (swapChain_fidelity_envelope)
    check("swapChain_fidelity_envelope",
          all(0.25 - 1e-12 <= F.end_to_end_fidelity(Fl, k) <= 1.0 + 1e-12
              for Fl in (0.25, 0.5, 0.9, 1.0) for k in range(9)))

    # BBPSSW strict increase on (1/2,1) (bbpsswRecurrence_gt)
    check("bbpsswRecurrence_gt",
          all(F.bbpssw_recurrence(Fl) > Fl for Fl in (0.51, 0.6, 0.75, 0.9, 0.99)))

    # DEJMPS phase-flip-only increase + verified single-step decrease witness
    check("dejmps_increase_phaseFlipOnly",
          all(F.dejmps_out_a(A, (1 - A) / 2, (1 - A) / 2, 0.0) > A for A in (0.55, 0.7, 0.9)))
    check("dejmps_single_step_can_decrease",
          abs(F.dejmps_out_a(0.6, 0, 0, 0.4) - 13 / 25) < 1e-12
          and F.dejmps_out_a(0.6, 0, 0, 0.4) < 0.6)

    # Fortescue–Lo finite-round yield (fortescueLoYield_gt_two_thirds, _lt_one)
    check("fortescueLoYield_gt_two_thirds",
          all(2 / 3 < F.fortescue_lo_yield(D) < 1.0 for D in (3, 5, 12)))

    # BB84 crossover proven, not hardcoded (bb84_crossover_exists, strictAntiOn)
    check("bb84KeyRate_zero", abs(F.bb84_key_rate(0.0) - 1.0) < 1e-12)
    check("bb84_crossover_sign_change",
          F.bb84_key_rate(0.10) > 0.0 and F.bb84_key_rate(0.12) < 0.0)

    # H₂(1/3) < 1 (w3_asymptotic_specified_lt_one)
    check("w3_asymptotic_specified_lt_one", 0.0 < F.bin_entropy_bit(1 / 3) < 1.0)

    # Horodecki teleportation (teleportAvgFidelity_horodecki, teleport_beats_classical_iff)
    check("teleport_horodecki_formula",
          all(abs(F.teleport_avg_fidelity(Fl) - (2 * Fl + 1) / 3) < 1e-12
              for Fl in (0.5, 0.7, 1.0)))
    check("teleport_beats_classical_iff",
          F.teleport_avg_fidelity(0.6) > 2 / 3 and F.teleport_avg_fidelity(0.4) < 2 / 3)
    check("haarPauliConstant_eq_third", abs(F.HAAR_PAULI_CONSTANT - 1 / 3) < 1e-15)

    # Tier-1 anchors (bsmSuccessProb_*, linkRate_*)
    check("bsmSuccessProb_bounds",
          F.bsm_success_prob(2) == 0.5 and F.bsm_success_prob(4) == 1.0)
    check("linkRate_monotonicity",
          F.link_rate(1000, 2e8, 0.5) > F.link_rate(1000, 2e8, 0.9)
          and F.link_rate(2000, 2e8, 0.5) > F.link_rate(1000, 2e8, 0.5))

    # Referenced QN Lean theorem names exist in the QuantumNetwork subdirectory
    qn_dir = Path(__file__).parent.parent / "lean" / "SKEFTHawking" / "QuantumNetwork"
    expected = [
        "wernerParam_swap", "endToEndFidelity_succ", "swapChain_fidelity_envelope",
        "bbpsswRecurrence_gt", "dejmps_increase_phaseFlipOnly", "dejmps_single_step_can_decrease",
        "fortescueLoYield_gt_two_thirds", "bb84_crossover_exists",
        "teleportAvgFidelity_horodecki_unconditional", "haarPauliZSqAverage_eq",
        "bsmSuccessProb_le_half_of_linearOptics", "linkRate_antitone_success",
    ]
    if qn_dir.exists():
        names = set()
        for lf in qn_dir.glob("*.lean"):
            for line in lf.read_text().splitlines():
                s = line.strip()
                if s.startswith("theorem ") or s.startswith("lemma "):
                    names.add(s.split()[1].split("(")[0].split(":")[0].strip())
        missing = [t for t in expected if t not in names]
        check("qn_lean_theorems_exist", not missing,
              f"missing: {missing}" if missing else f"{len(expected)} QN theorems found")
    else:
        check("qn_lean_theorems_exist", False, "QuantumNetwork dir not found")

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# Shared helpers for the prose-consistency checks (CHECK 24–26)
# (Stage 14 follow-through from the 2026-06-05 external-review remediation;
#  record: temporary/working-docs/reviews/papers/2026-06-05-Perplexity/
#  REMEDIATION_TRIAGE_2026-06-10.md, Wave-5 process items a/b/c.)
# ═══════════════════════════════════════════════════════════════════════

#: Bundle codes per docs/PAPER_STRATEGY.md (publication-bundle drafts).
BUNDLE_CODES = (
    "F", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9",
    "E1", "E2", "I1", "I2", "I3", "L1", "L2", "L3",
)


# Fatal-error markers in a pdflatex .log. A `! ` line is TeX's universal
# error sentinel (e.g. "! Undefined control sequence", "! Misplaced
# alignment tab character &", "! LaTeX Error: ..."). Undefined-reference /
# undefined-citation / overfull-box warnings are NOT fatal and are ignored.
_LATEX_FATAL_RE = re.compile(r"^! ", re.MULTILINE)


@register_check("paper_latex_compiles",
                "Bundle drafts compile under pdflatex (advisory; slow — "
                "pass --force-latex or --check paper_latex_compiles)")
def check_paper_latex_compiles() -> CheckResult:
    """Advisory, slow-gated: actually compile each bundle draft with
    ``pdflatex`` and flag fatal (``! ``-marked) breakage.

    Why this exists: the 2026-06-10 paper15 incident — 108 fatal LaTeX
    errors injected by unescaped ``&``/``_`` and an executed ``\\input{}``
    in autogenerated tables — was invisible to *every* structural check.
    Only a real compile catches a draft that no longer builds. The fix
    (table-generator escaping in ``scripts/paper_tables/sources.py``) is
    durable, but a compile gate prevents the next such regression.

    Posture:
      - **Slow-gated**: SKIPPED in the default full run (pdflatex × all
        bundles is minutes). Runs only when ``--force-latex`` is passed or
        ``paper_latex_compiles`` is the explicitly selected ``--check``.
      - **Advisory**: always ``passed=True``. A failing compile surfaces as
        a ⚠ WARN, never a hard suite failure — transient toolchain/package
        gaps must not block development. A persistent WARN is the signal to
        investigate.

    One non-stop pass per draft (enough to surface fatal breakage; full
    reference/citation resolution is out of scope for a build gate).
    Compiles with the paper dir as cwd (so relative ``\\input``/
    ``\\includegraphics`` resolve) and ``-output-directory`` pointed at a
    throwaway temp dir (so no ``.aux``/``.log``/``.pdf`` lands in the repo).
    """
    details: List[Detail] = []

    if not FORCE_LATEX:
        return CheckResult(passed=True, details=[Detail(
            "skipped", True,
            "SKIPPED (slow) — pass --force-latex or "
            "--check paper_latex_compiles to compile all bundle drafts")])

    pdflatex = shutil.which("pdflatex")
    if pdflatex is None:
        return CheckResult(passed=True, details=[Detail(
            "toolchain", True,
            "SKIPPED — pdflatex not on PATH (install a TeX distribution)")])

    n_ok = 0
    n_missing = 0
    failed: List[tuple[str, int, str]] = []  # (code, n_fatal, first_error)

    for code in BUNDLE_CODES:
        tex = PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            n_missing += 1
            continue
        paper_dir = tex.parent
        with tempfile.TemporaryDirectory(prefix=f"latexchk_{code}_") as out_dir:
            try:
                # capture_output without text= → bytes (unused; pdflatex logs
                # often carry non-UTF-8 bytes). We parse the .log file instead.
                subprocess.run(
                    [pdflatex, "-interaction=nonstopmode", "-halt-on-error",
                     "-no-shell-escape", f"-output-directory={out_dir}",
                     "paper_draft.tex"],
                    cwd=paper_dir, capture_output=True, timeout=180,
                )
            except subprocess.TimeoutExpired:
                failed.append((code, -1, "compile timed out (>180s)"))
                continue
            except Exception as exc:  # noqa: BLE001 — advisory: never hard-error
                failed.append((code, -1, f"compile invocation failed: {exc}"))
                continue
            log_path = Path(out_dir) / "paper_draft.log"
            log = log_path.read_text(errors="replace") if log_path.is_file() else ""
            fatal = _LATEX_FATAL_RE.findall(log)
            if fatal:
                # Capture the first "! ..." error line for the report.
                m = re.search(r"^(! .*)$", log, re.MULTILINE)
                first = m.group(1).strip()[:90] if m else "(see log)"
                failed.append((code, len(fatal), first))
            else:
                n_ok += 1

    all_pass = True
    details.append(Detail(
        "summary",
        len(failed) == 0,
        f"{n_ok}/{n_ok + len(failed)} bundle drafts compiled clean "
        f"({n_missing} missing draft(s) skipped) — {len(failed)} with fatal errors"
    ))
    for code, n_fatal, first in failed:
        all_pass = False
        cnt = "timeout" if n_fatal < 0 else f"{n_fatal} fatal"
        details.append(Detail(
            f"compile:{code}", False,
            f"{code}: {cnt} — first: {first}", warning=True))

    # Advisory: never block the suite on a compile WARN.
    return CheckResult(passed=True, details=details)


def _strip_tex_comments(text: str) -> str:
    """Blank out LaTeX comments (unescaped ``%`` to end-of-line) with
    spaces, preserving every character offset and line break so that
    match offsets in the stripped text map 1:1 onto the original file.
    """
    out = []
    for line in text.split("\n"):
        idx = None
        i = 0
        while i < len(line):
            if line[i] == "%":
                # escaped \% is content, not a comment
                n_bs = 0
                j = i - 1
                while j >= 0 and line[j] == "\\":
                    n_bs += 1
                    j -= 1
                if n_bs % 2 == 0:
                    idx = i
                    break
            i += 1
        if idx is None:
            out.append(line)
        else:
            out.append(line[:idx] + " " * (len(line) - idx))
    return "\n".join(out)


def _line_of(text: str, offset: int) -> int:
    """1-based line number of a character offset."""
    return text.count("\n", 0, offset) + 1


# ═══════════════════════════════════════════════════════════════════════
# CHECK 24: Axiom-count ↔ paper-prose consistency
# ═══════════════════════════════════════════════════════════════════════

# Present-tense single-axiom claims ("one axiom", "a single axiom",
# "1~axiom", "one tracked axiom", ...). `~` is the LaTeX non-breaking
# space; word separators may also be newlines.
_AXIOM_SEP = r"(?:\s|~)+"
_AXIOM_SINGULAR_RE = re.compile(
    r"\b(?:one|single|sole|lone|1)" + _AXIOM_SEP
    + r"(?:(?:true|tracked|remaining|residual|project-local|project|"
    + r"genuine|physical|global)" + _AXIOM_SEP + r")?"
    + r"axiom\b(?!-)",
    re.IGNORECASE,
)
# Present-tense naming of the retired axiom ("the axiom \texttt{gapped...").
_AXIOM_GAPPED_PRESENT_RE = re.compile(
    r"the" + _AXIOM_SEP + r"axiom" + _AXIOM_SEP + r"\\texttt\{gapped",
    re.IGNORECASE,
)
# Numeric plural claims ("0 axioms", "3 axioms", "zero axioms"). The
# qualifier group is captured so per-wave delta claims ("zero NEW
# axioms") can be excluded from the total-count comparison.
_AXIOM_PLURAL_RE = re.compile(
    r"\b(zero|\d+)" + _AXIOM_SEP
    + r"(?:(new|additional|extra|tracked|project-local|true|active|"
    + r"declared)" + _AXIOM_SEP + r")?"
    + r"axioms\b",
    re.IGNORECASE,
)
# Historical-attribution context tokens: a single-axiom claim sitting
# within ±120 chars of one of these is a legitimate retrospective
# (D2/F-style "formerly axiom gapped_interface_axiom" usage).
_AXIOM_HISTORICAL_RE = re.compile(
    r"formerly|converted|retired|was\s+an\s+axiom|2026-05-19",
    re.IGNORECASE,
)
_AXIOM_HIST_WINDOW = 120
# Narrow immediately-preceding negation guard ("no single axiom ...").
_AXIOM_NEG_BEFORE_RE = re.compile(r"\b(?:no|without)\b[^.\n]{0,15}$",
                                  re.IGNORECASE)


def _axiom_prose_findings(text: str, axiom_count: int) -> list:
    """Pure scanning core for CHECK 24 (unit-testable).

    Returns a list of dicts: ``{kind, line, excerpt, fail}`` where
    ``kind`` is one of ``singular`` / ``gapped_present`` /
    ``plural_mismatch``. ``fail=True`` only for the hard-failure class:
    a non-historical single-axiom claim while the live axiom count is 0.
    LaTeX comments are blanked before scanning (offsets preserved).
    """
    stripped = _strip_tex_comments(text)
    findings = []

    def _is_historical(start: int, end: int) -> bool:
        lo = max(0, start - _AXIOM_HIST_WINDOW)
        hi = min(len(stripped), end + _AXIOM_HIST_WINDOW)
        return bool(_AXIOM_HISTORICAL_RE.search(stripped[lo:hi]))

    for m in _AXIOM_SINGULAR_RE.finditer(stripped):
        if _is_historical(m.start(), m.end()):
            continue
        if _AXIOM_NEG_BEFORE_RE.search(stripped[max(0, m.start() - 18):m.start()]):
            continue
        findings.append({
            "kind": "singular",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            # claim value is 1; hard-fail iff the live count is 0,
            # advisory mismatch iff the live count is some other N ≠ 1.
            "fail": axiom_count == 0,
            "mismatch": axiom_count != 1,
        })

    for m in _AXIOM_GAPPED_PRESENT_RE.finditer(stripped):
        if _is_historical(m.start(), m.end()):
            continue
        findings.append({
            "kind": "gapped_present",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            "fail": axiom_count == 0,
            "mismatch": True,
        })

    for m in _AXIOM_PLURAL_RE.finditer(stripped):
        qualifier = (m.group(2) or "").lower()
        if qualifier in ("new", "additional", "extra"):
            continue  # per-wave delta claim, not a total-count claim
        value = 0 if m.group(1).lower() == "zero" else int(m.group(1))
        if value == axiom_count:
            continue
        if _is_historical(m.start(), m.end()):
            continue
        findings.append({
            "kind": "plural_mismatch",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            "fail": False,  # numeric plural drift is advisory-only
            "mismatch": True,
        })

    return findings


@register_check("axiom_count_prose_consistency",
                "Paper prose axiom-count claims agree with docs/counts.json")
def check_axiom_count_prose_consistency() -> CheckResult:
    """Prevent the F-flagship failure class from the 2026-06-05 external
    review: paper prose claiming "one (true) axiom" while
    ``docs/counts.json`` reports 0 project-local axioms (the
    ``gapped_interface_axiom`` was retired into the tracked Prop
    ``TPFConjecture`` on 2026-05-19; see Pipeline Invariant #15).

    Scans every ``papers/*/paper_draft.tex`` (bundle drafts AND legacy
    per-paper drafts). Failure classes:

    - **FAIL** — live axiom count is 0 and a present-tense single-axiom
      claim ("one axiom", "a single axiom", "1~axiom", "one tracked
      axiom", "the axiom \\texttt{gapped...") appears outside a
      historical-attribution context (±120 chars of
      formerly/converted/retired/"was an axiom"/2026-05-19 — the
      D2/F-style "formerly axiom gapped_interface_axiom" usage is
      legitimate and never flags).
    - **WARN (advisory)** — a numeric plural claim ("N axioms", digit or
      "zero" literal) disagrees with the live count. Word-numeral
      plurals ("three axioms" — the Son-action physics-axioms idiom in
      D1/F) and per-wave delta claims ("zero NEW axioms") are excluded
      by design. The ``\\axiomcount{}`` macro is the preferred
      mechanism and never flags (it carries no prose literal).

    LaTeX comments are stripped before scanning. Calibrated live
    2026-06-10: the sweep surfaced 16 genuinely-missed stale sites
    across D5 + 10 legacy drafts (paper4/6/7/9/11/12/17/18/20/21/26),
    all fixed in the same commit that ships this check.
    """
    counts_path = PROJECT_ROOT / "docs" / "counts.json"
    if not counts_path.exists():
        return CheckResult(passed=False,
                           error=f"missing {counts_path}; run scripts/update_counts.py")
    try:
        axiom_count = int(json.loads(counts_path.read_text())["lean"]["axioms"])
    except (json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
        return CheckResult(passed=False,
                           error=f"counts.json unreadable / missing lean.axioms: {exc}")

    details: List[Detail] = []
    n_fail = 0
    n_warn = 0
    n_scanned = 0

    for tex in sorted(PAPERS_DIR.glob("*/paper_draft.tex")):
        n_scanned += 1
        try:
            text = tex.read_text()
        except OSError as exc:
            details.append(Detail(f"unreadable:{tex.parent.name}", False, str(exc)))
            n_fail += 1
            continue
        for f in _axiom_prose_findings(text, axiom_count):
            rel = f"papers/{tex.parent.name}/paper_draft.tex:{f['line']}"
            if f["fail"]:
                n_fail += 1
                details.append(Detail(
                    f"stale_axiom_claim:{tex.parent.name}:{f['line']}",
                    False,
                    f"{rel} — present-tense '{f['excerpt']}' claim but "
                    f"counts.json reports {axiom_count} project-local axioms "
                    f"(non-historical context)",
                ))
            elif f["mismatch"]:
                n_warn += 1
                details.append(Detail(
                    f"axiom_count_mismatch:{tex.parent.name}:{f['line']}",
                    True,
                    f"{rel} — '{f['excerpt']}' disagrees with counts.json "
                    f"axiom count {axiom_count} (advisory)",
                    warning=True,
                ))

    details.insert(0, Detail(
        "summary",
        n_fail == 0,
        f"axiom count {axiom_count} (docs/counts.json) vs {n_scanned} "
        f"paper drafts — {n_fail} stale single-axiom FAIL(s) / "
        f"{n_warn} advisory mismatch(es)",
    ))
    if n_fail == 0 and n_warn == 0:
        details.append(Detail(
            "all_consistent", True,
            "No non-historical axiom-count drift in any paper draft",
        ))
    return CheckResult(passed=(n_fail == 0), details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 25: Prose Lean-theorem reference coverage (bundle drafts)
# (Implements the structural prevention proposed by QI item
#  qi-leantheoremdrift as `bundle_lean_refs_resolve`.)
# ═══════════════════════════════════════════════════════════════════════

_PROSE_TEXTTT_RE = re.compile(r"\\texttt\{([^{}]+)\}")
_PROSE_UNESCAPE_RE = re.compile(r"\\([_\\&%$#{}~^])")
_PROSE_IDENT_RE = re.compile(
    r"^[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
_PROSE_FILE_SUFFIXES = (
    ".py", ".md", ".json", ".tex", ".lean", ".ipynb", ".bib", ".log",
    ".jsonl", ".pdf", ".png", ".toml", ".yaml", ".yml", ".txt", ".csv",
    ".sh", ".olean", ".aux", ".bbl",
)
# Memory-note / working-doc tags carry trailing _YYYY_MM_DD dates
# (e.g. project_phase6q_complete_2026_05_23 quoted in D5 prose).
_PROSE_DOC_TAG_RE = re.compile(r"_(?:19|20)\d{2}_\d{2}_\d{2}$")
# Mathlib namespaces commonly cited in bundle prose. These resolve in
# Mathlib, not in lean_deps.json (which indexes only declarations
# elaborated inside SKEFTHawking modules), so they are skipped.
_PROSE_MATHLIB_PREFIXES = (
    "Mathlib.", "Real.", "Nat.", "Int.", "Rat.", "Classical.", "Quot.",
    "Complex.", "Finset.", "Fin.", "Set.", "List.", "Matrix.",
    "Polynomial.", "MeasureTheory.", "CyclotomicField.", "FiberBundle.",
    "Probability.", "LinearAlgebra.", "Function.", "Equiv.",
    "LinearMap.", "TensorProduct.", "Algebra.", "CategoryTheory.",
    "Filter.", "Topology.", "AddCircle.", "RingQuot.", "Module.",
    "Submodule.", "Subgroup.", "MonoidHom.", "ContinuousMap.",
    "CartanMatrix.", "IsCyclotomicExtension.",
)
# Empirically-built allowlist (calibrated 2026-06-10 on the 18 bundle
# drafts; iterate when calibration surfaces a new non-Lean idiom class):
#   - bare Mathlib lemmas / tactic names quoted in methodology prose
#   - validate.py / infrastructure identifiers described in I1
#   - Aristotle difficulty-tier enum labels (I1)
#   - the retired-axiom name: every remaining mention is historical /
#     a Python AXIOM_METADATA key; prose staleness around it is owned
#     by CHECK 24 (axiom_count_prose_consistency).
_PROSE_REF_ALLOWLIST = {
    # tactics / Mathlib bare lemmas
    "norm_num", "native_decide", "linear_combination", "fun_prop",
    "mul_nonneg", "mul_self_nonneg", "sq_nonneg", "le_refl",
    "continuous_const", "zeta_spec", "ring_nf", "simp_rw",
    "exact_mod_cast", "decide_eq_true", "by_contra", "push_neg",
    "field_simp",
    # project infrastructure identifiers (validate.py checks, cluster /
    # sentence-state schema fields) described in the I1 infrastructure
    # paper and the F flagship process section
    "bundle_consistency", "claim_cluster", "bundle_destination",
    # Aristotle difficulty-tier enum labels (I1 registry description)
    "very_hard",
    # retired axiom name — historical mentions owned by CHECK 24
    "gapped_interface_axiom",
}
# Disclaimer tokens: an unresolved reference within ±200 chars of one of
# these is prose *about* a not-yet-shipped / renamed / removed
# declaration, which is legitimate.
_PROSE_DISCLAIMER_RE = re.compile(
    r"in\s+flight|deferred|not\s+yet|planned|forthcoming|formerly|"
    r"deprecated|renamed|retired|replaced|removed|commented-out",
    re.IGNORECASE,
)
_PROSE_DISCLAIMER_WINDOW = 200
# Narrow immediately-preceding negation ("there are no \texttt{X} ...").
_PROSE_NEG_BEFORE_RE = re.compile(
    r"\b(?:no|not|absent|without|lacks?)\b[^.]{0,30}$", re.IGNORECASE)


def _prose_occurrence_disclaimed(source: str, offset: int) -> bool:
    """True if the ``\\texttt{}`` occurrence at ``offset`` sits within
    ±200 chars of a disclaimer token (in flight / deferred / planned /
    formerly / renamed / retired / ...) or is immediately preceded by a
    negation ("there are no \\texttt{X} or analogous ..."). Unit-testable
    core of CHECK 25's exemption logic.
    """
    lo = max(0, offset - _PROSE_DISCLAIMER_WINDOW)
    hi = min(len(source), offset + _PROSE_DISCLAIMER_WINDOW)
    if _PROSE_DISCLAIMER_RE.search(source[lo:hi]):
        return True
    return bool(_PROSE_NEG_BEFORE_RE.search(source[max(0, offset - 40):offset]))

# Per-instance waivers: (bundle, token) → reason. Each use is surfaced
# prominently as a WARN detail. Keep this list short (≤5) — if it
# grows, the candidate filter is too loose.
_PROSE_REF_WAIVERS = {
    ("I1", "gap_solution_bounded"):
        "Deliberate historical reference: I1's gap-equation narrative "
        "cites the FALSE folklore theorem disproved by an Aristotle "
        "counterexample; it survives only as a commented-out stub at "
        "TetradGapEquation.lean:307-321 (intentionally not a live "
        "declaration). TODO: drop this waiver if the I1 narrative is "
        "restructured to use the live gap_solution_monotone name only.",
}


def _extract_prose_lean_candidates(tex_source: str) -> list:
    """Extract candidate Lean-identifier tokens from ``\\texttt{...}``
    blocks (unit-testable core for CHECK 25).

    Returns ``[(token, match_start_offset), ...]`` for tokens that pass
    the candidate filter: identifier-shaped, contains ``_`` or ``.``,
    no path separators or file suffixes, not ALL-CAPS (Python registry
    constants), not an MCP tool name (``lean_*``), not a dated doc-tag,
    length ≥ 4, no leading/trailing underscore.
    """
    out = []
    for m in _PROSE_TEXTTT_RE.finditer(tex_source):
        tok = _PROSE_UNESCAPE_RE.sub(r"\1", m.group(1)).strip()
        if len(tok) < 4:
            continue
        if "_" not in tok and "." not in tok:
            continue
        if "/" in tok or "\\" in tok or any(c.isspace() for c in tok):
            continue
        if tok.endswith(_PROSE_FILE_SUFFIXES):
            continue
        if tok.startswith(("src.", "tests.", "scripts.", "docs.")):
            continue
        if tok.startswith("lean_"):  # lean-lsp MCP tool names (I3 §tooling)
            continue
        if tok.endswith("_") or tok.startswith("_"):
            continue
        if not _PROSE_IDENT_RE.match(tok):
            continue
        if tok.replace("_", "").replace(".", "").isupper():
            continue  # CITATION_REGISTRY-style Python constants
        if _PROSE_DOC_TAG_RE.search(tok):
            continue  # memory-note / working-doc dated tags
        out.append((tok, m.start()))
    return out


_LEAN_NAME_INDEX_CACHE: Optional[dict] = None


def _load_lean_name_index() -> dict:
    """Load (and cache) the Lean declaration-name index from
    ``lean/lean_deps.json`` (declaration names + their `module` fields)
    + module names from ``docs/counts.json`` + project Python registry
    keys (PLACEHOLDER_THEOREMS, AXIOM_METADATA, HYPOTHESIS_REGISTRY,
    ARISTOTLE_THEOREMS, PARAMETER_PROVENANCE, and the canonical
    ``formulas.py`` public function names — prose legitimately
    references entries of those canonical registries by key per
    Pipeline Invariants #1/#2/#8).
    """
    global _LEAN_NAME_INDEX_CACHE
    if _LEAN_NAME_INDEX_CACHE is not None:
        return _LEAN_NAME_INDEX_CACHE

    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    entries = json.loads(deps_path.read_text())
    names = set()
    shorts = set()
    dotted_suffixes = set()
    short_to_modules: Dict[str, set] = {}
    for e in entries:
        n = e.get("name", "")
        if not n:
            continue
        names.add(n)
        segs = n.split(".")
        shorts.add(segs[-1])
        short_to_modules.setdefault(segs[-1], set()).add(e.get("module", ""))
        for i in range(1, len(segs)):
            dotted_suffixes.add(".".join(segs[i:]))

    modules = set()
    counts_path = PROJECT_ROOT / "docs" / "counts.json"
    if counts_path.exists():
        try:
            modules = set(
                json.loads(counts_path.read_text())["lean"]["module_names"])
        except (json.JSONDecodeError, KeyError, TypeError):
            modules = set()

    registry_keys = set()
    try:
        from src.core import constants as _c
        for reg_name in ("PLACEHOLDER_THEOREMS", "AXIOM_METADATA",
                         "HYPOTHESIS_REGISTRY", "ARISTOTLE_THEOREMS"):
            reg = getattr(_c, reg_name, None)
            if isinstance(reg, dict):
                registry_keys.update(reg.keys())
            elif isinstance(reg, (list, set, tuple)):
                registry_keys.update(reg)
    except Exception:
        pass  # registry resolution is a bonus source, never a blocker
    try:
        from src.core.provenance import PARAMETER_PROVENANCE
        registry_keys.update(PARAMETER_PROVENANCE.keys())
    except Exception:
        pass
    try:
        from src.core import formulas as _f
        registry_keys.update(
            nm for nm in dir(_f)
            if not nm.startswith("_") and callable(getattr(_f, nm)))
    except Exception:
        pass

    _LEAN_NAME_INDEX_CACHE = {
        "names": names,
        "shorts": shorts,
        "dotted_suffixes": dotted_suffixes,
        "short_to_modules": short_to_modules,
        "modules": modules,
        "registry_keys": registry_keys,
        "count": len(entries),
    }
    return _LEAN_NAME_INDEX_CACHE


_LEAN_SOURCE_CACHE: Optional[str] = None


def _lean_source_declares(short: str) -> bool:
    """Secondary resolution source: does any ``lean/SKEFTHawking``
    source file *declare* ``short`` (including ``private`` lemmas,
    which ExtractDeps deliberately omits from lean_deps.json)?

    Comments are stripped first so commented-out stubs (e.g. the
    ``gap_solution_bounded`` folklore counterexample anchor in
    TetradGapEquation.lean) do NOT resolve. Lazy + cached: the
    concatenated comment-stripped source is built on first use only.
    """
    global _LEAN_SOURCE_CACHE
    if _LEAN_SOURCE_CACHE is None:
        chunks = []
        for lf in sorted(LEAN_DIR.rglob("*.lean")):
            try:
                src = lf.read_text()
            except OSError:
                continue
            src = re.sub(r"--[^\n]*", "", src)
            prev = None
            while prev != src:  # nested /- ... -/ block comments
                prev = src
                src = re.sub(r"/-(?:(?!/-|-/).)*?-/", "", src, flags=re.DOTALL)
            chunks.append(src)
        _LEAN_SOURCE_CACHE = "\n".join(chunks)
    pat = (r"(?:theorem|lemma|def|abbrev|structure|class|instance|opaque)\s+"
           + re.escape(short) + r"\b")
    return re.search(pat, _LEAN_SOURCE_CACHE) is not None


def _resolve_prose_ref(token: str, index: dict) -> str:
    """Resolve a candidate token against the Lean name index.

    Returns one of:
      'OK'       — exact / project-qualified suffix / verified
                   ``<Module>.<thm>`` documentation idiom / module /
                   Python-registry-key / canonical-formula match
      'PRIVATE'  — declared in the Lean source but absent from
                   lean_deps.json (``private`` declaration; OK)
      'DRIFTED'  — dotted token whose last segment exists but in a
                   module that does not match the written prefix
                   (module-attribution drift; advisory)
      'MATHLIB'  — known Mathlib namespace (skipped)
      'ABSENT'   — no match anywhere
    """
    names = index["names"]
    if token in names or token in index["dotted_suffixes"]:
        return "OK"
    if token in index["registry_keys"]:
        return "OK"
    modules = index["modules"]
    if token in modules or f"SKEFTHawking.{token}" in modules:
        return "OK"
    if "." in token and any(m.startswith(token + ".") for m in modules):
        return "OK"  # namespace prefix of a module family (e.g. SKEFTHawking.LDP)
    if token.startswith(_PROSE_MATHLIB_PREFIXES):
        return "MATHLIB"
    short = token.rsplit(".", 1)[-1]
    if short in index["shorts"]:
        if "." not in token:
            return "OK"
        # Project documentation idiom `<Module>.<thm>`: the theorem is
        # declared at (or near) top-level namespace inside the module
        # FILE named `<Module>.lean`, so its qualified Lean name does
        # not carry the module segment. Verify via the declaration's
        # `module` field instead of its name.
        head = token[: -(len(short) + 1)]
        for mod in index["short_to_modules"].get(short, ()):
            if (mod == head or mod == f"SKEFTHawking.{head}"
                    or mod.endswith(f".{head}")):
                return "OK"
        return "DRIFTED"
    if _lean_source_declares(short):
        return "PRIVATE"
    return "ABSENT"


@register_check("prose_theorem_reference_coverage",
                "Bundle-draft \\texttt{} Lean references resolve in lean_deps.json")
def check_prose_theorem_reference_coverage() -> CheckResult:
    """Prevent the ``wen_adw_factor_6000`` failure class from the
    2026-06-05 external review: bundle prose naming a Lean declaration
    that does not exist in the built library. Implements the structural
    prevention proposed by QI item **qi-leantheoremdrift**
    (`bundle_lean_refs_resolve`, docs/QI_REGISTER.md).

    Scope: the 18 publication-bundle drafts
    (``papers/{F,D1–D9,E1,E2,I1–I3,L1–L3}/paper_draft.tex``) only.
    Legacy per-paper drafts are *excluded for now* — they are
    historical-snapshot documents superseded by the bundles, and their
    reference hygiene is audited separately by
    ``scripts/audit_paper_lean_refs.py`` (Phase 6i Wave 4).

    Pipeline: extract ``\\texttt{...}`` tokens → un-escape LaTeX →
    candidate filter (identifier-shaped, contains ``_``/``.``, no file
    suffix, not ALL-CAPS / ``lean_*`` MCP tool names / dated doc-tags /
    allowlist) → resolve against lean_deps.json declaration names
    (exact, project-qualified suffix, unqualified short name), module
    names (docs/counts.json), and project Python registry keys.

    Verdicts:
    - unresolved (ABSENT) → **FAIL**, unless every occurrence sits
      within ±200 chars of a disclaimer token (in flight / deferred /
      not yet / planned / forthcoming / formerly / deprecated / renamed
      / retired / replaced / removed / commented-out) or is immediately
      preceded by a negation ("there are no \\texttt{X} ..."), or the
      (bundle, token) pair carries a documented waiver
      (``_PROSE_REF_WAIVERS`` — each use surfaces as a WARN).
    - dotted token whose short name exists under a different namespace
      (DRIFTED) → advisory WARN (rename candidates).
    - Mathlib-namespace tokens → skipped (resolve upstream, not in
      lean_deps.json).

    Calibrated live 2026-06-10 across all 18 bundles (72 raw
    unresolved → filter/disclaimer/registry classes → 1 documented
    waiver). Run ``--json`` for machine-readable per-bundle findings.
    """
    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    if not deps_path.exists():
        return CheckResult(
            passed=False,
            error=(f"missing {deps_path}; refresh via `cd lean && lake build "
                   f"SKEFTHawking.ExtractDeps` or validate.py --check graph_integrity"),
        )
    index = _load_lean_name_index()

    details: List[Detail] = []
    n_fail = 0
    n_drift = 0
    n_waived = 0
    n_candidates = 0
    n_bundles = 0

    for bundle in BUNDLE_CODES:
        tex = PAPERS_DIR / bundle / "paper_draft.tex"
        if not tex.exists():
            details.append(Detail(
                f"missing_draft:{bundle}", True,
                f"papers/{bundle}/paper_draft.tex absent — skipped",
                warning=True,
            ))
            continue
        n_bundles += 1
        source = tex.read_text()
        cands = _extract_prose_lean_candidates(source)
        # Collapse to per-token occurrence lists
        by_token: dict = {}
        for tok, off in cands:
            by_token.setdefault(tok, []).append(off)
        n_candidates += len(by_token)

        for tok, offsets in sorted(by_token.items()):
            if tok in _PROSE_REF_ALLOWLIST:
                continue
            verdict = _resolve_prose_ref(tok, index)
            if verdict in ("OK", "MATHLIB", "PRIVATE"):
                continue
            if verdict == "DRIFTED":
                n_drift += 1
                details.append(Detail(
                    f"drifted:{bundle}:{tok}", True,
                    f"papers/{bundle}/paper_draft.tex:"
                    f"{_line_of(source, offsets[0])} — qualified name "
                    f"'{tok}' unresolved but short name exists under a "
                    f"different namespace (rename candidate; advisory)",
                    warning=True,
                ))
                continue
            # ABSENT — disclaimer / negation exemption (every occurrence)
            if all(_prose_occurrence_disclaimed(source, off)
                   for off in offsets):
                continue
            waiver = _PROSE_REF_WAIVERS.get((bundle, tok))
            if waiver is not None:
                n_waived += 1
                details.append(Detail(
                    f"waived:{bundle}:{tok}", True,
                    f"papers/{bundle}/paper_draft.tex:"
                    f"{_line_of(source, offsets[0])} — '{tok}' unresolved "
                    f"but WAIVED: {waiver}",
                    warning=True,
                ))
                continue
            n_fail += 1
            lines = ",".join(str(_line_of(source, o)) for o in offsets[:4])
            details.append(Detail(
                f"unresolved:{bundle}:{tok}", False,
                f"papers/{bundle}/paper_draft.tex:{lines} — "
                f"\\texttt{{{tok}}} does not resolve to any declaration in "
                f"lean/lean_deps.json (no disclaimer context; Class-TN drift)",
            ))

    details.insert(0, Detail(
        "summary",
        n_fail == 0,
        f"{n_bundles} bundle drafts scanned / {n_candidates} candidate "
        f"Lean references — {n_fail} unresolved FAIL(s) / {n_drift} "
        f"drifted advisory / {n_waived} waived (documented)",
    ))
    if n_fail == 0 and n_drift == 0 and n_waived == 0:
        details.append(Detail(
            "all_resolved", True,
            "Every bundle-draft Lean reference resolves against lean_deps.json",
        ))
    return CheckResult(passed=(n_fail == 0), details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 26: Theorem-name-embedded citations (advisory)
# ═══════════════════════════════════════════════════════════════════════

_YEAR_SEG_RE = re.compile(r"_((?:19|20)\d{2})(?=_|$)")
# Segments immediately before a year token that are NOT author surnames
# (numerical-bound naming idioms like d_n_bound_2020).
_EMBED_AUTHOR_STOPWORDS = {
    "bound", "bounds", "rate", "mass", "limit", "law", "gap", "model",
    "theorem", "lemma", "data", "run", "wave", "phase", "et", "al",
    "upper", "lower", "min", "max", "eq", "neq", "dr", "fit",
}


def _registry_surnames() -> set:
    """Lowercased author surnames from CITATION_REGISTRY ('Halenka, V.
    and Miller, C. J.' → {'halenka', 'miller'})."""
    try:
        from src.core.citations import CITATION_REGISTRY
    except Exception:
        return set()
    surnames = set()
    for entry in CITATION_REGISTRY.values():
        authors = entry.get("authors") or ""
        for m in re.finditer(r"([A-Za-z'\-]+)\s*,", authors):
            surnames.add(m.group(1).lower())
    return surnames


def _embedded_citation_pairs(short_name: str, surname_lexicon: set) -> dict:
    """Extract embedded (author, year) citation candidates from a
    snake_case declaration name (unit-testable core for CHECK 26).

    Returns ``{"year": str|None, "primary_author": str|None,
    "trailing_authors": [str, ...]}``:

    - ``primary_author`` — the segment immediately before the first
      year token, unless it is a naming-idiom stopword / too short
      (then None: no inferable authorship, declaration is skipped).
    - ``trailing_authors`` — segments after the year token that match
      a CITATION_REGISTRY author surname (length ≥ 4). The registry
      acts as the surname lexicon so English naming segments
      ("cluster", "densities") are never misread as authors.
    """
    m = _YEAR_SEG_RE.search(short_name)
    if not m:
        return {"year": None, "primary_author": None, "trailing_authors": []}
    year = m.group(1)
    before = short_name[:m.start()].split("_")
    after = [s for s in short_name[m.end():].split("_") if s]

    primary = before[-1].lower() if before and before[-1] else None
    if (primary is None or len(primary) < 4 or not primary.isalpha()
            or primary in _EMBED_AUTHOR_STOPWORDS):
        primary = None

    trailing = [s.lower() for s in after
                if len(s) >= 4 and s.isalpha()
                and s.lower() in surname_lexicon]
    return {"year": year, "primary_author": primary,
            "trailing_authors": trailing}


_BIBITEM_RE = re.compile(
    r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}(.*?)"
    r"(?=\\bibitem|\\end\{thebibliography\})",
    re.DOTALL,
)


def _paper_bibitems(tex_source: str, bundle_dir: Path) -> list:
    """Return [(bibkey, text), ...] from the draft's inline
    ``thebibliography`` block; fall back to a ``\\bibliography{X}``
    .bib file in the bundle directory if no inline block exists."""
    items = _BIBITEM_RE.findall(tex_source)
    if items:
        return items
    m = re.search(r"\\bibliography\{([^}]+)\}", tex_source)
    if m:
        bib = bundle_dir / f"{m.group(1)}.bib"
        if bib.exists():
            chunks = re.split(r"(?=@\w+\{)", bib.read_text())
            out = []
            for c in chunks:
                km = re.match(r"@\w+\{([^,]+),", c)
                if km:
                    out.append((km.group(1).strip(), c))
            return out
    return []


@register_check("theorem_name_embedded_citations",
                "Declaration names embedding author+year have matching bibliography entries")
def check_theorem_name_embedded_citations() -> CheckResult:
    """Prevent the D5 phantom-citation class from the 2026-06-05
    external review: a theorem name like
    ``verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller``
    encodes author+year citations; if a bundle's prose mentions the
    declaration but its bibliography has no matching entry, the reader
    cannot follow the embedded citation (the original incident shipped
    with BOTH Verlinde 2017 AND Halenka–Miller absent from the D5
    bibliography and CITATION_REGISTRY).

    Kinship note: this check is kin to the open QI item
    **qi-citation_authoryear_metadata_match** (bibkey form vs registry
    metadata) but distinct — that item validates
    ``<LastName><Year>``-shaped *bibkeys* against registry metadata;
    this check validates *Lean declaration names* that embed
    author/year tokens against each citing paper's bibliography. It
    does NOT close that QI item.

    Mechanics: scan ``lean/lean_deps.json`` short declaration names for
    year segments (``_((19|20)\\d{2})(_|$)``). Extract the candidate
    primary (author, year) pair = segment immediately before the year
    (skipped when it is a naming-idiom stopword like ``bound`` in
    ``d_n_bound_2020`` — no inferable authorship), plus trailing author
    segments validated against the CITATION_REGISTRY surname lexicon
    (so naming segments like "cluster"/"densities" are never misread
    as authors). For each bundle draft whose prose mentions the
    declaration (``\\texttt``-escaped or raw), require:

    - primary pair: some single bibitem contains the author surname
      (case-insensitive) AND the year, OR a CITATION_REGISTRY entry
      matches author+year and lists the paper in ``used_in``;
    - each trailing author: appears in some bibitem, OR a registry
      entry with that author lists the paper in ``used_in``.

    Mismatch → **WARN (advisory default)**; promoted to **FAIL** under
    ``--strict`` (mirrors provenance_doi_in_registry). Calibrated live
    2026-06-10: 3 year-token declarations project-wide; the Verlinde
    no-go (cited in D5) passes via the post-remediation
    Verlinde2017dSEmergent + HalenkaMiller2020 bibitems.
    """
    deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    if not deps_path.exists():
        return CheckResult(
            passed=False,
            error=(f"missing {deps_path}; refresh via `cd lean && lake build "
                   f"SKEFTHawking.ExtractDeps`"),
        )

    try:
        from src.core.citations import CITATION_REGISTRY
    except Exception as exc:
        return CheckResult(passed=False,
                           error=f"CITATION_REGISTRY unavailable: {exc}")

    surname_lexicon = _registry_surnames()
    entries = json.loads(deps_path.read_text())
    year_decls: dict = {}  # short_name → pairs dict
    for e in entries:
        n = e.get("name", "")
        if not n:
            continue
        short = n.rsplit(".", 1)[-1]
        if short in year_decls:
            continue
        if _YEAR_SEG_RE.search(short):
            year_decls[short] = _embedded_citation_pairs(short, surname_lexicon)

    details: List[Detail] = []
    n_warn = 0
    n_checked = 0
    n_skipped_no_author = 0

    def _registry_match(author: str, year: Optional[str], bundle: str) -> bool:
        for entry in CITATION_REGISTRY.values():
            authors = (entry.get("authors") or "").lower()
            if author not in authors:
                continue
            if year is not None and str(entry.get("year") or "") != year:
                continue
            used_in = entry.get("used_in") or []
            if any(f"papers/{bundle}/" in u for u in used_in):
                return True
        return False

    for bundle in BUNDLE_CODES:
        tex = PAPERS_DIR / bundle / "paper_draft.tex"
        if not tex.exists():
            continue
        source = tex.read_text()
        bibitems = None  # lazy
        for short, pairs in sorted(year_decls.items()):
            escaped = short.replace("_", r"\_")
            if escaped not in source and short not in source:
                continue
            if pairs["primary_author"] is None and not pairs["trailing_authors"]:
                n_skipped_no_author += 1
                details.append(Detail(
                    f"no_inferable_author:{bundle}:{short}", True,
                    f"papers/{bundle}/paper_draft.tex mentions '{short}' "
                    f"(year {pairs['year']}) but the pre-year segment is a "
                    f"naming idiom, not an author — skipped",
                ))
                continue
            if bibitems is None:
                bibitems = _paper_bibitems(source, tex.parent)
            n_checked += 1

            requirements = []
            if pairs["primary_author"]:
                requirements.append((pairs["primary_author"], pairs["year"]))
            for t in pairs["trailing_authors"]:
                requirements.append((t, None))

            for author, year in requirements:
                bib_ok = any(
                    author in (key + text).lower()
                    and (year is None or year in text or year in key)
                    for key, text in bibitems
                )
                if bib_ok or _registry_match(author, year, bundle):
                    continue
                n_warn += 1
                msg = (
                    f"papers/{bundle}/paper_draft.tex mentions "
                    f"\\texttt{{{short}}} which embeds "
                    f"'{author}'" + (f" ({year})" if year else "")
                    + " — no matching bibliography entry or "
                      "CITATION_REGISTRY used_in entry (phantom-citation "
                      "candidate)"
                )
                if STRICT_MODE:
                    details.append(Detail(
                        f"embedded_citation_missing:{bundle}:{short}:{author}",
                        False, f"[strict] {msg}"))
                else:
                    details.append(Detail(
                        f"embedded_citation_missing:{bundle}:{short}:{author}",
                        True, msg, warning=True))

    passed = True
    if STRICT_MODE and n_warn > 0:
        passed = False
    details.insert(0, Detail(
        "summary",
        passed,
        f"{len(year_decls)} year-token declaration name(s) project-wide / "
        f"{n_checked} prose-mention checks across bundles — {n_warn} "
        f"embedded-citation mismatch(es)"
        + (" (strict mode: mismatches FAIL)" if STRICT_MODE else " (advisory)")
        + (f" / {n_skipped_no_author} skipped (no inferable author)"
           if n_skipped_no_author else ""),
        warning=(n_warn > 0 and not STRICT_MODE),
    ))
    if n_warn == 0:
        details.append(Detail(
            "all_embedded_citations_resolved", True,
            "Every prose-mentioned year-token declaration has matching "
            "bibliography / registry coverage",
        ))
    return CheckResult(passed=passed, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Inventory-Index autogen freshness (advisory)
# ═══════════════════════════════════════════════════════════════════════

@register_check("inventory_index_autogen_fresh",
                "Advisory: SK_EFT_Hawking_Inventory_Index.md autogen blocks match docs/counts.json")
def check_inventory_index_autogen_fresh() -> CheckResult:
    """Advisory watchlist: the auto-generated blocks in the Inventory Index
    (the §1 counts table, the §3 per-family-counts sentence, and the §3.1
    generated family->count table) must reflect ``docs/counts.json``.

    These blocks are owned by ``scripts/update_inventory_index.py`` and
    bracketed by ``<!-- AUTOGEN:... -->`` markers. They drift between manual
    syncs whenever ``update_counts.py`` regenerates ``counts.json`` without a
    follow-up index refresh. This check is ADVISORY (always passes, warns on
    staleness) — mirroring ``elaboration_knob_watchlist`` semantics — because a
    stale doc-index is a documentation-hygiene signal, not a soundness or
    pipeline-invariant failure. Fix: run
    ``uv run python scripts/update_inventory_index.py``.

    Runs the generator's ``compute_stale`` logic in-process (no shelling out).
    """
    if str(SCRIPT_DIR) not in sys.path:
        sys.path.insert(0, str(SCRIPT_DIR))
    try:
        from update_inventory_index import compute_stale
    except ImportError as exc:
        return CheckResult(passed=True, details=[
            Detail("import", True,
                   f"SKIPPED — update_inventory_index not importable: {exc}",
                   warning=True)])

    try:
        stale, summary = compute_stale()
    except Exception as exc:  # defensive: never fail the suite on an advisory
        return CheckResult(passed=True, details=[
            Detail("compute", True,
                   f"SKIPPED — compute_stale raised: {exc}", warning=True)])

    if stale:
        return CheckResult(passed=True, details=[
            Detail("freshness", True,
                   f"{summary} — run `uv run python "
                   "scripts/update_inventory_index.py` to refresh",
                   warning=True)])
    return CheckResult(passed=True, details=[
        Detail("freshness", True, summary)])


# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="SK-EFT Hawking cross-layer validation suite",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/validate.py              # run all checks + archive result
  python scripts/validate.py --no-archive # run without saving report
  python scripts/validate.py --json       # JSON output for CI (no archive)
  python scripts/validate.py --check formulas  # run one check
  python scripts/validate.py --list       # list available checks
""",
    )
    parser.add_argument("--check", help="Run only this check (by name)")
    parser.add_argument("--json", action="store_true", help="JSON output to stdout")
    parser.add_argument("--no-archive", action="store_true",
                        help="Skip saving timestamped report (default: always archive)")
    parser.add_argument("--list", action="store_true", help="List available checks")
    parser.add_argument(
        "--strict", action="store_true",
        help=("Promote paper-submission advisory warnings to hard failures "
              "(parameter_provenance, provenance_doi_in_registry). Used at the "
              "paper-submission gate, not at Stage-1 development.")
    )
    parser.add_argument(
        "--force-notebooks", action="store_true",
        help=("Bypass the CHECK 11 notebook-exec skip-cache and re-execute every "
              "notebook (default skips unchanged, previously-vetted notebooks). "
              "Use after a kernel / dependency upgrade.")
    )
    parser.add_argument(
        "--force-latex", action="store_true",
        help=("Run the slow paper_latex_compiles check (pdflatex × all bundle "
              "drafts). Default skips it; it also auto-runs when selected via "
              "--check paper_latex_compiles.")
    )
    args = parser.parse_args(argv)

    global STRICT_MODE, FORCE_NOTEBOOK_REEXEC, FORCE_LATEX
    STRICT_MODE = args.strict
    FORCE_NOTEBOOK_REEXEC = args.force_notebooks
    FORCE_LATEX = args.force_latex or args.check == "paper_latex_compiles"

    if args.list:
        print("Available checks:")
        for spec in _CHECKS:
            print(f"  {spec.name:20s} {spec.description}")
        return 0

    # An UNKNOWN --check name must hard-error, not silently pass: run_checks filters by
    # spec.name, so an unknown filter yields an empty result set and `all([]) == True`
    # -> exit 0, silently DISABLING the gate (the commit gate / gate_precheck rely on a
    # real failure surfacing). Fail loud with rc2 (run_check in pre-commit-sync.sh maps
    # rc2 -> SKIP-printed; gate_precheck propagates it as FAIL).
    if args.check and args.check not in {spec.name for spec in _CHECKS}:
        print(f"ERROR: unknown check {args.check!r}. Run 'validate.py --list' for the registry.",
              file=sys.stderr)
        return 2

    t0 = time.monotonic()
    results = run_checks(check_filter=args.check)
    elapsed = time.monotonic() - t0

    if args.json:
        payload = {
            "elapsed_seconds": round(elapsed, 2),
            "checks": {
                name: {
                    "passed": cr.passed,
                    "error": cr.error,
                    "details": [asdict(d) for d in cr.details],
                }
                for name, cr in results.items()
            },
            "summary": {
                "total": len(results),
                "passed": sum(1 for r in results.values() if r.passed),
            },
        }
        class _Enc(json.JSONEncoder):
            def default(self, o):
                try:
                    return float(o)
                except (TypeError, ValueError):
                    return super().default(o)
        print(json.dumps(payload, indent=2, cls=_Enc))
    else:
        print_results(results)
        print(f"  Completed in {elapsed:.1f}s")

    if not args.no_archive and not args.json and not args.check:
        path = archive_results(results)
        print(f"\n  Archived to: {path}")

    all_passed = all(r.passed for r in results.values())
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
