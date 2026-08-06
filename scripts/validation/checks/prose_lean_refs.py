"""Prose → Lean name resolution — ADR-009 Phase 2.

`prose_theorem_reference_coverage` (every verbatim Lean reference in a bundle
draft resolves to a real declaration) and `theorem_name_embedded_citations`
(a declaration name embedding author+year has a matching bibliography entry).

Split from `papers_prose`; see that module's header for the seam. This half owns
the **name index and its three caches** — `_LEAN_NAME_INDEX_CACHE`,
`_LEAN_SOURCE_CACHE`, `_PHYSLIB_SOURCE_CACHE`.

⚠️ **Those three caches are consumed by exactly ONE check's call tree** (this
module's `prose_theorem_reference_coverage`, via `_load_lean_name_index` and
`_resolve_prose_ref`). An earlier claim that they are "shared across checks" was
wrong and is corrected in `tests/validate_characterization.py`. Because they are
module-global and lazily filled, they are also why this module must not be
imported for a one-off resolution without expecting a 70 MB parse.

Resolution is deliberately tiered — project declaration, Mathlib namespace,
`private` decl found in source, then the resolved **PhysLib** Lake dependency.
Dropping the PhysLib tier turns every correct PhysLib reference into a false FAIL,
which is what happened to D10 the moment it entered `BUNDLE_CODES`.

⚠️ **"Verbatim" means THREE syntactic forms, and the corpus uses all three.**
`\\texttt{}`; a preamble one-argument alias for it (D8 and D9 write every
reference as `\\lean{}`); and `\\verb|...|` (D6 writes 235 of those against 25
`\\texttt`). Matching only the first left **564 references beyond the check while
it reported PASS** on a candidate count that read as thorough. Each form was
found separately, on 2026-08-05, during the ADR-010 measurement pass — the
second while re-measuring un-homed modules, the third minutes later while
re-measuring the D6/D9 overlap claim. If a fourth appears, it will be for the
same reason: **the count of things scanned is not evidence that the population
was reached.**

Import rules as in every module here; `theorem_name_embedded_citations` reads
`_cfg.STRICT_MODE` by attribute (H5). MOVED VERBATIM otherwise.
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict, List, Optional

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail, register_check
from validation._tex import _line_of

from bundle_registry import BUNDLE_CODES  # noqa: E402  — see papers_prose.


# ═══════════════════════════════════════════════════════════════════════
# CHECK 25: Prose Lean-theorem reference coverage (bundle drafts)
# (Implements the structural prevention proposed by QI item
#  qi-leantheoremdrift as `bundle_lean_refs_resolve`.)
# ═══════════════════════════════════════════════════════════════════════

_PROSE_TEXTTT_RE = re.compile(r"\\texttt\{([^{}]+)\}")
# A draft may route every Lean reference through a preamble alias for `\texttt`
# rather than writing `\texttt` at each site. D8 and D9 both do
# (`\newcommand{\lean}[1]{\texttt{#1}}`), which put **288 Lean references beyond
# this check's reach while it reported PASS** — the branch's own defect class
# (absence of measurement rendered as success), found by the ADR-010 measurement
# pass 2026-08-05. Discover the aliases from the preamble rather than hardcoding
# `\lean`, so the next bundle that defines `\leanref` does not reopen the hole.
_PROSE_VERBATIM_ALIAS_DEF_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand)\s*\{?\s*\\([A-Za-z]+)\s*\}?"
    r"\s*\[1\]\s*\{\s*\\(?:texttt|mathtt|verb|url|path|code)\s*\{\s*#1\s*\}\s*\}")


def _prose_verbatim_macros(tex_source: str) -> frozenset:
    """Names of preamble macros that are one-argument aliases for ``\\texttt``.

    Always includes ``texttt`` itself. Unit-testable core of the alias fix.
    """
    return frozenset({"texttt"} | set(_PROSE_VERBATIM_ALIAS_DEF_RE.findall(tex_source)))


def _prose_verbatim_re(tex_source: str) -> re.Pattern:
    """The ``\\texttt``-or-alias span regex for one draft."""
    names = sorted(_prose_verbatim_macros(tex_source), key=len, reverse=True)
    return re.compile(r"\\(?:" + "|".join(map(re.escape, names)) + r")\{([^{}]+)\}")


# The THIRD verbatim form, and the one that hid the most. `\verb|name|` takes an
# arbitrary delimiter rather than braces, so neither the `\texttt` regex nor the
# alias regex above sees it. D6 writes **235** `\verb` spans against 25 `\texttt`
# — roughly 90 % of its Lean references — and D2, L1 and L3 add more.
# Found 2026-08-05 immediately after the `\lean{}` fix, while re-measuring the
# audit's "D6 and D9 share 78 identical Lean theorems" claim: D6 appeared to name
# only 9 declarations because its references are `\verb`.
_PROSE_VERB_RE = re.compile(r"\\verb\*?(?P<d>[^A-Za-z0-9\s*])(?P<body>.*?)(?P=d)")


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
    # Surfaced 2026-08-05 when the `\texttt` alias fix (see
    # _PROSE_VERBATIM_ALIAS_DEF_RE) made paper14's `\lean{}` references visible.
    # Both are Mathlib CategoryTheory names the prose itself attributes to
    # Mathlib ("Mathlib's \lean{Rigid.Basic} module").
    "ObjectProperty.", "Rigid.",
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
    "field_simp", "fin_cases",
    # Surfaced 2026-08-05 when `\verb` spans became visible (D6 writes 235 of
    # them). Both are bare Mathlib lemmas D6's own prose attributes to Mathlib;
    # both VERIFIED present in the pinned source rather than taken on the prose's
    # word — Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:139 and
    # Mathlib/Analysis/LocallyConvex/Separation.lean:197.
    "binEntropy_lt_log_two", "geometric_hahn_banach_compact_closed",
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
    blocks, **from any preamble one-argument alias for it** (D8/D9's
    ``\\newcommand{\\lean}[1]{\\texttt{#1}}``), **and from ``\\verb`` spans**
    (D6 writes 235 of those against 25 ``\\texttt``) — unit-testable core
    for CHECK 25.

    Returns ``[(token, match_start_offset), ...]`` for tokens that pass
    the candidate filter: identifier-shaped, contains ``_`` or ``.``,
    no path separators or file suffixes, not ALL-CAPS (Python registry
    constants), not an MCP tool name (``lean_*``), not a dated doc-tag,
    length ≥ 4, no leading/trailing underscore.
    """
    out = []
    spans = [(m.group(1), m.start())
             for m in _prose_verbatim_re(tex_source).finditer(tex_source)]
    spans += [(m.group("body"), m.start())
              for m in _PROSE_VERB_RE.finditer(tex_source)]
    for raw, start in spans:
        tok = _PROSE_UNESCAPE_RE.sub(r"\1", raw).strip()
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
        out.append((tok, start))
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

    # NOTE: unguarded by design — this helper is only reached from checks that have
    # already established lean_deps.json exists. Preserved as-is (ADR-009 H4): making
    # it tolerant here would silently change four callers' behaviour.
    entries = _H.load_lean_deps()
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
    counts_path = _H.COUNTS_JSON_PATH   # one owner (audit QI-11); was re-derived
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
        for lf in sorted(_H.LEAN_DIR.rglob("*.lean")):
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


_PHYSLIB_SOURCE_CACHE: Optional[str] = None
def _physlib_dir():
    # ⚠️ H1: resolved AT EACH USE, not bound at import. A module-level
    # `X = _H.ANCHOR / "..."` is an import-time COPY: a test monkeypatching the
    # anchor does not reach it, so the check silently reads the PRODUCTION tree
    # while the test believes it is reading a fixture. Converted 2026-08-05
    # (PR-review pass 2, R3-I5 / R1).
    return _H.PROJECT_ROOT / "lean" / ".lake" / "packages" / "Physlib"


def _physlib_declares(short: str) -> bool:
    """Tertiary resolution source: does the resolved **PhysLib** Lake
    dependency declare ``short``?

    PhysLib is a first-class dependency of this project (pinned in
    ``lean/lakefile.toml``), and bundle prose legitimately names its
    declarations — e.g. D10 cites ``MatrixMap.of_kraus_CP`` for the Choi
    complete-positivity route, and the D11/D12 drafts lean on the PhysLib
    Schur and POVM/hypothesis-testing substrates. Those names are real but
    can never appear in ``lean_deps.json``, which carries *project*
    declarations only, and they do not start with a Mathlib namespace
    prefix — so without this tier every correct PhysLib reference is a
    false FAIL. (That false positive was live on D10 the moment D10 entered
    ``BUNDLE_CODES``, 2026-07-30.)

    Same comment-stripping + lazy-cache discipline as
    ``_lean_source_declares``. Returns False when the package is not
    vendored (fresh clone before ``lake build``), which degrades to the
    prior ABSENT behaviour rather than silently passing.
    """
    global _PHYSLIB_SOURCE_CACHE
    if _PHYSLIB_SOURCE_CACHE is None:
        if not _physlib_dir().exists():
            _PHYSLIB_SOURCE_CACHE = ""
        else:
            chunks = []
            for lf in sorted(_physlib_dir().rglob("*.lean")):
                try:
                    src = lf.read_text()
                except OSError:
                    continue
                src = re.sub(r"--[^\n]*", "", src)
                prev = None
                while prev != src:
                    prev = src
                    src = re.sub(r"/-(?:(?!/-|-/).)*?-/", "", src, flags=re.DOTALL)
                chunks.append(src)
            _PHYSLIB_SOURCE_CACHE = "\n".join(chunks)
    if not _PHYSLIB_SOURCE_CACHE:
        return False
    pat = (r"(?:theorem|lemma|def|abbrev|structure|class|instance|opaque)\s+"
           + re.escape(short) + r"\b")
    return re.search(pat, _PHYSLIB_SOURCE_CACHE) is not None


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
      'PHYSLIB'  — declared in the resolved PhysLib Lake dependency
                   (resolves upstream, not in lean_deps.json; skipped)
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
    if _physlib_declares(short):
        return "PHYSLIB"
    return "ABSENT"


@register_check("prose_theorem_reference_coverage",
                "Bundle-draft verbatim Lean references — \\texttt{}, preamble "
                "aliases for it (D8/D9's \\lean{}), and \\verb (D6) — resolve "
                "in lean_deps.json")
def check_prose_theorem_reference_coverage() -> CheckResult:
    """Prevent the ``wen_adw_factor_6000`` failure class from the
    2026-06-05 external review: bundle prose naming a Lean declaration
    that does not exist in the built library. Implements the structural
    prevention proposed by QI item **qi-leantheoremdrift**
    (`bundle_lean_refs_resolve`, docs/QI_REGISTER.md).

    Scope: the 21 publication-bundle drafts
    (``papers/{F,D1–D12,E1,E2,I1–I3,L1–L3}/paper_draft.tex``) only.
    D10 joined 2026-07-30 alongside the D11/D12 first-lift — it had been
    shipping since 2026-06-30 outside this gate's scope, which is exactly
    the drift exposure the check exists to close.
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
    # ⚠️ These were `TODO(semantic-review, ADR-009 Phase 3)` until 2026-08-04
    # (audit finding QI-15). Phase 3 is COMPLETE and its §Deferred item 4
    # explicitly DECLINED converting these sites wholesale: 5 are
    # optional-toolchain-absent, 3 advisory by design, 8 are this `lean_deps`
    # divergence kept VISIBLE on purpose, 2 are the annotated H1-silent sites.
    # A TODO pointing at a finished phase reads as unfinished work; the
    # population is frozen instead by `tests/test_cannot_measure_baseline.py`,
    # which fails both on a NEW silent PASS and on a converted site left stale
    # in the baseline.
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> FAIL here, but -> PASS in the
    # four substrate checks above. This is the stricter, arguably correct policy; the
    # divergence is preserved deliberately rather than unified by a refactor.
    if not _H.lean_deps_present():
        return CheckResult(
            passed=False,
            error=(f"missing {_H.LEAN_DEPS_PATH}; refresh via `cd lean && lake build "
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
        tex = _H.PAPERS_DIR / bundle / "paper_draft.tex"
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
            if verdict in ("OK", "MATHLIB", "PRIVATE", "PHYSLIB"):
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

    # ── LEGACY LEG (added 2026-08-05, audit finding QI-32) ──────────────────
    # The 43 non-bundle drafts. `paper_provenance` nominally covered these; its
    # `\texttt{}` regex could not cross the `\_` LaTeX escape, so it matched ZERO
    # references from 2026-03-26 onward while reporting "N verified". Deleting that
    # leg and leaving 43 drafts uncovered would be a walk-back, so the population is
    # measured here instead, with the SAME extractor and resolver the bundle leg
    # uses — one owner for the question.
    #
    # RATCHETED, not per-item failing: these are historical snapshots superseded by
    # the bundles (the scope decision in this docstring stands), and turning 81
    # inherited references red would fire the gate on work nobody is doing. Repairing
    # them is paper substance → ADR-010. What is NOT tolerated is a new one.
    legacy_fail = 0
    legacy_cand = 0
    legacy_drafts = 0
    legacy_by_draft: dict = {}
    for tex in _H.all_paper_drafts():
        name = tex.parent.name
        if name in set(BUNDLE_CODES):
            continue
        legacy_drafts += 1
        source = tex.read_text()
        by_token = {}
        for tok, off in _extract_prose_lean_candidates(source):
            by_token.setdefault(tok, []).append(off)
        legacy_cand += len(by_token)
        for tok, offsets in sorted(by_token.items()):
            if tok in _PROSE_REF_ALLOWLIST:
                continue
            verdict = _resolve_prose_ref(tok, index)
            if verdict in ("OK", "MATHLIB", "PRIVATE", "PHYSLIB", "DRIFTED"):
                continue
            if all(_prose_occurrence_disclaimed(source, off) for off in offsets):
                continue
            legacy_fail += 1
            legacy_by_draft.setdefault(name, []).append(tok)

    from src.core.constants import LEGACY_DRAFT_UNRESOLVED_REF_CEILING as _CEIL
    legacy_over = legacy_fail > _CEIL
    if legacy_over:
        details.append(Detail(
            "legacy_ratchet", False,
            f"{legacy_fail} unresolved reference(s) across {legacy_drafts} legacy "
            f"drafts exceeds the frozen ceiling of {_CEIL}. A NEW unresolved "
            f"\\texttt{{}} Lean reference was added to a legacy draft. Fix it, or "
            f"raise LEGACY_DRAFT_UNRESOLVED_REF_CEILING in src/core/constants.py "
            f"with a stated reason in the same commit."))
    else:
        details.append(Detail(
            "legacy_ratchet", True,
            f"{legacy_drafts} legacy drafts / {legacy_cand} candidate references — "
            f"{legacy_fail} unresolved, at or under the frozen ceiling {_CEIL} "
            f"(inherited debt, itemised below; repair is ADR-010 scope)",
            warning=legacy_fail > 0))
    for dname, toks in sorted(legacy_by_draft.items(),
                              key=lambda kv: (-len(kv[1]), kv[0]))[:12]:
        details.append(Detail(
            f"legacy:{dname}", not legacy_over,
            f"{len(toks)} unresolved: {sorted(toks)[:6]}"
            + (f" (+{len(toks) - 6} more)" if len(toks) > 6 else ""),
            warning=not legacy_over))

    details.insert(0, Detail(
        "summary",
        n_fail == 0 and not legacy_over,
        f"{n_bundles} bundle drafts scanned / {n_candidates} candidate "
        f"Lean references — {n_fail} unresolved FAIL(s) / {n_drift} "
        f"drifted advisory / {n_waived} waived (documented); plus "
        f"{legacy_drafts} legacy drafts / {legacy_cand} candidates / "
        f"{legacy_fail} unresolved vs ceiling {_CEIL}",
    ))
    if n_fail == 0 and n_drift == 0 and n_waived == 0:
        details.append(Detail(
            "all_resolved", True,
            "Every bundle-draft Lean reference resolves against lean_deps.json",
        ))
    return CheckResult(passed=(n_fail == 0 and not legacy_over), details=details)


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
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> FAIL (see the note in
    # prose_theorem_reference_coverage; five sibling checks PASS instead).
    if not _H.lean_deps_present():
        return CheckResult(
            passed=False,
            error=(f"missing {_H.LEAN_DEPS_PATH}; refresh via `cd lean && lake build "
                   f"SKEFTHawking.ExtractDeps`"),
        )

    try:
        from src.core.citations import CITATION_REGISTRY
    except Exception as exc:
        return CheckResult(passed=False,
                           error=f"CITATION_REGISTRY unavailable: {exc}")

    surname_lexicon = _registry_surnames()
    entries = _H.load_lean_deps()
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
        tex = _H.PAPERS_DIR / bundle / "paper_draft.tex"
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
                if _cfg.STRICT_MODE:
                    details.append(Detail(
                        f"embedded_citation_missing:{bundle}:{short}:{author}",
                        False, f"[strict] {msg}"))
                else:
                    details.append(Detail(
                        f"embedded_citation_missing:{bundle}:{short}:{author}",
                        True, msg, warning=True))

    passed = True
    if _cfg.STRICT_MODE and n_warn > 0:
        passed = False
    details.insert(0, Detail(
        "summary",
        passed,
        f"{len(year_decls)} year-token declaration name(s) project-wide / "
        f"{n_checked} prose-mention checks across bundles — {n_warn} "
        f"embedded-citation mismatch(es)"
        + (" (strict mode: mismatches FAIL)" if _cfg.STRICT_MODE else " (advisory)")
        + (f" / {n_skipped_no_author} skipped (no inferable author)"
           if n_skipped_no_author else ""),
        warning=(n_warn > 0 and not _cfg.STRICT_MODE),
    ))
    if n_warn == 0:
        details.append(Detail(
            "all_embedded_citations_resolved", True,
            "Every prose-mentioned year-token declaration has matching "
            "bibliography / registry coverage",
        ))
    return CheckResult(passed=passed, details=details)
