"""Citation and parameter-provenance checks — ADR-009 Phase 2.

`parameter_provenance` (every experimental parameter traces to a published source,
Invariant #8), `citation_primary_sources_present` (every cited bibkey has a cached
primary source, and its header AGREES with the registry),
`provenance_doi_in_registry`, and `bibitem_title_primary_source` (registry title vs
the cached PDF's page-1 form).

WHAT THIS MODULE IS FOR, in one line: it is the layer that stops a hallucinated
citation from surviving in the artifact the pipeline calls its strongest evidence.
`citation_primary_sources_present` originally checked only that a cache FILE
exists — which let a refuted citation be corrected in the .tex and in the registry
while the wrong metadata sat in the cache, still tagged "[fetched]". Its content-
agreement half compares Title/Authors/Venue(journal, volume, page)/Year/DOI/arXiv,
and its discovery is driven by the cache found on disk rather than by a registry
field, so blanking one field cannot opt a bibkey out. A declared
`primary_source_path` that resolves to nothing is a FAILURE for a cited bibkey, not
a silent skip — that skip is how the whole `Phase-6C`/`Phase-6c` cohort went
unchecked on any case-sensitive filesystem while the gate reported PASS.

⚠️ Year stays ADVISORY on purpose (Semantic Scholar returns `year: null` for the
Wiley records), and the venue comparison is abbreviation- and first-page-tolerant.
Both tolerances are pinned by tests; tightening either ships false positives on
formatting differences that are not citation defects.

Three of these read `_cfg.STRICT_MODE` by ATTRIBUTE (H5) — `parameter_provenance`
gates paper submission on human verification, `provenance_doi_in_registry` and
`bibitem_title_primary_source` promote advisories to failures. `--strict` is passed
by `gate_precheck.py submission`, the Paper Submission Gate (Invariant #12) — it is
deliberately NOT passed at wave close, where promoting an in-progress bundle's normal
WARNs to failures would fire the gate on correct work.

Import rules as elsewhere: framework from `validation._registry`, paths as
`_H.<NAME>` at each use, flags by attribute. MOVED VERBATIM otherwise.
"""
from __future__ import annotations

import ast
import re
from typing import List

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail, register_check
from validation._tex import _strip_tex_comments


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
    if _cfg.STRICT_MODE and not_human_required:
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
    #
    # Enforces Pipeline Invariant #8's value half: the provenance registry and the code
    # constant must agree.
    #
    # ⚠️ The comparison must stay GENUINELY RELATIVE. Several project constants are far
    # below 1e-30 (ℏ = 1.05e-34), so a `max(abs(actual), eps)` divide-by-zero guard would
    # silently turn this into an ABSOLUTE test and tolerate order-of-magnitude drift.
    # `actual == 0` is the only case needing special handling; handle it explicitly rather
    # than by flooring every denominator.
    #
    # Entries with no comparable code value are COUNTED and RATCHETED, never skipped in
    # silence — the success message must state the denominator it actually compared.
    mismatches = []
    null_values = []
    unresolvable = []
    compared = 0
    for prov_key, entry in PARAMETER_PROVENANCE.items():
        if entry['value'] is None:
            null_values.append(prov_key)
            continue

        # Look up actual value
        actual = _lookup_provenance_value(prov_key, EXPERIMENTS, ATOMS,
                                          POLARITON_PLATFORMS)
        if actual is None:
            unresolvable.append(prov_key)
            continue
        try:
            a = float(actual)
            r = float(entry['value'])
        except (TypeError, ValueError):
            unresolvable.append(prov_key)   # non-numeric (e.g. string params)
            continue
        compared += 1
        # Genuinely relative. `a == 0` is the only case the old floor was defending
        # against, and it is handled explicitly rather than by contaminating every
        # small-magnitude comparison.
        if a == 0.0:
            if r != 0.0:
                mismatches.append(f"{prov_key}: registry={r}, code=0")
            continue
        rel_err = abs(a - r) / abs(a)
        if rel_err > 0.001:
            mismatches.append(
                f"{prov_key}: registry={r}, code={a} (rel_err={rel_err:.3g})")

    from src.core.constants import PROVENANCE_UNRESOLVABLE_CEILING as _UNRES_CEIL
    if len(unresolvable) > _UNRES_CEIL:
        all_pass = False
        details.append(Detail(
            "value_coverage", False,
            f"{len(unresolvable)} of {len(PARAMETER_PROVENANCE)} provenance entries have "
            f"no comparable code value, above the frozen ceiling {_UNRES_CEIL}. A NEW "
            f"un-comparable entry was added. Wire it to its constant, or raise "
            f"PROVENANCE_UNRESOLVABLE_CEILING in src/core/constants.py with a stated "
            f"reason in the same commit. Newest: {', '.join(sorted(unresolvable)[:3])}"))
    else:
        details.append(Detail(
            "value_coverage", True,
            # ⚠️ The RATCHETED population leads the message. That is the parsing
            # convention `tests/test_ratchets_have_zero_headroom.py` relies on to
            # measure headroom without re-implementing any check's counting; this
            # message led with `compared` instead and read as 119 of slack.
            f"{len(unresolvable)} of {len(PARAMETER_PROVENANCE)} provenance entries "
            f"have no comparable code value (at or under the frozen ceiling "
            f"{_UNRES_CEIL} — inherited debt, repair is ADR-010 scope); "
            f"{compared} value(s) compared against code",
            warning=bool(unresolvable)))

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
                              f"all {compared} comparable provenance values match code"))

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


def _lookup_provenance_value(prov_key, experiments, atoms, polariton_platforms):
    """Look up the actual value in constants for a provenance key like 'Steinhauer.omega_perp'."""
    # (`import numpy as np` stood here and was never used — removed 2026-08-04, audit QI-10.)
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

    # The three registries the caller passes explicitly, then EVERY other
    # dict-of-dicts registry in constants.
    #
    # ⚠️ This branch used to hand-list ATOMS / EXPERIMENTS / POLARITON_PLATFORMS
    # only, so `GRAPHENE_PLATFORMS` was invisible: all six `Dean_bilayer_nozzle.*`
    # entries resolved to None and sat inside the "inherited debt" ceiling,
    # unnoticed, because an unresolvable entry is *counted* rather than *reported*.
    # A hand-listed consumer set beside a registry is the defect class ADR-009
    # exists to close (cf. H4), so the sweep is derived, not extended by one.
    for registry in (atoms, experiments, polariton_platforms):
        if group in registry:
            return registry[group].get(key)

    for reg in _dict_of_dict_registries():
        if group in reg:
            return reg[group].get(key)

    # ── FLAT registries (2026-08-15) ──────────────────────────────────────────────
    # ⚠️ A dotted key does not always name `registry[group][key]`. The electroweak
    # constants live in FLAT module-level dicts — `EW_PARAMS['M_H_GEV']`, not
    # `SOMETHING['EW']['M_H_GEV']` — so for that whole family the group is a
    # registry-name PREFIX rather than a key inside one, and every `EW.*` entry
    # resolved to None.
    #
    # This is the more expensive shape of the same defect the dict-of-dicts sweep
    # above was written to close: an unresolvable entry is COUNTED, not reported, so
    # the gap sat inside the ceiling silently. Worse, it made the ratchet reward
    # neglect — I1 Stage-13 finding 2.1 ADDED three well-sourced provenance entries
    # and the ceiling had to be RAISED by three, because recording a parameter's DOI
    # and abstract sentence moved it into the unresolvable population. A ratchet that
    # rises when provenance improves is measuring the wrong thing.
    #
    # Derived, not hand-listed (ADR-009 H4): the group is matched against module-level
    # dict names, never against an enumerated set of families.
    for reg in _flat_registries(group):
        if key in reg:
            return reg[key]

    return None


def _flat_registries(group: str):
    """Flat module-level dicts in `src.core.constants` that `group` could name.

    `EW` matches `EW_PARAMS` and `EW`; the `_PARAMS` suffix is this project's naming
    convention for a flat scalar registry. Only dicts with at least one NON-dict value
    are yielded, so a dict-of-dicts registry cannot be reached twice by two different
    rules and return different answers.
    """
    from src.core import constants as _c

    for name in (f"{group}_PARAMS", group):
        val = getattr(_c, name, None)
        if not isinstance(val, dict) or not val:
            continue
        if any(not isinstance(v, dict) for v in val.values()):
            yield val


def _dict_of_dict_registries():
    """Every module-level dict-of-dicts in `src.core.constants`.

    Yields the registries a dotted provenance key could name. Non-dict values
    and empty dicts are skipped, so a plain lookup table of scalars never
    masquerades as a platform registry.
    """
    from src.core import constants as _c

    for name in dir(_c):
        if name.startswith('_'):
            continue
        val = getattr(_c, name, None)
        if not isinstance(val, dict) or not val:
            continue
        if all(isinstance(v, dict) for v in val.values()):
            yield val


# ═══════════════════════════════════════════════════════════════════════
# CHECK 19: Citation primary-source cache present (Phase 6i Wave 1)
# ═══════════════════════════════════════════════════════════════════════

def _discover_cache_for(bibkey: str):
    """Find a primary-source cache for `bibkey` by globbing, independently of what the
    registry declares. Mirrors the discovery the existence half of
    `citation_primary_sources_present` performs, so the content half cannot be opted out
    of by editing one registry field (D11 round-8 finding 1.1)."""
    from src.core.workspace import find_workspace as _fw
    base = _fw() / "Lit-Search"
    if not base.is_dir():
        return None
    for phase in base.iterdir():
        d = phase / "primary-sources"
        if not d.is_dir():
            continue
        # Every cache extension the existence half accepts. A `.pdf` or `.json` cache is
        # a legitimate primary source with no parseable header — it resolves here (so it
        # is not reported unresolvable) and the caller skips the header comparison.
        for ext in ("abstract.txt", "txt", "md", "json", "pdf"):
            cand = d / f"{bibkey}.{ext}"
            if cand.is_file():
                return cand
        low = f"{bibkey}.".lower()
        for cand in d.iterdir():
            if cand.name.lower().startswith(low) and cand.is_file():
                return cand
    return None


# ── Venue agreement (D11 round-4 finding 1.1, round-8 finding 1.1) ──────────
# `READINESS_GATES.md:36` states Gate 1 passes iff "Journal/volume/page/year in bibitem
# matches registry (for published refs)". Until this was added, NOTHING compared those
# three: a reviewer mutated `Voigt1889`'s journal, volume AND page all at once and the
# check stayed green (MUT-7). Year deliberately stays advisory — Semantic Scholar returns
# `year: null` for both Wiley records, so gating on it would ship false positives.
_VENUE_STOP = {"the", "of", "and", "und", "der", "die", "das", "for", "fur", "in", "on",
               "a", "an", "de", "et", "zur", "zum", "part", "series", "section"}


def _venue_tokens(s: str) -> list[str]:
    """Accent-folded, lowercased content tokens of a journal name."""
    import unicodedata
    folded = unicodedata.normalize("NFKD", s)
    folded = "".join(c for c in folded if not unicodedata.combining(c))
    # ß folds to ss only under NFKC-casefold; do it explicitly so "Fließgrenze" style
    # names tokenize the same on both sides.
    folded = folded.replace("ß", "ss").lower()
    return [t for t in re.findall(r"[a-z0-9]+", folded)
            if len(t) > 1 and t not in _VENUE_STOP]


def _tok_match(a: str, b: str) -> bool:
    """Abbreviation-tolerant token equality: `phys` matches `physical`, `lett` matches
    `letters`. Equality alone would fail every abbreviated registry journal name against
    a spelled-out cache header, which is a formatting difference, not a citation defect."""
    if a == b:
        return True
    lo, hi = (a, b) if len(a) <= len(b) else (b, a)
    return len(lo) >= 3 and hi.startswith(lo)


def _token_subset(small: list[str], big: list[str]) -> bool:
    return all(any(_tok_match(s, t) for t in big) for s in small)


def _venue_mismatch(venue_line: str, entry: dict) -> str | None:
    """Compare a cache header `Venue:` line against the registry's journal/volume/page.

    The cache writes `Venue: <journal>, <volume>, p. <page> (<year>)`. Only the parts
    that parse on BOTH sides are compared, and each carries the tolerance the round-8
    finding measured as mandatory:

      journal — token-SUBSET, not equality. S2 returns
                "Zamm-zeitschrift Fur Angewandte Mathematik Und Mechanik" where the
                registry holds "Zeitschrift fur Angewandte Mathematik und Mechanik".
      volume  — exact.
      page    — first-page tolerant. A registry holding '573-587' against a bibitem
                printing '573' is the documented convention, not a drift.

    Returns a human-readable reason, or None when the two agree.
    """
    reasons: list[str] = []
    line = venue_line.strip()
    if not line:
        return None

    # ── journal ──────────────────────────────────────────────────────────────
    # Compare against the WHOLE line's tokens rather than a chopped prefix. The corpus
    # writes the volume glued to the name (`Physical Review A 70, 052328 (2004)`), and
    # writes the published venue inside a parenthetical when the cache records a preprint
    # (`arXiv preprint (later ACM Transactions on Quantum Computing)`). Any prefix rule
    # that tried to isolate the name mislabelled one of those two shapes; requiring the
    # registry's journal tokens to appear SOMEWHERE in the venue line handles both and
    # still fails a wholly different journal.
    reg_j = entry.get("journal")
    if reg_j:
        c_t, r_t = _venue_tokens(line), _venue_tokens(str(reg_j))
        if c_t and r_t and not _token_subset(r_t, c_t):
            reasons.append(f"journal registry={reg_j!r} not found in venue {line!r}")

    # ── volume / page ────────────────────────────────────────────────────────
    # Both are read from the one shape that is unambiguous on both sides: `<vol>, <page>`
    # (with an optional `p.`/`pp.`). A venue that does not carry that shape contributes no
    # volume/page comparison rather than a guessed one.
    m = re.search(r"(?<![0-9])([0-9]{1,4})\s*,\s*(?:pp?\.\s*)?([0-9]+(?:[-–][0-9]+)?)",
                  line)
    if m:
        v_cache, p_cache = m.group(1), m.group(2)
        reg_v = entry.get("volume")
        if reg_v not in (None, "") and str(reg_v).strip() != v_cache:
            reasons.append(f"volume cache={v_cache} registry={reg_v}")
        reg_p = entry.get("page") or entry.get("pages")
        if reg_p not in (None, ""):
            rp = str(reg_p).strip().replace("–", "-")
            cp = p_cache.replace("–", "-")
            # First-page tolerance in both directions: '573-587' vs '573'.
            if not (rp == cp or rp.startswith(cp + "-") or cp.startswith(rp + "-")):
                reasons.append(f"page cache={cp} registry={rp}")
    return "; ".join(reasons) if reasons else None


@register_check("citation_primary_sources_present",
                "Every cited external bibitem has a primary-source cache, and an "
                "abstract-only one is flagged rather than counted as the source")
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
    # (`import ast` / `import re` stood here, shadowing the module-level imports —
    #  removed 2026-08-04, audit QI-11.)
    from src.core.citations import CITATION_REGISTRY, bibkey_phase
    from src.core.workspace import find_workspace

    LIT_SEARCH = find_workspace() / "Lit-Search"
    FALLBACK = "Phase-1-and-Background"
    EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]

    # ── Duplicate-key guard (added 2026-07-31) ────────────────────────────────
    # CITATION_REGISTRY is a dict *literal*, so a repeated key is legal Python:
    # the later entry silently wins and the earlier one's `used_in` consumers and
    # `primary_source_path` become unreachable. That is invisible to every check
    # that reads the imported dict, because by then the duplicate is already gone.
    # It shipped undetected for two Stage-13 rounds ('Berry1984'). Detect it by
    # parsing the source, not the imported object.
    dup_details = []
    try:
        # ADR-009 H1 — the other SILENT site: the `except` below downgrades to an
        # advisory warning, so a retargeted anchor would disable this duplicate-key
        # guard without failing anything.
        _reg_src = (_H.SRC_DIR / "core" / "citations.py").read_text(encoding="utf-8")
        _tree = ast.parse(_reg_src)
        _seen: dict[str, int] = {}
        for _node in ast.walk(_tree):
            if not isinstance(_node, ast.Dict):
                continue
            for _k in _node.keys:
                if isinstance(_k, ast.Constant) and isinstance(_k.value, str):
                    _seen[_k.value] = _seen.get(_k.value, 0) + 1
        _dups = sorted(k for k, n in _seen.items() if n > 1 and k in CITATION_REGISTRY)
        if _dups:
            dup_details.append(Detail(
                "duplicate_bibkeys", False,
                f"{len(_dups)} bibkey(s) defined more than once in citations.py — the later "
                f"literal silently shadows the earlier, orphaning its used_in/primary_source_path: "
                f"{', '.join(_dups)}",
            ))
    except Exception as exc:  # pragma: no cover - guard must never mask the real check
        dup_details.append(Detail(
            "duplicate_bibkeys", True,
            f"duplicate-key scan skipped ({type(exc).__name__}: {exc})", warning=True,
        ))

    # Match \cite, \citep, \citet, \citeauthor, etc., with optional star,
    # optional [opt-args], then {key1,key2,...}
    CITE_RE = re.compile(r"\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}")

    details: List[Detail] = []
    all_pass = True

    paper_tex_files = _H.all_paper_drafts()     # ALL drafts (bundles + legacy)
    if not paper_tex_files:
        return CheckResult(passed=False, error="No papers/*/paper_draft.tex found")

    # First pass: collect (bibkey, paper_key) usage across all papers
    usage: dict[str, set[str]] = {}
    for tex_path in paper_tex_files:
        paper_key = tex_path.parent.name
        text = tex_path.read_text(encoding="utf-8", errors="replace")
        # Strip TeX comments so commented-out \cite{} are not gated.
        # DRY: the `\%`-aware canonical stripper. The naive `split("%", 1)[0]`
        # this replaced truncates at an ESCAPED percent — measured on papers/I1,
        # 1 hit against 3, a 3x undercount. Six copies of this existed.
        text_uncommented = _strip_tex_comments(text)
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
    abstract_only: list[tuple[str, list[str]]] = []    # (key, papers) — ADR-014 D1

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
                # ADR-014 D1 — FIDELITY, not mere presence. `abstract.txt` is an accepted
                # extension, so before this it was indistinguishable from a full text and the
                # check reported "cached" either way. Mather1982 is the measured cost: its
                # cache file's own last line says the body has never been read, and a
                # convention ambiguity worth 21.5 points at D12's worked point was recorded as
                # a property of the SOURCE rather than of not having read it — while this
                # check stayed green throughout.
                if ext == "abstract.txt":
                    abstract_only.append((bibkey, sorted(usage[bibkey])))
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

    n_abstract = len(abstract_only)

    details.append(Detail(
        "summary",
        n_uncached == 0 and n_missing == 0,
        f"{n_cited} bibkeys cited across {len(paper_tex_files)} papers — "
        f"{n_cached} cached ({n_cached - n_abstract} full text, "
        f"{n_abstract} ABSTRACT ONLY) / {n_inprep} inprep-exempt / "
        f"{n_textbook} textbook-exempt / "
        f"{n_uncached} need cache / {n_missing} missing-from-registry"
    ))

    if abstract_only:
        # ADVISORY, not a failure — ADR-014 D4, operator decision 2026-08-15. Acquisition is
        # the only remedy and it costs money, so blocking here would stall every downstream
        # stage behind a purchase queue, including the adversarial review that would find the
        # next such defect. It FLAGS, and the register ranks what is worth buying.
        sample = ", ".join(k for k, _ in abstract_only[:6])
        more = f" (and {n_abstract - 6} more)" if n_abstract > 6 else ""
        details.append(Detail(
            "abstract_only_fidelity",
            True,
            f"⚠️ {n_abstract} cited source(s) held as a publisher ABSTRACT, not full text: "
            f"{sample}{more}. An abstract is not evidence of what the source says, so a claim "
            f"resting on one is unbacked — and a provenance record describing such a source's "
            f"'ambiguity' is recording our own ignorance of it. Ranked by whether a claim "
            f"actually depends on it in docs/SOURCE_ACQUISITION_REGISTER.md; regenerate with "
            f"scripts/source_acquisition_register.py.",
            warning=True,
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

    # Fold in the duplicate-key guard: a shadowed bibkey is a CitationIntegrity
    # defect even when every cache file is present.
    details.extend(dup_details)
    all_pass = all_pass and all(d.passed for d in dup_details)

    # ── Cache CONTENT agreement (added 2026-07-31) ────────────────────────────
    # This check historically verified only that a cache file EXISTS. That let a
    # hallucinated citation be caught in the .tex, fixed in the .tex and in
    # CITATION_REGISTRY, and survive verbatim in the cache — the artifact the
    # pipeline calls its strongest evidence class — while this check reported
    # PASS. Two Stage-13 BLOCKERs of exactly that shape shipped
    # (BoldoLaxMilgram2016, LeanLJ2025), each with the refuted metadata still
    # tagged "[fetched]".
    #
    # (An earlier version of this comment claimed promote_primary_sources.py writes
    # cache contents back into the registry, making a stale cache self-propagating.
    # That was asserted without reading the script and is FALSE -- it reads only its
    # sidecar JSON, missing_bibkey_stubs.json and citations.py, and inserts only
    # 'inprep' and 'primary_source_path'. Corrected 2026-07-31, D11 round 4. The
    # cache is a bad RECORD, not a loaded gun -- which is reason enough to gate it.)
    #
    # Compare each cache header's Title:/arXiv: against the registry.
    title_details = []
    _norm_ws = lambda s: " ".join(s.split()).strip().lower()
    # ⚠️ BYPASS CLOSED 2026-07-31 (D11 Stage-13 round-8 finding 1.1). This loop used to
    # `continue` whenever `primary_source_path` was absent or did not end in
    # `.abstract.txt`, while the EXISTENCE half above globs for `<bibkey>.<ext>` by bibkey
    # independently of that field. So blanking one registry field passed existence (the
    # file is still on disk and still found by glob) and silently skipped every content
    # check — title, authors, year, DOI, arXiv. A reviewer took that path green in three
    # mutations. The loop is now driven by the cache DISCOVERED for each bibkey, so the
    # registry cannot opt itself out, and a declared-but-unresolvable path is a FAIL
    # rather than a silent skip.
    # A dangling `primary_source_path` is a hard FAIL for a bibkey some paper actually
    # cites — that is this check's population, and a cited entry whose declared cache
    # resolves to nothing gets NO content check while reading as provenance. For an entry
    # no draft cites yet it is an advisory: registry rows are routinely staged before
    # their cache is fetched, and failing those would make this gate report on work in
    # progress rather than on the corpus the papers ship.
    for bibkey, entry in sorted(CITATION_REGISTRY.items()):
        ps = entry.get("primary_source_path")
        declared = bool(ps)
        is_cited = bibkey in usage
        cache_file = (find_workspace() / ps) if ps else None
        if cache_file is None or not str(ps).endswith(".abstract.txt"):
            # No usable declared path: fall back to the same discovery the existence half
            # uses, so the content checks still run on whatever cache is actually present.
            found = _discover_cache_for(bibkey)
            if found is None:
                if declared:
                    title_details.append(Detail(
                        f"cache_path_unresolvable:{bibkey}", not is_cited,
                        f"registry declares primary_source_path={ps!r} but no cache "
                        f"resolves for this bibkey by any extension, so NO content check "
                        f"ran. A declared path that names nothing is worse than none: it "
                        f"reads as provenance."
                        + ("" if is_cited else " (advisory: no draft cites this bibkey"
                                              " yet)"),
                        warning=not is_cited))
                continue
            # Header comparison needs a parseable header. A `.pdf`/`.json` cache has none;
            # that is a real cache, just not one this half can read — skip silently, as the
            # `.abstract.txt` opt-in used to, but ONLY after discovery proved it exists.
            if found.suffix not in (".txt", ".md"):
                continue
            cache_file = found
        if not cache_file.exists():
            # Case-insensitive retry: registry paths say `Phase-6E`/`Phase-6C` while the
            # directories on disk are `Phase-6e`/`Phase-6c`. That resolves on APFS but NOT
            # on a case-sensitive filesystem, where every entry would fall through this
            # branch and the gate would report PASS having checked nothing (D11 round-4
            # finding). Resolve explicitly rather than skip.
            parent = cache_file.parent
            resolved = None
            if not parent.exists():
                gp = parent.parent
                if gp.exists():
                    for cand in gp.iterdir():
                        if cand.is_dir() and cand.name.lower() == parent.name.lower():
                            parent = cand
                            break
            if parent.exists():
                for cand in parent.iterdir():
                    if cand.name.lower() == cache_file.name.lower():
                        resolved = cand
                        break
            if resolved is None:
                # ⚠️ WAS A SILENT `continue` (D11 round-4 finding 1.2). A declared
                # `.abstract.txt` path that resolves to nothing skipped EVERY content
                # comparison — title, authors, DOI, arXiv, venue — and the check reported
                # `cache_content_agreement PASS` having read nothing for that entry. That
                # is the same failure mode as the opt-in bypass closed above, reached by a
                # typo instead of an edit; on a case-sensitive filesystem the whole
                # `Phase-6C`/`Phase-6c` cohort took it. Discovery gets one more chance
                # (the cache may exist under another extension), and if that also finds
                # nothing the declared path is a FAILURE, not a skip.
                found = _discover_cache_for(bibkey)
                if found is None:
                    title_details.append(Detail(
                        f"cache_path_unresolvable:{bibkey}", not is_cited,
                        f"registry declares primary_source_path={ps!r} but nothing "
                        f"resolves there and no cache resolves for this bibkey by any "
                        f"extension, so NO content check ran. A declared path that names "
                        f"nothing is worse than none: it reads as provenance."
                        + ("" if is_cited else " (advisory: no draft cites this bibkey"
                                              " yet)"),
                        warning=not is_cited))
                    continue
                title_details.append(Detail(
                    f"cache_path_wrong:{bibkey}", not is_cited,
                    f"registry declares primary_source_path={ps!r}, which does not "
                    f"resolve; the cache actually on disk is {found}. Correct the "
                    f"registry path — a provenance field that points at the wrong file "
                    f"is not provenance."))
                if found.suffix not in (".txt", ".md"):
                    continue
                cache_file = found
            else:
                cache_file = resolved
        try:
            head = cache_file.read_text(encoding="utf-8", errors="replace")[:4000]
        except OSError:
            continue
        m_title = re.search(r"^Title:\s*(.+)$", head, re.MULTILINE)
        reg_title = entry.get("title")
        if m_title and reg_title:
            if _norm_ws(m_title.group(1)) != _norm_ws(reg_title):
                title_details.append(Detail(
                    f"cache_title_mismatch:{bibkey}", False,
                    f"{cache_file} header Title disagrees with CITATION_REGISTRY. "
                    f"cache={m_title.group(1).strip()!r} registry={reg_title!r}. "
                    f"The cache is this pipeline's designated primary-source evidence; a "
                    f"disagreement means one of the two is wrong.",
                ))
        # Author-surname agreement. The round-2 LeanLJ2025 defect was a wrong TITLE *and*
        # three wrong author initials; a title-only check catches that one but not an
        # author-only drift, so compare surnames too (initials and accents vary).
        m_auth = re.search(r"^Authors:\s*(.+)$", head, re.MULTILINE)
        reg_auth = entry.get("authors")
        if m_auth and reg_auth:
            _STOP = {"and", "the", "van", "der", "den", "von", "de", "di", "el"}

            def _surnames(s: str) -> set:
                # Tokenize into WORDS, not comma-separated chunks: the cache writes
                # "Scott Aaronson, Daniel Gottesman" while the registry writes
                # "Aaronson, S. and Gottesman, D.", so a chunk comparison never
                # intersects. Drop initials (len<=2) and connectives.
                out = set()
                for w in re.findall(r"[A-Za-zÀ-ÿ'’-]+", s):
                    wl = w.lower()
                    if len(wl) > 2 and wl not in _STOP:
                        out.add(wl)
                return out
            c_s, r_s = _surnames(m_auth.group(1)), _surnames(reg_auth)
            if c_s and r_s and not (c_s & r_s):
                title_details.append(Detail(
                    f"cache_authors_mismatch:{bibkey}", False,
                    f"{ps} header Authors shares no surname with CITATION_REGISTRY. "
                    f"cache={m_auth.group(1).strip()!r} registry={reg_auth!r}",
                ))
        # Year is ADVISORY only: a cache recording an arXiv v1 year against a registry
        # holding the journal year is a legitimate convention difference, not a defect.
        m_year = re.search(r"^Year:\s*(\d{4})", head, re.MULTILINE)
        reg_year = entry.get("year")
        if m_year and reg_year and int(m_year.group(1)) != int(reg_year):
            title_details.append(Detail(
                f"cache_year_advisory:{bibkey}", True,
                f"{ps} header Year {m_year.group(1)} != registry {reg_year} "
                f"(preprint vs publication year?)", warning=True,
            ))
        m_doi = re.search(r"^DOI:\s*(\S+)", head, re.MULTILINE)
        reg_doi = entry.get("doi")
        if m_doi and reg_doi and m_doi.group(1).strip().rstrip('.') != str(reg_doi).strip():
            title_details.append(Detail(
                f"cache_doi_mismatch:{bibkey}", False,
                f"{ps} header DOI {m_doi.group(1)} != registry {reg_doi}",
            ))
        # Venue: journal / volume / page. See `_venue_mismatch` for the three
        # normalizations that keep this from firing on formatting differences.
        m_ven = re.search(r"^Venue:\s*(.+)$", head, re.MULTILINE)
        if m_ven:
            why = _venue_mismatch(m_ven.group(1), entry)
            if why:
                title_details.append(Detail(
                    f"cache_venue_mismatch:{bibkey}", False,
                    f"{cache_file} header Venue disagrees with CITATION_REGISTRY: {why}. "
                    f"Gate 1 requires journal/volume/page agreement for published refs.",
                ))
        m_ax = re.search(r"^arXiv:\s*([0-9]{4}\.[0-9]{4,5}|[a-z-]+/[0-9]{7})", head, re.MULTILINE)
        reg_ax = entry.get("arxiv")
        if m_ax and reg_ax and m_ax.group(1).strip() != str(reg_ax).strip():
            title_details.append(Detail(
                f"cache_arxiv_mismatch:{bibkey}", False,
                f"{ps} header arXiv {m_ax.group(1)} != registry {reg_ax}",
            ))
    if not title_details:
        title_details.append(Detail(
            "cache_content_agreement", True,
            "Every .abstract.txt cache header agrees with its registry "
            "Title/Authors/Venue(journal,volume,page)/Year/DOI/arXiv, and every "
            "declared primary_source_path resolves",
        ))
    details.extend(title_details)
    all_pass = all_pass and all(d.passed for d in title_details)

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
        if _cfg.STRICT_MODE:
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
    (`validate.py --strict`, reached via `gate_precheck.py submission`)
    promotes the **DROP-WORD class only** to FAIL, and only above the frozen
    `BIBITEM_TITLE_DRIFT_CEILING`.

    ⚠️ Corrected 2026-08-05 (audit QI-33). Strict promoted NOT-FOUND too, while
    this docstring and the code's own comments call NOT-FOUND advisory *because
    it is false-positive-prone* — page 1 is frequently a journal cover or a
    metadata block and the title is simply not on it. Live: 58 NOT-FOUND against
    7 DROP-WORD. That contradiction was inert only while nothing passed
    `--strict`; the submission gate became that caller the day before.

    ⚠️ MEASURED LIMITATION. DROP-WORD requires the REST of the title to match
    page 1, so an entry already flagged NOT-FOUND absorbs further drift without
    raising anything. 58 live entries are in that state, and this check must not
    be quoted as covering them.

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
    # (`import re` stood here, shadowing the module-level import — audit QI-11.)
    from src.core.citations import CITATION_REGISTRY
    from src.core.workspace import find_workspace

    # ps_path entries are workspace-relative (`Lit-Search/...`), so resolve
    # against the workspace root. Layout-independent (main checkout AND a
    # worktree slot); the old `__file__.parent×3` walk resolved to
    # `.claude/worktrees` from a worktree. Per CLAUDE.md: no parent-walks.
    PROJECT_ROOT_LOCAL = find_workspace()

    try:
        from pdfminer.high_level import extract_text  # type: ignore
    except ImportError:
        return CheckResult(
            passed=True, measured=False,
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

        # WHITESPACE-INSENSITIVE containment (added 2026-08-05, audit QI-33).
        # `pdfminer` splits and joins words in ways the publisher did not: a title
        # set across a line break arrives as `quasi distillation` for
        # `quasidistillation`, and a two-column page-1 header can interleave the
        # title's own characters. Both produced DROP-WORD flags — the check's
        # HIGH-CONFIDENCE class — for entries whose title is verbatim correct.
        # Measured over the live registry: 2 of 9 flags were this artifact
        # (`Horodecki1999`, `ElingGuedensJacobson2006fR`).
        #
        # Scoped deliberately as a containment test, not a normalisation change:
        # collapsing whitespace globally would also erase the word boundaries the
        # DROP-WORD signal depends on.
        if norm_title.replace(" ", "") in norm_page.replace(" ", ""):
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

    # Under `--strict` BOTH drift classes fail. In default mode NOTHING fails here:
    # DROP-WORD and NOT-FOUND are both surfaced as ⚠ warnings.
    #
    # ⚠️ Two corrections, 2026-08-04 (audit QI-08). The code read:
    #     summary_passed = _cfg.STRICT_MODE is False or (n_drop_word == 0 and ...)
    #     if not _cfg.STRICT_MODE:
    #         summary_passed = True
    # The `if` was a NO-OP — it can only fire when `STRICT_MODE` is False, which is
    # exactly the case where the first line has already produced `True`. And the
    # comment above it claimed "in default mode, only DROP-WORD flags fail", which
    # the body contradicts: the per-finding Details carry `passed=not STRICT_MODE`,
    # so in default mode a DROP-WORD hit passes too. The comment now describes what
    # the code does.
    # ⚠️ TWO FURTHER CORRECTIONS, 2026-08-05 (audit QI-33).
    #
    # (1) NOT-FOUND was promoted to a hard failure under `--strict`, while the comment
    #     eight lines up and the docstring both call it advisory *because it is
    #     false-positive-prone* — page 1 is often a journal cover, a chapter intro, or
    #     heavy metadata, and the title simply is not on it. Live: **62 NOT-FOUND**
    #     against 9 DROP-WORD. `--strict` now had a caller (`gate_precheck submission`,
    #     added the day before), so this would have made the submission gate red on 62
    #     entries the check itself declines to call defects — a gate that fires on
    #     correct data, which is a gate that gets switched off. `--strict` now promotes
    #     the HIGH-CONFIDENCE DROP-WORD class only; NOT-FOUND stays advisory in both
    #     modes, as documented.
    #
    # (2) DROP-WORD is RATCHETED rather than absolute. Measured after the
    #     whitespace-insensitive repair above: 7 flags remain, and they are real
    #     registry-vs-published differences ("entropy of the BTZ black hole" where the
    #     published title has no "the"; `Turyshev2026DESI`'s title is a stub). They are
    #     worth fixing — that is exactly the BLOCKER pattern this check was built for —
    #     but CITATION_REGISTRY is corpus-wide, so an unratcheted bar blocks submission
    #     of every paper on a drifted title used by any other. Repairing the 7 against
    #     their published sources is paper substance -> ADR-010. A NEW one fails today.
    from src.core.constants import BIBITEM_TITLE_DRIFT_CEILING as _DRIFT_CEIL
    over_ceiling = n_drop_word > _DRIFT_CEIL
    summary_passed = not _cfg.STRICT_MODE or not over_ceiling

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
        + (f" (strict mode: DROP-WORD promoted to FAIL above the frozen ceiling "
           f"{_DRIFT_CEIL}; NOT-FOUND stays advisory)" if _cfg.STRICT_MODE else ""),
        warning=(n_drop_word > 0 or n_not_found > 0) and summary_passed,
    ))

    # DROP-WORD findings: high-confidence drift (the BLOCKER class)
    for bibkey, msg, pdf_excerpt in drop_word_flags[:20]:
        details.append(Detail(
            f"drop_word:{bibkey}",
            not over_ceiling or not _cfg.STRICT_MODE,
            f"{msg} — pdf-page1≈{pdf_excerpt!r}",
            warning=not (_cfg.STRICT_MODE and over_ceiling),
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
