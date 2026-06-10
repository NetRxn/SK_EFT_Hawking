#!/usr/bin/env python3
"""
Deterministic cross-platform Lean-theorem reuse counter (bundle D1 / paper16).

Replaces the manual "109 of 119 (~92%)" count with a reproducible script
output (external-review finding D1-Y2; earlier Stage-13 findings flagged the
manual count as having "no reproducible artifact").

THE CLAIM BEING COUNTED
-----------------------
Bundle D1 (papers/D1/paper_draft.tex, "92% Lean theorem reuse" section) and
paper16 (papers/paper16_graphene_sk_eft/paper_draft.tex, "Formal
Verification" section) assert that the large majority of the 1+1D BEC Lean
theorem infrastructure applies *unchanged* to the graphene 2+1D Dirac-fluid
setup after the substitution c_s -> v_F/sqrt(2). "Unchanged" is meaningful in
Lean terms: a theorem whose statement is parametric in the sound speed,
transport coefficients, and EFT cutoff holds verbatim for the graphene
instantiation (Lean proves it once for all parameter values), whereas a
theorem whose statement bakes in 1+1D-explicit geometry or BEC-specific
microphysics does not transfer and is superseded by the graphene-side
modules (DiracFluidMetric, DiracFluidWKB, GrapheneNoiseFormula, ...).

POPULATION (the denominator)
----------------------------
The population is *defined* by the nine 1+1D BEC modules enumerated in
paper16's "Formal Verification" section (and restated in D1):

    AcousticMetric, HawkingUniversality, WKBConnection, WKBAnalysis,
    SecondOrderSK, CGLTransform, ThirdOrderSK, SKDoubling, KappaScaling

The module list IS the definition (it is inherently module-enumerated), so
it is encoded as the documented constant ``NINE_MODULES`` below. Within
those modules we count hand-written ``theorem``/``lemma`` declarations at
beginning-of-line, skipping block comments — the same convention as
``_module_thm_count_strict`` in scripts/update_counts.py (paper-claim
counting convention). Auto-generated environment lemmas (``*.mk.injEq``,
``*.eq_1``, structure-field projections, ...) are excluded, exactly as in
every per-module paper count in this project.

PARTITION (reused vs platform-specific)
---------------------------------------
A theorem is PLATFORM-SPECIFIC (does not transfer to the graphene 2+1D
Dirac fluid) iff its *statement* references one of the documented
``PLATFORM_SPECIFIC_ROOTS`` — definitions that encode either

  (a) 1+1D-explicit geometry: the 2x2 Painleve-Gullstrand matrix
      ``acousticMetric``/``acousticMetricInv``, the ``PhononEOM`` structure
      (2x2 coefficient matrix on ``Spacetime1D``), and the 1+1D
      d'Alembertian operators. The 2+1D metric is 3x3; its treatment lives
      in DiracFluidMetric (block-diagonalisation) — these statements are
      superseded there, not reused; or

  (b) BEC-specific microphysics: the Bogoliubov *dispersion law*
      (superluminal — the graphene Dirac fluid is subluminal, see
      ``DiracFluidWKB.soundSpeed_lt_vF``) and the two-component spin-sonic
      enhancement (no spin/density two-speed structure in a Dirac fluid).

Everything else is REUSED: its statement quantifies only over parametric
structures (ExactWKBParams, DissipativeDispersion, MaterialParams, KMS
coefficient records, ...) whose fields are platform-agnostic reals, so the
theorem applies verbatim with c_s -> v_F/sqrt(2).

Name-trap notes (why some "Bogoliubov"-named items are NOT roots):
  * ``WKBConnection.ModifiedBogoliubov`` is the alpha^2/beta^2 mode-mixing
    coefficient structure with the modified-unitarity field
    |alpha|^2 - |beta|^2 = 1 - delta_k. Bogoliubov *coefficients* are
    universal scattering theory — this is precisely D1's cross-platform
    headline prediction — so theorems over it transfer.
  * ``WKBAnalysis.bogoliubov_correction_bounded`` / ``_perturbative`` are
    stated for an arbitrary ``DissipativeDispersion`` (generic damping
    rate); despite the name, their statements carry no BEC-specific
    content and transfer.

The statement scan is two-layered for robustness:
  1. the kernel-elaborated type from lean/lean_deps.json (fully-qualified
     names; ground truth), and
  2. the source-level statement text (declaration head up to the
     proof-introducing ``:=``), which catches binder types the kernel
     pretty-printer elides (e.g. ``acoustic_metric_theorem`` prints as
     ``∃ (_ : PhononEOM ...), True`` -> ``Exists fun x => True``).

Both layers are deterministic functions of committed files
(lean/SKEFTHawking/*.lean + lean/lean_deps.json), so the output is stable.

FRESHNESS POLICY
----------------
The count depends only on the NINE population modules. Staleness handling is
scoped accordingly:
  * HARD ERROR (exit 1) if any population theorem cannot be uniquely
    resolved in lean_deps.json — that means the extraction is stale *for
    the population* (theorems added/renamed in the nine modules) and the
    kernel layer cannot be trusted. Remedy: scripts/extract_lean_deps.py.
  * WARNING (stderr + ``lean_deps_global_fresh: false`` in the JSON) if the
    repo-global source hash mismatches — i.e. some module *outside* the
    population changed since the last extraction. The count remains
    authoritative: the population resolves cleanly, and the source-level
    statement layer is always computed from the current sources. (A global
    hard-fail would make the counter unusable in this 900+-module repo,
    where unrelated modules change daily.)

Usage:
    uv run python scripts/count_theorem_reuse.py            # human report
    uv run python scripts/count_theorem_reuse.py --json     # machine JSON

Exit status: 0 on success; 1 on any parse/resolution error
(errors are loud — a silent wrong count would defeat the purpose).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_SRC_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
LEAN_DEPS = PROJECT_ROOT / "lean" / "lean_deps.json"
SCRIPTS_DIR = PROJECT_ROOT / "scripts"

# ---------------------------------------------------------------------------
# THE POPULATION DEFINITION.
#
# The nine 1+1D BEC modules named in paper16 ("The reused theorems span nine
# 1+1D BEC modules (AcousticMetric, HawkingUniversality, WKBConnection,
# WKBAnalysis, SecondOrderSK, CGLTransform, ThirdOrderSK, SKDoubling,
# KappaScaling)") and in bundle D1's graphene section. This list is the
# definition of "the 1+1D BEC infrastructure" for the reuse claim; do not
# add/remove entries without updating both paper sections.
# ---------------------------------------------------------------------------
NINE_MODULES = [
    "AcousticMetric",
    "HawkingUniversality",
    "WKBConnection",
    "WKBAnalysis",
    "SecondOrderSK",
    "CGLTransform",
    "ThirdOrderSK",
    "SKDoubling",
    "KappaScaling",
]

# ---------------------------------------------------------------------------
# THE PARTITION DEFINITION.
#
# Fully-qualified names of the 1+1D-explicit / BEC-microphysics-specific
# definitions. A theorem whose statement references any of these does not
# transfer to the graphene 2+1D Dirac fluid. Each entry documents why, and
# what supersedes it on the graphene side.
# ---------------------------------------------------------------------------
PLATFORM_SPECIFIC_ROOTS: dict[str, str] = {
    "SKEFTHawking.AcousticMetric.acousticMetric": (
        "explicit 2x2 (Fin 2) Painleve-Gullstrand matrix; the 2+1D metric is "
        "3x3 — superseded by DiracFluidMetric.diracFluidMetric + "
        "block-diagonalisation"
    ),
    "SKEFTHawking.AcousticMetric.acousticMetricInv": (
        "explicit 2x2 inverse acoustic metric; same supersession as "
        "acousticMetric"
    ),
    "SKEFTHawking.AcousticMetric.PhononEOM": (
        "phonon-EOM structure whose coefficient matrix is the 2x2 inverse "
        "metric on Spacetime1D; the 2+1D EOM requires the 3x3 "
        "block-diagonalised treatment (DiracFluidMetric, QuasiOneDReduction)"
    ),
    "SKEFTHawking.AcousticMetric.dAlembertian": (
        "1+1D-explicit d'Alembertian (flux components J^0, J^1 only)"
    ),
    "SKEFTHawking.AcousticMetric.partialT": (
        "partial derivative on the explicit 1+1D spacetime type"
    ),
    "SKEFTHawking.AcousticMetric.partialX": (
        "partial derivative on the explicit 1+1D spacetime type"
    ),
    "SKEFTHawking.Spacetime1D": (
        "explicit 1+1D spacetime point type (fields t, x only)"
    ),
    "SKEFTHawking.HawkingUniversality.bogoliubovDispersion": (
        "the BEC Bogoliubov dispersion law (superluminal); the graphene "
        "Dirac fluid is subluminal (DiracFluidWKB.soundSpeed_lt_vF), so "
        "superluminal-dispersion statements do not transfer"
    ),
    "SKEFTHawking.HawkingUniversality.spinSonicEnhancement": (
        "two-component (spin-sonic) BEC enhancement factor c_d^2/c_s^2; "
        "the Dirac fluid has no spin/density two-speed structure"
    ),
}

_DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z0-9_'₀-₉]+)")
_FQ_IDENT_RE = re.compile(r"SKEFTHawking\.[A-Za-z0-9_.'₀-₉]+")


def parse_module_theorems(path: Path) -> list[tuple[str, str]]:
    """Extract hand-written theorem declarations from a Lean source file.

    Returns ``[(name, statement_text), ...]`` in source order, where
    ``statement_text`` runs from the declaration keyword to the
    proof-introducing ``:=`` (bracket-depth-0, skipping ``let ... :=``
    binders inside the statement).

    Counting convention matches ``_module_thm_count_strict`` in
    scripts/update_counts.py: only ``theorem ``/``lemma `` at column 0,
    with ``/- ... -/`` block-comment spans skipped so docstring prose
    cannot false-positive.
    """
    lines = path.read_text().splitlines()
    out: list[tuple[str, str]] = []
    in_block = False
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()
        if in_block:
            if "-/" in line:
                in_block = False
            i += 1
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped[2:]:
                in_block = True
            i += 1
            continue
        m = _DECL_RE.match(line)
        if not m:
            i += 1
            continue
        name = m.group(2)
        # Accumulate the statement until the proof-introducing ':=':
        # bracket depth 0, and not the ':=' of a depth-0 'let' binder.
        depth = 0
        pending_lets = 0
        stmt_chars: list[str] = []
        j = i
        done = False
        while j < len(lines) and not done:
            text = lines[j]
            k = 0
            while k < len(text):
                c = text[k]
                if c in "([{⟨":
                    depth += 1
                elif c in ")]}⟩":
                    depth -= 1
                elif depth == 0 and text[k : k + 4] in ("let ", "let\t"):
                    # only count 'let' as a keyword token (preceded by
                    # whitespace or start-of-line)
                    if k == 0 or not (text[k - 1].isalnum() or text[k - 1] == "_"):
                        pending_lets += 1
                elif c == ":" and depth == 0 and k + 1 < len(text) and text[k + 1] == "=":
                    if pending_lets > 0:
                        pending_lets -= 1
                        stmt_chars.append(":")
                        stmt_chars.append("=")
                        k += 2
                        continue
                    done = True
                    break
                stmt_chars.append(c)
                k += 1
            stmt_chars.append("\n")
            j += 1
            if j - i > 200 and not done:
                raise RuntimeError(
                    f"{path.name}: could not find proof-introducing ':=' for "
                    f"theorem '{name}' within 200 lines — parser assumption "
                    "violated; fix parse_module_theorems."
                )
        if not done:
            raise RuntimeError(
                f"{path.name}: reached end of file looking for ':=' of "
                f"theorem '{name}'."
            )
        out.append((name, "".join(stmt_chars)))
        i = j
    return out


def check_lean_deps_fresh() -> bool:
    """Check lean_deps.json freshness. Returns the *global* freshness flag.

    Missing file is a hard error. A repo-global SHA-256 mismatch (canonical
    test from scripts/extract_lean_deps.py, as used by the validate.py graph
    pipeline) is only a WARNING here — see "FRESHNESS POLICY" in the module
    docstring: population-scoped staleness is what matters for this count,
    and it is enforced separately via the per-theorem resolution hard error
    in classify(). We do NOT auto-regenerate — extraction is a ~30-min
    interpreted-Lean walk and a counting script should never silently
    launch it.
    """
    if not LEAN_DEPS.exists():
        sys.exit(
            f"ERROR: {LEAN_DEPS} not found. Run: "
            "uv run python scripts/extract_lean_deps.py"
        )
    sys.path.insert(0, str(SCRIPTS_DIR))
    try:
        from extract_lean_deps import HASH_PATH, compute_lean_hash
    except ImportError:
        print(
            "WARNING: could not import extract_lean_deps; skipping "
            "lean_deps.json freshness check.",
            file=sys.stderr,
        )
        return True
    if not HASH_PATH.exists() or HASH_PATH.read_text().strip() != compute_lean_hash():
        print(
            "WARNING: lean/lean_deps.json is globally stale (some .lean "
            "source outside this count's nine population modules changed "
            "since the last extraction). The reuse count remains "
            "authoritative provided the population resolves cleanly (hard-"
            "checked below). Refresh at next Stage 12: "
            "uv run python scripts/extract_lean_deps.py",
            file=sys.stderr,
        )
        return False
    return True


def load_env_index() -> dict[str, dict[str, dict]]:
    """lean_deps.json as {module: {fq_name: entry}}, theorems only."""
    with open(LEAN_DEPS) as f:
        data = json.load(f)
    index: dict[str, dict[str, dict]] = {}
    for d in data:
        if d.get("kind") == "theorem":
            index.setdefault(d["module"], {})[d["name"]] = d
    return index


def classify() -> dict:
    """Run the full deterministic count. Returns the result dict."""
    global_fresh = check_lean_deps_fresh()
    env = load_env_index()

    # Pre-compile short-name (source-level, unqualified) root patterns.
    # Word boundaries: Lean identifiers may contain _ and ', so we forbid
    # identifier characters on both sides rather than using \b.
    short_pats = {
        root: re.compile(
            r"(?<![A-Za-z0-9_.'₀-₉])"
            + re.escape(root.rsplit(".", 1)[-1])
            + r"(?![A-Za-z0-9_'₀-₉])"
        )
        for root in PLATFORM_SPECIFIC_ROOTS
    }

    modules_out: dict[str, dict] = {}
    total = 0
    reused_total = 0
    for mod in NINE_MODULES:
        src = LEAN_SRC_DIR / f"{mod}.lean"
        if not src.exists():
            sys.exit(f"ERROR: population module missing: {src}")
        full_mod = f"SKEFTHawking.{mod}"
        env_mod = env.get(full_mod, {})
        rows = []
        for name, stmt in parse_module_theorems(src):
            cands = [e for fq, e in env_mod.items() if fq.endswith("." + name)]
            if len(cands) != 1:
                sys.exit(
                    f"ERROR: cannot uniquely resolve {mod}.{name} in "
                    f"lean_deps.json ({len(cands)} candidates). "
                    "lean_deps.json is likely stale — refresh with: "
                    "uv run python scripts/extract_lean_deps.py"
                )
            ktype = cands[0]["type"]
            kernel_mentions = set(_FQ_IDENT_RE.findall(ktype))
            hits = sorted(
                root
                for root in PLATFORM_SPECIFIC_ROOTS
                if root in kernel_mentions or short_pats[root].search(stmt)
            )
            rows.append({"name": cands[0]["name"], "platform_specific_roots": hits})
        n_total = len(rows)
        platform_specific = [r for r in rows if r["platform_specific_roots"]]
        modules_out[mod] = {
            "theorems": n_total,
            "reused": n_total - len(platform_specific),
            "platform_specific": platform_specific,
        }
        total += n_total
        reused_total += n_total - len(platform_specific)

    fraction = 100.0 * reused_total / total if total else 0.0
    return {
        "generated_by": "scripts/count_theorem_reuse.py",
        "definition": (
            "Hand-written theorem/lemma declarations in the nine 1+1D BEC "
            "modules (paper16 'Formal Verification' / D1 graphene section); "
            "REUSED = statement references no PLATFORM_SPECIFIC_ROOTS "
            "(1+1D-explicit geometry or BEC-specific microphysics), hence "
            "applies unchanged to the graphene 2+1D Dirac fluid with "
            "c_s -> v_F/sqrt(2)"
        ),
        "population_modules": NINE_MODULES,
        "platform_specific_roots": PLATFORM_SPECIFIC_ROOTS,
        "lean_deps_global_fresh": global_fresh,
        "modules": modules_out,
        "totals": {
            "theorems": total,
            "reused": reused_total,
            "platform_specific": total - reused_total,
            "reuse_fraction_percent": round(fraction, 2),
            "reuse_percent_rounded": round(fraction),
        },
    }


def print_report(result: dict) -> None:
    t = result["totals"]
    print("Cross-platform Lean theorem reuse — deterministic count")
    print("=" * 60)
    print(
        "Population: hand-written theorems in the nine 1+1D BEC modules\n"
        "Reused: statement is platform-parametric (applies unchanged to\n"
        "the graphene 2+1D Dirac fluid with c_s -> v_F/sqrt(2))\n"
    )
    print(f"{'Module':<22}{'theorems':>9}{'reused':>8}{'specific':>9}")
    print("-" * 48)
    for mod in result["population_modules"]:
        m = result["modules"][mod]
        print(
            f"{mod:<22}{m['theorems']:>9}{m['reused']:>8}"
            f"{len(m['platform_specific']):>9}"
        )
    print("-" * 48)
    print(
        f"{'TOTAL':<22}{t['theorems']:>9}{t['reused']:>8}"
        f"{t['platform_specific']:>9}"
    )
    print(
        f"\nREUSE {t['reused']}/{t['theorems']} = "
        f"{t['reuse_fraction_percent']:.2f}% "
        f"(rounds to {t['reuse_percent_rounded']}%)"
    )
    print("\nPlatform-specific (non-transferring) theorems:")
    for mod in result["population_modules"]:
        for r in result["modules"][mod]["platform_specific"]:
            roots = ", ".join(
                root.rsplit(".", 1)[-1] for root in r["platform_specific_roots"]
            )
            print(f"  {r['name']}")
            print(f"      via: {roots}")
    print("\nRoot justifications:")
    for root, why in result["platform_specific_roots"].items():
        print(f"  {root.rsplit('.', 1)[-1]}: {why}")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Deterministic 1+1D->2+1D Lean theorem reuse counter "
        "(bundle D1 / paper16 claim)."
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable JSON only (stable, no timestamps)",
    )
    args = ap.parse_args()
    result = classify()
    if args.json:
        json.dump(result, sys.stdout, indent=2)
        print()
    else:
        print_report(result)


if __name__ == "__main__":
    main()
