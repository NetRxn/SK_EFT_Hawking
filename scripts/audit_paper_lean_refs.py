#!/usr/bin/env python3
"""Audit paper Lean references against the canonical declaration index.

Phase 6i Wave 4 (Lean Proof Substance Audit) deliverable. Walks every
`papers/<paper_key>/paper_draft.tex`, extracts every cited Lean
identifier from `\\texttt{...}` blocks, and verifies each resolves to
an actually-shipped declaration in `lean/lean_deps.json` (the
ExtractDeps output, refreshed by `validate.py --check graph_integrity`).

Reports drift in three classes:
  - ABSENT:  cited name does not match any declaration
  - DRIFTED: closest fuzzy match exists with a different name (rename)
  - OK:      cited name is in lean_deps.json

The audit is deliberately conservative — only flags `\\texttt{}` tokens
that look like Lean identifiers (CamelCase / snake_case, dots allowed,
no leading lowercase Greek). Common non-Lean idioms (file paths,
filenames, command names) are filtered.

Usage:
    uv run python scripts/audit_paper_lean_refs.py
    uv run python scripts/audit_paper_lean_refs.py --paper paper20_scalar_rung
    uv run python scripts/audit_paper_lean_refs.py --json   # machine-readable

Codifies the `feedback_python_lean_refs_drift.md` memory pattern.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Iterable

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_DEPS_PATH = PROJECT_ROOT / "lean" / "lean_deps.json"
PAPERS_DIR = PROJECT_ROOT / "papers"

# Identifiers that look like Lean theorem/def names. Permits:
#   foo_bar_baz, FooBar.foo_bar, FooBar.snake_case, A.B.C.foo
# Rejects:
#   plain English words ("crossover"), file paths ("src/core/x.py"),
#   commands ("uv run pytest"), all-uppercase MACROS, Greek lowercase.
_IDENT_RE = re.compile(
    r"""
    ^
    [A-Za-z_]                       # first char alpha or underscore
    [A-Za-z0-9_]*                   # rest of head segment
    (?:                             # optional dotted segments
      \.
      [A-Za-z_][A-Za-z0-9_]*
    )*
    $
    """,
    re.VERBOSE,
)

# `\texttt{...}` blocks. Captures content; allows `\_` (LaTeX-escaped
# underscore) which is the dominant pattern in this project's papers.
_TEXTTT_RE = re.compile(r"\\texttt\{([^}]+)\}")

# Strip LaTeX escapes inside texttt content.
_LATEX_ESC_RE = re.compile(r"\\([_\\&%$#{}])")


def _normalize(token: str) -> str:
    """Strip LaTeX escapes from a `\\texttt{}` content token."""
    return _LATEX_ESC_RE.sub(r"\1", token).strip()


_TACTIC_BUILTINS = {
    "True", "False", "None", "trivial", "rfl", "decide", "ring", "simp",
    "linarith", "norm_num", "omega", "noncomm_ring", "aesop", "exact",
    "intro", "rcases", "split", "constructor", "use", "native_decide",
    "nlinarith", "noncomputable", "sorry", "sorryAx", "Quot.sound",
    "propext", "Classical.choice", "DecidableEq", "ring_nf", "simp_rw",
    "exact_mod_cast", "fin_cases", "induction", "match_scalars",
    "have", "let", "show", "by", "apply", "refine", "subst", "cases",
    "obtain", "set", "calc", "by_contra", "push_neg",
}

# Mathlib top-level namespace prefixes — papers commonly cite Mathlib
# helpers in `\texttt{}` blocks. These resolve in Mathlib, not in
# lean_deps.json (which contains only SKEFTHawking project decls).
_MATHLIB_PREFIXES = (
    "Algebra.", "AlgHom", "AlgEquiv", "Bialgebra", "Coalgebra",
    "ExteriorAlgebra", "FreeAlgebra", "HopfAlgebra", "TensorAlgebra",
    "TensorProduct.", "RingQuot", "Polynomial.", "Matrix.", "Module.",
    "OrthonormalBasis", "EuclideanSpace", "IsHermitian",
    "LaurentPolynomial", "MulOpposite", "TrivialStar",
    "Real.", "Nat.", "Int.", "Rat.", "Fin.", "Function.", "Set.",
    "Finset.", "List.", "Array.", "Option.", "Prod.", "Sigma.",
    "Equiv.", "Iso.", "LinearMap.", "LinearEquiv.", "ContinuousMap.",
    "MeasureTheory.", "Topology.", "AddCircle.",
    "IsUnit", "Ring.inverse", "Ring", "Polynomial",
    "AddCommMonoid", "CommSemiring", "CommRing", "Semiring",
    "Monoid", "Group", "AddGroup", "Module", "Submodule",
    "lp.", "Pi.", "Subset.", "spectrum",
)

# Common single-token Mathlib classes (no dot prefix)
_MATHLIB_BARE = {
    "AlgEquiv", "AlgHom", "Bialgebra", "Coalgebra",
    "ExteriorAlgebra", "FreeAlgebra", "HopfAlgebra", "TensorAlgebra",
    "RingQuot", "Polynomial", "Matrix", "OrthonormalBasis",
    "EuclideanSpace", "LaurentPolynomial", "MulOpposite", "TrivialStar",
    "Ring", "DecidableEq", "IsUnit", "AddCircle",
    "AddCommMonoid", "CommSemiring", "CommRing", "Semiring",
    "Monoid", "Group", "AddGroup", "Module", "Submodule",
    "spectrum", "PiTensorProduct", "Coinvariants", "Submodulei",
    "PiNotation", "Module.Basis",
    # mathlib lemmas commonly cited
    "map_sub", "mkAlgHom_rel", "fromBlocks_multiply", "fromBlocks_transpose",
    "basisOfOrthonormalOfCardEqFinrank", "eigh",
}


def _looks_like_lean_ident(token: str) -> bool:
    """Heuristic: token looks like a Lean theorem/def identifier."""
    if not token or len(token) < 4:
        return False
    if not _IDENT_RE.match(token):
        return False
    # Reject obvious non-Lean tokens.
    if token.startswith(("src/", "lean/", "scripts/", "tests/", "docs/",
                         "papers/", "data/", "Lit-Search/", "notebooks/",
                         "src.core", "src.")):
        return False
    if token in _TACTIC_BUILTINS:
        return False
    if token.startswith(_MATHLIB_PREFIXES):
        return False
    if token in _MATHLIB_BARE:
        return False
    # Run-IDs / paper keys / phase tags that show up in `\texttt{}`
    if re.match(r"^run_\d+_\d+$", token):
        return False
    if re.match(r"^paper\d+_", token):
        return False
    # Reject pure-uppercase macros (LaTeX command shortcuts).
    if token.isupper() and len(token) <= 6:
        return False
    # File extensions
    if any(token.endswith(ext) for ext in (".lean", ".py", ".tex",
                                            ".ipynb", ".md", ".json")):
        return False
    return True


def load_lean_deps() -> dict:
    """Load lean_deps.json and build name → entry index."""
    if not LEAN_DEPS_PATH.exists():
        print(
            f"ERROR: {LEAN_DEPS_PATH} missing. Refresh via:\n"
            f"  cd lean && rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps\n"
            f"or run validate.py --check graph_integrity.",
            file=sys.stderr,
        )
        sys.exit(1)
    with open(LEAN_DEPS_PATH) as f:
        entries = json.load(f)

    by_name: dict[str, dict] = {}
    by_short: dict[str, list[dict]] = {}
    for e in entries:
        name = e.get("name", "")
        if not name:
            continue
        by_name[name] = e
        # Index by last segment for fuzzy matching (e.g. paper cites
        # `kaulMajumdarS` but Lean has `SKEFTHawking.BHEntropyMicroscopic.kaulMajumdarS`).
        short = name.rsplit(".", 1)[-1]
        by_short.setdefault(short, []).append(e)

    return {"by_name": by_name, "by_short": by_short, "count": len(entries)}


def extract_texttt_refs(tex_path: Path) -> set[str]:
    """Walk a paper_draft.tex; return set of `\\texttt{}` tokens that
    look like Lean identifiers."""
    try:
        source = tex_path.read_text()
    except OSError:
        return set()
    refs: set[str] = set()
    for m in _TEXTTT_RE.finditer(source):
        token = _normalize(m.group(1))
        if _looks_like_lean_ident(token):
            refs.add(token)
    return refs


def resolve(token: str, deps: dict) -> tuple[str, list[str]]:
    """Resolve `token` against the Lean deps index.

    Returns (verdict, candidates) where verdict is one of:
      'OK'      — exact name match, OR project-relative match
                  (e.g. token `Foo.bar` matches `SKEFTHawking.Foo.bar`),
                  OR short-name match in lean_deps
      'ABSENT'  — no match anywhere
      'DRIFTED' — short-name has matches but namespace prefix differs
                  (i.e. paper claims `Foo.bar` but Lean has `Baz.bar`)
    """
    by_name = deps["by_name"]
    by_short = deps["by_short"]

    # Direct full-name match
    if token in by_name:
        return ("OK", [by_name[token]["name"]])

    # Project-relative match: paper cites `Foo.bar`; Lean has
    # `SKEFTHawking.Foo.bar` (or `SKEFTHawking.Foo.Bar.bar` etc.). Treat
    # any candidate whose path ends with `.<token>` as canonical for
    # this token (paper convention drops the SKEFTHawking prefix).
    candidates_endswith = [
        n for n in by_name
        if n.endswith("." + token) or n == token
    ]
    if candidates_endswith:
        return ("OK", candidates_endswith[:5])

    # Match by last segment only (paper might cite just the short form
    # or the prefix has drifted).
    short = token.rsplit(".", 1)[-1]
    if short in by_short:
        candidates = [e["name"] for e in by_short[short]]
        if "." not in token:
            # Single-segment short name resolves anywhere → OK
            return ("OK", candidates)
        # Multi-segment with mismatched prefix → real drift
        return ("DRIFTED", candidates[:5])

    return ("ABSENT", [])


def audit_paper(paper_dir: Path, deps: dict) -> dict:
    """Audit a single paper. Returns per-token verdicts."""
    tex = paper_dir / "paper_draft.tex"
    if not tex.exists():
        return {"paper": paper_dir.name, "skipped": "no paper_draft.tex"}

    refs = extract_texttt_refs(tex)
    results = {"OK": [], "ABSENT": [], "DRIFTED": []}
    for token in sorted(refs):
        verdict, candidates = resolve(token, deps)
        results[verdict].append({"token": token, "candidates": candidates})

    return {
        "paper": paper_dir.name,
        "total_refs": len(refs),
        "ok": len(results["OK"]),
        "absent": len(results["ABSENT"]),
        "drifted": len(results["DRIFTED"]),
        "details": results,
    }


def render_text_report(audits: list[dict]) -> str:
    lines: list[str] = []
    lines.append("# Lean-Reference Audit (Phase 6i Wave 4)")
    lines.append("")
    total_papers = len([a for a in audits if "skipped" not in a])
    total_refs = sum(a.get("total_refs", 0) for a in audits)
    total_ok = sum(a.get("ok", 0) for a in audits)
    total_absent = sum(a.get("absent", 0) for a in audits)
    total_drifted = sum(a.get("drifted", 0) for a in audits)
    lines.append(f"**Papers audited:** {total_papers}")
    lines.append(f"**Total `\\texttt{{...}}` Lean-ident candidates:** {total_refs}")
    lines.append(f"**OK:** {total_ok}    **ABSENT:** {total_absent}    **DRIFTED:** {total_drifted}")
    lines.append("")

    drifted_papers = [a for a in audits if a.get("absent", 0) + a.get("drifted", 0) > 0]
    drifted_papers.sort(key=lambda a: -(a["absent"] + a["drifted"]))

    if not drifted_papers:
        lines.append("**ALL PAPERS CLEAN** — no drift detected.")
        return "\n".join(lines)

    for a in drifted_papers:
        lines.append(f"## {a['paper']} — {a['absent']} ABSENT, {a['drifted']} DRIFTED")
        lines.append("")
        for entry in a["details"]["ABSENT"]:
            lines.append(f"  - **ABSENT:** `\\texttt{{{entry['token']}}}` — no match in lean_deps.json")
        for entry in a["details"]["DRIFTED"]:
            cands = ", ".join(f"`{c}`" for c in entry["candidates"][:3])
            lines.append(f"  - **DRIFTED:** `\\texttt{{{entry['token']}}}` → candidates: {cands}")
        lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", help="Audit single paper key (without 'paper' prefix folder)")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of markdown")
    parser.add_argument("--strict", action="store_true",
                        help="Exit non-zero if any ABSENT or DRIFTED found")
    args = parser.parse_args()

    deps = load_lean_deps()
    if not args.json:
        print(f"Loaded {deps['count']} Lean declarations from {LEAN_DEPS_PATH}",
              file=sys.stderr)

    if args.paper:
        paper_dir = PAPERS_DIR / args.paper
        if not paper_dir.exists():
            print(f"ERROR: {paper_dir} not found", file=sys.stderr)
            return 2
        audits = [audit_paper(paper_dir, deps)]
    else:
        audits = [audit_paper(p, deps)
                  for p in sorted(PAPERS_DIR.iterdir())
                  if p.is_dir() and not p.name.startswith(".") and p.name != "AutomatedReviews"]

    if args.json:
        print(json.dumps(audits, indent=2))
    else:
        print(render_text_report(audits))

    if args.strict:
        bad = sum(a.get("absent", 0) + a.get("drifted", 0) for a in audits)
        if bad > 0:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
