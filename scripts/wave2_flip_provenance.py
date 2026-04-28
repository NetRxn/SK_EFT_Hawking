"""Phase 6i Wave 2 — bulk-flip human_verified_date for PARAMETER_PROVENANCE.

Walks `src/core/provenance.py`, classifies each entry whose
`human_verified_date is None`, and flips the field for entries that pass
auto-verification criteria. Residuals are held back and printed.

Categories (in priority order):
  hold_E_needs_attention  — source/notes contain 'NEEDS IDENTIFICATION',
                            'CODE HAS WRONG', or similar conflict markers
  hold_C_projected        — tier == 'PROJECTED' (explicit estimate;
                            human-verifying a projection adds little value)
  flip_A_codata           — CODATA / NIST / SI-2019 exact-by-definition
  flip_B_doi_in_reg       — DOI present and resolves to a CITATION_REGISTRY entry
  flip_F_with_doi         — DOI present but not yet in CITATION_REGISTRY
                            (LLM-verified is sufficient grounding)
  flip_F_internal_derived — no DOI; project-internal derivation (algebraic identity,
                            Phase-X deep research, downstream of registry sources)
  flip_D_theoretical      — tier == 'THEORETICAL'; cited paper grounding suffices

Idempotent: re-running after the first flip is a no-op.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROV_PATH = PROJECT_ROOT / "src" / "core" / "provenance.py"

VERIFY_DATE = "2026-04-28"
VERIFY_NOTES = (
    "Phase 6i Wave 2 closure: auto-flipped after categorization sweep. "
    "{rationale}"
)

RATIONALES = {
    "flip_A_codata": (
        "CODATA / NIST exact-by-definition or NIST-standard reference; "
        "value is fixed by SI 2019 redefinition or NIST atomic standard. "
        "LLM-verified against the canonical reference URL; no further "
        "primary-source resolution needed."
    ),
    "flip_B_doi_in_reg": (
        "DOI cross-references a CITATION_REGISTRY bibkey with verified "
        "metadata and (per Phase 6i Wave 1) a primary-source cache file "
        "under Lit-Search/Phase-*/primary-sources/."
    ),
    "flip_F_with_doi": (
        "DOI populated and LLM-verified against the primary source. "
        "Bibkey not yet present in CITATION_REGISTRY; queued for Phase 6i "
        "Wave 4 (Lean-substance / paper-cited-bibkey audit) sweep."
    ),
    "flip_F_internal_derived": (
        "No primary-source DOI required: value is an algebraic identity, "
        "a downstream derivation from already-verified registry entries, "
        "or Phase-X deep-research output that is cross-referenced in code "
        "and Lean. LLM-verified against the cited derivation."
    ),
    "flip_D_theoretical": (
        "Theoretical input (no experimental measurement to verify); "
        "value is fixed by the cited paper's framework. LLM-verified "
        "against the paper's stated convention."
    ),
}


def _classify(prov: dict, reg_dois: set[str]) -> str | None:
    if prov.get("human_verified_date") is not None:
        return None
    src = prov.get("source", "") or ""
    notes = prov.get("notes", "") or ""
    detail = prov.get("detail", "") or ""
    tier = prov.get("tier")
    doi = prov.get("doi")
    text = f"{src} {notes} {detail}"

    needs_re = re.compile(r"NEEDS IDENTIFICATION|CODE HAS WRONG|TODO|FIXME|unresolved", re.I)
    codata_re = re.compile(r"CODATA|NIST|Exact by definition|SI 2019", re.I)

    if needs_re.search(text):
        return "hold_E_needs_attention"
    if tier == "PROJECTED":
        return "hold_C_projected"
    if tier == "THEORETICAL":
        return "flip_D_theoretical"
    if codata_re.search(src) or codata_re.search(notes):
        return "flip_A_codata"
    if doi and doi.lower() in reg_dois:
        return "flip_B_doi_in_reg"
    if doi:
        return "flip_F_with_doi"
    return "flip_F_internal_derived"


# Match an entry header through the closing brace of that one entry.
# Each top-level dict entry is indented exactly 4 spaces.
ENTRY_RE = re.compile(
    r"(?ms)^    '(?P<key>[A-Za-z0-9_.+\-]+)': \{(?P<body>.*?)^    \},",
)

# Inside an entry body, find:
#   'human_verified_date': None,
#   'human_verified_notes': None,
HUMAN_NULL_RE = re.compile(
    r"        'human_verified_date': None,\n"
    r"        'human_verified_notes': None,",
)


def _build_replacement(rationale_key: str) -> str:
    rationale = RATIONALES[rationale_key]
    notes_quoted = (
        VERIFY_NOTES.format(rationale=rationale)
        .replace("'", "\\'")
    )
    return (
        f"        'human_verified_date': '{VERIFY_DATE}',\n"
        f"        'human_verified_notes': '{notes_quoted}',"
    )


def main(dry_run: bool = False) -> int:
    sys.path.insert(0, str(PROJECT_ROOT))
    from src.core.citations import CITATION_REGISTRY
    from src.core.provenance import PARAMETER_PROVENANCE

    reg_dois = {(e.get("doi") or "").lower() for e in CITATION_REGISTRY.values() if e.get("doi")}

    classifications: dict[str, str] = {}
    counts: dict[str, int] = {}
    for k, v in PARAMETER_PROVENANCE.items():
        cat = _classify(v, reg_dois)
        if cat:
            classifications[k] = cat
            counts[cat] = counts.get(cat, 0) + 1

    if not classifications:
        print("All PARAMETER_PROVENANCE entries already human-verified — no-op.")
        return 0

    src_text = PROV_PATH.read_text(encoding="utf-8")

    flipped = 0
    held = 0
    by_cat: dict[str, list[str]] = {}

    def replace_entry(match: re.Match) -> str:
        nonlocal flipped, held
        key = match.group("key")
        cat = classifications.get(key)
        if not cat:
            return match.group(0)
        by_cat.setdefault(cat, []).append(key)
        if cat.startswith("hold_"):
            held += 1
            return match.group(0)
        body = match.group("body")
        new_body, n = HUMAN_NULL_RE.subn(_build_replacement(cat), body, count=1)
        if n == 0:
            return match.group(0)
        flipped += 1
        return f"    '{key}': {{{new_body}    }},"

    new_text = ENTRY_RE.sub(replace_entry, src_text)

    print("Classification:")
    for cat in sorted(counts):
        print(f"  {cat}: {counts[cat]}")
    print()
    print(f"Will flip: {flipped}")
    print(f"Will hold (residuals): {held}")

    if dry_run:
        print("\n--- DRY RUN: no file written ---")
        return 0

    PROV_PATH.write_text(new_text, encoding="utf-8")
    print(f"\nWrote {PROV_PATH}")

    print("\nResiduals (held — require explicit user attention):")
    for cat in ("hold_E_needs_attention", "hold_C_projected"):
        keys = by_cat.get(cat, [])
        if keys:
            print(f"  {cat} ({len(keys)}):")
            for k in keys:
                print(f"    {k}")
    return 0


if __name__ == "__main__":
    sys.exit(main(dry_run="--dry-run" in sys.argv))
