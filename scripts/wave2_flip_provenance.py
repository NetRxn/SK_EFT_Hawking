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


def _both_human_fields_null(key: str) -> bool:
    """The sweep's ORIGINAL gate, restored: both human fields must be unset.

    Derived by AST rather than by the old `HUMAN_NULL_RE` literal-pair regex, so quoting,
    line wrapping and an adjacent comment cannot change the answer — the same reason
    `provenance_writer` stopped using a line regex for the force guard.
    """
    sys.path.insert(0, str(PROJECT_ROOT))
    from src.core.provenance_writer import _entry_keys, PROVENANCE_PATH
    import ast as _ast
    src = PROVENANCE_PATH.read_text(encoding="utf-8")
    if _entry_keys(src, key) is None:
        return False
    for node in _ast.walk(_ast.parse(src)):
        if not (isinstance(node, _ast.Assign)
                and any(getattr(t, "id", None) == "PARAMETER_PROVENANCE"
                        for t in node.targets)
                and isinstance(node.value, _ast.Dict)):
            continue
        for k, v in zip(node.value.keys, node.value.values):
            if not (isinstance(k, _ast.Constant) and k.value == key
                    and isinstance(v, _ast.Dict)):
                continue
            vals = {kk.value: vv for kk, vv in zip(v.keys, v.values)
                    if isinstance(kk, _ast.Constant)}
            return all(
                isinstance(vals.get(f), _ast.Constant) and vals[f].value is None
                for f in ("human_verified_date", "human_verified_notes"))
    return False


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

    # ⚠️ THIS SCRIPT NO LONGER WRITES THE FILE (ADR-012 P9a Task 5). It keeps its
    # CLASSIFIER — which is the part with real judgement in it — and delegates every write
    # to `src.core.provenance_writer.set_human_verified`. Two implementations of one write
    # is how they drift, and these two already had: this one stamped a frozen
    # `VERIFY_DATE` and matched only entries literally holding `None`, so it could neither
    # record today's confirmation nor revise an existing entry, while the dashboard wrote
    # an audit event and no field at all. Precedent: `close_finding` imports the
    # extractor's `mint_finding_id` rather than reimplementing it.
    # ⚠️ THE SWEEP IS NOT ATOMIC, AND THE PER-ENTRY WRITER'S DOCSTRING SAYING "the write is
    # atomic" IS TRUE PER ENTRY AND FALSE PER SWEEP. Each call re-reads and replaces the
    # whole file, so N entries is N independent read-modify-replace cycles. An interrupt at
    # entry 13 leaves 13 flipped and 13 not. Each key is therefore printed AS IT LANDS, so
    # an interrupted run is reconstructible from stdout rather than only from a diff.
    from src.core.provenance_writer import set_human_verified

    flipped = 0
    held = 0
    refused: list[tuple[str, str]] = []
    by_cat: dict[str, list[str]] = {}

    for key, cat in sorted(classifications.items()):
        by_cat.setdefault(cat, []).append(key)
        if cat.startswith("hold_"):
            held += 1
            continue
        # ⚠️ THE OLD GATE REQUIRED BOTH FIELDS NULL, AND DROPPING HALF OF IT SILENTLY
        # WIDENED WHAT THIS SWEEP WRITES. `HUMAN_NULL_RE` matched the literal pair
        # `'human_verified_date': None,` / `'human_verified_notes': None,`; the per-entry
        # writer gates on the DATE alone. Measured: 79 entries carry a null date, 77 carry
        # both null — so 2 entries the sweep has never touched became writable. Those two
        # are exactly the shape a `REJECTED:` or `FLAGGED:` note leaves behind, so a bulk
        # flip would have overwritten a recorded human rejection with a categorisation
        # rationale. The old population is restored explicitly rather than inherited.
        if not _both_human_fields_null(key):
            refused.append((key, "carries a human_verified_notes value — a recorded "
                                 "rejection or flag. A bulk categorisation sweep does not "
                                 "overwrite one; use the dashboard, or the writer directly"))
            continue
        ok, msg = set_human_verified(
            key, date=VERIFY_DATE,
            notes=VERIFY_NOTES.format(rationale=RATIONALES[cat]),
            actor="script:wave2_flip_provenance", dry_run=dry_run)
        if ok:
            flipped += 1
            if not dry_run:
                print(f"  flipped {key}", flush=True)
        else:
            refused.append((key, msg))

    print("Classification:")
    for cat in sorted(counts):
        print(f"  {cat}: {counts[cat]}")
    print()
    print(f"{'Would flip' if dry_run else 'Flipped'}: {flipped}")
    print(f"Held (residuals): {held}")

    # ⚠️ REFUSALS ARE NAMED, never summed away. The old regex silently left an entry
    # unchanged when its pattern did not match — `n == 0` returned the original text and
    # nothing was reported — so a shape it could not handle was indistinguishable from a
    # key it was never asked about.
    if refused:
        print(f"\nREFUSED ({len(refused)}) — each writes NOTHING:")
        for key, msg in refused:
            print(f"  {key}: {msg}")

    if dry_run:
        print("\n--- DRY RUN: no file written ---")
        return 1 if refused else 0

    # ⚠️ BOTH OF THESE WERE UNCONDITIONAL, WHICH IS THE DEFECT THIS FILE'S SIBLING NAMES —
    # "a command reporting success for work it did not do, this audit's defect class wearing
    # a CLI". With every write refused, the last line of stdout said `Wrote …` and the exit
    # status said success, over a file nothing had touched.
    if flipped:
        print(f"\nWrote {flipped} entr{'y' if flipped == 1 else 'ies'} to {PROV_PATH}")
    else:
        print(f"\nNo entries written to {PROV_PATH}.")

    print("\nResiduals (held — require explicit user attention):")
    for cat in ("hold_E_needs_attention", "hold_C_projected"):
        keys = by_cat.get(cat, [])
        if keys:
            print(f"  {cat} ({len(keys)}):")
            for k in keys:
                print(f"    {k}")
    # A refusal is a failure of this command's stated job, and the exit code must say so.
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main(dry_run="--dry-run" in sys.argv))
