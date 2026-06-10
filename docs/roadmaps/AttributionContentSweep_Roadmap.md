# Attribution-Content Sweep + Stage-13 Re-Review — Roadmap

**Authorized:** 2026-06-10 (user-scoped, "load-bearing first"). **Status:** READY — designed to run as its own dedicated `/goal`.

## Why this exists

The 2026-06-10 external-review remediation found a failure class the citation infrastructure cannot catch: **a citation can be metadata-valid (DOI verified, primary source cached, bibitem correct) while the claim attributed to it is fabricated.** Three instances found in ~10 spot-checks:

1. **Vergeles2025** — cited for "RPA bubble-integral natural range χ_vest ∈ [0.1,10]"; the cached PDF (lattice-gravity unitarity proof) contains no RPA/susceptibility/range content whatsoever. (Fixed: project-adopted-window phrasing, `ca0d0f36`/`f1a0829f`.)
2. **Halenka-Miller** — prose attributed "CMB + Bullet-cluster, ≥5σ (2018)"; the real paper is PRD 102, 084007 (2020), relaxed-cluster mass densities, nominal-assumptions-only exclusion. (Fixed: `d83ff8b6`/`196a5a70`.)
3. **GoltermanShamir2026** — registry history carried a fabricated title ("Generalized no-go theorem…") and wrong journal coordinates; actual paper frames conditional constraints. (Fixed: `1bb62842`.)

Base rate justifies a systematic sweep. CHECK 26 (`theorem_name_embedded_citations`) now guards the *presence* of embedded citations; only content-reading verifies *support*.

## Scope and protocol

Per bundle, two passes in one visit (fresh-context agent each):

**Pass 1 — Stage-13 re-invocation** (obligation from the 2026-06-10 edits; per pipeline rule "the re-run is evidence"). Touched bundles: F, D1, D2, D3, D5, D6, D7, E2, I1, I2, L1, L2 (+ E1/L3/D4/D8 only if their re-review dates predate any substantive edit).

**Pass 2 — attribution-content verification.** For each load-bearing (bibkey, claim-sentence) pair per the bundle's anchor list (`docs/agents/claims-reviewer-bundle-prompts.md`): read the cached primary source (`Lit-Search/*/primary-sources/<bibkey>.*`) and verify the specific quantitative/structural claim the paper attributes to it. Verdicts: SUPPORTED / SUPPORTED-WITH-CAVEAT (paper must carry the caveat) / NOT-SUPPORTED (fix prose + registry notes; Lean rename if theorem-name-embedded) / SOURCE-MISSING (fetch then verify). Every NOT-SUPPORTED gets a supersession-ledger-style record in the bundle's change_log + registry `notes` with date.

**Widening (after load-bearing tranche):** remaining registry entries cited in bundle drafts (~440 bibkeys total; load-bearing tranche ≈ anchor-listed subset).

## Priority order

1. **L1, D5, D3** — falsification-critical claims (GW170817, dark-sector no-go ledgers, emergent-gravity bounds).
2. **D1, E1, E2** — experimental platform set (device parameters, transport coefficients).
3. **D2, L2** — ⚠ COORDINATE with the active Phase 5q.B session first: the 2026-06-08-2242 internal-adversarial review of `paper10_modular_generation` has 6 open findings (3 critical) with zero supersession entries — F/D2/L2 currently RED on the heatmap for this reason. The 5q.B session owns the unconditional-16∣σ reframe; its supersession records must land before/with this sweep's D2/L2 visit.
4. **D4, D8, I1, I2, I3, L3, D6, D7** — remaining.
5. **F** — last (inherits all sibling corrections).

## Exit criteria

- Every touched bundle has a post-2026-06-10 fresh-context Stage-13 review recorded in `bundle_metadata.json` (heatmap GREEN under the new recorded-review semantics, commit `3e0e8252`).
- Every bundle visit also applies the standard disclosure block (correct variant per the register-derived rule) per `docs/DISCLOSURE_TEXT.md`.
- Every anchor-listed (bibkey, claim) pair has a dated verification verdict.
- `validate.py` 30/30 + CHECK 24/25/26 green; suite green.
- QI item filed if any new systematic failure class emerges.
