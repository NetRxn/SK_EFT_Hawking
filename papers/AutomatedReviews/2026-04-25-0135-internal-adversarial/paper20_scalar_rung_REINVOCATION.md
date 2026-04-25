---
paper: paper20_scalar_rung
reviewer: adversarial-reviewer (re-invocation)
model: claude-opus-4-7
review_date: 2026-04-25T01:50:00Z
prior_review: paper20_scalar_rung.md (same directory)
readiness_gates_version: 1
---

# Adversarial Review Re-Invocation — paper20_scalar_rung

## Summary

Re-invocation of Stage 13 after author addressed prior findings. **All 18 BLOCKERs closed; 1 REQUIRED deferred (1.11 WebFetch verification, awaiting authorized-WebFetch round); remaining 7 REQUIREDs all closed.** Paper is structurally submission-ready; submission-final gate still requires the deferred WebFetch verifications to flip `doi_verified: None → True` on the 10 new registry entries (1.1–1.9, 1.10).

No new BLOCKERs introduced by remediation.

## BLOCKER closure verification

### Class 3 — Lean Proof Substance (4/4 closed)

| Finding | Original | Status | Evidence |
|---------|----------|--------|----------|
| 3.1 | `isHiggsBilinear_of_scalarChannel` cited (removed thm) | ✅ closed | 0 refs to removed name; 2 refs to replacement `IsHiggsBilinearCandidate` and load-bearing `not_isHiggsBilinearCandidate_of_vev_too_large` |
| 3.2 | `mexican_hat_is_tetrad_bifurcation` cited (removed thm) | ✅ closed | 0 refs to removed name; 1 ref to replacement `mexican_hat_vev_under_supercritical_bridge` + 2 refs to `H_ScalarChannelIsTetradBifurcationOutput` (tracked hypothesis) |
| 3.3 | `gap_equation_supercritical` cited (does not exist) | ✅ closed | 0 refs to wrong name; 1 ref to correct name `gap_nontrivial_exists` |
| 3.4 | "orthogonality on distinct Fermi points" overclaim | ✅ closed | Prose now reads "two structural relations — linearity in the overlap density and zero-coupling iff zero-overlap" with explicit deferral statement |

### Class 1 — Citation Integrity (9/9 registry-presence BLOCKERs closed)

| Finding | Bibkey | Registry status |
|---------|--------|-----------------|
| 1.1 | `ADW` | ✅ registered (Akama 1978, DOI 10.1143/PTP.60.1900) |
| 1.2 | `WetterichSpinor` (split) | ✅ registered as `WetterichSpinor2013` + `WetterichSpinor2022` |
| 1.3 | `WetterichNJL` | ✅ registered (Wetterich 2024, DOI 10.1016/j.physletb.2024.136223) |
| 1.4 | `Fierz` | ✅ registered (Fierz 1937, DOI 10.1007/BF01330070) |
| 1.5 | `NJL61` | ✅ registered (Nambu-Jona-Lasinio 1961, DOI 10.1103/PhysRev.122.345) |
| 1.6 | `GiesScherer` | ✅ registered (Gies-Lippoldt 2013, DOI 10.1103/PhysRevD.87.104026, arXiv:1305.6940) — note: bibkey is project-local shorthand; rename suggestion documented in registry notes |
| 1.7 | `BardeenHillLindner` | ✅ registered (Bardeen-Hill-Lindner 1990, DOI 10.1103/PhysRevD.41.1647) |
| 1.8 | `PDG2024` | ✅ registered (Navas et al. 2024, DOI 10.1103/PhysRevD.110.030001) |
| 1.9 | `PeskinSchroeder` | ✅ registered (textbook, ISBN 978-0201503975) |
| 1.10 | `WetterichSpinor` was combined bibitem | ✅ closed: split into `WetterichSpinor2013` (Lect. Notes Phys. 863) + `WetterichSpinor2022` (JHEP 02 169) bibitems and registry entries; in-text `\cite` updated |

Pipeline validation: `paper20_scalar_rung/paper_draft.tex` shows 13 bibitems; all 13 keys present in `src/core/citations.py CITATION_REGISTRY` per direct registry import + intersection check.

### Class 7 — Count Freshness (3/3 closed)

| Finding | Original | Status |
|---------|----------|--------|
| 7.1 | "18 theorems" in 4 places | ✅ closed: 0 stale "18 theorems" refs; 3 "20 theorems" refs (abstract, contributions, table, closure) |
| 7.2 | Definition count "nine non-computable definitions" | ✅ closed: paper now reads "three structures, nine non-computable definitions for VEV/mass/Yukawa formulas, and three Prop-level definitions" |
| 7.3 | RECOMMENDED — macro usage spot-check | ✅ confirmed `\input{../../docs/counts.tex}` at line 10 + `\totaltheorems{} / \substantivetheorems{}` macros expand to current 3993 / 3882 |

### Class 5 / 6 — Narrative & Disclosure (3/3 closed)

| Finding | Original | Status |
|---------|----------|--------|
| 5.1 | First-claim without exhaustive search | ✅ closed: `\subsection*{Prior-art search}` added before Conclusion documenting search of HepLean, Lean Zulip, Mathlib, Coq QuantumLib/QWIRE, Isabelle/HOL AFP, Agda |
| 5.2 | M_W/M_Z rounding mismatch (cosmetic) | ✅ closed: 80.47/91.21 GeV values are within 0.0006% of pipeline (80.465/91.211); kept at 2-decimal display per paper convention |
| 6.1 | Tracked hypothesis not disclosed | ✅ closed: 5 references to `H_ScalarChannelIsTetradBifurcationOutput` and "tracked external hypothesis" pattern, with project-precedent citations to `HiddenSectorMixedCharge.H_MixedChannelZ16Cancels` and `DarkSectorSynthesis.H_VestigialRelicCarriesZ16Charge` |

## Pipeline state at re-invocation

- `lake build SKEFTHawking.ExtractDeps`: clean (8431 jobs)
- `validate.py` 21/21 PASS at 2026-04-25T01:43Z (final post-remediation run)
- pytest `test_scalar_rung.py`: 24/24 PASS
- Paper compiles to 5 pages (was 4 — extra page from §Prior-art-search subsection)
- Lean module: 20 theorems / 9 def / 3 structures / 3 Prop-defs / 0 sorry / 0 new axioms

## Remaining open item (REQUIRED, deferred — not a re-blocker)

### 1.11 (deferred) — 🟡 REQUIRED — Citation arXiv/DOI verifications still not WebFetched

- **Status:** still `doi_verified: None` for all 10 new registry entries
- **Why deferred:** prior agent run halted on denied WebFetches; direct-author re-run did not retry
- **Impact at draft stage:** none — paper is draft-ready
- **Impact at submission stage:** **submission-blocking until each `doi_verified: None → True` flip is recorded**, with corresponding `citation_verifications.jsonl` entries
- **Path to closure:** schedule a future authorized-WebFetch run (or manual verification with `scripts/citation_cache.py append_record`) for the 10 entries; the entries are already structured to receive the verification (each has `doi`, `arxiv` fields populated where applicable)

## QI register update

The pattern documented in the prior review (strengthening-pass refactors leave stale paper prose) is now directly evidenced. Suggest the project add:

1. A `validate.py --check paper_lean_refs` that greps every paper's `\texttt{Module.theorem_name}` references and verifies they resolve against the live Lean source (`lean_deps.json`'s declaration list)
2. A doc-sync gate in Stage 12 of the pipeline that runs the check before claiming the wave shipped

This QI item should be propagated to `docs/QI_REGISTER.md` per Stage 14 protocol.

## Verdict

**Submission-ready at draft stage.** All BLOCKERs closed; remaining REQUIRED (1.11) is a deferred WebFetch round that must be performed before final submission but does not impede further authorial / pipeline progress.

The paper is structurally complete, all Lean references resolve to live theorems, all bibkeys are registered, all narrative claims are grounded with appropriate scope-disclosure, and validate.py is fully green.
