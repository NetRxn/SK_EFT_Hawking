# Stage 13 Adversarial Review — paper41_diff_invariance

**Reviewer:** physics-qa:adversarial-reviewer (fresh-context Opus)
**Date:** 2026-04-28 07:27 UTC
**Target:** `papers/paper41_diff_invariance/paper_draft.tex` (Phase 6e Wave 3, path-(b) order-by-order diffeomorphism invariance)
**Lean module:** `lean/SKEFTHawking/NonlinearDiffInvariance.lean` (10 theorems, 0 sorry)
**Python mirror:** `src/diff_invariance/` (36 tests)

## Severity counts

- **BLOCKER:** 1
- **REQUIRED:** 3
- **RECOMMENDED:** 3

## Mandatory reads completed

1. `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/CLAUDE.md`
2. `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/READINESS_GATES.md`
3. `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md` (Stage 13 protocol)
4. `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/papers/paper41_diff_invariance/paper_draft.tex`

---

## Findings

### F1 — [BLOCKER] [Gate 4 ComputationCorrectness] N_f scan claim "$\Nf \in \{1, 24, 27\}$" is unsupported by the computation pipeline

**Claim (paper §3.3):** "The Python mirror in `src/diff_invariance/` reproduces all predicates over a 16-point parameter scan grid covering $\Rsq \in [0, 50],\, \Ric \in [0, 50],\, \Riem \in [0, 25]$ at $\Nf \in \{1, 24, 27\}$."

**Reality (`src/diff_invariance/anomaly_hunt.py:21-77`):** `parameter_grid_scan_a4()` takes a **single** `N_f` argument and runs one scan. There is no $\{1, 24, 27\}$ multi-N_f sweep anywhere in `src/diff_invariance/`, `src/core/visualizations.py:fig_diff_invariance_order_check()`, or `src/core/constants.py:DIFF_INVARIANCE_PARAMS`. The figure-generating function (`visualizations.py:10414-10416`) uses **only** `N_f = 24.0`. Likewise `report_anomaly_hunt(N_f=24.0, ...)` defaults to a single value. The 16-point scan + ranges are reproducible; the 3-point N_f set is not.

**Why BLOCKER:** A specific numerical claim in the paper that cannot be regenerated from the code is a Gate 4 violation by definition (every numerical claim must be recomputable). The fix is one of: (a) extend `report_anomaly_hunt` / the figure to actually iterate over $\{1, 24, 27\}$ and report per-`N_f` max-residuals, or (b) drop the spurious set and write "at $\Nf = 24$" (matches both $N_f$ used in the figure and `TEST_GRID_N_F_RANGE = (1, 27)` cited as the SU(5) GUT-scale species count anchored elsewhere in the project).

---

### F2 — [REQUIRED] [Gate 1 CitationIntegrity] Three registry entries missing `paper41_diff_invariance` in their `used_in` arrays

**Bibkeys cited in `paper_draft.tex` lines 391-405 but whose `CITATION_REGISTRY` entries do not list paper41 in `used_in`:**

- `Stelle1977` — `used_in: ['papers/paper40_higher_curvature/paper_draft.tex']` only (`src/core/citations.py:2162`)
- `Vassilevich2003` — `used_in: ['papers/paper39_heat_kernel_expansion/paper_draft.tex', 'papers/paper40_higher_curvature/paper_draft.tex']` only (line 2127-2128)
- `ChristensenDuff1979` — `used_in: ['papers/paper39_heat_kernel_expansion/paper_draft.tex', 'papers/paper40_higher_curvature/paper_draft.tex']` only (line 2145-2146)

**Why REQUIRED, not BLOCKER:** The bibitems themselves resolve correctly (Crossref-verified live in this review — see below); the bug is bookkeeping drift in the `used_in` index. But Gate 11 FixPropagation depends on `used_in` being authoritative — fix-propagation queries that walk from a registry entry to all consuming papers will silently miss paper41.

**Live Crossref verification this run:**
- Stelle1977 → DOI `10.1103/PhysRevD.16.953` resolves to "Renormalization of higher-derivative quantum gravity", K. S. Stelle, Phys. Rev. D **16**, 953 (1977). ✓
- Vassilevich2003 → DOI `10.1016/j.physrep.2003.09.002` resolves to "Heat kernel expansion: user's manual", D. V. Vassilevich, Phys. Rep. **388**, 279 (2003); arXiv `hep-th/0306138` resolves to the same title/author. ✓
- ChristensenDuff1979 → DOI `10.1016/0550-3213(79)90516-9` resolves to "New gravitational index theorems and **super theorems**" (Crossref renders with a space; the paper bibitem and registry both render "supertheorems" without space). Cosmetic; same paper. RECOMMENDED to align in registry.notes.
- Wald1984 → DOI `10.7208/chicago/9780226870373.001.0001` resolves to "General Relativity", Robert M. Wald, U. Chicago Press, 1984. ✓ (book reference, no arXiv)
- Roehm2026Wave1 / HigherCurvature2026 — registered correctly (companions to paper39 / paper40 in preparation), `used_in` correctly lists paper41.

**Fix:** add `'papers/paper41_diff_invariance/paper_draft.tex'` to the `used_in` arrays on lines 2127, 2145, 2162 of `src/core/citations.py`.

---

### F3 — [REQUIRED] [Gate 1 CitationIntegrity] In-prep self-cites carry `doi_verified: True` despite having no DOI

**`Roehm2026Wave1`** (citations.py:2056-2058) and **`HigherCurvature2026`** (citations.py:2101-2103) both set `doi: None, arxiv: None, doi_verified: True`. Per Gate 1 ("Every registry entry has `arxiv_verified == True` AND `doi_verified == True` (where applicable)"), the `True` flag on a `None` DOI is structurally meaningless and may cause downstream tools to consider these "verified" when nothing was actually verified.

**Fix:** set `doi_verified: None` on both entries (or add an `inprep: True` discriminator field that the readiness-gate evaluator treats as exempt). Note: the project memory `feedback_citation_verification_required.md` warns explicitly against trusting `doi_verified` flags; this is the same anti-pattern.

---

### F4 — [REQUIRED] [Gate 4 ComputationCorrectness] `parameter_grid_scan_a4` uses `TEST_GRID_RICCI_SQ_RANGE` for the R² channel

**Code (`anomaly_hunt.py:55-58`):**
```
R_sq_grid = _grid_points(*DI['TEST_GRID_RICCI_SQ_RANGE'], n_pts)
Ricci_sq_grid = _grid_points(*DI['TEST_GRID_RICCI_SQ_RANGE'], n_pts)
Riemann_sq_grid = _grid_points(*DI['TEST_GRID_RIEMANN_SQ_RANGE'], n_pts)
```

The `R_sq` (= R²) curvature channel uses `TEST_GRID_RICCI_SQ_RANGE = (0, 50)` instead of the dedicated `TEST_GRID_R_RANGE = (0, 100)`. Both R² and Ricci² channels read from the same dictionary key. The paper's claim "$\Rsq \in [0, 50]$" matches what the code actually does, so the paper is internally consistent — but the constants file declares a separate `TEST_GRID_R_RANGE` that is **never read by the diff-invariance pipeline**, leaving the constant orphaned and inviting future drift.

**Fix:** either (a) change line 55 to read `TEST_GRID_R_RANGE`, document the (0,100) range in the paper, and align the plot; or (b) delete the unused `TEST_GRID_R_RANGE` from `DIFF_INVARIANCE_PARAMS`. Either is acceptable; do not leave an orphan constant.

---

### F5 — [RECOMMENDED] [Gate 7 CountsFreshness] Counts verified, but `\diffInvarianceThms{10}` count discipline note

`docs/counts.tex` declares `\diffInvarianceThms{10}` and `\diffInvarianceTests{36}`. Direct inspection:
- `grep -cE "^theorem " lean/SKEFTHawking/NonlinearDiffInvariance.lean` → **10** ✓ (line-anchored count; a comment at line 240 starts with "theorem" but is not a declaration)
- `grep -cE "def test_" tests/test_diff_invariance.py` → **36** ✓

Counts match. Recommendation: ensure `scripts/update_counts.py` uses a regex anchored at `^theorem ` (with leading whitespace) rather than a substring match — otherwise the comment at line 240 ("...this theorem would not hold...") could artificially inflate the count to 11 if the regex changes. (My direct `grep -c` initially returned 11; only line-anchored `grep -nE "^theorem "` correctly returned 10.)

---

### F6 — [RECOMMENDED] [Gate 4 ComputationCorrectness] Spelling drift "supertheorems" vs "super theorems" in ChristensenDuff1979

Paper bibitem (line 393) reads "*New gravitational index theorems and supertheorems*". Crossref title field on `10.1016/0550-3213(79)90516-9` is "New gravitational index theorems and **super theorems**" (space). Most existing bibliographies render this without the space, and the registry follows that convention; minor cosmetic. RECOMMENDED to add a `known_aliases` field on the registry entry or document the spelling choice.

---

### F7 — [RECOMMENDED] [Gate 6 AssumptionDisclosure] `H_NonlinearDiffInvariance` tracked-Prop disclosure is implicit

Paper §5 mentions "Tracked-Prop `H_NonlinearDiffInvariance`" and §7 references its consumption by future Wave 4 (`NonlinearEFE.lean`). The Lean definition (`NonlinearDiffInvariance.lean:388-392`) is a **derived** theorem (not a `private abbrev` or `axiom`): the conjunction is fully proved by `dirac_H_NonlinearDiffInvariance` via the three order-by-order witnesses, all of which reduce to the Wave 2 `a4_density_eq_a4_density_in_RC2GB_basis`. So calling it a "tracked-Prop" / "tracked-hypothesis" in the paper risks confusing readers about what is assumed vs proved. RECOMMENDED to clarify in §3.3 / §4.1 that `H_NonlinearDiffInvariance` is a **derived** Prop bundle (witness shipped) — the "tracked-hypothesis" framing is appropriate for downstream Wave 4 *consumers* but not for paper41 itself.

---

## Cross-paper consistency (Gate 4 cross-check)

Paper41 §3.3 cites Wave 2's `a4_density_eq_a4_density_in_RC2GB_basis` as the load-bearing identity. Confirmed in:
- `lean/SKEFTHawking/HigherCurvatureStructure.lean` (declaration exists)
- `papers/paper40_higher_curvature/paper_draft.tex:171-178` (paper40 cites the same theorem name)

Paper41 §3.1 names five Wave 1 coefficients (`a0_dirac`, `a2_R_coefficient`, `a4_R_sq_coef`, `a4_Ricci_sq_coef`, `a4_Riemann_sq_coef`). All five exist in `lean/SKEFTHawking/HeatKernelExpansion.lean` (lines 102, 128, 322, 328, 334) ✓. Closed-form values quoted in paper §3.1 match Lean defs exactly:
- `a4_R_sq_coef N_f = N_f * (-5 / (12 * 180)) * fourPiSqInv` ↔ paper "$-\tfrac{5 \Nf}{12 \cdot 180\, (4\pi)^{2}}$" ✓
- `a4_Ricci_sq_coef N_f = N_f * (7 / (12 * 180)) * fourPiSqInv` ↔ paper "$+\tfrac{7 \Nf}{12 \cdot 180\, (4\pi)^{2}}$" ✓
- `a4_Riemann_sq_coef N_f = N_f * (-12 / (12 * 180)) * fourPiSqInv` ↔ paper "$-\tfrac{12 \Nf}{12 \cdot 180\, (4\pi)^{2}}$" ✓

No CONTRADICTS edges between paper41 and paper39/paper40. Cross-paper consistency PASSES.

---

## Gate-by-gate disposition (pre-fix)

| Gate | Status | Notes |
|---|---|---|
| 1 CitationIntegrity | **blocked (F2 + F3)** | bookkeeping; primary sources resolve |
| 2 CrossPaperConsistency | passed | no contradicts; Wave 2 cross-bridge intact |
| 3 ParameterProvenance | needs-recheck | DIFF_INVARIANCE_PARAMS is methodological/PROJECTED, not in PARAMETER_PROVENANCE; OK if explicitly classified |
| 4 ComputationCorrectness | **blocked (F1)** | `N_f ∈ {1,24,27}` claim has no code path |
| 5 LeanProofSubstance | passed | 10 thms / 0 sorry; biconditional substantively reduces both directions to Wave 2 |
| 6 AssumptionDisclosure | passed | (F7 minor wording recommendation) |
| 7 NarrativeGrounding | passed | Decision Gate E.3 PASS verdict supported by `dirac_H_NonlinearDiffInvariance` + Wave 2 cross-bridge |
| 8 ProductionRunHealth | N/A | no production-run claims |
| 9 NumericalFreshness | passed | `\diffInvarianceThms{10}` and `\diffInvarianceTests{36}` match canonical sources |
| 10 FirstClaimVerification | N/A | paper makes no "first in any proof assistant" claim |
| 11 FixPropagation | passed | no open ReviewFinding edges |

**Submission readiness:** RED until F1, F2, F3 are addressed.

## Recommended fix order

1. **F1** (BLOCKER): drop the unsupported `\Nf \in \{1, 24, 27\}` set in §3.3, OR extend `report_anomaly_hunt` + the figure to actually scan it. One-line prose fix is the cheapest correct path.
2. **F2** (REQUIRED): add `'papers/paper41_diff_invariance/paper_draft.tex'` to `used_in` for Stelle1977, Vassilevich2003, ChristensenDuff1979.
3. **F3** (REQUIRED): set `doi_verified: None` on Roehm2026Wave1 and HigherCurvature2026 (no DOI to verify).
4. **F4** (REQUIRED): align `anomaly_hunt.py:55` with the dedicated `TEST_GRID_R_RANGE` constant, or delete the orphan.
5. **F5–F7** (RECOMMENDED): cosmetic / discipline-tightening; non-blocking.

After F1+F2+F3+F4 land, re-invoke this reviewer in a fresh-context window.
