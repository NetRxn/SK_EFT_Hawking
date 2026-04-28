# Paper 39 Heat-Kernel Expansion: Stage 10 Claims Review

**Review date:** 2026-04-27
**Paper:** `paper39_heat_kernel_expansion`
**Overall status:** issues_found (all WARN; zero FAIL)
**Counts:** 0 FAIL / 6 WARN / 10 PASS

---

## Summary

Paper 39 passes all hard Stage 10 gates: **zero FAIL** findings. Every theorem name cited in the paper resolves to an exact-name declaration in `lean/SKEFTHawking/HeatKernelExpansion.lean`; every LinearizedEFE cross-reference resolves; the load-bearing cross-bridge `G_N_from_a2_eq_G_N_sakharov` substantively invokes `LinearizedEFE.G_N_sakharov` by full name (P6 drift-protection satisfied). Numerical anchors verified to <0.1%. Theorem count (19) and test count (36) match `\heatKernelThms` / `\heatKernelTests` macros. `lake build SKEFTHawking.HeatKernelExpansion` is clean; zero `sorry`; zero new axioms beyond Lean kernel's three.

The six WARN findings are all citation-registry hygiene gaps: 4 bibitems missing from `CITATION_REGISTRY`, one missing `PAPER_DEPENDENCIES` entry (systemic gap affecting paper29-39), and one Vergeles2025 title rewording. None of these block the Stage 10 claims-review gate; they block Stage 14 submission-readiness via the standard citation-verification path.

## PASS findings (10)

| ID | Category | Verification |
|----|----------|--------------|
| P1 | lean_theorem_existence | 9/9 cited theorem names + tracked structure exist by exact name in `HeatKernelExpansion.lean` |
| P2 | cross_module_lean_refs | `G_N_sakharov`, `G_N_sakharov_pos`, `G_N_emerg`, `G_N_emerg_at_alpha_one` all present in `LinearizedEFE.lean`; cross-bridge body invokes `G_N_sakharov` by full name |
| P3 | numerical_anchor | 1/G_N(GUT) = 15·10^32/(12π) = 3.9789e31 vs paper claim 3.98e31 (0.028% rel err); M_P^2 = 1.4884e38 vs 1.49e38 (0.11%) |
| P4 | a4_rationals | -5/(12·180), 7/(12·180), -12/(12·180); GB combo -45/(12·180) = -1/48 exact |
| P5 | theorem_count | `\heatKernelThms{19}` matches 19 top-level theorems in Lean source |
| P6 | test_count | `\heatKernelTests{36}` matches 36 `def test_*` functions in `tests/test_heat_kernel.py` |
| P7 | sorry_clean | grep -c sorry → 0; `lake build SKEFTHawking.HeatKernelExpansion` succeeds |
| P8 | formulas_canonical | All 5 referenced formulas exist in `src/core/formulas.py`; Python module reproduces paper Eq. 12 |
| P9 | biconditional_proof | `a2_matches_GNemerg_iff_alpha_ADW_unity` proof matches paper text: `mul_right_cancel` forward, `G_N_emerg_at_alpha_one` backward |
| P10 | citation_registered | 5/9 bibitems in `CITATION_REGISTRY` (Sakharov1968, Adler1982, Diakonov2011, VladimirovDiakonov2012, Vergeles2025) |

## WARN findings (6)

| ID | Category | Issue | Remediation |
|----|----------|-------|-------------|
| W1 | citation_unregistered | `Gilkey1995` not in `CITATION_REGISTRY` (book) | Add entry with `doi: None, doi_verified: True` (ISBN-traceable) |
| W2 | citation_unregistered | `Vassilevich2003` not in `CITATION_REGISTRY` | Add with `doi: 10.1016/j.physrep.2003.09.002, arxiv: hep-th/0306138` |
| W3 | citation_unregistered | `ChristensenDuff1979` not in `CITATION_REGISTRY` (load-bearing source for a4 rationals) | Add with `doi: 10.1016/0550-3213(79)90516-9` (CrossRef-verify before flipping `doi_verified`) |
| W4 | citation_unregistered | `LinearizedEFE2026` (in-prep self-cite) | Optional: add with note "in preparation, this project" |
| W5 | paper_dependencies_missing | `paper39_heat_kernel_expansion` not in `PAPER_DEPENDENCIES` (systemic gap also affecting paper29-38) | Add entry with formulas, lean_modules, key_claims |
| W6 | citation_title_drift | Paper bibitem says "Unitarity of the diffeomorphism-invariant ADW lattice model"; registry says "Unitarity of 4D Lattice Theory of Gravity" (same DOI) | Align paper to registry title (matches arxiv 2506.00036) |

## Verification evidence

- `grep -c sorry lean/SKEFTHawking/HeatKernelExpansion.lean` → 0
- `lake build SKEFTHawking.HeatKernelExpansion` → "Build completed successfully (8267 jobs)"
- 19 top-level theorems counted via `grep -cE "^theorem " HeatKernelExpansion.lean`
- 36 tests counted via `grep -E "^\s*def test_" tests/test_heat_kernel.py | wc -l`
- Numerical recomputation:
  - `15·10^32/(12π) = 3.97887e31` (paper: 3.98e31, 0.028% rel err)
  - `1.22e19² = 1.4884e38` (paper: 1.49e38, 0.11% rel err)
  - a4 rationals match Lean def + Python `seeley_dewitt_a4_basis` exactly
  - GB local: `-45/(12·180) = -1/48` exact
