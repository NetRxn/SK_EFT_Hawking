# Phase 6AG — Operational quantum-network certification layer

**Status:** OPEN (2026-06-02). Bundle-target **D6 §6**. Public repo `SK_EFT_Hawking`,
namespace `SKEFTHawking.QuantumNetwork.*`. Makes the shipped 6AE/6AF functional-analytic QI
bricks (`traceNorm`/`traceDist`/`fidelity`/FvdG/`diamondDist`/`choiMatrix`/`maxEntangled`/
`krausMap`) **operational**: a two-sided diamond envelope, named-channel diamond bounds,
general-state network monotonicity, gate-fidelity↔diamond bridges.

**Source spec (asks — reference only, NOT a dependency):**
`temporary/working-docs/20260602-public-substrate-asks-general-state-QN-certification.md`.

**LEAK DISCIPLINE:** build PURE public QI theorems only. NEVER write the hyphenated private-repo
directory name, any private identifier, or any oracle/harness/cert/product framing into public
Lean or public docs — frame everything as standard quantum-information mathematics.

**Inherited invariants:** pin v4.29.1/`5e932f97`; kernel-pure `{propext, Classical.choice,
Quot.sound}`; NO sorry / new project-local axiom / `maxHeartbeats` / `native_decide`; Stage-9 per
increment (root-import + ExtractDeps + `update_counts.py`); preemptive-strengthening checklist
(load-bearing, non-tautological statements); lean-lsp MCP loop, not edit→`lake build`.

## Build order (each kernel-pure, committed incrementally, root-imported)

### 1. Candidate B / Ask 2 increment — quantitative Choi TRACE-NORM lower bound
Completes the two-sided sandwich `(1/2n)‖J₁−J₂‖₁ ≤ diamondDist ≤ n‖J₁−J₂‖∞`.
**Target:** `diamondDist K₁ K₂ ≥ (1/(2*n)) * traceNorm (choiMatrix (krausMap K₁) − choiMatrix (krausMap K₂))`.
- **DONE** (commit `abc26174`, `DiamondNormChoi.lean`): `traceNorm_submatrix_equiv`
  (`‖M.submatrix e e‖₁=‖M‖₁` via `traceNorm_eq_sqrtRootSum`+`submatrix_mul_equiv`+`charpoly_reindex`).
- **(a)** PSD-square-root uniqueness `posSemidef_eq_of_mul_self_eq` (`P,Q` PSD, `P*P=Q*Q ⟹ P=Q`)
  via the ELEMENTARY trace argument (NO `cfc_comp`, NO CFC instance): `D=P−Q`; `PD+DQ=P²−Q²=0`;
  `tr(DPD)=−tr(DQD)`, both `≥0` ⟹ `=0`; `DPD` PSD with trace 0 ⟹ `DPD=0`
  (`Matrix.PosSemidef.trace_eq_zero_iff`); `DPD=(√P D)ᴴ(√P D) ⟹ √P D=0 ⟹ PD=0`; likewise `QD=0`;
  `D²=DP−DQ=0`; `D` Hermitian, `D²=0 ⟹ D=0`. Uses `psdSqrt`/`psdSqrt_mul_self`/
  `conjTranspose_mul_mul_same`/`trace_mul_cycle`.
- **(b)** `traceNorm_smul_nonneg` (`traceNorm ((c:ℂ)•M)=c*traceNorm M` for `0≤c` real) via
  `traceNorm_eq_trace_absOp` + `absOp(c•M)=(c:ℂ)•absOp M` (both PSD, both square to `(c²:ℂ)•(MᴴM)`
  via `absOp_mul_self` ⟹ equal by (a)).
- **(c)** ω↔Choi swap identity `krausMap (tensorKraus K) (omegaVec n * (omegaVec n)ᴴ) =
  (choiMatrix (krausMap K)).submatrix (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n))`
  via `krausMap_tensorKraus_apply` + `omegaVec` collapse (entrywise both `= ∑ₖ Kₖ(y,α)·conj(Kₖ(y',β))`
  up to the swap).
- **(d)** `maxEntangled n = (n:ℂ)⁻¹•(ωωᴴ)` + `krausMap` linearity (`krausMap_smul`, derive if absent)
  ⟹ assemble with `diamondDist_ge_maxEntangled` + `traceNorm_submatrix_equiv` + `traceNorm_smul_nonneg`.

### 2. Ask 3 cheap (🟠, near-free) — general-state swap-chain monotonicity
Via the SHIPPED data-processing inequality `traceDist_krausMap_le` (`CPTPChannel.lean`). Model a
swap/LOCC segment as a Kraus channel; prove the end-to-end TRACE-DISTANCE to a target does not
increase under an additional swap segment, for ARBITRARY density-matrix links (trace-distance
version; the fidelity version needs fidelity-DPI which is NOT shipped — do trace-distance). New
file `QuantumNetwork/GeneralStateNetwork.lean`.

### 3. Ask 1 (🔴 GATING) — operational diamond-norm bounds for NAMED channels
Define `depolarizingKraus`/`dephasingKraus`/`ampDampKraus` + `IsKrausChannel` proofs (single-qubit
first; `d`-dim depolarizing the natural generalization). LOWER bounds via
`diamondDist_ge_maxEntangled` (explicit finite evaluation of `D((Φ⊗id)Ω,(id⊗id)Ω)`). UPPER: either
the shipped `diamondDist_le_choi_opNorm` (a bracket, "≤ acceptable as first cut") OR the exact
closed form via maximally-entangled-is-optimal for covariant channels (depolarizing `p(d²−1)/d²`,
dephasing `γ`, amp-damp `≤√γ`). Pursue symmetry/maxEntangled-optimal for exactness; bracket is the
acceptable fallback.

### 4. Ask 4 (🟠) — process / avg-gate-fidelity ↔ diamond bridges (LAST)
`avgGateFidelity_eq : F_avg Φ = (d·F_e Φ + 1)/(d+1)` (finite linear algebra over
`maxEntangled`/`choiMatrix`); fidelity↔diamond bounds (Wallman/Flammia: `1−F_e ≤ ½ diamondDist`,
`½ diamondDist ≤ √(1−F_e)·C(d)`) composing the lower (Cand. B/`maxEntangled`) + upper.

## OUT — do NOT attempt
The FULL general arbitrary-channel **primal=dual Choi-SDP EQUALITY**: needs a hand-built
finite-dim PSD-cone SDP-duality layer from Mathlib's Farkas (`ProperCone.hyperplane_separation_point`)
+ a Slater point (laborious-but-buildable, large); **the product does NOT need it and the asks
route around it.** Keep documented-deferred with this precise, fan-out-verified status: Mathlib at
pin has Farkas + Krein-Milman + cone-dual defs but **NO** Sion/von Neumann minimax, **NO** Fenchel
conjugate, **NO** Slater, **NO** zero-gap SDP strong duality, **NO** Bauer maximum principle.
**FENCE-DISCIPLINE** still applies to any NEW fence: fresh 2–4-agent fan-out + written
grep-verified blocker before fencing.

## DONE
Items 1–4 PROVEN (or any genuinely-blocked sub-item fenced with a precise fan-out-verified blocker —
NOT the whole asks); all kernel-pure, no sorry/new-axiom/maxHeartbeats/native_decide; new files
root-imported in `lean/SKEFTHawking.lean`; `lake build SKEFTHawking.ExtractDeps` clean; counts
regenerated (`scripts/update_counts.py`); D6 §6 + `papers/phase6AA_qnetwork_preprint/preprint_draft.md`
§3d extended (D6 LaTeX compile-clean); this roadmap maintained; memory note + MEMORY.md index +
Inventory updated; fresh-context Stage-13 review (general-purpose read-only agent) GREEN per major
increment (at least Candidate B and Ask 1). Commit each coherent lemma on `main`; do NOT push;
stage only own paths (never `git add -A`).
