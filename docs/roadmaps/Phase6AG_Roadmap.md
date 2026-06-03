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

## PROGRESS (2026-06-02)
- ✅ **6AG-1 / Candidate B DONE** (`diamondDist_ge_choi_traceNorm`, `DiamondNormChoiUpper.lean`, commit `5b103dd9`, kernel-pure `{propext,Classical.choice,Quot.sound}` fresh-process-verified): `diamondDist K₁ K₂ ≥ (1/2n)·‖J₁−J₂‖₁` — two-sided Choi sandwich CLOSED. Supporting (in `DiamondNormChoi.lean`, commit `6AG-1(a,b)`): `traceNorm_submatrix_equiv` (reindex-invariance), `posSemidef_eq_of_mul_self_eq` (PSD-sqrt uniqueness, elementary trace argument), `traceNorm_smul_nonneg`; + `krausMap_smul` + `krausMap_tensorKraus_omegaVec` (ω↔Choi = J reindexed by `prodComm`).
- ✅ **6AG-3 / Ask 3 DONE** (`GeneralStateNetwork.lean`, kernel-pure): `IsChannelStep`, `isChannelStep_krausMap`, `applyChain`, `traceDist_applyChain_le` (arbitrary-density-matrix network data-processing monotonicity). Root-imported.
- 🟢 **6AG-2 / Ask 1 (🔴 gating) — DEPHASING bound DONE (exact), amp-damp/depolarizing NEXT (established recipe).** `diamondDist_dephasing_ge : γ ≤ diamondDist (dephasingKraus γ) (idKrausPad 1 2)` PROVEN (commit `4af99b78`, fresh-process axioms `{propext,Classical.choice,Quot.sound}`) — the EXACT lower bound (maxEntangled optimal for dephasing). **RECIPE (reuse for amp-damp/depolarizing):** (1) `<chan>_choi_diff`: `choiMatrix(krausMap chan) − choiMatrix(krausMap idKrausPad) = scalar • <base>` via `choiMatrix_krausMap_apply` + 16-case `fin_cases` ext + √-squares; (2) `traceNorm <base>`: via `absOp <base> = c • (<base>·<base>)` (`posSemidef_eq_of_mul_self_eq` + explicit `<base>·<base>` = diagonal + its `(·)²=4•(·)` + trace); (3) assemble with `diamondDist_ge_choi_traceNorm` + `traceNorm_smul_nonneg`. NOTE: depolarizing is also Pauli-covariant (lower bound exact, = p·(d²−1)/d²); amp-damp is NOT covariant — Candidate-B lower + op-norm upper give a bracket, exact `≤√γ` needs the op-norm Choi computation. `idKrausPad m n` (padded identity) shipped.
  - 🔑 **DEPOLARIZING derivation worked out (use idKrausPad 3 2, Fin 4):** for the Pauli-split `Φ_p(ρ)=(1−p)ρ+(p/3)(XρX+YρY+ZρZ)`, `Choi(Φ_p)−Choi(id) = p·Base_dep` (basis {00,01,10,11}): diag `(00,00)=−2/3,(11,11)=−2/3,(01,01)=2/3,(10,10)=2/3`, off `(00,11)=(11,00)=−4/3`. Eigenvalues `{2/3,2/3,2/3,−2}` ⟹ `traceNorm(Base_dep)=4`, so `traceNorm(Choi diff)=4p`, `diamondDist ≥ (1/4)·4p = p` (EXACT, covariant). ⚠️ HARDER than dephasing: `Base_dep²` is NOT a scalar multiple of `|Base_dep|` (mixed-sign eigenvalues 2/3 vs −2), so the `absOp=½·B²` shortcut FAILS; `traceNorm(Base_dep)=4` needs the genuine charpoly route: `traceNorm = sqrtRootSum((Base_dep·Base_dep).charpoly)`, `Base_dep·Base_dep` has eigenvalues `{4/9,4/9,4/9,4}` (charpoly `(X−4/9)³(X−4)`), `sqrtRootSum = (2/3)·3 + 2 = 4`. The `Base_dep·Base_dep` is NOT diagonal (the {00,11} coupling block squares to `[[20/9,16/9],[16/9,20/9]]`) — so this is a real 4×4 charpoly computation, the genuinely fiddly part. The Choi-diff `= p·Base_dep` half follows the dephasing recipe (16-case ext + 4-Pauli sum incl. imaginary Y + √-squares).
  - **AMP-DAMP derivation worked out:** `Choi(ampDamp γ)−Choi(id)` (basis {00,01,10,11}): `(00,11)=(11,00)=√(1−γ)−1`, `(11,11)=−γ`, `(10,10)=γ`, else 0. NOT covariant; eigenvalues messy (not a clean multiple) — the clean `≤√γ` is the OP-NORM upper bound `diamondDist_le_choi_opNorm` (`n·‖Choi diff‖_∞`), needing `‖·‖_∞` of this 4×4, NOT the trace-norm lower route. Deprioritize vs depolarizing.
- 🟡 **6AG-2 / Ask 1 — SUBSTRATE DONE (historical), numerical bounds.** Channel defs + CPTP shipped (`NamedChannels.lean`, commits through counts 780 mod/10264 thm/0/0, full ExtractDeps clean): `dephasingKraus`/`ampDampKraus`/`depolarizingKraus` (Pauli form, p split over X/Y/Z) + `isKrausChannel_*`; `pauliX`/`pauliY` (+ Hermitian + square=1); reuses `HaarPauli.pauliZ` (NAME COLLISION lesson: `pauliZ` already in HaarPauli — import it, don't redefine). REMAINING (numerical diamond bounds): ⚠️ **`m`-matching wrinkle** — `diamondDist K₁ K₂` needs BOTH `K₁ K₂ : Fin m → …` with the SAME `m`; the identity channel must be PADDED to match (e.g. `idKrausPad : Fin 2 → … | 0 => 1 | 1 => 0` for dephasing's Fin 2; `Fin 4` for depolarizing). Then bounds: lower via `diamondDist_ge_choi_traceNorm` (constant 1/2n ⟹ BRACKET, e.g. dephasing ≥ γ/2, NOT exact γ), upper via `diamondDist_le_choi_opNorm`; both need explicit 4×4 Choi-difference traceNorm/op-norm (eigenvalue computation — the fiddly part). EXACT closed forms (dephasing γ, depolarizing p·(d²−1)/d², amp-damp ≤√γ) need the maxEntangled-optimal/covariance argument (a real theorem). Bracket is the acceptable first cut per spec.
  - 🔑 **DEPHASING computation worked out (lower bound is TIGHT):** for `Δ = Φ_γ − id`, `Δ(E_{ab}) = γ(z_a z_b − 1)E_{ab}` (`z₀=1,z₁=−1`) = `0` if `a=b`, `−2γ E_{ab}` if `a≠b`. So `Choi(Φ_γ) − Choi(id) = Choi(Δ)` has the single off-diagonal pair `−2γ` at `((0,0),(1,1))` and `((1,1),(0,0))`, eigenvalues `{2γ, −2γ, 0, 0}`, hence `traceNorm = 4γ`. Then `diamondDist_ge_choi_traceNorm` gives `diamondDist ≥ (1/(2·2))·4γ = γ` — the EXACT value (op-norm upper is the looser `n‖J‖∞ = 2·2γ = 4γ`). So the achievable clean Ask-1 result is the exact LOWER bound `diamondDist (dephasingKraus γ) (idKrausPad) ≥ γ`; the work is computing `traceNorm(Choi Δ) = 4γ` (sparse 4×4: `traceNorm_hermitian` ∑|eig|, eig via charpoly `X²(X²−4γ²)`). Needs `idKrausPad : Fin 2 → … | 0 => 1 | 1 => 0` (CPTP: `1+0=1`).
- ✅ **6AG-2 / Ask 1 (🔴 gating) FULLY DONE — all 3 named channels (2026-06-02).** Dephasing `diamondDist_dephasing_ge ≥ γ` (exact, commit `4af99b78`); **depolarizing `diamondDist_depolarizing_ge ≥ p`** (exact, commit `2be10940`): the `½·B²` shortcut fails (mixed-sign eigenvalues) so used `|B| = 1 − ½B` via minimal poly `B²=(4/3)(1−B)`, PSD-exhibited as `½·1 + (3/8)·BᴴB` (sum of two PSD) — **dodged the charpoly route entirely**; `traceNorm(Base_dep)=4` ⟹ `4p`. **amp-damp `diamondDist_ampDamp_ge ≥ γ/2`** (commit `7a4149bc`): non-covariant ⟹ Candidate B not tight; used the Hermitian dual-norm keystone `re_trace_mul_le_traceNorm_hermitian` with a diagonal Loewner contraction (`+1` at (1,0), `−1` at (1,1)) aligned with the `±γ` diagonal Choi entries ⟹ `traceNorm ≥ 2γ`. All kernel-pure, fresh-process-verified.
- ✅✅ **6AG-4 / Ask 4 FULLY DONE — bridges PROVEN + Haar formula PROVEN (FENCE DOWN, 2026-06-02).** `GateFidelityBridge.lean`: `one_sub_sqrtFidelity_output_le_diamondDist` + contrapositive (commit `5f5ad76d`). **`avgGateFidelity_eq : F_avg(Φ)=(d·F_e+1)/(d+1)` general qudit dimension d — PROVEN, kernel-pure, UNCONDITIONAL (only `IsKrausChannel`), commits `46a8fee6`→`5f73d749`.** The earlier FENCE (Mathlib v4.29.1 has NO Weingarten/t-design/twirl 2nd-moment) was REAL for *imported* machinery, but the user pushed past it: the identity is reachable WITHOUT that machinery via the **constructive Gaussian→sphere route**. Build (each kernel-pure, root-imported): brick 1 `GaussianMoments` (1-D moments ∫xⁿexp(−x²/2)); brick 2 `GaussianWick` (multivariate Isserlis tensor); brick 3 `GaussianPolar` (homogeneous polar reduction via `measurePreserving_homeomorphUnitSphereProd`); brick 4 `GaussianComplexMoment`/`GaussianComplexTensor` `complexSphereTensor` (degree-(2,2) complex sphere moment `=(δ_pq δ_rs+δ_ps δ_qr)·S₁/(d(d+1))` — the unitary-2-design 2nd moment as a THEOREM, not an import); brick 5 `GateFidelity` (`sphere_qform_term`→`sphere_braKet_normSq` contraction, `delta_contraction`, `kraus_normSq_sum` CPTP collapse `∑ₖtr(KₖᴴKₖ)=d`, `sphereTotal_ne_zero`, headline `avgGateFidelity_eq`). 790 mod/10393 thm/0 axiom/0 sorry, full ExtractDeps clean, D6 §6(iv′)+preprint §3e PROSE updated (D6 LaTeX compile-clean 9pp), Stage-13 GREEN (one preprint-only d=2 'recovered'→'consistent with' overclaim softened — the single-qubit `HaarPauli.teleportAvgFidelity_horodecki_unconditional` is a distinct teleportation quantity, consistent but not formally derived). **LESSON: a grep-verified Mathlib-gap FENCE is about *imported* machinery — a constructive build can still route around it; the user's "knock down the fence" instinct was right.**

## 🎯 Ask-2 TIGHT-UPPER FENCE KNOCKED DOWN (2026-06-02, fence-reframe — weak vs strong duality)
- ✅ **Watrous weak-dual upper bound `diamondDist_le_dual_witness`** (`DiamondNormDual.lean`, commit `40fabe52`, kernel-pure): for any Hermitian `W` with `W ≥ 0` and `W ≥ C = J₁−J₂` (Loewner), `diamondDist ≤ ‖ptrace2 W‖`. **KEY REFRAME:** the Ask-2 fence was on *strong* duality (primal=dual, needs absent Slater/minimax/Fenchel); the tight UPPER bound needs only *weak* duality (any feasible W ⟹ upper bound), which needs none of that. Verified the shipped `diamondDist_le_choi_opNorm` (`n‖C‖`) is the trivial-witness `W=‖C‖·1` special case (`ptrace2(‖C‖·1)=n‖C‖·1`) ⟹ this strictly GENERALIZES it. Linchpin: `choiContraction 1 ρ = inMarginal ρ ⊗ₖ 1` + partial-trace identity `tr(W·(G⊗1))=tr(ptrace2 W·G)`; Loewner monotonicity `re_trace_mul_le_of_loewner`; the `P≤1` step.
- ✅ **EXACT named-channel diamond distances via optimal dual witness** (`NamedChannelDiamondExact.lean`, commits `fe92dd3a`+`c5a4d8ea`+`53da20c2`, kernel-pure): `posSemidef_smul_outer` (γ-scaled real rank-1 outer is PSD). **`diamondDist_dephasing_eq = γ`** (witness `γ·v vᵀ`, `v=e₀₀−e₁₁`; `ptrace2 W=γ·1`) — first two-sided EXACT for a named channel, NO twirl. **`diamondDist_depolarizing_eq = p`** (witness `C₊=(2p/3)P₊` = sum of 3 rank-1 projectors onto the +2/3 eigenspace; `ptrace2 W=p·1`). **`diamondDist_ampDamp_le ≤ γ+1−√(1−γ)`** (non-covariant ⟹ clean non-optimal witness; correct-direction two-sided bracket `γ/2 ≤ ◇ ≤ γ+1−√(1−γ)` — answers the private "wrong-direction" flag). Counts now **783 mod/10338 thm/0 axiom/0 sorry**; D6 §6(v)+preprint extended.
- 🔑 LESSONS: (a) `simp only` (not full `simp`) to fire `Matrix.smul_apply` on `(c:ℂ)•namedDef` — full simp prematurely unfolds the def to a raw lambda (Pi-smul); (b) define witnesses via a real `s : ι→ℝ` with casts so `posSemidef_smul_outer` matches syntactically (ℂ-valued `if`s cause a whnf-defeq blowup on `exact`); (c) `Real.sqrt_le_sqrt` via `calc` not `rw [show 1 = √1]` (rewrites ALL `1`s).
- ✅ **RESOLVED 2026-06-02: Ask-4 Haar `avgGateFidelity_eq` PROVEN.** The toehold was correct — the Gaussian→sphere route bypassed the absent Weingarten machinery. It took FIVE bricks (not one lemma) — the degree-4 complex sphere moment needed the full 1-D-moments → Wick-tensor → polar-reduction → ℂ^d≅ℝ^{2d} chain plus the Kraus contraction + CPTP collapse — but it is a discrete build, no wall. NO public fences remain in Phase 6AG (all 4 asks done).

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
