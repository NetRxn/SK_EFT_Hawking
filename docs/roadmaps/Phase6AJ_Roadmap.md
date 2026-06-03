# Phase 6AJ — Fidelity-domain data processing (MOONSHOT E, public)

**Status:** ✅ **COMPLETE (2026-06-03)** — all primary deliverables PROVEN kernel-pure, no fence, no
axiom; the optional rank-deficient-output strengthening also discharged (OUTCOME 2 + 2b below).
Public-only. Lifts the general-state network monotonicity from the trace-distance domain (shipped:
`traceDist_applyChain_le`) into the **fidelity** domain, so a downstream chain certificate can live in
fidelity, not only trace distance.

**Closure summary (what to read):** the mixed-unitary headline (OUTCOME, `7ac93fe0`) → general-CPTP +
joint-concavity + chain (OUTCOME 2, `fecc5341`→`cf1b8c55`) → fully-general rank-deficient-output DP
(OUTCOME 2b, `655260a8`). Single-step fidelity DP `sqrtFidelity_krausMap_ge_psd` is now fully general
(any trace-preserving Kraus channel, PosDef inputs, *arbitrary* outputs). Files: `FidelityBlockForm`,
`FidelityForwardBound`, `OpNormHolder`, `FidelityKrausDP`, `FidelityForwardBoundPSD`.

**The target.** Uhlmann's monotonicity / data-processing inequality for fidelity: for any CPTP map
`Φ` and density operators `ρ, σ`,
`F(Φρ, Φσ) ≥ F(ρ, σ)`  (equivalently `sqrtFidelity(Φρ,Φσ) ≥ sqrtFidelity(ρ,σ)`),
and then the chain corollary mirroring `traceDist_applyChain_le`:
`sqrtFidelity(applyChain K ρ, applyChain K σ) ≥ sqrtFidelity(ρ, σ)` (fidelity is non-decreasing along
a CPTP network — the opposite monotone direction from trace distance).

**Why it's a moonshot.** Fidelity DP is genuinely harder than trace-distance DP. The standard proofs
go through (i) Uhlmann's theorem (fidelity = max overlap over purifications) + Stinespring, or (ii) an
integral / variational representation of fidelity, or (iii) operator-concavity / joint concavity of
fidelity (Lieb). Pinned Mathlib likely lacks all three packaged. We DO have, as scaffolding: the
Uhlmann `sqrtFidelity` definition + `sqrtFidelity_eq_traceNormOf` (`F = ‖√σ√ρ‖₁`), the trace-norm
machinery, CPTP/Kraus model, and trace-distance DP (`traceDist_krausMap_le`).

**Invariants:** kernel-pure; **NO new project-local axiom without explicit user sign-off**;
fence-discipline (interactive lean4 scouting + written blocker for any new fence). If the full DP
inequality is unreachable, a strictly-weaker-but-honest deliverable (e.g. fidelity DP for the
restricted unital / mixed-unitary case, or a joint-concavity lemma) is acceptable and must be labeled
as the restricted result, not the general one.

---

## Wave 6AJ.0 — Mathlib scouting (interactive lean4 skill, NOT deep research)
Via `lean_local_search`/`lean_leansearch`/`lean_loogle`: search for purifications, Uhlmann's theorem,
Stinespring dilation, joint concavity of fidelity, operator concavity (`OperatorConcave`/Löwner),
`√` operator-monotonicity (Ando), and any fidelity monotonicity already in Mathlib's quantum-info /
matrix-analysis corner. Output: present/absent table with exact names. This decides the route.

## Wave 6AJ.1 — Route selection + core inequality
Pick the most-supported route:
- **(a) Operator-monotone / Ando route:** if `√` operator-monotonicity + a Kraus-map Löwner argument
  are reachable, prove DP directly on `F = ‖√σ√ρ‖₁` via the trace-norm contraction already used for
  `traceDist_krausMap_le` (the pos/neg-part / dual-norm keystone may transfer).
- **(b) Block-matrix / joint-concavity route:** prove joint concavity of `(ρ,σ) ↦ F(ρ,σ)` (Lieb) and
  derive DP from concavity + the channel as an average of unitaries (for the mixed-unitary subclass)
  or via the Choi/dilation if reachable.
- **(c) Uhlmann-purification route:** only if Stinespring/purification is reachable in pin (likely not).
Headline `sqrtFidelity_krausMap_ge` (CPTP fidelity DP), with hypotheses honestly scoped to whatever
subclass the chosen route supports.

## Wave 6AJ.2 — Chain corollary + symmetry with trace-distance
`sqrtFidelity_applyChain_ge` mirroring `traceDist_applyChain_le`; note the monotone-direction duality
(trace distance ↓, fidelity ↑) consistent with FvdG. Recommend (do not scope) the private chain cert
gain a fidelity-domain branch.

## Wave 6AJ.3 — Consolidation
Headline(s) + D6 §6 + preprint update; Stage-13.

---

## Phase exit (two acceptable outcomes)
EITHER (a) general (or honestly-scoped restricted) fidelity DP `sqrtFidelity_krausMap_ge` + the chain
corollary, PROVEN kernel-pure; OR (b) a fence with an interactive-lean4-verified written blocker and
the partial deliverable (e.g. joint concavity, or the restricted-subclass DP) clearly labeled. NO
axiom without sign-off. Counts/docs/memory synced.

---

## ✅✅ OUTCOME 2 (2026-06-03, autonomous /goal) — GENERAL-CPTP UHLMANN MONOTONICITY + JOINT CONCAVITY + CHAIN **PROVEN** (`FidelityKrausDP.lean`, commits `fecc5341`→`cf1b8c55`)

**ALL FOUR PRIMARY DELIVERABLES CLOSED, kernel-pure `{propext, Classical.choice, Quot.sound}`, NO
axiom, NO fence.** The roadmap's fear that "general CPTP needs Stinespring/Choi/Lieb — larger" was
WRONG (the 6AI lesson again): the mixed-unitary proof GENERALIZED directly because
`diagDil_conj_fidelityBlock` already holds for an *arbitrary* matrix, not just a unitary.

1. **General-CPTP fidelity DP** `sqrtFidelity_krausMap_ge`: `F(Φρ,Φσ) ≥ F(ρ,σ)` for an arbitrary
   trace-preserving Kraus channel `Φ(·)=∑ₖKₖ·Kₖᴴ` (`∑ₖKₖᴴKₖ=1`), PosDef inputs whose outputs are
   PosDef. Bricks: `fidelityBlock_sum` (finite additivity) + `fidelityBlock_krausMap_posSemidef`
   (block-PSD transport via the sum of `(Kₖ⊕Kₖ)`-congruences) + `trace_krausMap` (TP) ∘ the shipped
   Alberti forward bound + attainment. **No Stinespring/Choi/Lieb.**
2. **Output-PosDef discharged for the broad unital-faithful class** `posDef_krausMap_of_sum`: if the
   channel's unital part `∑ₖKₖKₖᴴ` is PosDef then `Φ` preserves PosDef (quadratic-form argument via
   `posDef_iff_dotProduct_mulVec`; some `Kₖᴴv≠0` forced by the unital-part PosDef). Hypothesis-free
   corollary `sqrtFidelity_krausMap_ge'`. Subsumes mixed-unitary (`∑pᵢUᵢUᵢᴴ=1`).
3. **Joint concavity** `sqrtFidelity_jointly_concave`: `t·F₁+(1−t)·F₂ ≤ F(combo,combo)` — drops out of
   the Alberti max-of-linear form (`fidelityBlock_smul_add_smul` + `posDef_convex`).
4. **Fidelity-domain network chain** `sqrtFidelity_applyChain_ge` (mirror of `traceDist_applyChain_le`,
   opposite monotone direction — `D↓`, `F↑`, FvdG-consistent): `IsFidelityStep` abstraction
   (preserves PosDef + fidelity-monotone) + `isFidelityStep_krausMap`/`isFidelityStep_krausMap'`
   (Kraus constructors) + `applyChain_posDef` + `sqrtFidelity_step_ge`. The dependent PosDef proofs in
   `sqrtFidelity` are absorbed by proof irrelevance in the `le_trans` induction.

**Remaining (optional, NOT a fence):** fully general arbitrary-PSD-output DP (drop the output-PosDef
regularity entirely) would need `sqrtFidelity` continuity + ε-regularization of the Schur-based forward
bound — a measure-zero boundary case handled by continuity in the standard treatment; not required for
the operational chain certificate (states are full-rank generically). New file: `FidelityKrausDP.lean`.

### ✅ OUTCOME 2b (2026-06-03, same /goal) — output-PosDef regularity DISCHARGED (`FidelityForwardBoundPSD.lean`, commit `655260a8`)

The "optional remaining" item above is now **DONE**, kernel-pure. `re_trace_block_le_sqrtFidelity_psd`
relaxes the forward Alberti bound from positive-DEFINITE to positive-SEMIdefinite `ρ,σ`, so
`sqrtFidelity_krausMap_ge_psd` gives the **textbook Uhlmann DP** `F(Φρ,Φσ) ≥ F(ρ,σ)` for PosDef inputs
and an **arbitrary** trace-preserving Kraus channel — *outputs may be rank-deficient* (e.g. a reset
channel); no output hypothesis at all.

🔑 **The toehold that cracked it (3-agent fan-out, then a route the scouts missed):** the obvious
ε-regularization needs `sqrtFidelity`-continuity = `psdSqrt`-continuity, and the direct Mathlib route
(`CFC.continuousOn_sqrt`) is **blocked** — the non-unital isometric CFC instance genuinely does not
resolve on bare `Matrix ι ι ℂ` (verified by direct probe; would need a `CStarMatrix` detour). The
winning move: do continuity only **along the commuting ray** `ρ+ε·1`, where the eigenbasis is *fixed*
(`ρ+ε·1` shares `ρ`'s eigenvectors), so by PSD-square-root **uniqueness** (`posSemidef_eq_of_mul_self_eq`)
`psdSqrt(ρ+ε·1) = U·diag(√(λᵢ+ε))·Uᴴ` with `U` constant — continuity in `ε` then reduces to continuity
of the diagonal map `c ↦ diag(√(λᵢ+c))`. No CFC continuity, no `CStarMatrix`, no Powers–Størmer. Bricks:
`psdSqrt_eq_conj_diag` / `psdSqrt_eq_conj_diag0` (uniqueness, fixed `U` from `eigenvectorUnitary_conj_eq_diagonal`)
→ `tendsto_psdSqrt_perturb` (ray continuity) → `fidelityBlock_add_smul_one` → the ε-limit via
`continuous_traceNorm` + `ge_of_tendsto` (the `traceNorm_mul_le` perturbation pattern).

Note the *chain* corollary still requires PosDef-preserving steps (`IsFidelityStep.posDef`) — chaining
attainment needs full-rank intermediates; the single-step DP is now fully general.

---

## ✅ OUTCOME (2026-06-03, autonomous /goal) — MIXED-UNITARY UHLMANN MONOTONICITY **PROVEN** (`sqrtFidelity_mixedUnitary_ge`, commit `7ac93fe0`)

**HEADLINE CLOSED:** `F(Φρ,Φσ) ≥ F(ρ,σ)` for mixed-unitary `Φ(·)=∑pᵢUᵢ·Uᵢᴴ`, PosDef `ρ,σ`, kernel-pure.
Built end-to-end from scratch: the full **Alberti SDP characterization** `F(ρ,σ)=max{Re tr X :
[[ρ,X],[Xᴴ,σ]]⪰0}` (forward bound `re_trace_block_le_sqrtFidelity` + attainment
`exists_block_re_trace_eq_sqrtFidelity`) + the **op-norm/trace-norm Hölder machinery**
(`re_trace_mul_le_opNorm_mul_trace`/`…_traceNorm`) + the **EuclideanLin `‖K‖≤1` infra**
(`opNorm_le_one_of_mul_conjTranspose_le_one`, routing around the matrix-`CStarAlgebra` instance
whnf-wall via `isPositive_toEuclideanLin_iff`+`opNNNorm_le_iff`). `posDef_mixedUnitary` +
`trace_mixedUnitary` close the channel-preservation steps. NO axiom. Modules: `OpNormHolder.lean`,
`FidelityBlockForm.lean`, `FidelityForwardBound.lean`. **Remaining (larger, optional):** joint-concavity
corollary (drops out of the Alberti form); general CPTP via a project-side Stinespring/Choi dilation.

---

### (superseded) earlier outcome — reversible-channel fidelity DP SHIPPED; general/mixed-unitary route mapped

**Wave 6AJ.0 scout (interactive lean4 on Mathlib v4.29.1).** PRESENT: operator-monotone
`CFC.monotone_sqrt`. ABSENT (verified — leansearch/loogle): joint concavity of fidelity, operator
convexity of `t⁻¹` (Choi's inequality), Lieb concavity, purification / Stinespring dilation. ⟹ the
general-CPTP and mixed-unitary Uhlmann-monotonicity routes all lack a ready theorem.

**SHIPPED (constructive, the reachable toehold):** `FidelityDataProcessing.lean` (root-imported,
kernel-pure) — fidelity is exactly invariant under unitary conjugation, i.e. data processing for the
*reversible* (unitary-channel) subclass as an EQUALITY:
- `posSemidef_unitary_conj`: `U M Uᴴ ⪰ 0`.
- `psdSqrt_unitary_conj`: `√(U M Uᴴ) = U √M Uᴴ` (via `posSemidef_eq_of_mul_self_eq` — NO CFC
  conjugation lemma needed, dodging the Mathlib gap).
- `absOp_unitary_conj`: `|U A Uᴴ| = U |A| Uᴴ`.
- `traceNorm_unitary_conj`: `‖U A Uᴴ‖₁ = ‖A‖₁` (modulus conjugation + trace cyclicity).
- `sqrtFidelity_unitary_conj`: **`F(UρUᴴ, UσUᴴ) = F(ρ, σ)`** — the headline reversible-channel DP.

**ROUTE MAPPED — general/mixed-unitary monotonicity is an in-progress continuation, NOT a fence
(Explore fan-out 2026-06-02).** The most reachable route is the **block-PSD / Alberti SDP form**
`F(ρ,σ) = max{ Re tr X : [[ρ, X],[Xᴴ, σ]] ⪰ 0 }`. Mathlib ships the Schur-complement support
(`Matrix.PosDef.fromBlocks₂₂` / `fromBlocks₁₁`, `schur_complement_eq₁₁/₂₂`,
`LinearAlgebra/Matrix/PosDef.lean` + `…/Hermitian.lean`) and the conjugation-monotonicity bricks
(`star_left_conjugate_le_conjugate`, `conjugate_le_conjugate_of_nonneg`, `Matrix.PosSemidef.kronecker`).
With the block characterization, mixed-unitary monotonicity is immediate (conjugate the feasible `X` by
`∑ pᵢ Uᵢ`, same trace) and joint concavity drops out. NO joint concavity / Lieb / Stinespring needed
for the mixed-unitary case.

**Brick sequence (continuation — precisely pinned):**
1. ✅ **DONE** `fidelityBlock_posDef_schur` (`FidelityBlockForm.lean`, commit `6e19aae1`): for `σ`
   PosDef, `[[ρ,X],[Xᴴ,σ]] ⪰ 0 ↔ ρ − X σ⁻¹ Xᴴ ⪰ 0` (wraps Mathlib `PosDef.fromBlocks₂₂`,
   `PosDef.isUnit` for invertibility). Exhibits `X = √ρ K √σ`, `KKᴴ = ρ^{-½}(Xσ⁻¹Xᴴ)ρ^{-½} ⪯ 1`.
2. ✅ **DONE** `fidelityBlock_mixedUnitary_posSemidef` (TRANSPORT, commit `676791f9`): feasible `X`
   for `(ρ,σ)` ⟹ `∑pᵢUᵢXUᵢᴴ` feasible for `(Φρ,Φσ)`, via `diagDil`/`fidelityBlock_sum_smul`.
3. **NEXT — op-norm/trace-norm Hölder `‖K·M‖₁ ≤ ‖K‖ · ‖M‖₁`** (the genuine new analytic brick).
   ROUTE (verified reachable, NO SVD): `|KM| = √(Mᴴ(KᴴK)M) ⪯ √(‖K‖²·MᴴM) = ‖K‖·|M|` by
   **operator-monotone √** (Mathlib `CFC.monotone_sqrt`, bridged to the project's `psdSqrt` — or a
   direct `psdSqrt`-monotone lemma) on the conjugation `Mᴴ(KᴴK)M ⪯ ‖K‖²MᴴM` (from `KᴴK ⪯ ‖K‖²·1`
   + `conjTranspose_mul_mul_same` Loewner-monotone), then `tr|KM| ≤ ‖K‖ tr|M|` (trace-monotone).
   The contraction `‖K‖ ≤ 1` from `KKᴴ ⪯ 1` is `eigenvalue_le_l2opNorm` / L2Operator.
3a. ✅ **DONE** `re_trace_antiHermitian_mul_posSemidef` + `re_trace_mul_le_opNorm_mul_trace`
   (`OpNormHolder.lean`, commit `03059518`): general `Re tr(C·P) ≤ ‖C‖·tr P` (arbitrary C, PSD P),
   CFC-free via the Hermitian-part split + shipped Hermitian keystone.
3b. ✅ **DONE** `re_trace_mul_le_opNorm_mul_traceNorm` (commit `6db70cc6`): `Re tr(K·M) ≤ ‖K‖·‖M‖₁`
   for invertible M, via polar `M=U|M|` + 3a + unitary `‖U‖=1` (`CStarRing.norm_star_mul_self`).
   ⚠️ **CONFIRMED BLOCKER for `‖K‖≤1`:** the matrix `CStarAlgebra` instance whnf-times-out (200k
   heartbeats) — `CStarAlgebra.norm_le_one_iff_of_nonneg`, `norm_cfc_le`, and the whole isometric-CFC
   family are UNUSABLE on `Matrix ι ι ℂ` (verified in isolation via `lean_run_code`). The `spectrum`
   route (`spectrum.norm_le_norm_of_mem`, used by the shipped `eigenvalue_le_l2opNorm`) works but is
   the wrong direction.
4. **`‖K‖ ≤ 1` from `KKᴴ ⪯ 1` — EuclideanLin CLM bridge (avoids CStarAlgebra), CLEAN lemmas:**
   `Matrix.isPositive_toEuclideanLin_iff : (toEuclideanLin A).IsPositive ↔ A.PosSemidef` gives
   `(toEuclideanLin (1−KKᴴ)).IsPositive` ⟹ `0 ≤ re⟪v,(1−KKᴴ)v⟫` ⟹ `‖Kᴴv‖²=re⟪v,KKᴴv⟫ ≤ ‖v‖²` (adjoint
   `toEuclideanLin Kᴴ` of `toEuclideanLin K`); then `Matrix.cstar_nnnorm_def : ‖A‖₊=‖toEuclideanCLM A‖₊`
   + `ContinuousLinearMap.opNNNorm_le_iff : ‖f‖₊≤C ↔ ∀x,‖f x‖₊≤C‖x‖₊` gives `‖Kᴴ‖≤1`, then `‖K‖=‖Kᴴ‖`
   (`norm_star`). `toEuclideanCLM A x = (WithLp.equiv 2 _).symm (A.mulVec ((WithLp.equiv 2 _) x))`.
   **Then forward bound** `re_trace_block_le_sqrtFidelity`:
   `Re tr X = Re tr(K√σ√ρ) ≤ ‖K‖·‖√σ√ρ‖₁ ≤ F` (brick 3b + `re_trace_le_traceNorm` SHIPPED + cyclic).
   Perturb singular `ρ,σ` via the shipped `+1/k•1` + `continuous_traceNorm`.
4a. ✅ **DONE** `opNorm_le_one_of_mul_conjTranspose_le_one` (`OpNormHolder.lean`, commit `125958f1`):
   `‖K‖≤1` from `KKᴴ⪯1` via the EuclideanLin CLM route (`cstar_nnnorm_def`+`opNNNorm_le_iff`+
   `isPositive_toEuclideanLin_iff`+adjoint), AVOIDING the matrix-CStarAlgebra whnf-wall. Infra built.
4. ✅ **DONE** `re_trace_block_le_sqrtFidelity` (`FidelityForwardBound.lean`, commit `f2bd646a`):
   PosDef `ρ,σ`, block-PSD ⟹ `Re tr X ≤ F`. `isUnit_psdSqrt` + Schur ⟹ `X=√ρK√σ`,
   `1−KKᴴ=√ρ⁻¹(ρ−Xσ⁻¹Xᴴ)√ρ⁻¹⪰0`, then brick4a + brick3b + cyclic trace.
5. ✅ **DONE** `exists_block_re_trace_eq_sqrtFidelity` (attainment, commit `6150284a`; decomposed via `sqrt_mul_inv_mul_sqrt`+`polar_witness_schur_eq` to dodge heartbeat walls). **The full Alberti characterization F=max{Re tr X} is now formalized (forward+attainment).** Original plan: `X* = √ρ·W·√σ`, `W=|√σ√ρ|⁻¹(√σ√ρ)ᴴ`
   the polar unitary (project's `traceNorm_mul_le_of_isUnit` internal construction — EXPOSE it as a
   standalone `traceNorm M = Re tr(W·M)`, `W` unitary, invertible M). Block-PSD via Schur (`ρ−X*σ⁻¹X*ᴴ
   = ρ−√ρ W Wᴴ √ρ = 0 ⪰0`); `Re tr X* = Re tr(W·√σ√ρ) = ‖√σ√ρ‖₁ = F`.
6. **Headline `sqrtFidelity_mixedUnitary_ge`** = forward (brick 4 at `(Φρ,Φσ)`) on the transported
   optimizer (brick 2) ∘ attainment (brick 5): `F(Φρ,Φσ) ≥ Re tr(∑pᵢUᵢX*Uᵢᴴ) = Re tr X* = F(ρ,σ)`.
   Sub-needs: (a) `Φ` preserves PosDef (convex combo of PosDef conjugations); (b) transport preserves
   trace (`tr(∑pᵢUᵢX*Uᵢᴴ)=tr X*`, `∑pᵢ=1`, Uᵢ unitary). Then joint-concavity corollary; general CPTP
   via a project-side Stinespring dilation (larger). NO axiom.
