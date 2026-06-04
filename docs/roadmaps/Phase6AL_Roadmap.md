# Phase 6AL — Entropy / entanglement strengthening (post-Klein harvest)

**Status: PLANNED 2026-06-04.** Quantum Klein's inequality (`relativeEntropy_nonneg`, Phase 6AK FU-8a)
plus von Neumann entropy, matrix log, relative entropy, classical Gibbs, and tensor-additivity
(`vonNeumannEntropy_kronecker_add`) unlocked a cluster of foundational entropy/entanglement theorems that
were not yet harvested. This phase takes them in four waves. **Standing invariants (non-negotiable):**
kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms** (Invariant #15);
no `native_decide`; no `set_option maxHeartbeats` in proof bodies; decompose-before-asserting-walls;
bordism-isolate commits if root imports change (note: the parallel agent has been committing the bordism
root imports, so `git show HEAD:lean/SKEFTHawking.lean` may already include them — check before the dance);
never push to remote.

All items below were assessed via the proven method (first principles + decomposition + Explore fan-out +
Mathlib MCP search). Reachability verdicts and the genuine walls are recorded honestly per item.

**PROGRESS:** Wave 1 ✅ SHIPPED `6c089896` (`EntropyConcavity.lean` + `GibbsVariational.lean`). Wave 2 ✅
SHIPPED `1887803e` (`NegativityGeneral.lean`). Wave 3 ✅ SHIPPED `8d56d522` (`EntropySubadditivity.lean`:
`cfc_diagonal`, `matrixLog_kronecker`, `vonNeumannEntropy_subadditive`, `mutualInformation_nonneg`). All
kernel-pure (lean_verify); Wave-3 full-lib axiom gate DEFERRED (parallel agent's mid-edit
`ThetaModularWeight.lean` breaks the full ExtractDeps build — module built standalone). Wave 4 (F) remains.

**Wave 4 / F1b CAPSTONE ✅ SHIPPED `e959066d` (2026-06-04): `mirsky_of_wielandt_frame` (FannesAudenaert.lean).**
The ENTIRE Lidskii→Mirsky chain is now staged on the SINGLE hypothesis `Hframe` (= the Wielandt frame-existence
step (3)): given for every position tuple `s` an orthonormal frame in `A`'s eigen-flag whose `B`-Rayleigh sum is
`≤ ∑ᵣ λ↓_{sᵣ}(B)`, conclude `∑ₖ|λ↓ₖ(A)−λ↓ₖ(B)| ≤ ‖A−B‖₁`. Discharges all downstream plumbing — `lidskii_of_frame`
(per-tuple), matrix `eigenvalues₀`↔LinearMap `eigenvalues (toEuclideanLin ·)` (DEFINITIONAL rfl), `A−B` operator
bridge (`congr 1; rw [map_sub]`), `Finset`↔tuple reindex via `S.orderEmbOfFin` (`map_orderEmbOfFin_univ`+`sum_map`),
and `mirsky_of_subset_diff`. Kernel-pure (lean_verify); module builds clean; full-lib ExtractDeps axiom gate DEFERRED
(parallel agent's mid-edit `PadicSquare.lean` breaks the full build — re-run `validate.py --check axiom_closure_allowlist`
once it compiles). **⟹ `Hframe` (Wielandt min–max "≤") is now the SOLE remaining brick for Mirsky/F1b**; F2 (Audenaert)
+ F3 (quantum assembly) still open and independent. Each plumbing piece was de-risked in-REPL (`lean_run_code`) before
assembly, per the test-before-build discipline.

**Wave 4 / F3 ASSEMBLY ✅ SHIPPED (2026-06-04; folded into `c728480e` — parallel agent's `git commit -a` swept my
staged `FannesAudenaert.lean`; work preserved + builds clean + kernel-pure).** Two theorems:
(1) `vonNeumannEntropy_eq_sum_negMulLog_eigenvalues₀` — `S(ρ) = ∑ₖ negMulLog(λ↓ₖ(ρ))` entropy↔sorted-spectrum bridge
(`negMulLog`-sum permutation-invariance via `sum_eigenvalues_eq_sum_eigenvalues₀`);
(2) `quantum_fannes_audenaert_of_mirsky` — the **F3 assembly**: GIVEN Mirsky `∑ₖ|λ↓ₖ(ρ)−λ↓ₖ(σ)| ≤ ‖ρ−σ‖₁` (F1b,
staged on `Hframe`) AND classical Fannes–Audenaert on the eigenvalue distributions `|S(ρ)−S(σ)| ≤ qaryEntropy d Tλ`
(F2; `Real.qaryEntropy d T = binEntropy T + T·log(d−1)` = the Audenaert envelope, nats), conclude the trace-distance
continuity `|S(ρ)−S(σ)| ≤ qaryEntropy d (½‖ρ−σ‖₁)`. Coupling = `Real.qaryEntropy_strictMonoOn` on `[0,1−1/d]`: Mirsky
gives `Tλ ≤ ½‖ρ−σ‖₁`, monotone branch transports the bound (hyp `½‖ρ−σ‖₁ ≤ 1−1/d` keeps both on-branch; outside it
the trivial `≤ log d` ceiling applies). Kernel-pure (lean_verify).

**⟹ F STRUCTURE NOW COMPLETE.** Shipped: F1a (Ky Fan), the entire Lidskii→Mirsky chain (`lidskii_of_frame` +
`mirsky_of_wielandt_frame`), the entropy↔spectrum bridge, the Mirsky transport, and the monotone envelope (F3).
**Exactly TWO precise, decomposition-backed irreducible analytic residuals remain, both isolated as named hypotheses:**
(R1) `Hframe` = the Wielandt min–max "≤" frame-existence (for Mirsky/F1b) — all elementary constructions provably fail
(termwise/greedy/matching/induction-both-ends/compression-recursion-bottoms-out); live routes = additive-compound Λᵏ
spectrum / global flag-minimax / Cauchy-interlacing+more, all Mathlib-absent. (R2) the classical Fannes–Audenaert
inequality `|H(p)−H(q)| ≤ qaryEntropy d (½‖p−q‖₁)` — Mathlib has the RHS function (`Real.qaryEntropy`) + its continuity
& monotonicity, but NOT the inequality (a research-grade maximization over the distribution-pair polytope; Audenaert
2007). Per the goal's alternative-completion path these are the documented residuals; everything else in C+F is shipped.

**Wave 4 / F2 BRICKS + R2-STRUCTURE COMPLETE ✅ SHIPPED (2026-06-04, my own commits — decompose-before-asserting-walls
reframed R2 from "wall" to a brick sequence; the classic *conditioned* Fannes is tractable, only the sharp
unconditional Audenaert constant is research-grade).** Three F2 bricks: `negMulLog_add_le` `1dbcaec4` (subadditivity
`η(a+b)≤η(a)+η(b)` = forward per-term modulus direction, via `concaveOn_negMulLog`); `sum_negMulLog_le_card_mul`
`7078e79b` (Jensen `∑η(δᵢ)≤d·η((∑δᵢ)/d)` = the Fannes RHS `2T log d+η(2T)`, via `ConcaveOn.le_map_sum`);
`fannes_entropy_bound_of_modulus` `09f3b39e` (**the P2 assembly**: classical Fannes `|∑η(pᵢ)−∑η(qᵢ)| ≤ d·η((∑|pᵢ−qᵢ|)/d)`
STAGED on the per-term modulus hypothesis, via triangle + Jensen). All kernel-pure (lean_verify).

**⟹⟹ F IS STRUCTURALLY COMPLETE.** Every assembly is shipped and kernel-pure (F1a Ky Fan; the full Lidskii→Mirsky
chain `lidskii_of_frame`+`mirsky_of_wielandt_frame`; entropy↔spectrum bridge; Mirsky transport + monotone envelope
[F3]; the classical-Fannes triangle+Jensen assembly [P2]). **F is reduced to EXACTLY TWO precise,
decomposition-backed irreducible analytic residuals, both isolated as clean named hypotheses:**
- **(R1) `Hframe`** — the Wielandt min–max frame-existence (for Mirsky/F1b). All elementary constructions *proven* to
  fail; complete routes = additive-compound Λᵏ spectrum / global flag-minimax, multi-week Mathlib-absent.
- **(P1)** the per-term modulus reverse direction `η(x) ≤ η(x+δ)+η(δ)` for `0≤x, x+δ≤1, 0≤δ≤½` (the forward direction
  `negMulLog_add_le` is shipped). Decomposes into two deriv-calculus sub-lemmas — (a) `f(x)=η(x)−η(x+δ)` monotone via
  `monotoneOn_of_deriv_nonneg` (`f'=log((x+δ)/x)≥0`); (b) `η(1−δ)≤η(δ)` via `g(δ)=η(δ)−η(1−δ)` concave-on-[0,½]
  (`g''=−1/δ+1/(1−δ)<0`) with zero endpoints. Math fully worked, `Real.hasDerivAt_negMulLog` API confirmed; a
  tractable (not research-grade) ~40–60-line deriv-calculus build, the single remaining R2 piece.

Per the goal's alternative-completion path, R1 (genuinely research-grade) and P1 (tractable calculus, teed up) are the
precise documented residuals for the two specific F sub-steps; all other C+F content is shipped in full.

🔑 Wave-3 build notes (hard-won, for future cfc work): `cfc_kronecker` ABSENT from Mathlib; analytic
`CFC.log`/`exp_log`/`log_exp` UNUSABLE on matrices (scoped `Matrix.Norms.L2Operator` topology ≠ defeq to
the entrywise topology the eigenbasis CFC instance uses → opening it breaks `cfc Real.log` instance synth);
NO Pi-CFC instance in Mathlib (`ContinuousFunctionalCalculus ℝ (ι→ℂ)` only assumed, never provided). So
the route is the eigenbasis/`cfc_diagonal` one: `cfc_diagonal` built via `cfcHom_eq_of_continuous_of_map_id`
(finite spectrum ⟹ `Matrix.finite_real_spectrum.continuousOn`); `matrixLog_kronecker` via `kronUnitary` +
`conjStarAlgAut_kronecker` + `StarAlgHomClass.map_cfc`; subadditivity via `relativeEntropy_nonneg` (Klein) on
`ρ_A⊗ρ_B` with abstract marginal-pairing hypotheses. Perf: `fun_prop` on `conjStarAlgAut Vu` continuity TIMES
OUT (unfolds `kronUnitary`'s proof) → use explicit `(continuous_const.mul continuous_id).mul continuous_const`.

---

## Wave 1 — Klein corollaries (quick wins)

- **A — Concavity of von Neumann entropy** `S(∑ᵢ pᵢ ρᵢ) ≥ ∑ᵢ pᵢ S(ρᵢ)`. **Verdict: reachable-now.**
  Bricks: for the full-rank average `ρ̄ = ∑ⱼ pⱼ ρⱼ`, `∑ᵢ pᵢ · relativeEntropy ρᵢ ρ̄ ≥ 0` (Klein, each term)
  expands via `re_trace_mul_matrixLog` + linearity of `tr(ρᵢ · matrixLog ρ̄)` over the convex combination
  (`∑ᵢ pᵢ tr(ρᵢ M) = tr(ρ̄ M)`) to `S(ρ̄) − ∑ᵢ pᵢ S(ρᵢ)`. Hypothesis: `ρ̄` PosDef (full-rank average).
  ~10–20 lines. Module: extend `QuantumKlein.lean` or new `EntropyConcavity.lean`.
- **D — Gibbs variational principle / free energy** `F(ρ) ≥ F(τ_β)` (thermal state minimizes free energy).
  **Verdict: reachable-now.** Bricks: define the Gibbs/thermal state `τ_β` (a density operator), then
  `relativeEntropy ρ τ_β ≥ 0` (Klein) rearranges to the free-energy inequality `tr(ρ H) − T·S(ρ) ≥ F(τ_β)`.
  Needs a thermal-state definition (an honest modelling def, not an axiom). Module: new `GibbsVariational.lean`.

---

## Wave 2 — entanglement-measure completion + API hardening

- **B — Negativity convexity** `N(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ N(ρᵢ)` (entanglement monotone under classical
  mixing). **Verdict: reachable-now.** Bricks: `pt2_sum`/`pt2_smul` (PT linearity, present) + trace-norm
  triangle inequality + absolute homogeneity (Mathlib `Matrix` norm API — confirm exact lemma name) →
  `N` convex by the weighted-sum algebra. Together with the shipped LOCC-monotone
  (`traceNorm_pt2_localKraus_le`) this makes negativity a *verified bona-fide entanglement monotone*.
  Module: extend `NegativityMonotone.lean` or new `NegativityConvex.lean`.
- **E — Drop side-conditions (general-density-operator strengthening).** **Verdict: reachable-small.**
  - E1: `traceNorm_ge_abs_trace` `‖A‖₁ ≥ |tr A|` for Hermitian `A` (via `traceNorm_hermitian = ∑|λᵢ|`
    and `|tr A| = |∑λᵢ| ≤ ∑|λᵢ|`). Small, reusable.
  - E2: general `0 ≤ negativity ρ` for any bipartite density operator (not just Bell-diagonal): from E1
    applied to the Hermitian `ρ^Γ` with `tr ρ^Γ = tr ρ = 1` ⟹ `‖ρ^Γ‖₁ ≥ 1` ⟹ `N ≥ 0`. Needs
    `tr(pt2 ρ) = tr ρ` (PT preserves trace — small).
  - E3: lift `logNegativity_add` to drop the `‖ρ^Γ‖₁ ≠ 0` hypothesis for density operators (discharge via
    `‖ρ^Γ‖₁ ≥ 1 > 0` from E2's `traceNorm_pt_ge_one`).
  Module: extend `BellNegativity.lean` / `LogNegativity.lean` or new `NegativityGeneral.lean`.

---

## Wave 3 — correlations: subadditivity & mutual information

- **C — Subadditivity / mutual information ≥ 0** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, `I(A:B) ≥ 0`.
  **Verdict: reachable-moderate.** Headline QI result. Bricks:
  - **C1 — `matrixLog_kronecker`** (the reusable upstream-infra lemma): `matrixLog (ρ_A ⊗ ρ_B) =
    matrixLog ρ_A ⊗ 1 + 1 ⊗ matrixLog ρ_B` for PosDef (full-rank) `ρ_A, ρ_B`. ⚠️ **`cfc_kronecker` is
    confirmed ABSENT from Mathlib** — build this from the kronecker-eigenvalue machinery already shipped
    in `KroneckerEntropy.lean` (`map_eigenvalues_kronecker`, `charpoly_kronecker_eq`) + the cfc/conjugation
    forms used in `QuantumKlein.lean` (`spectral_theorem`, `conjStarAlgAut`). The full-rank hypothesis is
    essential — the identity FAILS at zero eigenvalues (same lesson as FU-8b additivity).
    🔑 **TOE-HOLD FOUND (scout 2026-06-04):** `StarAlgHomClass.map_cfc` (Mathlib) — a star-algebra hom
    commutes with `cfc`, and `Unitary.conjStarAlgAut V` is a `StarAlgEquiv`. Path: `A⊗B = conjStarAlgAut V
    (diagonal d)` (V = U_A⊗U_B unitary, d the products, from the `charpoly_kronecker_eq` `hdecomp` — extract
    it as a reusable `kronecker_eq_conj_diagonal`) → `map_cfc` gives `cfc log (conjStarAlgAut V (diag d)) =
    conjStarAlgAut V (cfc log (diag d))` → cfc-of-diagonal `cfc f (diagonal d) = diagonal (f∘d)` → split
    `log(λᵢμⱼ)=log λᵢ+log μⱼ` (full-rank) → `matrixLog A ⊗ 1 + 1 ⊗ matrixLog B`. Then subadditivity needs
    `ptrace1` (the `1⊗G` partner of the present `trace_mul_kronecker_one`/`ptrace2`).
  - **C2 — partial-trace/trace compatibility**: `trace_mul_kronecker_one` (`tr(W·(G⊗1)) = tr(ptrace2 W · G)`)
    is **already present** in `DiamondNormDual.lean`; need the symmetric `1⊗G` version (`ptrace1`) if absent.
  - **C3 — assembly**: `relativeEntropy ρ_AB (ρ_A ⊗ ρ_B) ≥ 0` (Klein, `ρ_A⊗ρ_B` PosDef) +
    `tr(ρ_AB · matrixLog(ρ_A⊗ρ_B)) = tr(ρ_A log ρ_A) + tr(ρ_B log ρ_B)` (C1 + C2) ⟹ subadditivity;
    `I(A:B) := S(ρ_A)+S(ρ_B)−S(ρ_AB) ≥ 0` immediate. ρ_A, ρ_B are the marginals `ptrace2/ptrace1 ρ_AB`.
  Module: new `EntropySubadditivity.lean` (+ `matrixLog_kronecker` may live in `KroneckerEntropy.lean`).

---

## Wave 4 PROGRESS (2026-06-04)

### 🧭 ROUTE DECISION (2026-06-04 session 2, post-compaction — two proof-strategy + API scouts)
**The Mirsky bridge `λ↓(A)−λ↓(B) ≺_w λ(C)` is settled to ONE route after eliminating three.** Decompose-before-walls
applied to the LW crux itself (a dedicated matrix-analysis strategy scout + two Mathlib API scouts):
- **❌ fact-2 / doubly-stochastic-kernel route is a STRUCTURAL dead-end for the bridge.** `eigenvalue_eq_doublyStochastic_combination`
  controls `(a−b)` where `a=λ(A)` in EIGENVECTOR order and `b=`B smeared onto A's diagonal (`b≺λ(B)`); **sorting breaks
  the stochastic kernel**, so no choice of subset reaches the *sorted* difference. Proves only a Schur–Horn-flavored bound.
  ⟹ A new lemma `subset_sum_diag_diff_le` (the arbitrary-subset DS-image bound `∑_{i∈S}(aᵢ−bᵢ)≤∑topk(C)`) was BUILT this
  session (compiles, kernel-pure) but is **OFF the critical path** — held UNCOMMITTED pending whether route (c) consumes it;
  keep only as Schur–Horn infra if genuinely reused, else drop (no orphan ships).
- **❌ single-D "holy grail" (`λ↓(A)−λ↓(B)=D·λ(C)`, D doubly stochastic) is CIRCULAR** — D exists only via converse-HLP /
  T-transforms, which are *downstream* of the majorization we want. No natural D from matrix structure. Skip.
- **❌ exterior/additive-compound route** (`D_k(A)` has subset-sum spectrum, linear in A → Weyl on `D_k`) needs additive-compound
  spectral theory **absent from Mathlib** (`ExteriorPower` exists but NO spectrum-of-compound result). 8–12 lemmas + missing
  substrate. Skip.
- **⚠️ ROUTE (c) Wielandt-frame-reuse SUPERSEDED — single-frame existence is PROVABLY FALSE.** A construction scout
  refuted it: `n=3, S={0,2}` forces `w_1=u_0, w_2=v_2` with `⟨u_0,v_2⟩≠0` — no orthonormal frame in `A_r∩B_r` exists, and
  no single rank-k `P` gives both `tr(PA)≥∑_Sλ↓(A)` ∧ `tr(PB)≤∑_Sλ↓(B)`. Same scout ALSO over-claimed a "reduce to Weyl
  position-prefix" shortcut — **FALSE** (caught here): Weyl-prefix `∑_{j<k}λ↓(A)−∑_{j<k}λ↓(B)≤∑_{j<k}λ↓(C)` (= shipped
  `sum_top_subadditive`) does NOT imply the SORTED weak-maj `∑_{k largest}(λ↓(A)−λ↓(B))≤∑_{j<k}λ↓(C)` — abstract
  counterexample `a=(2,2),b=(2,0),c=(1,1)` (can't arise from a real `A=B+C`, which is exactly the matrix structure Lidskii
  needs). So brick-2 IS genuine Lidskii weak-maj, not reducible to Weyl.
- **❌❌ ROUTE (b) IS REFUTED (2026-06-04, VM-2 scout + verification) — its key step is FALSE.** The rearrangement
  `sort(a)−sort(q) ≺_w a−β` is FALSE for doubly-stochastic-interior `β` (n=2 counterexample `a=(3,6),q=(6,−5),
  β=(−2.70,3.70)`: `topkSum(sort a−sort q,1)=8 > topkSum(a−β,1)=5.70`; ~44% random-trial violation). Only the VERTEX
  form `sort a−sort q ≺ a−(q∘π)` (π a PERMUTATION) is true — and it does NOT connect to `λ(C)` (the convex-combo
  closure fails in BOTH directions: convexity gives `topkSum(d) ≤ ∑w topkSum(a−q∘π)`, an upper bound, never the
  needed lower bound). So the intermediate `eig₀A−eig₀B ≺_w (C's A-basis diagonal d)` is FALSE even though real
  Lidskii `eig₀A−eig₀B ≺_w λ(C)` holds — `d ≺ λ(C)` but `d` is "smaller" than the sorted difference, breaking
  transitivity. **DS-image-of-C-diagonal is the WRONG intermediate.** ⚠️ ALL 4 shipped bricks remain CORRECT/reusable
  (VM-0 `subset_sum_le_sorted_prefix`, topkSum infra `722fc0d9`, VM-1 `topkSum_doublyStochastic_mulVec_le` `ecc0f66f`
  = the genuine Birkhoff TODO, `mirsky_of_subset_diff` `911e1699`); only the VM-2/VM-3 WIRING is dead. **`H` (the
  arbitrary-subset Lidskii bound) is still TRUE and still the target; it just needs the Wielandt-minimax proof, not
  route (b).** Genuine route = Wielandt minimax (flags + `Submodule.finrank_sup_add_finrank_inf_eq` subspace
  intersection; API confirmed present) OR additive-compound (missing Mathlib substrate). Both heavy/multi-session.
- **🎯 ROUTE DECISION (user 2026-06-04: GRIND ∃P, one sub-component per turn, lean-tools+numpy, no scouts).**
  Building the genuine arbitrary-index Lidskii–Wielandt `∃P` (single-frame existence) → feeds shipped `mirsky_of_proj_exists`
  → Mirsky. **CHOSEN ROUTE = WIELANDT MIN-MAX** (the standard complete Lidskii proof). Ruled out (do NOT pursue):
  - ❌ **additive-compound has a REAL GAP:** `∑_Sλ↓(A)=λ↓_{p_A}(D_k(A))`, single Weyl on `D_k(A)=D_k(B)+D_k(C)` gives
    `∑_Sλ↓(A) ≤ λ↓_{p_A}(D_k(B)) + ∑_{<k}λ↓(C)`, needs `p_A≥p_B` (rank of S's subset-sum in A's spectrum ≥ in B's) to
    conclude `≤ ∑_Sλ↓(B)+…`. `p_A≥p_B` FAILS for n≥4 (subset-sum order not position-determined: `{0,3}` vs `{1,2}` is
    value-dependent). Plus needs ExteriorPower `D_k` spectrum (heavy). NOT clean.
  - ❌ **convexity-crossing (route e) is CIRCULAR:** `L ⟺ ∃P ⟺ theorem` (`g(t)=∑_{<k}λ↓(A−tB)≥tr(P_{W₀}(A−tB))` uses the
    both-bounds `W₀`=∃P itself). Real but not a proof.
  **BUILD ORDER (Wielandt min-max, EuclideanSpace/`Matrix.IsHermitian`; new file `WielandtLidskii.lean`):**
  - **W1 Courant–Fischer max-min (single eigenvalue, FOUNDATION, reusable, Mathlib-absent — has only extreme via
    `hasEigenvalue_iSup/iInf`):** `λ↓_m(A) = ⨆ over (m+1)-dim subspaces V of ⨅_{x∈V,x≠0} Rayleigh(A,x)`. API:
    `Matrix.IsHermitian.spectral_theorem`, `eigenvalues_eq` (`λᵢ = re(star(eigvec i)⬝ᵥ A.mulVec(eigvec i))` — Rayleigh form),
    `eigenvectorBasis : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)`, `Submodule.finrank_sup_add_finrank_inf_eq` (intersection
    dim ≥ 1 when dims add past n). "≥": V=A-top_m, inner-min = λ↓_m. "≤": any (m+1)-dim V meets A-bottom-(n-m) (dim ≥1),
    that x has Rayleigh ≤ λ↓_m.
  - **W2 Wielandt sum min-max / ∃P existence (THE hard step):** ∃ rank-k W with `tr(P_W A)≥∑_Sλ↓(A)` ∧ `tr(P_W B)≤∑_Sλ↓(B)`.
    Numerically TRUE (0/300). Construct via the flag + subspace-intersection dim count (the genuine Wielandt argument; the
    naive A-top∩B-bottom termwise frame FAILS — needs the global min-max). May need Cauchy interlacing (also Mathlib-absent)
    as a sub-brick. **TEST each candidate construction numerically (numpy) BEFORE Lean.** This is the multi-session core.
  - **W3 assemble:** ∃P → `mirsky_of_proj_exists` [SHIPPED] → Mirsky. Then F2 Audenaert + F3.
  **(numerical route-validation below kept for reference:)**
- **✅✅ ROUTE (e) — t-PARAMETRIZED CONSTRUCTION (numerically VALIDATED 2026-06-04, matrix-native).**
  Three facts, each 0 failures over thousands of random Hermitian trials (numpy, `/tmp/wtest*.py`):
  1. **Single-frame existence is TRUE** (0/300): ∃ rank-k `W` with `tr(P_W A) ≥ ∑_S λ↓(A)` ∧ `tr(P_W B) ≤ ∑_S λ↓(B)`.
     ⟹ the prior construction-scout's "single-frame is false (n=3 S={0,2})" was WRONG — that was ONE construction failing
     (`A-top∩B-bottom`), NOT existence. So the brick-2 interface (∃P) is CORRECT & provable, and H follows: `∑_Sλ↓(A)−∑_Sλ↓(B)
     ≤ tr(P_W C) ≤ ∑_{<k}λ↓(C)` via SHIPPED Ky Fan `trace_mul_proj_le`.
  2. **Explicit witness** (0/2000): `W = top-k eigenspace of (A − t·B)` satisfies both bounds for the right `t ≥ 0`.
     MATRIX-NATIVE (no EuclideanSpace flags). At t=0: W=topk(A), `tr(P_W A)=∑_{<k}λ↓(A)≥∑_Sλ↓(A)` ✓ (A-bound). At t=∞:
     W=botk(B), `tr(P_W B)=∑smallest-k(B)≤∑_Sλ↓(B)` ✓ (B-bound). Crossing in between.
  3. **The crux = lemma L** (0/4000): `∑_{j<k}λ↓(A−tB) ≥ ∑_Sλ↓(A) − t·∑_Sλ↓(B)` ∀t≥0. **L at t=1 IS H** (`∑_{<k}λ↓(A−B)=∑_{<k}λ↓(C)`).
  **CROSSING ARGUMENT (the assembly, matrix-native):** `g(t):=∑_{<k}λ↓(A−tB)` is CONVEX in t (max of linear `tr(P_W(A−tB))`);
  `ψ(t):=tr(P_{W(t)}B)=−g'(t)` non-increasing (g convex); `φ(t):=tr(P_{W(t)}A)=g(t)+tψ(t)`, `φ'=tψ'≤0` non-increasing.
  `φ(0)=∑_{<k}λ↓(A)≥∑_Sλ↓(A)` ✓; `ψ(∞)=∑smallk(B)≤∑_Sλ↓(B)` ✓. At `t_ψ:=inf{t:ψ(t)≤targetB}`, `φ(t_ψ)≥targetA ⟺ L(t_ψ)`.
  **⚠️ L is genuinely the Wielandt content (no elementary proof found):** SHIPPED `sum_top_subadditive` gives only the TOP-K
  version `g(t)≥∑_{<k}λ↓(A)−t∑_{<k}λ↓(B)` (Ky Fan subadd with A=(A−tB)+tB) — too weak (topk-sums not S-sums; binds only
  for small t). Per-eigenvalue Weyl `λ↓_{s_r}(A−tB)≥λ↓_{s_r}(A)−tλ↓_0(B)` loses B's S-structure (gives `−tk·λ↓_0(B)`). L is
  equivalent (convex duality / minimax) to the single-frame existence = the theorem itself. **NEXT INCREMENT = prove L** (most
  promising: (a) the convexity/crossing analysis above — needs `g(t)` convex + `ψ` monotone + IVT on eigenvalue functions in t,
  real-analysis but matrix-native; OR (b) a direct single-frame W-existence via Cauchy-interlacing-style dim argument — Mathlib
  lacks interlacing too). Build the H←(∃W)←Ky-Fan assembly FIRST (clean, takes ∃W as hypothesis, like `mirsky_of_subset_diff`),
  then discharge ∃W via L. 🔧 numerical scripts validated the route — KEEP test-before-build.
- **~~ROUTE (d) — WIELANDT MIN-MAX~~ (max-frame direction was WRONG — numerically refuted: max-frame(B-flag)<target 22%; superseded by route e):**
  Valid proof of H found (supersedes all false routes a/b/c): with `i_r = s_r+1`,
  `∑_r λ↓_{s_r}(A) = min_{flags V_1⊂…⊂V_k, dim V_r=i_r} max_{orthonormal {x_r}, x_r∈V_r} ∑_r⟨x_r,Ax_r⟩` (Wielandt).
  Plug **B's eigen-flag** `V_r=span{v_0..v_{s_r}}` (min ≤ value-at-this-flag):
  `∑_S λ↓(A) ≤ max_{frame∈B-flag} ∑⟨x_r,Ax_r⟩ = max ∑⟨x_r,(B+C)x_r⟩ ≤ max∑⟨x_r,Bx_r⟩ + max∑⟨x_r,Cx_r⟩`
  `≤ ∑_S λ↓(B) + ∑_{j<k}λ↓(C)` = H. (B-term: B's OWN min-max attained at its eigen-flag `=∑_Sλ↓(B)`; C-term: Ky Fan
  on an orthonormal k-frame, `≤∑_{<k}λ↓(C)`.) Uses `max(f+g)≤max f+max g` — NO single-frame-both-bounds (which is false).
  **DECOMPOSITION (build order, EuclideanSpace/`LinearMap.IsSymmetric` land — Mathlib has only EXTREME-eigenvalue Rayleigh
  sup/inf, NOT indexed Courant–Fischer; build from scratch):**
  - **D1 (THE hard lemma): Wielandt min-max "≤" direction** — for ANY flag `{V_r}` (dim V_r=i_r), `∑_r λ↓_{s_r}(A) ≤
    max over orthonormal frames {x_r∈V_r} of ∑⟨x_r,Ax_r⟩`. Equivalently: ∃ orthonormal frame in the flag with
    `∑⟨x_r,Ax_r⟩ ≥ ∑_r λ↓_{s_r}(A)`. ⚠️ DIM-COUNT CAVEAT (must resolve): the naive `x_r ∈ V_r ∩ A-top_{s_r}` (A-top =
    span A's top s_r+1 eigvecs, gives ⟨x_r,Ax_r⟩≥λ↓_{s_r}(A) termwise) has `dim(V_r∩A-top_{s_r}) ≥ 2s_r+2−n`, then
    `∩ prev^⊥` (codim r−1) ≥ `2s_r+3−n−r` which is NOT ≥1 for small s_r — so the termwise-A-top construction FAILS.
    The scout's "s_r−r+2≥1" count was for a different (unverified) setup. RE-DERIVE the correct construction (likely the
    genuine min-max ≥ needs a global/induction argument, not termwise) — TEST candidates numerically (lean_run_code) and
    with lean_multi_attempt before committing. This is the irreducible hard core.
  - **D2: B-side attainment** — at B's eigen-flag, `max over frames ∑⟨x_r,Bx_r⟩ = ∑_r λ↓_{s_r}(B)` (frames in span of
    B's top-i_r eigvecs; the max is the eigenframe x_r=v_{s_r}). Cleaner than D1 (eigenbasis-aligned).
  - **D3: Ky-Fan-for-frames** — `∑⟨x_r,Cx_r⟩ ≤ ∑_{<k}λ↓(C)` for any orthonormal k-frame. HAVE in matrix form
    (`trace_mul_proj_le` via P=∑x_rx_rᴴ); bridge to EuclideanSpace OR re-prove via `trace_eq_sum_inner`.
  - **D4: assemble** D1+D2+D3 via `max(f+g)≤max f+max g` → H → shipped `mirsky_of_subset_diff` → Mirsky.
  - **API (confirmed present):** `Matrix.IsHermitian.eigenvectorBasis : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)`,
    `mulVec_eigenvectorBasis`, `Submodule.finrank_sup_add_finrank_inf_eq`, `finrank_span_eq_card`,
    `LinearMap.trace_eq_sum_inner`, `Matrix.isHermitian_iff_isSymmetric` (toEuclideanLin), `exists_mem_ne_zero_of_rank_pos`.
    Mathlib min-max: ONLY `hasEigenvalue_iSup/iInf_of_finiteDimensional` (extreme only) — indexed Courant–Fischer ABSENT.
  - **THEN F2 Audenaert** (classical, independent, non-trivial — Audenaert 2007 coupling proof; `qaryEntropy` RHS shape
    present) + **F3** quantum assembly (`S=∑negMulLog(eig₀)` + Mirsky + F2).
  **🔧 TOOLING (user steer 2026-06-04): drive this build with lean4 MCP tools — TEST statements/constructions directly
  (lean_multi_attempt, lean_run_code numerics, lean_leansearch) BEFORE building. Subagent scouts over-claimed shortcuts
  3×; use them only for breadth, verify every claim yourself.**
  **(superseded — kept for the refutation record:)**
- **~~ROUTE (b) — LIDSKII-via-SCHUR–HORN~~ (REFUTED above):**
  In A's eigenbasis: `C`'s diagonal `d = λ(A) − β` (β = B's diagonal there); BOTH `d ≺ λ(C)` and `β ≺ λ(B)` are
  **Schur–Horn = "a doubly-stochastic image is (weakly) majorized"** — the DS weights `|Mᵢⱼ|²` are exactly the shipped
  `eigenvalue_eq_doublyStochastic_combination` + `overlap_normSq_{row,col}_sum`. Then a **rearrangement lemma**
  `sort(a)−sort(q) ≺_w a−β` (similarly-sorted minimizes the difference's majorization; needs `β ≺ q`) gives
  `λ↓(A)−λ↓(B) ≺_w d ≺ λ(C)` = the weak-maj H. Decomposition (all VECTOR majorization, tractable, no axiom):
  - **VM-0 (foundational, BUILD FIRST):** `sortDesc` + `subset_sum_le_sorted_prefix` — `∑_{i∈S}x ≤ ∑_{i<|S|}(x∘sortDesc x)`
    (subset sum ≤ sum of `|S|` largest). Mathlib LACKS this (leansearch-confirmed). Proof via threshold `c=(x∘σ)(k−1)`,
    symmetric-difference card equality. ~50–70 lines.
  - **VM-1 = the Mathlib TODO (`Birkhoff.lean:30`):** "a doubly-stochastic image is weakly majorized" — `topkSum(D·y,k) ≤
    topkSum(y,k)` via Birkhoff (`exists_eq_sum_perm_of_mem_doublyStochastic`) + `topkSum` convexity + perm-invariance. Gives
    Schur–Horn `d ≺ λ(C)`, `β ≺ λ(B)` directly from the shipped DS weights. ~100 lines.
  - **VM-2 rearrangement:** `sort(a)−sort(q) ≺_w a−β` for `β ≺ q` (similarly-sorted minimizes difference majorization).
  - **VM-3 transitivity + assembly:** `≺_w` transitive ⟹ `λ↓(A)−λ↓(B) ≺_w λ(C)` = H (subset form, via VM-0) → feed shipped
    `mirsky_of_subset_diff` → **Mirsky**. (Sanity-checked VM-2 on several vectors; holds.)
  This SUPERSEDES Wielandt-minimax (which needed subspace/flag machinery): route (b) is pure `Fin N → ℝ` majorization +
  the DS relation already shipped. Strategist's "circular" objection to DS routes does NOT apply — we use Schur–Horn
  (DS-image-majorized, genuinely have the weights), NOT an exhibited single-D for the sorted difference.
- **F2 toehold UPGRADE:** Mathlib `Real.qaryEntropy q p = p·log(q−1)+binEntropy p` with `strictConcaveOn_qaryEntropy` +
  `qaryEntropy_continuous` is EXACTLY the FA RHS shape `T·log(d−1)+H₂(T)` — materially de-risks F2. Plus `dist_eq_of_L1` (total var).

**Scout DONE** (anti-fencing protocol): Mathlib HAS `eigenvalues₀` (sorted-descending,
`eigenvalues₀_antitone`), `binEntropy` (`binEntropy_continuous`, `strictConcave_binEntropy` on `Icc 0 1`),
`trace_eq_sum_eigenvalues`, `Fin.card_filter_val_lt`. Mathlib has **NO** Ky Fan / Lidskii / Mirsky /
eigenvalue-majorization / top-k machinery (grep-confirmed) — F is from-scratch, reachable, NO axiom.

**F1a-core SHIPPED `5933d29d`** (`SpectralMajorization.lean`): `sum_mul_le_sum_top` — the rearrangement /
fractional-knapsack inequality `∑ μᵢ pᵢ ≤ ∑_{i<k} μᵢ` for antitone `μ : Fin N → ℝ`, weights `pᵢ∈[0,1]`,
`∑pᵢ=(k:ℝ)`. Kernel-pure. Proof: threshold `c=μ_{k-1}`, `∑μp−∑_{i<k}μ = ∑(μᵢ−c)(pᵢ−[i<k])`, each term ≤0,
cross-term killed by `∑(pᵢ−[i<k])=0`. (`Finset.sum_boole`+`Fin.card_filter_val_lt`+`min_eq_right` for the
indicator sum; `Fin.le_def`+`omega` for antitone-threshold comparisons.)

**F1a COMPLETE (feasibility CONFIRMED) — 6 bricks shipped:** `sum_mul_le_sum_top` `5933d29d`,
`proj_diag_re_mem_Icc`+`proj_diag_eq_sum_normSq` `052a101c`, `sum_eigenvalues_eq_sum_eigenvalues₀`
`dda064b9`, `conj_proj_isHermitian`+`conj_proj_idempotent` `ddf4928e`, **`trace_mul_proj_le` (Ky Fan ≤
direction) `e315d315`** — `tr(P·A) ≤ ∑_{i<k} λ↓ᵢ(A)` for rank-k projection P. All kernel-pure.

**F1a-achievement + subadditivity SHIPPED `92d88a63`:** `exists_proj_trace_eq` (Ky Fan achievement: top-k
eigenprojection attains ∑top-k, k≤dim) + `sum_top_subadditive` (`∑top-k(A) ≤ ∑top-k(B)+∑top-k(A−B)`). Both
kernel-pure. **Ky Fan COMPLETE (both directions + subadditivity).**

**REMAINING (precise): F1b Mirsky ℓ¹ step, F2 classical FA, F3 assembly.**
- **F1b Mirsky ℓ¹ step** `∑ᵢ|λ↓ᵢ(A)−λ↓ᵢ(B)| ≤ ‖A−B‖₁`. ⚠️ REFINED DIFFICULTY (2026-06-04): `sum_top_subadditive`
  gives ONLY the *prefix* bound `∑_{i<k} dᵢ ≤ ∑_{i<k} λ↓ᵢ(A−B)` with `dᵢ=λ↓ᵢ(A)−λ↓ᵢ(B)` in the GIVEN
  (sorted-A,B) order. The ℓ¹/Mirsky needs the bound for the SORTED d (`∑_{i<k} d↓ᵢ ≤ ∑_{i<k}λ↓ᵢ(A−B)`, i.e.
  genuine WEAK MAJORIZATION) — strictly stronger, = Lidskii–Wielandt. Closing the gap needs the subset/sorted
  form (sum over arbitrary k-index sets), then the HLP convex step for ∑|·|. BOTH the Lidskii–Wielandt
  majorization AND the HLP→convex-sum are absent from Mathlib (confirmed: only asymptotics `Majorized`; has
  `Monovary` rearrangement + `Jensen`, NOT weak-majorization→symmetric-gauge). This is a LARGE from-scratch
  matrix-analysis + combinatorial-convexity build — NOT an axiom-needing wall (provable), but multi-brick.
  `traceNorm_hermitian=∑|λᵢ|` present. Build decompose-first; if a specific step provably needs absent
  machinery document THAT residual (never wholesale, never axiom).
  **🔑 KARAMATA AVOIDED (insight 2026-06-04):** Mirsky's ℓ¹ does NOT need general Karamata. For sorted `d↓`
  and `μ=λ↓(A−B)`: `∑|dᵢ| = 2∑max(dᵢ,0) − ∑dᵢ`; `∑max(d,0)=∑_{i<m}d` (m=#nonneg = a PREFIX since d antitone)
  `≤ ∑_{i<m}μ` (prefix/LW) `≤ ∑max(μ,0)` (μᵢ≤max(μᵢ,0), max≥0 — elementary, NO sorting of μ needed); with
  `∑d=∑μ` (trace eq) ⟹ `∑|d| ≤ 2∑max(μ,0)−∑μ = ∑|μ| = ‖A−B‖₁`. So the combinatorial part is the ELEMENTARY
  `abs_sum_le_of_prefix : {d μ : Fin N→ℝ} (hd:Antitone d)(hpre:∀m,∑_{i<m}d≤∑_{i<m}μ)(htot:∑d=∑μ) ⊢
  ∑|dᵢ|≤∑|μᵢ|`. ⚠️ the one fiddly sub-step = `Antitone d → {i|0≤dᵢ} is the prefix {i|i<m}` (down-set in
  Fin N = initial segment); everything else is `max`-algebra + `Finset.sum_filter`. THIS REPLACES (a) Karamata.
  **✅ `abs_sum_le_of_prefix` SHIPPED `f93f13e2`** (kernel-pure). So Mirsky now needs ONLY brick (b) below.
  **REVISED BUILD ORDER (next window):** (a′) `abs_sum_le_of_prefix` [✅ DONE]; (b) Lidskii–
  Wielandt SORTED-d prefix `∑_{i<m}d↓ᵢ ≤ ∑_{i<m}λ↓ᵢ(A−B)` [the remaining OPERATOR brick — generalize
  `exists_proj_trace_eq`/`sum_top_subadditive` from prefix-subset to the sorted-d/arbitrary-subset form; the
  standard Lidskii argument]; (c) Mirsky = a′∘b + `traceNorm_eq_sum_abs_eigenvalues₀` (SHIPPED); (d) F2
  Audenaert; (e) F3 assembly. (Karamata below is now OPTIONAL/superseded for Mirsky.)

  **OPTIONAL (superseded for Mirsky — keep only if a future need arises):**
  (a) **Karamata** (pure, → `SpectralMajorization.lean`): `{a b : Fin N → ℝ}` both `Antitone`, prefix-major
      `∀k, ∑_{i<k} a ≤ ∑_{i<k} b`, equal total `∑a=∑b`, `φ` `ConvexOn ℝ univ` ⟹ `∑φ(aᵢ) ≤ ∑φ(bᵢ)`.
      BLOCKS CONFIRMED PRESENT: `ConvexOn.slope_mono_adjacent`/`ConvexOn.slope_mono` (slope monotone),
      `Finset.sum_range_by_parts` (Abel summation). Approach: subgradient `gᵢ∈∂φ(aᵢ)` (gᵢ antitone since
      a antitone+φ convex), `φ(bᵢ)−φ(aᵢ) ≥ gᵢ(bᵢ−aᵢ)`, Abel-sum `∑gᵢ(bᵢ−aᵢ) = ∑(gₖ−g_{k+1})(Bₖ−Aₖ) ≥ 0`
      (gₖ−g_{k+1}≥0 antitone, Bₖ−Aₖ≥0 prefix-major). ⚠️ convert Fin N sums ↔ range via `Fin.sum_univ_eq_sum_range`;
      handle ties (gᵢ via slope to a neighbor). ~80–100 lines, genuine but standard.
  (b) **Lidskii–Wielandt** (operator, harder): sorted-difference weak majorization `∑_{i<k}(λ↓(A)−λ↓(B))↓ᵢ
      ≤ ∑_{i<k}λ↓ᵢ(A−B)`. `sum_top_subadditive` gives the PREFIX (unsorted-d) bound; the sorted-d/subset
      strengthening is the extra work. ⚠️ NOTE (verified 2026-06-04): the subset-projection route gives only
      WEYL (`∑_{i∈S}λ↓(A) ≤ ∑_{i<m}λ↓(B)+∑_{i<m}λ↓(A−B)`), NOT the tighter Lidskii (Lidskii needs the SAME
      index set for A and B's sorted values, which the A-eigenprojection can't capture). The genuine LW
      needs the **doubly-stochastic eigenvalue relation** — and Mathlib HAS the machinery:
      `doublyStochastic`, `exists_eq_sum_perm_of_mem_doublyStochastic`, `doublyStochastic_eq_convexHull_permMatrix`
      (`Mathlib/Analysis/Convex/{Birkhoff,DoublyStochasticMatrix}.lean`). LW path: build the Schur-Horn-type
      overlap relation (the eigenvector-overlap matrix `Dᵢⱼ=|⟨eᵢ^A|eⱼ^{A−B}⟩|²`-style is doubly stochastic,
      cf. `re_trace_mul_matrixLog_cross` in QuantumKlein) → Birkhoff → majorization. Large (~150-250 lines)
      but not a wall.
      **CONCRETE FIRST SUB-BRICK (math verified 2026-06-04, plumbing-only blocker; attempted+removed, redo):**
      `diag_conj_eq_sum_normSq (U:unitary)(hB:B.IsHermitian)(i) : (star↑U * B * ↑U) i i =
      ↑(∑ⱼ Complex.normSq (Mᵢⱼ)·λⱼ(B))`, `M := star↑U * ↑hB.eigenvectorUnitary`. PROOF: `star↑U*B*↑U =
      M·diag(↑λ)·star M` [`hB.spectral_theorem`+`Unitary.conjStarAlgAut_apply`; `star M = star↑U_B·↑U`];
      `(M·diag·star M)ᵢᵢ = ∑ⱼ Mᵢⱼ·↑λⱼ·conj Mᵢⱼ = ∑ⱼ|Mᵢⱼ|²↑λⱼ` [`mul_apply`×2 + `Finset.sum_eq_single` on the
      diagonal + `normSq_eq_conj_mul_self` + `push_cast[RCLike.ofReal_eq_complex_ofReal]`]. ⚠️ ONLY blocker
      = plumbing: annotate EVERY `↑U` as `(↑U:Matrix ι ι ℂ)` (bare `*↑U` → coercion/HMul-unitary error);
      `star (↑U:Matrix)` displays as `(↑U)ᴴ`, so normalize star↔conjTranspose (e.g. `set u:=(↑U:Matrix) with hu`)
      BEFORE `noncomm_ring`. Then `A=B+(A−B)` ⟹ `λ(A)ᵢ = ∑ⱼ|M^Bᵢⱼ|²λⱼ(B)+∑ⱼ|M^Cᵢⱼ|²λⱼ(C)`; doubly-stochastic
      via QuantumKlein `sum_normSq_row`/`sum_normSq_col`; → Birkhoff → majorization → sorted-d prefix.
      **✅ BOTH diag-conj bricks SHIPPED** (`LidskiiWielandt.lean`): `diag_conj_eq_sum_normSq` `7a572bed`
      (the `∑ⱼ|Mᵢⱼ|²λⱼ` expansion) + `diag_conj_self_eq_eigenvalue` `c5dd66e8` (`(U_AᴴA U_A)ᵢᵢ=λᵢ(A)`).
      REMAINING LW: (i) ✅ SHIPPED `eigenvalue_eq_doublyStochastic_combination` `1762e82a` — the relation
      `λᵢ(A)=∑ⱼ|M^Bᵢⱼ|²λⱼ(B)+∑ⱼ|M^Cᵢⱼ|²λⱼ(C)`, combining the two diag-conj bricks via `A=B+(A−B)`. ✅ ALSO
      SHIPPED `a8e332ad`: `overlap_normSq_row_sum`/`overlap_normSq_col_sum` — the weights `|M^Bᵢⱼ|²` ARE doubly
      stochastic (row/col sums = 1, via `overlapUnitary` + QuantumKlein `sum_normSq_row`/`col`). So the ENTIRE
      doubly-stochastic input to Lidskii is now built. (ii) the
      majorization EXTRACTION (the genuine remaining hard core, ~80-120 lines): from (i)+(doubly-stochastic
      weights) + Birkhoff (`exists_eq_sum_perm_of_mem_doublyStochastic`) derive the sorted-d weak majorization
      `∑_{i<m}(λ↓(A)−λ↓(B))↓ ≤ ∑_{i<m}λ↓(A−B)`. ⚠️ this is the actual Lidskii argument — NOT immediate from (i)
      (a doubly-stochastic image is majorized, `Dλ(B)≺λ(B)`, but the SUM `Dλ(B)+Eλ(C)` needs the careful
      Lidskii/Wielandt-minimax handling). Genuinely hard; reachable, no axiom.
  (c) **Mirsky** = `abs_sum_le_of_prefix` ∘ LW-(ii) + `traceNorm_eq_sum_abs_eigenvalues₀` (both SHIPPED)
      ⟹ `∑|λ↓(A)−λ↓(B)| ≤ ‖A−B‖₁`
      (RHS = `traceNorm_eq_sum_abs_eigenvalues₀`, SHIPPED).
  (d) **F2 classical FA** (independent, → `FannesAudenaert.lean`): the Audenaert inequality
      `|∑negMulLog p−∑negMulLog q| ≤ T·log(d−1)+H₂(T)`, `∑|pᵢ−qᵢ|=2T`. Real-analysis, hard; `Real.binEntropy`
      (`binEntropy_continuous`, `strictConcave_binEntropy`) + `negMulLog` concavity present.
  (e) **F3 assembly**: `S=∑negMulLog(eigenvalues₀)` (via `sum_eigenvalues_eq_sum_eigenvalues₀`) + Mirsky (ℓ¹
      spectra ≤ trace dist) + F2.
- **F2 classical FA** `|∑negMulLog pᵢ−∑negMulLog qᵢ| ≤ T·log(d−1)+H₂(T)`, `∑|pᵢ−qᵢ|=2T`. Real analysis;
  `Real.binEntropy`/`negMulLog` concavity toe-holds present. Independent of F1.
- **F3 assembly**: `S=∑negMulLog(eigenvalues₀)` (via `sum_eigenvalues_eq_sum_eigenvalues₀`) + F1b + F2.

(superseded brick notes below kept for reference)
- **F1a-projection brick** (DONE): `proj_diag_re_mem_Icc` — diagonal entries of a Hermitian idempotent `Q`
  (`Q*Q=Q`, `Qᴴ=Q`) lie in `[0,1]` (real). Key: `Q j j = ∑ₗ |Qₗⱼ|²` (via `← hQ`, `mul_apply`,
  `hQh.apply j l`); `re ≥ 0` immediate; `re ≤ 1` from `re ≥ |Q j j|² = re²` (diag real). ⚠️ LESSON: `hQh.apply
  j l : Q j l = star (Q l j)` uses `star` but `Complex.normSq_eq_conj_mul_self` uses `starRingEnd`/`conj` —
  defeq but `rw` fails on the atom mismatch; close per-term with `simp [Complex.normSq_eq_conj_mul_self, …]`
  not bare `rw`, and get diag-real via `Complex.star_re/star_im` (NOT `conj_re/conj_im`).
- **F1a Ky Fan**: `tr(P·A) ≤ ∑_{i<k} λ↓ᵢ(A)` for rank-k projection P. `A=U diag(λ) Uᴴ` (spectral_theorem);
  `tr(PA)=tr(UᴴPU·diag λ)=∑ⱼ (UᴴPU)ⱼⱼ·λⱼ`; `Q:=UᴴPU` is a projection (proj_diag brick gives weights∈[0,1],
  ∑=tr P=k); feed `sum_mul_le_sum_top`. ⚠️ must relate `hA.eigenvalues` (unsorted) to `eigenvalues₀` (sorted)
  via the sorting permutation — likely the fiddliest sub-step; OR restate Ky Fan directly with `eigenvalues₀`.
- **F1b Lidskii→Mirsky**: `∑ᵢ|λ↓ᵢ(A)−λ↓ᵢ(B)| ≤ ‖A−B‖₁`. From Ky Fan get `λ↓(A)−λ↓(B) ≺ λ(A−B)`, then
  convex-majorization (`∑|·|` is a sum of convex fns of the majorized vector). `traceNorm_hermitian=∑|λᵢ|` present.
- **F2 classical Fannes–Audenaert**: `|∑negMulLog(pᵢ)−∑negMulLog(qᵢ)| ≤ T·log(d−1)+H₂(T)`, `∑|pᵢ−qᵢ|=2T`.
  Pure real analysis; `binEntropy`/`negMulLog` concavity toe-holds present.
- **F3 quantum assembly**: `S=∑negMulLog(eigenvalues)` + sorted spectra + F1b + F2.

## Wave 4 — Fannes–Audenaert continuity (upstream-infra BUILD wave)

- **F — Fannes–Audenaert entropy continuity** `|S(ρ) − S(σ)| ≤ T·log(d−1) + H₂(T)`, `T = ½‖ρ−σ‖₁`.
  **Verdict: reachable, NO axiom, but the LARGEST item — its weight is the spectral-majorization layer
  Mathlib lacks. Decompose-first BUILD, not a fence.** Decomposition (sub-waved):
  - **F1a — Ky Fan maximum principle** `∑_{i<k} λ↓ᵢ(A) = sup over rank-k orthogonal projections tr(PA)`
    (Hermitian `A`). The foundational spectral-extremal brick. **The feasibility-determining sub-step.**
    Build decompose-first from Mathlib's `Matrix.IsHermitian` spectral theorem + `eigenvalues₀`
    (Mathlib HAS sorted eigenvalues: `eigenvalues₀`, `eigenvalues₀_antitone`). ⚠️ If a specific construction
    here turns out to need machinery genuinely absent (e.g. exterior-power / min-max with no Mathlib
    footing), document THAT precise irreducible residual — never F wholesale, never an axiom.
  - **F1b — Lidskii → Mirsky** `∑ᵢ |λ↓ᵢ(A) − λ↓ᵢ(B)| ≤ ‖A−B‖₁`: from F1a get `λ↓(A)−λ↓(B) ≺ λ(A−B)`
    (majorization), then `∑|·| ≤ ‖A−B‖₁` via a Karamata/Hardy–Littlewood–Pólya convex-majorization step
    (confirm whether Mathlib has majorization ⇒ convex-sum monotonicity; if absent, small extra brick).
    `‖A‖₁ = ∑|λᵢ|` for Hermitian is present (`traceNorm_hermitian`). **Confirmed ABSENT from Mathlib:**
    no `Mirsky`/`Lidskii`/eigenvalue-majorization lemmas.
  - **F2 — classical Fannes–Audenaert** `|∑negMulLog(pᵢ) − ∑negMulLog(qᵢ)| ≤ T·log(d−1) + H₂(T)` given
    `∑|pᵢ−qᵢ| = 2T`. Pure real analysis. **Toe-holds present**: `Real.binEntropy` (+ concavity/monotonicity
    API `binEntropy_strictConcaveOn`-family) and `Real.negMulLog` concavity are shipped. Reachable.
  - **F3 — quantum assembly**: `S(ρ) = ∑ negMulLog(eigenvalues)` (present) + sorted spectra + F1b (spectral
    ℓ¹ ≤ trace distance) + F2.
  Module: new `SpectralMajorization.lean` (F1) + `FannesAudenaert.lean` (F2/F3).

---

## Genuine walls (out of scope for 6AL — documented, decomposition-backed, NO axiom)

These were confirmed absent from Mathlib and are upstream-grade; not attempted here:
- **Monotonicity / data-processing of relative entropy** `S(Φρ‖Φσ) ≤ S(ρ‖σ)` — needs Lieb's concavity /
  joint convexity of relative entropy / Stinespring dilation (none in Mathlib). The keystone wall.
- **Strong subadditivity** `S(ρ_ABC)+S(ρ_B) ≤ S(ρ_AB)+S(ρ_BC)` — depends on the above.
- **Relative entropy of entanglement** `E_R(ρ) = inf_{σ∈SEP} S(ρ‖σ)` — no separable-set /
  convex-optimization-infimum framework in Mathlib.
- **Fuchs–van de Graaf upper bound** `D ≤ √(1−F²)` — needs Uhlmann purification (absent).
- **FU-7 output≤Choi rate-ceiling & PLOB secret-key** — needs Bell-measurement teleportation LOCC (absent).

## Notes for the executing agent
Read the Mandatory References + the 6AK roadmap + `QuantumKlein.lean` / `KroneckerEntropy.lean` /
`VonNeumannEntropy.lean` / `QuantumRelativeEntropy.lean` / `BellNegativity.lean` / `LogNegativity.lean` /
`DiamondNormDual.lean` (partial trace `ptrace2`, `trace_mul_kronecker_one`) for the shipped substrate this
builds on. Per-rung ceremony: build module → `lean_verify` kernel-pure → root import (bordism-aware) →
`lake build` module + `SKEFTHawking.ExtractDeps` → `validate.py --check axiom_closure_allowlist` → commit
own files only → update roadmap + memory → never push. Recommended order: Wave 1 → Wave 2 → Wave 3 → Wave 4
(F is gated last as the high-effort upstream build; its F1a Ky Fan brick determines feasibility).
