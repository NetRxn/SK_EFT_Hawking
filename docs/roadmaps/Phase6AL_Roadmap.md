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
SHIPPED `1887803e` (`NegativityGeneral.lean`). Axiom gate GREEN; all kernel-pure. Waves 3–4 remain.

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
