# Phase 6BB — Density-Functional-Theory Foundations (Molecular Hamiltonian → Hohenberg–Kohn)

**Status: PLANNED (authorized 2026-06-29).** The verified foundations of density-functional theory: self-adjointness of the molecular many-body Coulomb Hamiltonian (Kato–Rellich), the **Hohenberg–Kohn I** density-determines-potential uniqueness theorem, **Hohenberg–Kohn II** variational principle, and the Levy–Lieb constrained-search functional. The program's strongest *public* computational-chemistry flagship (clean whitespace — no formalized DFT foundations in any prover). Distinct phase in the `6B*` chemistry series. PhysLib's Schmüdgen-grade spectral substrate makes this **MODERATE**, not "years-scale."

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** PhysLib `…/Operators/Unbounded.lean` — `UnboundedOperator` (structure), `.adjoint` (`U†`), `.closure`, `.IsClosed`, `adjoint_dense_of_isClosable`, `closure_isClosed`; `…/SpectralTheory/Basic.lean` — `resolvent`, `defectNumber`/`deficiencySubspace`, `IsClosed.defectNumber_eq_zero_iff` (**self-adjointness via deficiency indices**); `…/SpectralTheory/Symmetric.lean` — `numericalRange`/`realNumericalRange`, `im_eq_zero_of_mem_numericalRange`. Mathlib `LinearPMap` (the `H →ₗ.[ℂ] H` type). Mathlib `Analysis.InnerProductSpace.Rayleigh` — `LinearMap.IsSymmetric.hasEigenvalue_iInf/iSup_of_finiteDimensional` (**extremal** eigenvalue = variational, for HK II). PhysLib `StatisticalMechanics/CanonicalEnsemble/TwoState.lean` — `twoState`, `twoState_partitionFunction_apply` (the finite-T Mermin bridge).
- **Absent → build:** Kato–Rellich relative-boundedness for the molecular Coulomb potential (no ready molecular self-adjointness in Mathlib); HK uniqueness/variational; Levy–Lieb. (Mathlib `Rayleigh` gives only the *extremal* eigenvalue — fine for HK II.)
- **New content:** N-body Coulomb potential + Kato–Rellich ⇒ essential self-adjointness on PhysLib's deficiency machinery; HK I; HK II (via `Rayleigh` extremal); Levy–Lieb.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target candidate **D10** (pending roster auth) — record it; do **not** create a `papers/` bundle or edit `_VALID_BUNDLE_TARGETS` without the user's roster sign-off. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)** — DR "ship as axiom" is advisory; use a disclosed tracked-Prop. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** W1 (molecular Coulomb Hamiltonian + Kato–Rellich self-adjointness) is the **gating analysis wave** — hardest; do it first. HK I is a **constructive reductio**, not an axiom.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms (#15)** — HK I is a constructive reductio, not an axiom; no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual publication — quantum-chemistry venues — + flagship scope).

**Bundle target:** **D10** (authorized 2026-06-29; §DFT). Roster-expansion mechanics at first content-lift per `BUNDLE_LIFT_PROCEDURE`. A Stage-1 option (decide at first-lift): split DFT as its own flagship vs. keep it in the shared D10 with transport (6BA) + open-systems (6BC).

---

## Wave 1 — molecular Hamiltonian + self-adjointness
- **Goal:** the N-electron Coulomb Hamiltonian on PhysLib `LinearPMap`; **Kato–Rellich** relative-boundedness of the Coulomb potential w.r.t. the Laplacian ⇒ essential self-adjointness. **Verdict: reachable-moderate** — the hardest wave (Kato's inequality), but on a strong substrate.
- **Why:** without self-adjointness the spectral theory (and every later wave) is ill-posed.
- **Bricks:** PhysLib unbounded spectral theory + symmetric momentum/position; Mathlib `InnerProductSpace.LinearPMap`, Hardy/Kato inequality if present (else build).
- **Done (AC / `/goal` condition):**
  - [ ] `MolecularHamiltonian.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] N-body Coulomb Hamiltonian defined; `molecularHamiltonian_essSelfAdjoint` proven via Kato–Rellich (hypotheses load-bearing, not vacuous)

## Wave 2 — Hohenberg–Kohn I (uniqueness)
- **Goal:** the ground-state density determines the external potential up to an additive constant (reductio via the Rayleigh–Ritz variational inequality + non-degeneracy). **Verdict: reachable.**
- **Why:** the theorem that makes "functional of the density" well-defined — the conceptual core of DFT.
- **Bricks:** W1 self-adjointness; variational (Rayleigh) inequality.
- **Done (AC / `/goal` condition):**
  - [ ] `HohenbergKohnUniqueness.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `hohenberg_kohn_uniqueness` (potential ↦ density injective up to a constant) proven + a falsifier (two potentials → same density ⇒ ⊥)

## Wave 3 — Hohenberg–Kohn II (variational principle)
- **Goal:** the universal functional `F[n]`; `E_v[n] ≥ E₀` with equality iff `n` is the true ground-state density. **Verdict: reachable.**
- **Why:** the variational handle that makes DFT computable.
- **Bricks:** W2; Rayleigh–Ritz.
- **Done (AC / `/goal` condition):**
  - [ ] `HohenbergKohnVariational.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `hohenberg_kohn_variational` (`E_v[n] ≥ E₀`, equality iff true density) proven on the `Rayleigh` extremal substrate

## Wave 4 — Levy–Lieb constrained search
- **Goal:** the constructive `F_LL[n] = inf_{ψ→n} ⟨ψ| T + V_ee |ψ⟩`; agreement with `F[n]` on v-representable densities; optional finite-T **Mermin** bridge via PhysLib `CanonicalEnsemble`. **Verdict: reachable.**
- **Why:** turns HK II into a constructive object; the finite-T bridge connects to statistical-mechanics substrate.
- **Bricks:** W3; PhysLib `CanonicalEnsemble.twoState` + `twoState_partitionFunction_apply` (the project's `thermalExcitedPop` is *derived* from this in 6AQ — reuse that derivation pattern).
- **Done (AC / `/goal` condition):**
  - [ ] `LevyLiebFunctional.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `levyLieb_functional` + `levyLieb_eq_HK_on_vrep` proven; (optional) finite-T Mermin bridge via `CanonicalEnsemble.twoState`

## Sequencing
W1 (self-adjointness) → W2 (HK I) → W3 (HK II) → W4 (Levy–Lieb). Strictly linear; W1 is the gating analysis wave. Independent of 6BA/6BC/6BD.

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D10 §DFT row staged for first-lift; roadmap status updated.
