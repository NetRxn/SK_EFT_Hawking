# Phase 6BB — Density-Functional-Theory Foundations (Molecular Hamiltonian → Hohenberg–Kohn)

**Status: PLANNED (authorized 2026-06-29).** The verified foundations of density-functional theory: self-adjointness of the molecular many-body Coulomb Hamiltonian (Kato–Rellich), the **Hohenberg–Kohn I** density-determines-potential uniqueness theorem, **Hohenberg–Kohn II** variational principle, and the Levy–Lieb constrained-search functional. The program's strongest *public* computational-chemistry flagship (clean whitespace — no formalized DFT foundations in any prover). Distinct phase in the `6B*` chemistry series. PhysLib's Schmüdgen-grade spectral substrate makes this **MODERATE**, not "years-scale."

> **⚠️ CHECK PhysLib FIRST.** PhysLib `QuantumMechanics/DDimensions/Operators/SpectralTheory/*` + `Unbounded.lean` ship spectrum decomposition, resolvent identities, `U†† = closure`, momentum/position **proven symmetric**, HO completeness via Plancherel — the self-adjointness foundation largely exists. New work = the N-body Coulomb potential + HK uniqueness/variational. Verify by search before re-deriving.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms (#15)** — HK I is a constructive reductio, not an axiom; no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual publication — quantum-chemistry venues — + flagship scope).

**Bundle target:** **D10** (authorized 2026-06-29; §DFT). Roster-expansion mechanics at first content-lift per `BUNDLE_LIFT_PROCEDURE`. A Stage-1 option (decide at first-lift): split DFT as its own flagship vs. keep it in the shared D10 with transport (6BA) + open-systems (6BC).

---

## Wave 1 — molecular Hamiltonian + self-adjointness
- **Goal:** the N-electron Coulomb Hamiltonian on PhysLib `LinearPMap`; **Kato–Rellich** relative-boundedness of the Coulomb potential w.r.t. the Laplacian ⇒ essential self-adjointness. **Verdict: reachable-moderate** — the hardest wave (Kato's inequality), but on a strong substrate.
- **Why:** without self-adjointness the spectral theory (and every later wave) is ill-posed.
- **Bricks:** PhysLib unbounded spectral theory + symmetric momentum/position; Mathlib `InnerProductSpace.LinearPMap`, Hardy/Kato inequality if present (else build).
- **Gate:** `molecularHamiltonian_essSelfAdjoint` kernel-pure.

## Wave 2 — Hohenberg–Kohn I (uniqueness)
- **Goal:** the ground-state density determines the external potential up to an additive constant (reductio via the Rayleigh–Ritz variational inequality + non-degeneracy). **Verdict: reachable.**
- **Why:** the theorem that makes "functional of the density" well-defined — the conceptual core of DFT.
- **Bricks:** W1 self-adjointness; variational (Rayleigh) inequality.
- **Gate:** `hohenberg_kohn_uniqueness` (potential ↦ density injective up to constants), kernel-pure + falsifier.

## Wave 3 — Hohenberg–Kohn II (variational principle)
- **Goal:** the universal functional `F[n]`; `E_v[n] ≥ E₀` with equality iff `n` is the true ground-state density. **Verdict: reachable.**
- **Why:** the variational handle that makes DFT computable.
- **Bricks:** W2; Rayleigh–Ritz.
- **Gate:** `hohenberg_kohn_variational` kernel-pure.

## Wave 4 — Levy–Lieb constrained search
- **Goal:** the constructive `F_LL[n] = inf_{ψ→n} ⟨ψ| T + V_ee |ψ⟩`; agreement with `F[n]` on v-representable densities; optional finite-T **Mermin** bridge via PhysLib `CanonicalEnsemble`. **Verdict: reachable.**
- **Why:** turns HK II into a constructive object; the finite-T bridge connects to statistical-mechanics substrate.
- **Bricks:** W3; PhysLib `CanonicalEnsemble`/`thermalExcitedPop`.
- **Gate:** `levyLieb_functional` + `levyLieb_eq_HK_on_vrep`, kernel-pure.

## Sequencing
W1 (self-adjointness) → W2 (HK I) → W3 (HK II) → W4 (Levy–Lieb). Strictly linear; W1 is the gating analysis wave. Independent of 6BA/6BC/6BD.

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D10 §DFT row staged for first-lift; roadmap status updated.
