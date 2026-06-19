import Mathlib
import SKEFTHawking.SingularRelativeUC
import SKEFTHawking.SingularChartBridge

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4e) — the local cohomology `Hⁿ(M|x) ≅ ℤ/2`

The cohomology dual of `SingularChartBridge.manifoldLocalIso` (`Hₙ(M|x) ≅ ℤ/2`): for `M` a `T1`
topological manifold modeled on `ℝᵐ⁺²`, the **local cohomology** `Hᵐ⁺²(M, M∖x) ≅ ℤ/2`. This is the
cohomology-side input to the Poincaré-duality base case (the duality map `D_x` at a point), obtained
from the relative universal coefficients of the previous brick (`SingularRelativeUC`).

**Construction (pure linear algebra over `ℤ/2`).** Let `g := (manifoldLocalIso x).symm 1` be the
generator of `Hₙ(M|x) ≅ ℤ/2`. The map `Φ := relKroneckerH · g : Hⁿ(M|x) → ℤ/2` (pairing against `g`) is
- **injective**: `Φ ω = 0` and `g` spans the 1-dimensional `Hₙ(M|x)` (`β = (manifoldLocalIso x β) • g`)
  force `relKroneckerH ω β = 0` for *every* `β`, so `ω = 0` by the cohomology-side relative UC
  (`relCohomology_eq_zero_of_relKroneckerH`);
- **surjective**: if `Φ` were the zero map then `g` pairs to `0` with every class, so `g = 0` by the
  homology-side relative UC (`relHomology_eq_zero_of_relKroneckerH`) — contradicting `g ≠ 0`; hence
  some `ω₀` has `Φ ω₀ ≠ 0`, i.e. `= 1` in `ℤ/2`, and `y • ω₀ ↦ y` hits every value.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeUC SKEFTHawking.SingularChartBridge

namespace SKEFTHawking.SingularLocalCohomology

/-- **The local cohomology of a topological manifold is `ℤ/2`** at every point: for `M` a `T1`
topological manifold modeled on `ℝᵐ⁺²`, `Hᵐ⁺²(M, M∖x) ≅ ℤ/2`. The cohomology dual of
`SingularChartBridge.manifoldLocalIso`, via the relative universal coefficients
(`SingularRelativeUC`). The cohomology-side generator for the Poincaré-duality base case. -/
noncomputable def manifoldLocalCohomologyIso {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    RelativeCohomology (X := TopCat.of M) {y | y ≠ x} (m + 2) ≃ₗ[ZMod 2] ZMod 2 := by
  set S : Set ↑(TopCat.of M) := {y | y ≠ x} with hS
  set g : RelativeHomology (X := TopCat.of M) S (m + 2) := (manifoldLocalIso x).symm 1 with hg
  refine LinearEquiv.ofBijective
    ((relKroneckerH (X := TopCat.of M) S (N := m + 1)).flip g) ⟨?_, ?_⟩
  · -- injective: `Φ ω = 0 ⟹ ω = 0` (cohomology-side relative UC; `g` spans `Hₙ(M|x)`)
    rw [injective_iff_map_eq_zero]
    intro ω hω
    rw [LinearMap.flip_apply] at hω
    refine relCohomology_eq_zero_of_relKroneckerH (S := S) (N := m + 1) ω (fun β => ?_)
    have hβ : (manifoldLocalIso x β) • g = β := by
      rw [hg, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    rw [← hβ, map_smul, hω, smul_zero]
  · -- surjective: `Φ ≠ 0` (else `g = 0`, homology-side relative UC) ⟹ onto `ℤ/2`
    have hg_ne : g ≠ 0 := by
      rw [hg]
      intro h
      exact one_ne_zero ((LinearEquiv.map_eq_zero_iff _).1 h)
    have hΦne : ∃ ω, (relKroneckerH (X := TopCat.of M) S (N := m + 1)).flip g ω ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      refine hg_ne (relHomology_eq_zero_of_relKroneckerH (S := S) (N := m + 1) g (fun ω => ?_))
      have := hall ω
      rwa [LinearMap.flip_apply] at this
    obtain ⟨ω₀, hω₀⟩ := hΦne
    have hz2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    have hΦ1 : (relKroneckerH (X := TopCat.of M) S (N := m + 1)).flip g ω₀ = 1 := hz2 _ hω₀
    intro y
    exact ⟨y • ω₀, by rw [map_smul, smul_eq_mul, hΦ1, mul_one]⟩

/-- **`manifoldLocalCohomologyIso` evaluates by the Kronecker pairing against the local generator**:
`manifoldLocalCohomologyIso x ω = ⟨ω, (manifoldLocalIso x).symm 1⟩`. The defining `LinearEquiv.ofBijective`
+ `LinearMap.flip` β-reduction, exposed as a rewrite rule so downstream modules avoid re-unfolding the
whole definition (which triggers the manifold-context `RelativeHomology` heartbeat wall). -/
@[simp] theorem manifoldLocalCohomologyIso_apply {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M)
    (ω : RelativeCohomology (X := TopCat.of M) {y | y ≠ x} (m + 2)) :
    manifoldLocalCohomologyIso x ω
      = relKroneckerH (X := TopCat.of M) {y | y ≠ x} ω ((manifoldLocalIso x).symm 1) :=
  rfl

end SKEFTHawking.SingularLocalCohomology
