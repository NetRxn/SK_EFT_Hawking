import Mathlib
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularPDWindow

/-!
# Phase 5q.G (G1 (1,2)-window extension, X5 core) — the absolute UC-dual iso and the
Erdős–Kaplansky finiteness forcing

* `kroneckerH_surjective_field` — the ABSOLUTE mirror of
  `SingularRelativeUCSurj.relKroneckerH_surjective_field`: over `ℤ/2` every functional on
  `Hₙ₊₁(Y)` is a Kronecker pairing.
* `ucDualEquiv` — `Hⁿ⁺¹(Y) ≃ₗ (Hₙ₊₁(Y))*` (injectivity = `cohomology_eq_zero_of_kroneckerH`).
* `finiteDimensional_of_linearEquiv_dual` — self-duality forces finite dimension
  (Erdős–Kaplansky, `lift_rank_lt_rank_dual`).
* `fundamentalDuality_bijective_of_openDuality_univ_bijective` — the BIJECTIVE upgrade of the
  W-d1 endpoint bridge (the same `⊤`-collapse square transfers surjectivity).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularUniversalCoeff SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularOpenDuality
open SKEFTHawking.SingularPDWindow

namespace SKEFTHawking.SingularUCFinite

/-- **Absolute universal coefficients, surjectivity** (mirror of
`relKroneckerH_surjective_field`): every functional on `Hₙ₊₁(Y; ℤ/2)` is `kroneckerH` of a
cohomology class. -/
theorem kroneckerH_surjective_field {Y : TopCat} {N : ℕ} :
    Function.Surjective (kroneckerH (X := Y) (N + 1)) := by
  intro φ
  set ψ : ↥(cycles Y (N + 1)) →ₗ[ZMod 2] ZMod 2 :=
    φ.comp ((boundaries Y (N + 1)).submoduleOf (cycles Y (N + 1))).mkQ with hψ
  obtain ⟨F, hF⟩ := LinearMap.exists_extend ψ
  obtain ⟨a, ha⟩ := exists_cochain_of_functional F
  have hFcyc : ∀ z : ↥(cycles Y (N + 1)), F (z : SingularChain Y (N + 1)) = ψ z :=
    fun z => LinearMap.congr_fun hF z
  have hFbd : ∀ w : SingularChain Y (N + 2), F (chainBoundary Y (N + 1) w) = 0 := by
    intro w
    have hmem : chainBoundary Y (N + 1) w ∈ boundaries Y (N + 1) := ⟨w, rfl⟩
    have hcyc : chainBoundary Y (N + 1) w ∈ cycles Y (N + 1) :=
      boundaries_le_cycles Y (N + 1) hmem
    have hzero : ((boundaries Y (N + 1)).submoduleOf (cycles Y (N + 1))).mkQ
        ⟨chainBoundary Y (N + 1) w, hcyc⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hmem
    have h1 : F (chainBoundary Y (N + 1) w) = ψ ⟨chainBoundary Y (N + 1) w, hcyc⟩ :=
      hFcyc ⟨chainBoundary Y (N + 1) w, hcyc⟩
    exact h1.trans ((congrArg φ hzero).trans (map_zero φ))
  have hcocycle : a ∈ LinearMap.ker (coboundaryₗ Y (N + 1)) := by
    rw [LinearMap.mem_ker]
    funext σ
    have hkz : kronecker (coboundaryₗ Y (N + 1) a) (Finsupp.single σ 1) = 0 := by
      rw [show coboundaryₗ Y (N + 1) a = coboundary Y (N + 1) a from rfl,
        kronecker_coboundary_chainBoundary, ha, hFbd]
    rw [kronecker_single, one_mul] at hkz
    exact hkz
  refine ⟨Cohomology.mk Y (N + 1) ⟨a, hcocycle⟩, ?_⟩
  ext z'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
  rw [Cohomology.mk, kroneckerH_mk_mk, ha, hFcyc z, hψ, LinearMap.comp_apply]
  rfl

/-- **The UC-dual iso** `Hⁿ⁺¹(Y) ≃ₗ (Hₙ₊₁(Y))*` over `ℤ/2`. -/
noncomputable def ucDualEquiv (Y : TopCat) (N : ℕ) :
    Cohomology Y (N + 1) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Homology Y (N + 1)) :=
  LinearEquiv.ofBijective (kroneckerH (X := Y) (N + 1))
    ⟨(injective_iff_map_eq_zero _).mpr (fun ω h =>
        cohomology_eq_zero_of_kroneckerH N ω (fun β => by rw [h]; rfl)),
      kroneckerH_surjective_field⟩

/-- **Erdős–Kaplansky forcing**: a `ℤ/2`-space linearly isomorphic to its own dual is
finite-dimensional (`lift_rank_lt_rank_dual`: infinite rank strictly grows under dualization). -/
theorem finiteDimensional_of_linearEquiv_dual {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) : FiniteDimensional (ZMod 2) V := by
  by_contra h
  have hrank : Cardinal.aleph0 ≤ Module.rank (ZMod 2) V := by
    rw [← not_lt]
    intro hlt
    exact h (Module.rank_lt_aleph0_iff.mp hlt)
  have hlt := lift_rank_lt_rank_dual (K := ZMod 2) (V := V) hrank
  rw [e.rank_eq, Cardinal.lift_id] at hlt
  exact lt_irrefl _ hlt

open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularMayerVietorisLES in
/-- **The BIJECTIVE W-d1 endpoint bridge**: the fundamental duality is bijective when `D_univ`
is (the `⊤`-collapse square transfers surjectivity too). -/
theorem fundamentalDuality_bijective_of_openDuality_univ_bijective {M : TopCat}
    [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChain M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Function.Bijective
      ⇑(SKEFTHawking.SingularFundamentalDuality.fundamentalDuality k m z hz) := by
  constructor
  · exact fundamentalDuality_injective_of_openDuality_univ_injective hop z hz hD.injective
  · intro y
    obtain ⟨y', hy'⟩ := (homology_map_ambIncl_univ_bijective (m + 1)).surjective y
    obtain ⟨α, hα⟩ := hD.surjective y'
    obtain ⟨x, rfl⟩ := (of_top_univ_bijective (M := M) k).surjective α
    refine ⟨Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M)
      (SKEFTHawking.SingularCohomologyColimit.cohomG k)
      (SKEFTHawking.SingularCohomologyColimit.cohomF k) ⊤ x, ?_⟩
    have hfac : ∀ w, SKEFTHawking.SingularFundamentalDuality.fundamentalDuality k m z hz
          (Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M)
            (SKEFTHawking.SingularCohomologyColimit.cohomG k)
            (SKEFTHawking.SingularCohomologyColimit.cohomF k) ⊤ w)
        = SKEFTHawking.SingularRelativeDuality.relativeDuality
            ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
            (by rw [hz]; exact Submodule.zero_mem _) w := fun w =>
      Module.DirectLimit.lift_of _ _ w
    rw [hfac x, relativeDuality_top_eq_map_legW hop z hz x]
    rw [show legW hop z hz (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn
          (Set.univ : Set ↑M)) x
        = openDuality (k := k) (m := m) hop z hz
            (Module.DirectLimit.of (ZMod 2)
              (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M))
              (cohomGW (Set.univ : Set ↑M) k) (cohomFW (Set.univ : Set ↑M) k) ⊤ x)
      from (openDuality_of hop z hz ⊤ x).symm]
    rw [hα, hy']

end SKEFTHawking.SingularUCFinite
