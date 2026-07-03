import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularRelativeHomologyMod2
import SKEFTHawking.SingularCapHomology

/-!
# Phase 5q.G (G1 PD-induction, base-case B5) — chart-convex subspaces are acyclic

`H_{k+1}(sub W) = 0` for a chart-convex open `W ⊆ M` (the chart carries `W` to an open convex
`C ⊆ ℝⁿ`): the straight-line contraction of the convex subspace `sub C` (mirroring
`SingularDiskAcyclic`) kills its positive homology, and the chart-restricted homeomorphism
`sub W ≃ₜ sub C` transports the vanishing (`Homology.map_bijective_of_comp_id_all`).

The `H₂ = H₁ = 0` inputs of the base-case `(2,1)`/`(3,0)` conjuncts (zero maps between zeros).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularConvexSubAcyclic

/-- Convexity membership for the straight-line contraction. -/
theorem contraction_mem {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C)
    (x : ↥(sub (X := SingularEuclideanAcyclic.Eucl n) C)) (t : unitInterval) :
    (1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n)) + (t : ℝ) • p₀ ∈ C :=
  hC x.2 hp₀ (by linarith [t.2.2]) t.2.1 (by ring)

/-- The **straight-line contraction** of a convex subspace to an interior point `p₀`. -/
noncomputable def convexContraction {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) :
    C(↑(sub (X := SingularEuclideanAcyclic.Eucl n) C) × unitInterval,
      ↑(sub (X := SingularEuclideanAcyclic.Eucl n) C)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin n)) + (p.2 : ℝ) • p₀,
    contraction_mem hC hp₀ p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.add ?_ ?_) _
    · exact Continuous.smul
        (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
        (continuous_subtype_val.comp continuous_fst)
    · exact Continuous.smul (continuous_subtype_val.comp continuous_snd) continuous_const

theorem slice_convexContraction_zero {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) :
    slice (convexContraction hC hp₀) 0
      = ContinuousMap.id ↑(sub (X := SingularEuclideanAcyclic.Eucl n) C) := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((0 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n))
      + ((0 : unitInterval) : ℝ) • p₀ = (x : _)
  simp

theorem slice_convexContraction_one {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) :
    slice (convexContraction hC hp₀) 1
      = ContinuousMap.const ↑(sub (X := SingularEuclideanAcyclic.Eucl n) C) ⟨p₀, hp₀⟩ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((1 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n))
      + ((1 : unitInterval) : ℝ) • p₀ = p₀
  simp

/-- **A convex subspace is acyclic**: `H_{k+1}(sub C) = 0` for `C` convex with `p₀ ∈ C`. -/
theorem homology_convexSub_eq_zero {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) (k : ℕ)
    (x : Homology (sub (X := SingularEuclideanAcyclic.Eucl n) C) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk z : Homology _ (k + 1)) = Homology.mk _ (k + 1) z from rfl,
    SKEFTHawking.SingularCapHomology.Homology.mk_eq_zero]
  exact Submodule.mem_comap.mpr (by
    simpa using cycle_mem_boundaries_of_contraction (convexContraction hC hp₀) ⟨p₀, hp₀⟩
      (slice_convexContraction_zero hC hp₀) (slice_convexContraction_one hC hp₀)
      z.1 (LinearMap.mem_ker.mp z.2))

/-- **The chart-restricted homeomorphism** `sub W ≃ₜ sub C` for a chart-convex `W`. -/
noncomputable def chartSubHomeo {M : TopCat} {m : ℕ}
    {U : Set ↑M} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C)) :
    ↥(sub W) ≃ₜ ↥(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C) where
  toFun x :=
    ⟨((e ⟨(x : ↑M), hWU x.2⟩ : ↥V) : ↑(SingularEuclideanAcyclic.Eucl (m + 2))),
      show ((e ⟨(x : ↑M), hWU x.2⟩ : ↥V) : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C from
        (hWe ⟨(x : ↑M), hWU x.2⟩).mp x.2⟩
  invFun y :=
    ⟨((e.symm ⟨(y : ↑(SingularEuclideanAcyclic.Eucl (m + 2))), hCV y.2⟩ : ↥U) : ↑M),
      show ((e.symm ⟨(y : _), hCV y.2⟩ : ↥U) : ↑M) ∈ W from
        (hWe (e.symm ⟨(y : _), hCV y.2⟩)).mpr (by
          rw [e.apply_symm_apply]
          exact y.2)⟩
  left_inv x := by
    refine Subtype.ext ?_
    show ((e.symm (e ⟨(x : ↑M), hWU x.2⟩) : ↥U) : ↑M) = (x : ↑M)
    rw [e.symm_apply_apply]
  right_inv y := by
    refine Subtype.ext ?_
    show ((e (e.symm ⟨(y : ↑(SingularEuclideanAcyclic.Eucl (m + 2))), hCV y.2⟩) : ↥V)
          : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
        = (y : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
    rw [e.apply_symm_apply]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (e.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (e.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

/-- **B5: a chart-convex open subspace of a manifold is acyclic** — `H_{k+1}(sub W) = 0`. -/
theorem homology_chartConvexSub_eq_zero {M : TopCat} {m : ℕ}
    {U : Set ↑M} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    (k : ℕ) (x : Homology (sub W) (k + 1)) : x = 0 := by
  set φ := chartSubHomeo e hCV hWU hWe with hφ
  have hbij : Function.Bijective
      (Homology.map (⟨φ, φ.continuous⟩ : C(↑(sub W), ↑(sub (X := SingularEuclideanAcyclic.Eucl
        (m + 2)) C))) (k + 1)) :=
    Homology.map_bijective_of_comp_id_all
      (⟨φ, φ.continuous⟩ : C(↑(sub W), ↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C)))
      (⟨φ.symm, φ.symm.continuous⟩ :
        C(↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C), ↑(sub W)))
      (ContinuousMap.ext fun z => show φ.symm (φ z) = z from φ.symm_apply_apply z)
      (ContinuousMap.ext fun z => show φ (φ.symm z) = z from φ.apply_symm_apply z) (k + 1)
  exact hbij.injective (by
    rw [map_zero]
    exact homology_convexSub_eq_zero hCconv hp₀ k _)

end SKEFTHawking.SingularConvexSubAcyclic
