/-
# Route (c′) P3 — `dim_{ℤ/2} H₄(S²×S²;ℤ/2) = 1`, and every nonzero boundary class is `betaClass`

`H₄(S²×S²;ℤ) ≅ ℤ` (`SphereProdHFourInt.sphereProdHFourEquivInt`, free rank 1) and `H₃(S²×S²;ℤ) = 0`
(2-torsion-free), so the rank-preserving UCT (`SphereProdHTwoMod2.redHomology_surjective` /
`exists_two_smul_of_redHomology_eq_zero`) gives `dim_{ℤ/2} H₄(S²×S²;ℤ/2) = 1` — the rank-1 mirror of the
banked `finrank_sphereProd_homologyMod2_two = 2`, one degree up. Transported along the boundary-inclusion
homeomorphism `sphereDiskInclHomeo`, `dim H₄(sub sphereDiskBoundarySet) = 1`, so the connecting image
`[∂cls]` (nonzero by P1) equals `betaClass` (the transported `S²×S²` fundamental class) — the route-(c′)
identification that P4/P5 detect.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SphereProdHTwoMod2
import SKEFTHawking.SphereProdHFourInt
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SphereProdHTwoMod2
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)

namespace SKEFTHawking.SphereProdHFourMod2Detect

/-- The reduction of the integral generator of `H₄(S²×S²;ℤ) ≅ ℤ` into `H₄(S²×S²;ℤ/2)`. -/
noncomputable def gen4 : Homology (TopCat.of SphereProd) 4 :=
  SingularHomologyInt.redHomology (TopCat.of SphereProd) 4
    (SphereProdHFourInt.sphereProdHFourEquivInt.symm 1)

/-- `H₃(S²×S²;ℤ)` is 2-torsion-free (it vanishes, `SphereProdHFourInt.sphereProd_homology_three_eq_zero`). -/
theorem sphereProd_intHomology_three_torsionFree
    (x : SingularHomologyInt.Homology (TopCat.of SphereProd) 3) (_ : (2 : ℤ) • x = 0) : x = 0 :=
  SphereProdHFourInt.sphereProd_homology_three_eq_zero x

/-- `redHomology (e.symm s) = (s : ℤ/2) · gen4`. -/
theorem redHomology_symm_apply_four (s : ℤ) :
    SingularHomologyInt.redHomology (TopCat.of SphereProd) 4
        (SphereProdHFourInt.sphereProdHFourEquivInt.symm s)
      = (s : ZMod 2) • gen4 := by
  have h1 : SphereProdHFourInt.sphereProdHFourEquivInt.symm s
      = s • SphereProdHFourInt.sphereProdHFourEquivInt.symm 1 := by
    rw [← map_smul]; congr 1; simp
  rw [h1, map_zsmul, gen4, Int.cast_smul_eq_zsmul (ZMod 2) s]

/-- The `ℤ/2`-linear map `a ↦ a·gen4 : ℤ/2 → H₄(S²×S²;ℤ/2)` is a **bijection**: surjective by
`redHomology` surjectivity (`H₃(S²×S²;ℤ)` 2-torsion-free), injective by the `2·H₄` kernel identity +
`H₄(ℤ) ≅ ℤ`. The rank-1 mirror of the `(gen0,gen1)` degree-2 bijection, one degree up. -/
theorem toSpanSingleton_gen4_bijective :
    Function.Bijective
      (LinearMap.toSpanSingleton (ZMod 2) (Homology (TopCat.of SphereProd) 4) gen4) := by
  have hΨ : ∀ a : ZMod 2,
      LinearMap.toSpanSingleton (ZMod 2) (Homology (TopCat.of SphereProd) 4) gen4 a = a • gen4 :=
    fun a => rfl
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hΨ] at ha
    have hcast : ((a.val : ℤ) : ZMod 2) = a := by
      rw [Int.cast_natCast]; exact ZMod.natCast_rightInverse (n := 2) a
    have ha' : SingularHomologyInt.redHomology (TopCat.of SphereProd) 4
        (SphereProdHFourInt.sphereProdHFourEquivInt.symm (a.val : ℤ)) = 0 := by
      rw [redHomology_symm_apply_four, hcast]; exact ha
    obtain ⟨d, hd⟩ :=
      exists_two_smul_of_redHomology_eq_zero (X := TopCat.of SphereProd) 3 _ ha'
    have hval : (a.val : ℤ) = (2 : ℤ) • SphereProdHFourInt.sphereProdHFourEquivInt d := by
      rw [SphereProdHFourInt.sphereProdHFourEquivInt.symm_apply_eq] at hd
      rw [hd, map_zsmul]
    have ha2 : (2 : ℤ) ∣ (a.val : ℤ) :=
      ⟨SphereProdHFourInt.sphereProdHFourEquivInt d, by simpa [smul_eq_mul] using hval⟩
    have ha2n : 2 ∣ a.val := by exact_mod_cast ha2
    have hva : a.val = 0 := by have := ZMod.val_lt a; omega
    have h := ZMod.natCast_rightInverse (n := 2) a
    rw [hva] at h; simpa using h.symm
  · intro v
    obtain ⟨x, rfl⟩ := redHomology_surjective (X := TopCat.of SphereProd) 3
      sphereProd_intHomology_three_torsionFree v
    refine ⟨((SphereProdHFourInt.sphereProdHFourEquivInt x : ℤ) : ZMod 2), ?_⟩
    rw [hΨ, ← redHomology_symm_apply_four,
      SphereProdHFourInt.sphereProdHFourEquivInt.symm_apply_apply]

/-- The rank-1 iso `ℤ/2 ≃ₗ H₄(S²×S²;ℤ/2)`. -/
noncomputable def sphereProdHFourMod2Equiv :
    ZMod 2 ≃ₗ[ZMod 2] Homology (TopCat.of SphereProd) 4 :=
  LinearEquiv.ofBijective _ toSpanSingleton_gen4_bijective

instance : FiniteDimensional (ZMod 2) (Homology (TopCat.of SphereProd) 4) :=
  Module.Finite.equiv sphereProdHFourMod2Equiv

instance : FiniteDimensional (ZMod 2)
    (Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 4) :=
  Module.Finite.equiv (homeoHomologyEquiv sphereDiskInclHomeo 4)

/-- **`dim_{ℤ/2} H₄(S²×S²;ℤ/2) = 1`.** The rank-1 mirror of `finrank_sphereProd_homologyMod2_two`. -/
theorem finrank_sphereProd_homologyMod2_four :
    Module.finrank (ZMod 2) (Homology (TopCat.of SphereProd) 4) = 1 := by
  rw [← sphereProdHFourMod2Equiv.finrank_eq, Module.finrank_self]

/-- **`dim_{ℤ/2} H₄(sub sphereDiskBoundarySet;ℤ/2) = 1`.** Transport of the `S²×S²` rank-1 fact along
the boundary-inclusion homeomorphism `sphereDiskInclHomeo`. -/
theorem finrank_sphereDiskBoundary_homologyMod2_four :
    Module.finrank (ZMod 2)
        (Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 4) = 1 := by
  rw [← (homeoHomologyEquiv sphereDiskInclHomeo 4).finrank_eq,
    finrank_sphereProd_homologyMod2_four]

/-- **Every nonzero boundary class is `betaClass`.** In the rank-1 space `H₄(sub sphereDiskBoundarySet)`,
`betaClass ≠ 0` spans, so any `y ≠ 0` equals `betaClass` — the route-(c′) identification of `[∂cls]`
(nonzero by P1) with the transported `S²×S²` fundamental class. -/
theorem eq_betaClass_of_ne_zero
    (y : Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 4) (hy : y ≠ 0) :
    y = betaClass := by
  have hspan : Submodule.span (ZMod 2) {betaClass} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_sphereDiskBoundary_homologyMod2_four,
      finrank_span_singleton betaClass_ne_zero]
  have hy_mem : y ∈ Submodule.span (ZMod 2) {betaClass} := hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hy_mem
  obtain ⟨a, ha⟩ := hy_mem
  have ha0 : a ≠ 0 := fun h => hy (by rw [← ha, h, zero_smul])
  have hne : a.val ≠ 0 := by
    intro h
    apply ha0
    have hr := ZMod.natCast_rightInverse (n := 2) a
    rw [h] at hr; simpa using hr.symm
  have hv1 : a.val = 1 := by have := ZMod.val_lt a; omega
  have ha1 : a = 1 := by
    have hr := ZMod.natCast_rightInverse (n := 2) a
    rw [hv1] at hr; simpa using hr.symm
  rw [← ha, ha1, one_smul]

end SKEFTHawking.SphereProdHFourMod2Detect
