/-
# Phase 5q.H — K7 opener: the seam homology + the Mayer–Vietoris skeleton

The `KummerWeld` topological `KummerK3` is covered by two closed pieces `qImage` (the free quotient
`Q = T⁴°/τ`) and `eImage` (the 16 resolution pieces `E`), meeting along the **seam**
`qImage ∩ eImage = seam`, which is 16 disjoint embedded copies of `ℝP³` (`KummerResolutionPiece.RP3`,
the antipodal quotient `S³/±1`). This file opens the K7 accounting:

* §0 — **`H₀(ℝP³; ℤ) ≅ ℤ`**, the connected seam piece's degree-0 integral homology, via
  path-connectedness of the bespoke `S³ ⊂ ℂ²` (image of the path-connected Euclidean 4-sphere) pushed
  through the antipodal quotient `mkRP3`, then the banked
  `KummerH0T4.homologyZeroPathConnectedEquivInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.KummerFreeQuotient
import SKEFTHawking.KummerWeld
import SKEFTHawking.KummerH0T4
import SKEFTHawking.SingularMayerVietorisLESInt

namespace SKEFTHawking.KummerK7Opener

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerResolutionPiece (S3 RP3 mkRP3 negS3 continuous_mkRP3)

noncomputable section

/-! ## §0. `H₀(ℝP³; ℤ) ≅ ℤ` — the connected seam piece -/

/-- The coordinate map `ℝ⁴ → ℂ²`, `v ↦ (v₀ + v₁ i, v₂ + v₃ i)`. Continuous and ℝ-linear; its image of
the Euclidean unit 4-sphere is exactly the `S³ ⊂ ℂ²` carrier set. -/
def eucToC2 (v : EuclideanSpace ℝ (Fin 4)) : ℂ × ℂ :=
  (Complex.equivRealProdCLM.symm (v 0, v 1), Complex.equivRealProdCLM.symm (v 2, v 3))

theorem continuous_eucToC2 : Continuous eucToC2 := by
  unfold eucToC2
  fun_prop

/-- The carrier set of `S³ ⊂ ℂ²`. -/
def S3set : Set (ℂ × ℂ) := {p : ℂ × ℂ | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1}

/-- `‖v₀ + v₁ i‖² = v₀² + v₁²` for the coordinate embedding. -/
theorem norm_sq_symm (a b : ℝ) : ‖Complex.equivRealProdCLM.symm (a, b)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.equivRealProdCLM_symm_apply, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

/-- `‖z‖² = z.re² + z.im²` for a complex number. -/
theorem complex_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  nth_rewrite 1 [← Complex.re_add_im z]
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

/-- The Euclidean-norm-squared of a 4-vector as a sum of its four squared coordinates. -/
theorem euc4_norm_sq (v : EuclideanSpace ℝ (Fin 4)) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

theorem eucToC2_image_sphere : eucToC2 '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 = S3set := by
  ext p
  simp only [S3set, Set.mem_image, Metric.mem_sphere, dist_zero_right, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv2 : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
    rw [euc4_norm_sq] at hv2
    show ‖(eucToC2 v).1‖ ^ 2 + ‖(eucToC2 v).2‖ ^ 2 = 1
    unfold eucToC2
    rw [norm_sq_symm, norm_sq_symm]
    linarith
  · intro hp
    set v : EuclideanSpace ℝ (Fin 4) :=
      (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![p.1.re, p.1.im, p.2.re, p.2.im] with hvdef
    have hv0 : v 0 = p.1.re := by simp [hvdef]
    have hv1 : v 1 = p.1.im := by simp [hvdef]
    have hv2 : v 2 = p.2.re := by simp [hvdef]
    have hv3 : v 3 = p.2.im := by simp [hvdef]
    refine ⟨v, ?_, ?_⟩
    · have hsq : ‖v‖ ^ 2 = 1 := by
        rw [euc4_norm_sq, hv0, hv1, hv2, hv3]
        rw [complex_norm_sq p.1, complex_norm_sq p.2] at hp
        linarith [hp]
      nlinarith [norm_nonneg v, hsq]
    · show eucToC2 v = p
      unfold eucToC2
      rw [hv0, hv1, hv2, hv3, Complex.equivRealProdCLM_symm_apply,
        Complex.equivRealProdCLM_symm_apply]
      simp only [Complex.re_add_im, Prod.mk.eta]

theorem one_lt_rank_euc4 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

theorem isPathConnected_S3set : IsPathConnected S3set := by
  rw [← eucToC2_image_sphere]
  exact (isPathConnected_sphere one_lt_rank_euc4 0 (by norm_num)).image continuous_eucToC2

instance instPathConnectedS3 : PathConnectedSpace S3 :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_S3set

theorem surjective_mkRP3 : Function.Surjective mkRP3 := fun q => by
  obtain ⟨a, ha⟩ := Quotient.exists_rep q; exact ⟨a, ha⟩

instance instPathConnectedRP3 : PathConnectedSpace RP3 :=
  surjective_mkRP3.pathConnectedSpace continuous_mkRP3

/-- **`H₀(ℝP³; ℤ) ≅ ℤ`** — the seam piece is connected. -/
noncomputable def rp3H0EquivInt : Homology (TopCat.of RP3) 0 ≃ₗ[ℤ] ℤ :=
  KummerH0T4.homologyZeroPathConnectedEquivInt (TopCat.of RP3)

/-! ## §1. The K7 Mayer–Vietoris skeleton — the `b₂ = 22` accounting target -/

open SKEFTHawking.KummerWeld (KummerK3 qImage eImage seam)
open SKEFTHawking.SingularMayerVietorisLESInt
  (mvDeltaInt mvHomDiagInt mvHomSumInt mv_exact_ambientInt mv_exact_interInt mv_exact_middleInt)

/-- `K3` as a bundled `TopCat`. -/
abbrev KummerK3top : TopCat := TopCat.of KummerK3

/-- **The `b₂ = 22` accounting target** — the consumer-facing `Prop` the K7 accounting discharges:
`H₂(K3; ℤ)` is free of rank `22` (`≅ ℤ²²`). This is the K3 second Betti number; the Kummer
Mayer–Vietoris splits it as `6` (the `τ`-invariant part of `H₂(T⁴) ≅ ℤ⁶`, the `Q`-side) `+ 16` (one
`(-2)`-class per exceptional `E`-copy — `KummerResolutionPieceH2.zeroSectionH2EquivInt`). Stated as the
target the accounting will discharge; NOT proved here. -/
def kummerK3_b2_target : Prop := Nonempty (Homology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ))

/-- **The K7 seam interior-cover hypothesis** — the single geometric input the MV skeleton still needs:
the interiors of the two closed pieces `qImage`, `eImage` cover `K3`. This is discharged by the
parallel smooth-boundary / double-collar work (each welded seam point gets an `ℝ⁴` neighborhood), NOT
here. Every `k7MV*` map / exactness statement below is conditional on this. -/
abbrev K7SeamCoverHyp : Prop :=
  (⋃ U ∈ ({qImage, eImage} : Set (Set KummerK3)), interior U) = Set.univ

/-- **The K7 MV connecting map** `∂ : H₃(K3; ℤ) → H₂(seam; ℤ)`, conditional on the seam interior-cover.
`seam = qImage ∩ eImage` (`KummerWeld.qImage_inter_eImage`), so the codomain is the seam's `H₂`. -/
noncomputable def k7MVConnecting (h : K7SeamCoverHyp) :=
  mvDeltaInt (X := KummerK3top) qImage eImage 2 h

/-- **K7 MV exactness at the seam** (conditional): `H₃(K3) →[∂] H₂(seam) →[diag] H₂(qImage) × H₂(eImage)`
is exact at `H₂(seam)`. -/
theorem k7_mv_exact_seam (h : K7SeamCoverHyp) :
    Function.Exact (mvDeltaInt (X := KummerK3top) qImage eImage 2 h)
      (mvHomDiagInt (X := KummerK3top) qImage eImage 2) :=
  mv_exact_interInt (X := KummerK3top) qImage eImage 2 h

/-- **K7 MV exactness at the middle** (conditional): `H₂(seam) →[diag] H₂(qImage) × H₂(eImage) →[sum]
H₂(K3)` is exact at `H₂(qImage) × H₂(eImage)`. The `b₂ = 22` accounting reads the rank of `H₂(K3)` off
this middle term. -/
theorem k7_mv_exact_middle (h : K7SeamCoverHyp) :
    Function.Exact (mvHomDiagInt (X := KummerK3top) qImage eImage 2)
      (mvHomSumInt (X := KummerK3top) qImage eImage 2) :=
  mv_exact_middleInt (X := KummerK3top) qImage eImage 1 h

/-- **K7 MV exactness at the ambient** (conditional): `H₃(qImage) × H₃(eImage) →[sum] H₃(K3) →[∂]
H₂(seam)` is exact at `H₃(K3)`. -/
theorem k7_mv_exact_ambient (h : K7SeamCoverHyp) :
    Function.Exact (mvHomSumInt (X := KummerK3top) qImage eImage 3)
      (mvDeltaInt (X := KummerK3top) qImage eImage 2 h) :=
  mv_exact_ambientInt (X := KummerK3top) qImage eImage 2 h

/-! ## §2. `H₀(Q; ℤ) ≅ ℤ` opener — the free-quotient side -/

open SKEFTHawking.KummerFreeQuotient (FreeQuotient qmk)
open SKEFTHawking.KummerPuncturedTorus (puncturedTorus)

/-- `qmk : T⁴° → Q` is surjective (`Quotient.mk`). -/
theorem surjective_qmk : Function.Surjective qmk := fun q => by
  obtain ⟨a, ha⟩ := Quotient.exists_rep q; exact ⟨a, ha⟩

/-- `qmk : T⁴° → Q` is continuous (`Quotient.mk`). -/
theorem continuous_qmk : Continuous qmk := continuous_quotient_mk'

/-- **`Q = T⁴°/τ` is path-connected given the punctured torus is** — `qmk` is a continuous surjection,
so path-connectedness descends. The hypothesis `PathConnectedSpace ↥puncturedTorus` (the torus minus
its 16 excised balls stays connected) is the localized floor; the parallel punctured-torus work supplies
it. -/
theorem freeQuotient_pathConnected (hpt : PathConnectedSpace ↥puncturedTorus) :
    PathConnectedSpace FreeQuotient :=
  haveI := hpt
  surjective_qmk.pathConnectedSpace continuous_qmk

/-- **`H₀(Q; ℤ) ≅ ℤ`** (conditional on the punctured-torus floor) — the connected `Q`-side degree-0
integral homology, the `Q`-feeder for the K7 MV. The augmentation is the iso
(`KummerH0T4.homologyZeroPathConnectedEquivInt`). -/
noncomputable def qH0EquivInt (hpt : PathConnectedSpace ↥puncturedTorus) :
    Homology (TopCat.of FreeQuotient) 0 ≃ₗ[ℤ] ℤ :=
  haveI := freeQuotient_pathConnected hpt
  KummerH0T4.homologyZeroPathConnectedEquivInt (TopCat.of FreeQuotient)

/-! ## §3. The seam is `16 × ℝP³` — the seam-homology feeder -/

open SKEFTHawking.KummerWeld (weldMk weldMk_inr_injective EIndex)
open SKEFTHawking.KummerResolutionPiece (bdryMapRP3 continuous_bdryMapRP3 bdryMapRP3_injective)

/-- **The seam parametrisation** `EIndex × ℝP³ → K3`, `(c, r) ↦ weld (inr (c, ρ̄ r))` — the E-side end
of each of the 16 welded boundary `ℝP³`'s. -/
def seamParam (p : EIndex × RP3) : KummerK3 := weldMk (Sum.inr (p.1, bdryMapRP3 p.2))

theorem continuous_seamParam : Continuous seamParam :=
  SKEFTHawking.KummerWeld.continuous_weldMk.comp
    (continuous_inr.comp (continuous_fst.prodMk (continuous_bdryMapRP3.comp continuous_snd)))

/-- The seam parametrisation is injective: `weldMk ∘ inr` is injective (`weldMk_inr_injective`) and so
is `ρ̄` (`bdryMapRP3_injective`). -/
theorem seamParam_injective : Function.Injective seamParam := by
  rintro ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ h
  have hpair : (c₁, bdryMapRP3 r₁) = (c₂, bdryMapRP3 r₂) := weldMk_inr_injective h
  simp only [Prod.mk.injEq] at hpair ⊢
  exact ⟨hpair.1, bdryMapRP3_injective hpair.2⟩

/-- The seam parametrisation's range is exactly the seam (`KummerWeld.seam`, the E-side presentation). -/
theorem range_seamParam : Set.range seamParam = seam := by
  ext x
  simp only [seam, seamParam, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨c, r⟩, rfl⟩; exact ⟨c, r, rfl⟩
  · rintro ⟨c, r, rfl⟩; exact ⟨(c, r), rfl⟩

/-- The bijection `EIndex × ℝP³ ≃ ↥seam` (16 disjoint `ℝP³`'s), corestriction of `seamParam`. -/
noncomputable def seamEquiv : (EIndex × RP3) ≃ ↥seam :=
  Equiv.ofBijective (fun p => ⟨seamParam p, by rw [← range_seamParam]; exact Set.mem_range_self p⟩)
    ⟨fun a b h => seamParam_injective (Subtype.ext_iff.mp h), fun y => by
      have hy : y.1 ∈ Set.range seamParam := by rw [range_seamParam]; exact y.2
      obtain ⟨p, hp⟩ := hy
      exact ⟨p, Subtype.ext hp⟩⟩

/-- **The seam is `16 × ℝP³`** — `EIndex × ℝP³ ≃ₜ ↥seam`, a continuous bijection from the compact
`EIndex × ℝP³` onto the Hausdorff seam, hence a homeomorphism. This is the topological content of
"the seam is the 16 embedded copies of `ℝP³`". -/
noncomputable def seamHomeo : (EIndex × RP3) ≃ₜ ↥seam :=
  Continuous.homeoOfEquivCompactToT2 (f := seamEquiv)
    (continuous_seamParam.subtype_mk _)

/-- **The seam-homology feeder** `H_n(16 × ℝP³; ℤ) ≅ H_n(seam; ℤ)` in every degree — the homeomorphism
`seamHomeo` transported through the integral homology functor. The MV skeleton consumes the seam's
`H_n` through this identification with the 16 disjoint `ℝP³`'s. -/
noncomputable def seamHomeoCM : C(EIndex × RP3, ↥seam) := ⟨seamHomeo, seamHomeo.continuous⟩

noncomputable def seamHomeoSymmCM : C(↥seam, EIndex × RP3) := ⟨seamHomeo.symm, seamHomeo.symm.continuous⟩

noncomputable def seamHomologyEquivInt (n : ℕ) :
    Homology (TopCat.of (EIndex × RP3)) n ≃ₗ[ℤ] Homology (TopCat.of ↥seam) n :=
  LinearEquiv.ofBijective
    (SingularFunctorialityInt.Homology.mapInt
      (X := TopCat.of (EIndex × RP3)) (Y := TopCat.of ↥seam) seamHomeoCM n)
    (SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all
      (X := TopCat.of (EIndex × RP3)) (Y := TopCat.of ↥seam)
      seamHomeoCM seamHomeoSymmCM
      (ContinuousMap.ext fun x => seamHomeo.symm_apply_apply x)
      (ContinuousMap.ext fun y => seamHomeo.apply_symm_apply y) n)

end

end SKEFTHawking.KummerK7Opener
