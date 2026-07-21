/-
# Phase 5q.H — K7: the unconditional collar-thickened Mayer–Vietoris over the Kummer weld

The K7 `b₂ = 22` accounting, assembled UNCONDITIONALLY over the weld carrier
`K3 = Q ∪_{16 × ℝP³} (16 × E)` (`KummerWeld.KummerK3`). The K7 opener's MV skeleton was
conditional on `K7SeamCoverHyp` — the interiors of the two CLOSED pieces `qImage`, `eImage`
covering `K3` — which fails at the seam (a seam point is interior to neither closed piece). This
file replaces that hypothesis with the standard collar thickening and discharges the cover:

* §1 the **collar-thickened pieces**: `qThick = qImage ∪ eOuter` (the `Q`-piece plus the outer
  half-collars `fiberNorm ≥ 1/2` of the 16 `E`-copies) and `eImage`, with
  `qThick ∩ eImage = eOuter` and the **interior-cover discharge** `k7_hcov`.
* §2 the **unconditional K7 MV** — `SingularMayerVietorisLESInt` instantiated at
  `(qThick, eImage)`: the connecting map and all three exactness statements, hypothesis-free.
* §3–4 the **piece homologies**: `weldFlow` (the outward fiber flow, `KummerWeldFiberFlow`)
  deformation-retracts `qThick` onto `qImage ≃ₜ Q` and the collar `qThick ∩ eImage` onto the
  seam `≃ 16 × ℝP³`; `eImage ≃ₜ EIndex × E` splits by the 16 discrete copies.
* §5 the **value table** (from the banked `E`- and `ℝP³`-tables):
  `H₂(collar) = 0`, `H₁(collar) ≅ (ℤ/2)¹⁶`, `H₃(collar) ≅ ℤ¹⁶`,
  `H₂(eImage) ≅ ℤ¹⁶`, `H₁(eImage) = H₃(eImage) = 0`, `Hₙ₊₁(qThick) ≅ Hₙ₊₁(Q)`.
* §6 the **degree-2/3 windows** (the `b₂ = 22` structure, sharp):
  `Σ₂ : H₂(qThick) ⊕ H₂(eImage) → H₂(K3)` is INJECTIVE (`k7Sum2_injective`), the 16-fold
  exceptional block `ℤ¹⁶ ↪ H₂(K3)` (`exceptionalEmbed_injective`), `2·H₂(K3) ⊆ im Σ₂`
  (`k7H2_two_smul_mem_range` — the cokernel embeds in `H₁(16 × ℝP³) = (ℤ/2)¹⁶`, exponent 2),
  `Σ₃` surjective with the `E`-side dead (`k7H3_surjective_from_qThick`), and the conditional
  capstone `kummerK3_b2_window_of_qH2`: given the (open) `Q`-side input `H₂(Q;ℤ) ≅ ℤ⁶`, a rank-22
  free block embeds in `H₂(K3;ℤ)` containing `2·H₂(K3)` — the `b₂ = 22` rank window. The sharp
  residual for the full `kummerK3_b2_target` is the `Q`-side `H₂` computation plus the
  `δ₁`-image (extension) analysis.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerWeldFiberFlow
import SKEFTHawking.KummerK7Opener
import SKEFTHawking.SingularFiniteProdDiscreteHnInt
import SKEFTHawking.KummerBaseSphereH2Int
import SKEFTHawking.KummerRP3HomologySolve
import SKEFTHawking.KummerRP3HomologyUnconditional

namespace SKEFTHawking.KummerK7MVAssembly

open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularFiniteProdDiscreteHnInt
open SKEFTHawking.KummerK7Opener (KummerK3top)

noncomputable section

/-! ## §1. The collar-thickened pieces and the interior-cover discharge -/

/-- The outer-collar carrier: `E`-copy points of fiber radius `≥ 1/2`. -/
def eOuterCarrier : Set (EIndex × ResE) := {p | 1 / 2 ≤ fiberNorm p.2}

theorem isClosed_eOuterCarrier : IsClosed eOuterCarrier :=
  isClosed_le continuous_const (continuous_fiberNorm.comp continuous_snd)

/-- **The outer collar** — the image in `K3` of the 16 outer half-collars `fiberNorm ≥ 1/2`. -/
def eOuter : Set KummerK3 := (fun p : EIndex × ResE => weldMk (Sum.inr p)) '' eOuterCarrier

theorem isClosed_eOuter : IsClosed eOuter :=
  (isClosed_eOuterCarrier.isCompact.image (continuous_weldMk.comp continuous_inr)).isClosed

/-- **The collar-thickened `Q`-piece**: `Q` together with the 16 outer half-collars. -/
def qThick : Set KummerK3 := qImage ∪ eOuter

theorem isClosed_qThick : IsClosed qThick := isClosed_qImage.union isClosed_eOuter

theorem qImage_subset_qThick : qImage ⊆ qThick := Set.subset_union_left

theorem eOuter_subset_eImage : eOuter ⊆ eImage := by
  rintro x ⟨p, _, rfl⟩; exact ⟨p, rfl⟩

theorem seam_subset_qImage : seam ⊆ qImage :=
  qImage_inter_eImage ▸ Set.inter_subset_left

theorem seam_subset_eImage : seam ⊆ eImage :=
  qImage_inter_eImage ▸ Set.inter_subset_right

/-- The canonical seam membership: `weldMk (inr (c, ρ̄ r)) ∈ seam`. -/
theorem mem_seam (c : EIndex) (r : RP3) : weldMk (Sum.inr (c, bdryMapRP3 r)) ∈ seam :=
  Set.mem_iUnion.mpr ⟨c, ⟨r, rfl⟩⟩

theorem seam_subset_eOuter : seam ⊆ eOuter := by
  intro x hx
  simp only [seam, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨c, r, rfl⟩ := hx
  exact ⟨(c, bdryMapRP3 r), by
    rw [eOuterCarrier, Set.mem_setOf_eq, fiberNorm_bdryMapRP3]; norm_num, rfl⟩

/-- **The pieces meet exactly on the outer collar**: `qThick ∩ eImage = eOuter`. -/
theorem qThick_inter_eImage : qThick ∩ eImage = eOuter := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hq | ho, he⟩
    · exact seam_subset_eOuter (qImage_inter_eImage ▸ (⟨hq, he⟩ : x ∈ qImage ∩ eImage))
    · exact ho
  · exact fun x hx => ⟨Or.inr hx, eOuter_subset_eImage hx⟩

/-- The inner region `fiberNorm ≤ 1/2` — everything outside `qThick` lives here. -/
def eInner : Set KummerK3 :=
  (fun p : EIndex × ResE => weldMk (Sum.inr p)) '' {p | fiberNorm p.2 ≤ 1 / 2}

theorem isClosed_eInner : IsClosed eInner :=
  (((isClosed_le (continuous_fiberNorm.comp continuous_snd) continuous_const)).isCompact.image
    (continuous_weldMk.comp continuous_inr)).isClosed

theorem compl_qThick_subset_eInner : qThickᶜ ⊆ eInner := by
  intro x hx
  obtain ⟨a, rfl⟩ := weldMk_surjective x
  cases a with
  | inl q => exact absurd (Or.inl ⟨q, rfl⟩) hx
  | inr p =>
    by_cases hf : 1 / 2 ≤ fiberNorm p.2
    · exact absurd (Or.inr ⟨p, hf, rfl⟩) hx
    · exact ⟨p, (not_le.mp hf).le, rfl⟩

/-- The `Q`-piece never meets the inner region (an inner point has fiber radius `≤ 1/2 < 1`, so it
is not a seam point — but a `Q ∩ E` point must be on the seam). -/
theorem qImage_disjoint_eInner : ∀ x ∈ qImage, x ∉ eInner := by
  rintro x ⟨q, rfl⟩ ⟨p, hp, heq⟩
  rcases Quotient.exact heq with h | hsj | hsj
  · exact absurd h (by simp)
  · obtain ⟨c, r, h1, _⟩ := hsj
    exact absurd h1 (by simp)
  · obtain ⟨c, r, _, h2⟩ := hsj
    have hp2 : p = (c, bdryMapRP3 r) := Sum.inr.inj h2
    rw [hp2, Set.mem_setOf_eq, fiberNorm_bdryMapRP3] at hp
    norm_num at hp

/-- **The K7 interior-cover discharge** — the collar-thickened `Q`-piece and the `E`-piece have
interiors covering `K3`. This is the Mayer–Vietoris hypothesis the K7 opener left conditional
(`K7SeamCoverHyp` for the un-thickened closed pieces), now proven for the thickened pair. -/
theorem k7_hcov :
    (⋃ U ∈ ({qThick, eImage} : Set (Set KummerK3)), interior U) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop]
  by_cases hx : x ∈ eInner
  · refine ⟨eImage, Or.inr rfl, ?_⟩
    have hsub : qImageᶜ ⊆ eImage := fun y hy => by
      rcases (Set.eq_univ_iff_forall.mp qImage_union_eImage y) with h | h
      · exact absurd h hy
      · exact h
    exact interior_maximal hsub isClosed_qImage.isOpen_compl
      (fun hq => qImage_disjoint_eInner x hq hx)
  · refine ⟨qThick, Or.inl rfl, ?_⟩
    have hsub : eInnerᶜ ⊆ qThick := fun y hy => by
      by_contra hns
      exact hy (compl_qThick_subset_eInner hns)
    exact interior_maximal hsub isClosed_eInner.isOpen_compl hx

/-! ## §2. The unconditional K7 Mayer–Vietoris -/

/-- **The K7 connecting map** `∂ : Hₙ₊₁(K3;ℤ) → Hₙ(qThick ∩ eImage;ℤ)` — UNCONDITIONAL (the cover
hypothesis is `k7_hcov`). -/
def k7Delta (n : ℕ) :
    Homology KummerK3top (n + 1) →ₗ[ℤ] Homology (sub (X := KummerK3top) (qThick ∩ eImage)) n :=
  mvDeltaInt (X := KummerK3top) qThick eImage n k7_hcov

/-- **K7 MV exactness at the ambient** `Hₙ₊₁(K3)`: `im Σₙ₊₁ = ker ∂ₙ`. -/
theorem k7_exact_ambient (n : ℕ) :
    Function.Exact (mvHomSumInt (X := KummerK3top) qThick eImage (n + 1)) (k7Delta n) :=
  mv_exact_ambientInt (X := KummerK3top) qThick eImage n k7_hcov

/-- **K7 MV exactness at the collar** `Hₙ(qThick ∩ eImage)`: `im ∂ₙ = ker Δₙ`. -/
theorem k7_exact_inter (n : ℕ) :
    Function.Exact (k7Delta n) (mvHomDiagInt (X := KummerK3top) qThick eImage n) :=
  mv_exact_interInt (X := KummerK3top) qThick eImage n k7_hcov

/-- **K7 MV exactness at the middle** `Hₙ₊₁(qThick) ⊕ Hₙ₊₁(eImage)`: `im Δₙ₊₁ = ker Σₙ₊₁`. -/
theorem k7_exact_middle (n : ℕ) :
    Function.Exact (mvHomDiagInt (X := KummerK3top) qThick eImage (n + 1))
      (mvHomSumInt (X := KummerK3top) qThick eImage (n + 1)) :=
  mv_exact_middleInt (X := KummerK3top) qThick eImage n k7_hcov

/-! ## §3. Piece models: `qImage ≃ₜ Q`, `eImage ≃ₜ EIndex × E`, and the 16-fold splitters -/

/-- `Q ≃ ↥qImage` — the `Q`-piece is the bijective image of the free quotient. -/
def qImageEquiv : FreeQuotient ≃ ↥qImage :=
  Equiv.ofBijective (fun q => ⟨weldMk (Sum.inl q), ⟨q, rfl⟩⟩)
    ⟨fun a b h => weldMk_inl_injective (Subtype.ext_iff.mp h),
     fun y => by obtain ⟨q, hq⟩ := y.2; exact ⟨q, Subtype.ext hq⟩⟩

/-- **`Q ≃ₜ ↥qImage`** — continuous bijection, compact source, Hausdorff target. -/
def qImageHomeo : FreeQuotient ≃ₜ ↥qImage :=
  Continuous.homeoOfEquivCompactToT2 (f := qImageEquiv)
    (((continuous_weldMk.comp continuous_inl)).subtype_mk _)

/-- `EIndex × E ≃ ↥eImage` — the 16 `E`-copies are the bijective image. -/
def eImageEquiv : (EIndex × ResE) ≃ ↥eImage :=
  Equiv.ofBijective (fun p => ⟨weldMk (Sum.inr p), ⟨p, rfl⟩⟩)
    ⟨fun a b h => weldMk_inr_injective (Subtype.ext_iff.mp h),
     fun y => by obtain ⟨p, hp⟩ := y.2; exact ⟨p, Subtype.ext hp⟩⟩

/-- **`EIndex × E ≃ₜ ↥eImage`**. -/
def eImageHomeo : (EIndex × ResE) ≃ₜ ↥eImage :=
  Continuous.homeoOfEquivCompactToT2 (f := eImageEquiv)
    (((continuous_weldMk.comp continuous_inr)).subtype_mk _)

/-- `EIndex × Y ≃ₜ Fin 16 × Y` for any space `Y` — the 16-element index reindexed (generic form of
the banked `seamProdHomeo`). -/
def eIndexProdHomeoGen (Y : TopCat) : (EIndex × ↑Y) ≃ₜ (Fin 16 × ↑Y) :=
  { toEquiv := eIndexEquivFin.prodCongr (Equiv.refl ↑Y)
    continuous_toFun := continuous_of_discreteTopology.prodMap continuous_id
    continuous_invFun := continuous_of_discreteTopology.prodMap continuous_id }

/-- **`Hₙ(EIndex × Y; ℤ) ≅ (EIndex → Hₙ(Y; ℤ))`** for any `Y` — the 16 discrete copies split
integral homology (generic form of the banked `eIndexProdHnEquivInt`). -/
def eIndexProdHnEquivIntGen (Y : TopCat) (n : ℕ) :
    Homology (TopCat.of (EIndex × ↑Y)) n ≃ₗ[ℤ] (EIndex → Homology Y n) :=
  (homologyCongrInt (X := TopCat.of (EIndex × ↑Y)) (Y := TopCat.of (Fin 16 × ↑Y))
      (eIndexProdHomeoGen Y) n).trans
    ((finProdHnEquivInt Y n 15).trans
      (LinearEquiv.funCongrLeft ℤ (Homology Y n) eIndexEquivFin))

/-- **`Hₙ(eImage; ℤ) ≅ (EIndex → Hₙ(E; ℤ))`** — the `E`-piece homology splits into the 16 copies. -/
def eImageHnEquivInt (n : ℕ) :
    Homology (sub (X := KummerK3top) eImage) n ≃ₗ[ℤ] (EIndex → Homology (TopCat.of ResE) n) :=
  (homologyCongrInt (X := sub (X := KummerK3top) eImage) (Y := TopCat.of (EIndex × ResE))
      eImageHomeo.symm n).trans (eIndexProdHnEquivIntGen (TopCat.of ResE) n)

/-! ## §4. The collar retractions via the weld flow -/

theorem weldFlow_mem_eOuter {x : KummerK3} (hx : x ∈ eOuter) (t : unitInterval) :
    weldFlow (x, t) ∈ eOuter := by
  obtain ⟨⟨c, e⟩, hf, rfl⟩ := hx
  rw [weldFlow_mk_inr]
  refine ⟨(c, resFlow (e, t)), ?_, rfl⟩
  rw [eOuterCarrier, Set.mem_setOf_eq, fiberNorm_resFlow]
  refine le_min (by norm_num) ?_
  calc (1 : ℝ) / 2 ≤ fiberNorm e := hf
    _ = 1 * fiberNorm e := (one_mul _).symm
    _ ≤ (2 - (t : ℝ)) * fiberNorm e :=
        mul_le_mul_of_nonneg_right (one_le_two_sub t) (fiberNorm_nonneg _)

theorem weldFlow_mem_qThick {x : KummerK3} (hx : x ∈ qThick) (t : unitInterval) :
    weldFlow (x, t) ∈ qThick := by
  rcases hx with hq | ho
  · rw [weldFlow_qImage hq]; exact Or.inl hq
  · exact Or.inr (weldFlow_mem_eOuter ho t)

/-- At `t = 0` the flow pushes the outer collar onto the seam. -/
theorem weldFlow_zero_mem_seam_of_eOuter {x : KummerK3} (hx : x ∈ eOuter) :
    weldFlow (x, 0) ∈ seam := by
  obtain ⟨⟨c, e⟩, hf, rfl⟩ := hx
  rw [weldFlow_mk_inr]
  have hf' : 1 / 2 ≤ fiberNorm e := hf
  have h1 : fiberNorm (resFlow (e, 0)) = 1 := by
    rw [fiberNorm_resFlow, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
    exact min_eq_left (by linarith [hf'])
  obtain ⟨r, hr⟩ : resFlow (e, 0) ∈ Set.range bdryMapRP3 := by
    rw [range_bdryMapRP3_eq_boundaryE]; exact fiberNorm_eq_one_iff.mp h1
  rw [← hr]
  exact mem_seam c r

theorem weldFlow_zero_mem_qImage {x : KummerK3} (hx : x ∈ qThick) :
    weldFlow (x, 0) ∈ qImage := by
  rcases hx with hq | ho
  · rw [weldFlow_qImage hq]; exact hq
  · exact seam_subset_qImage (weldFlow_zero_mem_seam_of_eOuter ho)

theorem weldFlow_mem_inter {x : KummerK3} (hx : x ∈ qThick ∩ eImage) (t : unitInterval) :
    weldFlow (x, t) ∈ qThick ∩ eImage := by
  rw [qThick_inter_eImage] at hx ⊢
  exact weldFlow_mem_eOuter hx t

theorem weldFlow_zero_mem_seam {x : KummerK3} (hx : x ∈ qThick ∩ eImage) :
    weldFlow (x, 0) ∈ seam := by
  rw [qThick_inter_eImage] at hx
  exact weldFlow_zero_mem_seam_of_eOuter hx

theorem seam_subset_inter : seam ⊆ (qThick ∩ eImage : Set KummerK3) := fun _ hx =>
  ⟨qImage_subset_qThick (seam_subset_qImage hx), seam_subset_eImage hx⟩

/-- The inclusion `Q-piece ↪ thickened piece` as a continuous map. -/
def qInclC : C(↑(sub (X := KummerK3top) qImage), ↑(sub (X := KummerK3top) qThick)) :=
  ⟨fun x => ⟨x.1, qImage_subset_qThick x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- The retraction `thickened piece → Q-piece` (the `t = 0` weld flow). -/
def qRetrC : C(↑(sub (X := KummerK3top) qThick), ↑(sub (X := KummerK3top) qImage)) :=
  ⟨fun x => ⟨weldFlow (x.1, 0), weldFlow_zero_mem_qImage x.2⟩,
    ((continuous_weldFlow.comp (continuous_subtype_val.prodMk continuous_const))).subtype_mk _⟩

/-- The deformation `qThick × [0,1] → qThick` (the weld flow, collar-invariant). -/
def qThickHtpyC :
    C(↑(sub (X := KummerK3top) qThick) × unitInterval, ↑(sub (X := KummerK3top) qThick)) :=
  ⟨fun p => ⟨weldFlow (p.1.1, p.2), weldFlow_mem_qThick p.1.2 p.2⟩,
    ((continuous_weldFlow.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).subtype_mk _⟩

/-- The trivial homotopy on the `Q`-piece. -/
def qTrivHtpyC :
    C(↑(sub (X := KummerK3top) qImage) × unitInterval, ↑(sub (X := KummerK3top) qImage)) :=
  ⟨fun p => p.1, continuous_fst⟩

/-- **The thickening is a homotopy equivalence**: `Hₙ₊₁(qImage) ≅ Hₙ₊₁(qThick)` via the inclusion. -/
theorem qIncl_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt qInclC (n + 1)) := by
  refine SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    qInclC qRetrC qTrivHtpyC ?_ ?_ qThickHtpyC ?_ ?_ n
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (x : KummerK3) = weldFlow ((x : KummerK3), 0)
    exact (weldFlow_qImage x.2 0).symm
  · exact ContinuousMap.ext fun _ => rfl
  · exact ContinuousMap.ext fun x => Subtype.ext rfl
  · exact ContinuousMap.ext fun x => Subtype.ext (weldFlow_one _)

/-- **`Hₙ₊₁(qThick; ℤ) ≅ Hₙ₊₁(Q; ℤ)`** — the thickened piece carries the free-quotient homology. -/
def qThickHnEquivInt (n : ℕ) :
    Homology (sub (X := KummerK3top) qThick) (n + 1)
      ≃ₗ[ℤ] Homology (TopCat.of FreeQuotient) (n + 1) :=
  ((LinearEquiv.ofBijective (Homology.mapInt qInclC (n + 1)) (qIncl_mapInt_bijective n)).symm).trans
    (homologyCongrInt (X := sub (X := KummerK3top) qImage) (Y := TopCat.of FreeQuotient)
      qImageHomeo.symm (n + 1))

/-- The inclusion `seam ↪ collar` as a continuous map. -/
def seamInclC :
    C(↑(sub (X := KummerK3top) seam), ↑(sub (X := KummerK3top) (qThick ∩ eImage))) :=
  ⟨fun x => ⟨x.1, seam_subset_inter x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- The retraction `collar → seam` (the `t = 0` weld flow). -/
def seamRetrC :
    C(↑(sub (X := KummerK3top) (qThick ∩ eImage)), ↑(sub (X := KummerK3top) seam)) :=
  ⟨fun x => ⟨weldFlow (x.1, 0), weldFlow_zero_mem_seam x.2⟩,
    ((continuous_weldFlow.comp (continuous_subtype_val.prodMk continuous_const))).subtype_mk _⟩

/-- The deformation `collar × [0,1] → collar`. -/
def interHtpyC :
    C(↑(sub (X := KummerK3top) (qThick ∩ eImage)) × unitInterval,
      ↑(sub (X := KummerK3top) (qThick ∩ eImage))) :=
  ⟨fun p => ⟨weldFlow (p.1.1, p.2), weldFlow_mem_inter p.1.2 p.2⟩,
    ((continuous_weldFlow.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).subtype_mk _⟩

/-- The trivial homotopy on the seam. -/
def seamTrivHtpyC :
    C(↑(sub (X := KummerK3top) seam) × unitInterval, ↑(sub (X := KummerK3top) seam)) :=
  ⟨fun p => p.1, continuous_fst⟩

/-- **The collar retracts to the seam**: `Hₙ₊₁(seam) ≅ Hₙ₊₁(qThick ∩ eImage)` via the inclusion. -/
theorem seamIncl_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt seamInclC (n + 1)) := by
  refine SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    seamInclC seamRetrC seamTrivHtpyC ?_ ?_ interHtpyC ?_ ?_ n
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (x : KummerK3) = weldFlow ((x : KummerK3), 0)
    exact (weldFlow_seam x.2 0).symm
  · exact ContinuousMap.ext fun _ => rfl
  · exact ContinuousMap.ext fun x => Subtype.ext rfl
  · exact ContinuousMap.ext fun x => Subtype.ext (weldFlow_one _)

/-- **`Hₙ₊₁(qThick ∩ eImage; ℤ) ≅ (EIndex → Hₙ₊₁(ℝP³; ℤ))`** — the collar carries the 16-fold
`ℝP³` seam homology (retraction to the seam + the opener's seam identification + the 16-fold
split). -/
def interHnEquivInt (n : ℕ) :
    Homology (sub (X := KummerK3top) (qThick ∩ eImage)) (n + 1)
      ≃ₗ[ℤ] (EIndex → Homology (TopCat.of RP3) (n + 1)) :=
  (((LinearEquiv.ofBijective (Homology.mapInt seamInclC (n + 1))
      (seamIncl_mapInt_bijective n)).symm).trans
    ((SKEFTHawking.KummerK7Opener.seamHomologyEquivInt (n + 1)).symm)).trans
    (SingularFiniteProdDiscreteHnInt.eIndexProdHnEquivInt (n + 1))

/-! ## §5. The K7 piece-homology value table -/

/-- **`H₂(collar; ℤ) = 0`** — `H₂(ℝP³; ℤ) = 0` on each of the 16 copies. -/
theorem interH2_eq_zero (x : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 2) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (interHnEquivInt 1)).mp
    (funext fun _ => SKEFTHawking.KummerRP3HomologySolve.rp3_homology_two_eq_zero _)

/-- **`H₁(collar; ℤ) ≅ (ℤ/2)¹⁶`** — the 16 deck classes. -/
def interH1EquivInt :
    Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 1 ≃ₗ[ℤ] (EIndex → ZMod 2) :=
  (interHnEquivInt 0).trans
    (LinearEquiv.piCongrRight fun _ => SKEFTHawking.KummerRP3HomologySolve.rp3H1EquivZMod2)

/-- **`H₃(collar; ℤ) ≅ ℤ¹⁶`** — the 16 fundamental classes of the seam `ℝP³`'s. -/
def interH3EquivInt :
    Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 3 ≃ₗ[ℤ] (EIndex → ℤ) :=
  (interHnEquivInt 2).trans
    (LinearEquiv.piCongrRight fun _ =>
      SKEFTHawking.KummerRP3HomologyUnconditional.rp3H3EquivInt_unconditional)

/-- **`H₂(eImage; ℤ) ≅ ℤ¹⁶`** — one zero-section class per `E`-copy. -/
def eImageH2EquivInt : Homology (sub (X := KummerK3top) eImage) 2 ≃ₗ[ℤ] (EIndex → ℤ) :=
  (eImageHnEquivInt 2).trans
    (LinearEquiv.piCongrRight fun _ => SKEFTHawking.KummerBaseSphereH2Int.resEH2EquivInt)

/-- **`H₁(eImage; ℤ) = 0`**. -/
theorem eImageH1_eq_zero (x : Homology (sub (X := KummerK3top) eImage) 1) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (eImageHnEquivInt 1)).mp
    (funext fun _ => SKEFTHawking.KummerBaseSphereH2Int.resE_homology_one_eq_zero _)

/-- **`H₃(eImage; ℤ) = 0`**. -/
theorem eImageH3_eq_zero (x : Homology (sub (X := KummerK3top) eImage) 3) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (eImageHnEquivInt 3)).mp
    (funext fun _ => SKEFTHawking.KummerBaseSphereH2Int.resE_homology_three_eq_zero _)

/-- **`H₄(collar; ℤ) = 0`** — `H₄(ℝP³; ℤ) = 0` on each copy (degree-4 window input for the
`[K]` fundamental-class arc). -/
theorem interH4_eq_zero (x : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 4) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (interHnEquivInt 3)).mp
    (funext fun _ => SKEFTHawking.KummerRP3HomologyUnconditional.rp3_homology_four_eq_zero _)

/-- **`H₄(eImage; ℤ) = 0`**. -/
theorem eImageH4_eq_zero (x : Homology (sub (X := KummerK3top) eImage) 4) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (eImageHnEquivInt 4)).mp
    (funext fun _ => SKEFTHawking.KummerBaseSphereH2Int.resE_homology_four_eq_zero _)

/-! ## §6. The degree-2 and degree-3 windows — the `b₂ = 22` structure -/

/-- **`Σ₂` is injective** — `H₂(collar) = 0` kills the incoming diagonal, so the piece classes
inject into `H₂(K3; ℤ)`. -/
theorem k7Sum2_injective :
    Function.Injective (mvHomSumInt (X := KummerK3top) qThick eImage 2) := by
  intro p q hpq
  have hker : mvHomSumInt (X := KummerK3top) qThick eImage 2 (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  obtain ⟨w, hw⟩ := (k7_exact_middle 1 (p - q)).mp hker
  rw [interH2_eq_zero w, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

/-- **The 16-fold exceptional block** `ℤ¹⁶ →ₗ H₂(K3; ℤ)` — the `E`-side of the MV sum, through the
per-copy zero-section classes. -/
def exceptionalEmbed : (EIndex → ℤ) →ₗ[ℤ] Homology KummerK3top 2 :=
  (mvHomSumInt (X := KummerK3top) qThick eImage 2).comp
    ((LinearMap.inr ℤ (Homology (sub (X := KummerK3top) qThick) 2)
        (Homology (sub (X := KummerK3top) eImage) 2)).comp
      eImageH2EquivInt.symm.toLinearMap)

/-- **The exceptional block embeds**: the 16 zero-section classes are independent in `H₂(K3; ℤ)` —
the rank-16 half of the `b₂ = 22` accounting. -/
theorem exceptionalEmbed_injective : Function.Injective exceptionalEmbed := by
  intro v w hvw
  have h1 := k7Sum2_injective hvw
  have h2 : eImageH2EquivInt.symm v = eImageH2EquivInt.symm w :=
    congrArg Prod.snd h1
  exact eImageH2EquivInt.symm.injective h2

/-- **`Σ₄` is injective** — `H₄(collar) = 0` (degree-4 window: with `H₄(eImage) = 0`, the
`Q`-side `H₄` embeds in `H₄(K3;ℤ)`; the `[K]` fundamental-class arc reads through this). -/
theorem k7Sum4_injective :
    Function.Injective (mvHomSumInt (X := KummerK3top) qThick eImage 4) := by
  intro p q hpq
  have hker : mvHomSumInt (X := KummerK3top) qThick eImage 4 (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  obtain ⟨w, hw⟩ := (k7_exact_middle 3 (p - q)).mp hker
  rw [interH4_eq_zero w, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

/-- **`Σ₃` is surjective** — `H₂(collar) = 0` kills the outgoing connecting map. -/
theorem k7Sum3_surjective :
    Function.Surjective (mvHomSumInt (X := KummerK3top) qThick eImage 3) := fun x =>
  (k7_exact_ambient 2 x).mp (interH2_eq_zero _)

/-- **Every `H₃(K3; ℤ)` class comes from the thickened `Q`-piece alone** — the `E`-side is dead in
degree 3 (`H₃(eImage) = 0`). -/
theorem k7H3_surjective_from_qThick :
    Function.Surjective (Homology.mapInt (ambIncl (X := KummerK3top) qThick) 3) := by
  intro x
  obtain ⟨⟨u, v⟩, h⟩ := k7Sum3_surjective x
  rw [mvHomSumInt_apply, eImageH3_eq_zero v, map_zero, sub_zero] at h
  exact ⟨u, h⟩

/-- **The doubling window**: `2·H₂(K3; ℤ) ⊆ im Σ₂` — the MV cokernel of the piece classes embeds
in `H₁(collar) ≅ (ℤ/2)¹⁶`, hence has exponent 2. Together with `k7Sum2_injective` this pins
`H₂(K3; ℤ)` between the rank-22 piece block and its `2`-divisible closure. -/
theorem k7H2_two_smul_mem_range (x : Homology KummerK3top 2) :
    ∃ p, mvHomSumInt (X := KummerK3top) qThick eImage 2 p = (2 : ℤ) • x := by
  have hδ : k7Delta 1 ((2 : ℤ) • x) = 0 := by
    rw [map_smul]
    refine (LinearEquiv.map_eq_zero_iff interH1EquivInt).mp ?_
    rw [map_smul]
    funext c
    show (2 : ℤ) • (interH1EquivInt (k7Delta 1 x) c) = 0
    rw [two_smul]
    exact CharTwo.add_self_eq_zero _
  exact (k7_exact_ambient 1 ((2 : ℤ) • x)).mp hδ

/-- **The `b₂ = 22` rank window** (conditional ONLY on the open `Q`-side input `H₂(Q; ℤ) ≅ ℤ⁶`):
a rank-22 free block `ℤ⁶ × ℤ¹⁶` embeds in `H₂(K3; ℤ)` and contains `2·H₂(K3; ℤ)` — so
`H₂(K3; ℤ)` is squeezed between `ℤ²²` and its index-`2^k` overlattice. The sharp residual to
`kummerK3_b2_target` (`H₂(K3) ≅ ℤ²²` on the nose): the `Q`-side `H₂` computation and the
`δ₁`-image (extension) analysis over `H₁(collar) = (ℤ/2)¹⁶`. -/
theorem kummerK3_b2_window_of_qH2
    (hQ : Homology (TopCat.of FreeQuotient) 2 ≃ₗ[ℤ] (Fin 6 → ℤ)) :
    ∃ φ : ((Fin 6 → ℤ) × (EIndex → ℤ)) →ₗ[ℤ] Homology KummerK3top 2,
      Function.Injective φ ∧ ∀ x, ∃ v, φ v = (2 : ℤ) • x := by
  set e : ((Fin 6 → ℤ) × (EIndex → ℤ)) ≃ₗ[ℤ]
      (Homology (sub (X := KummerK3top) qThick) 2 × Homology (sub (X := KummerK3top) eImage) 2) :=
    LinearEquiv.prodCongr (hQ.symm.trans (qThickHnEquivInt 1).symm) eImageH2EquivInt.symm with he
  refine ⟨(mvHomSumInt (X := KummerK3top) qThick eImage 2).comp e.toLinearMap, ?_, ?_⟩
  · exact k7Sum2_injective.comp e.injective
  · intro x
    obtain ⟨p, hp⟩ := k7H2_two_smul_mem_range x
    exact ⟨e.symm p, by rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      e.apply_symm_apply, hp]⟩

end

end SKEFTHawking.KummerK7MVAssembly
