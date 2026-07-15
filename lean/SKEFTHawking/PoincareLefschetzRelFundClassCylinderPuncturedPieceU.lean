/-
# Phase 5q.H (W-A arm 4) — the `puncU` MV piece `H_{k+2}(M×I, M×(I∖t)) ≅ H_{k+1}(M)` (finrank)

Route-B infrastructure for the punctured-product local homology. Of the two pieces of the MV cover
of `{x}ᶜ` (`PoincareLefschetzRelFundClassCylinderPuncturedCover`), the `I`-punctured piece
`puncU x = M × (I∖{t})` has the DISCONNECTED interval factor. At an interior point (`0 < t < 1`) the
punctured interval `I∖{t}` clopen-splits into the two half-open pieces `belowT = [0,t)` and
`aboveT = (t,1]`, each of which deformation-retracts (straight-line, endpoint-preserving) to a slice
`M×{0}` resp. `M×{1}`. So the subspace `sub(puncU x)` splits, ⊔-additively, as `H_k(M)²`, and the
bottom-slice inclusion makes `homIncl : H_k(sub(puncU x)) → H_k(M×I)` a surjection. The generic
pair-LES rank count `finrank_relHom_of_homIncl_surj` (Suspension §3) then gives

  `dim H_{k+2}(M×I, M×(I∖t)) = dim H_{k+1}(sub(puncU x)) − dim H_{k+1}(M×I) = 2·b_{k+1} − b_{k+1}
     = b_{k+1} = dim H_{k+1}(M)`.

This is the `puncU` (interval-suspension) input to the relative-MV LES dimension count — the mirror,
one dimension up, of `SingularIntervalPairClass.finrank_intervalLocalPair` (`dim H_1(I,I∖t) = 1`).

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the clopen split of `sub(puncU x)`** into `leftPieceU`/`(leftPieceU)ᶜ` (below/above `t`).
* **§2 — each half `≃ M`**: the projection/bottom-(top-)slice homotopy equivalences `leftHalfBij`,
  `rightHalfBij` (interval-contraction, endpoint-preserving), giving `H_{k+1}(half) ≅ H_{k+1}(M)`.
* **§3 — the subspace split** `puncUSubHomEquiv : H_{k+1}(sub(puncU x)) ≅ H_{k+1}(M)²` and its
  finrank `= 2·b_{k+1}`.
* **§4 — `homIncl` surjectivity** (via the left half being a homology iso onto `M×I`) and the
  **pair-LES finrank count** `cylinder_puncU_relHom_finrank : dim H_{k+2}(M×I, puncU x) = b_{k+1}`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularPairLES
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU

noncomputable section

variable {N : TopCat}

/-! ## §1. The clopen split of `sub(puncU x)` into the below-`t` / above-`t` halves -/

/-- **The "below `t`" half** of `sub(puncU x)`: the points of the punctured product whose interval
coordinate is `< t = x.2`. -/
def leftPieceU (x : ↑(cyl N)) : Set ↑(sub (puncU x)) :=
  {q | ((q.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)}

/-- The interval coordinate `↥(sub(puncU x)) → ℝ` is continuous. -/
theorem continuous_coordU (x : ↑(cyl N)) :
    Continuous (fun q : ↑(sub (puncU x)) => ((q.1.2 : unitInterval) : ℝ)) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

theorem isOpen_leftPieceU (x : ↑(cyl N)) : IsOpen (leftPieceU x) :=
  isOpen_Iio.preimage (continuous_coordU x)

/-- **The complement of `leftPieceU x` is the above-`t` half** `{q | t < q.1.2}` (pulled back): every
point of the punctured product has interval coordinate `≠ t`, so either `< t` or `> t`. -/
theorem leftPieceU_compl (x : ↑(cyl N)) :
    (leftPieceU x)ᶜ = (fun q : ↑(sub (puncU x)) => ((q.1.2 : unitInterval) : ℝ)) ⁻¹' Set.Ioi (x.2 : ℝ) := by
  ext q
  have hq : (q.1.2 : unitInterval) ≠ x.2 := q.2
  have hqR : ((q.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hq (Subtype.ext h)
  simp only [leftPieceU, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
  rcases lt_or_gt_of_ne hqR with h | h
  · simp [not_lt.mpr h.le, h]
  · simp [not_lt_of_gt h, h]

theorem isOpen_leftPieceU_compl (x : ↑(cyl N)) : IsOpen (leftPieceU x)ᶜ := by
  rw [leftPieceU_compl]
  exact isOpen_Ioi.preimage (continuous_coordU x)

theorem isClopen_leftPieceU (x : ↑(cyl N)) : IsClopen (leftPieceU x) :=
  ⟨isOpen_compl_iff.mp (isOpen_leftPieceU_compl x), isOpen_leftPieceU x⟩

/-! ## §2a. The below-`t` half `≃ M` (bottom-slice interval contraction) -/

section LeftHalf

variable (x : ↑(cyl N)) (ht0 : (0 : ℝ) < (x.2 : ℝ))

/-- **The projection** `sub(leftPieceU x) → M`, `q ↦ q.1.1.1` (the base coordinate). -/
def projLeft : C(↑(sub (leftPieceU x)), ↑N) :=
  ⟨fun q => q.1.1.1,
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- **The bottom slice** `M → sub(leftPieceU x)`, `a ↦ (a, 0)`. Lands in `leftPieceU` since `0 < t`. -/
def botSecLeft : C(↑N, ↑(sub (leftPieceU x))) := by
  refine ⟨fun a => ⟨⟨(a, 0), ?_⟩, ?_⟩, ?_⟩
  · show (0 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (by simpa using ne_of_lt ht0)
  · show ((0 : unitInterval) : ℝ) < (x.2 : ℝ)
    simpa using ht0
  · exact Continuous.subtype_mk (Continuous.subtype_mk (continuous_id.prodMk continuous_const) _) _

/-- The bottom slice is a section of the projection: `projLeft ∘ botSecLeft = id_M`. -/
theorem projLeft_comp_botSecLeft :
    (projLeft x).comp (botSecLeft x ht0) = ContinuousMap.id ↑N := rfl

/-- **The interval-contraction homotopy** on `sub(leftPieceU x)`: `H(q,u) = (q.1.1.1, u·q.1.1.2)` —
straight-line to the bottom endpoint, endpoint-preserving (`u·s ≤ s < t`). `slice 0 =
botSecLeft ∘ projLeft`, `slice 1 = id`. -/
def leftHtpy : C(↑(sub (leftPieceU x)) × unitInterval, ↑(sub (leftPieceU x))) := by
  refine ⟨fun p => ⟨⟨(p.1.1.1.1, p.2 * p.1.1.1.2), ?_⟩, ?_⟩, ?_⟩
  · -- ≠ x.2
    have hlt : ((p.2 * p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ) := by
      have hs : ((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ) := p.1.2
      have hu : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
      have hsnn : (0 : ℝ) ≤ ((p.1.1.1.2 : unitInterval) : ℝ) := unitInterval.nonneg p.1.1.1.2
      show (p.2 : ℝ) * (p.1.1.1.2 : ℝ) < (x.2 : ℝ)
      nlinarith
    show (p.2 * p.1.1.1.2 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (ne_of_lt hlt)
  · -- ∈ leftPieceU
    show ((p.2 * p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)
    have hs : ((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ) := p.1.2
    have hu : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hsnn : (0 : ℝ) ≤ ((p.1.1.1.2 : unitInterval) : ℝ) := unitInterval.nonneg p.1.1.1.2
    show (p.2 : ℝ) * (p.1.1.1.2 : ℝ) < (x.2 : ℝ)
    nlinarith
  · -- continuity
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _) _
    · exact continuous_fst.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_fst))
    · exact ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_fst))))).subtype_mk _

theorem slice_leftHtpy_zero :
    slice (leftHtpy x) 0 = (botSecLeft x ht0).comp (projLeft x) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (0 : unitInterval) * q.1.1.2 = (0 : unitInterval)
  rw [zero_mul]

theorem slice_leftHtpy_one :
    slice (leftHtpy x) 1 = ContinuousMap.id ↑(sub (leftPieceU x)) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (1 : unitInterval) * q.1.1.2 = q.1.1.2
  rw [one_mul]

include ht0 in
/-- **The below-`t` half is a homology iso onto `M`** (positive degree): `H_{k+1}(sub(leftPieceU x))
→ H_{k+1}(M)` via the projection is bijective (interval contraction). -/
theorem leftHalfBij (k : ℕ) :
    Function.Bijective (Homology.map (projLeft x) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (projLeft x) (botSecLeft x ht0)
    (leftHtpy x) (slice_leftHtpy_zero x ht0) (slice_leftHtpy_one x)
    (constHomotopy N)
    ((slice_constHomotopy N 0).trans (projLeft_comp_botSecLeft x ht0).symm)
    (slice_constHomotopy N 1) k

end LeftHalf

/-! ## §2b. The above-`t` half `(leftPieceU x)ᶜ ≃ M` (top-slice interval contraction) -/

section RightHalf

variable (x : ↑(cyl N)) (ht1 : (x.2 : ℝ) < 1)

/-- **The projection** `sub((leftPieceU x)ᶜ) → M`, `q ↦ q.1.1.1`. -/
def projRight : C(↑(sub (leftPieceU x)ᶜ), ↑N) :=
  ⟨fun q => q.1.1.1,
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- **The top slice** `M → sub((leftPieceU x)ᶜ)`, `a ↦ (a, 1)`. Lands in `(leftPieceU x)ᶜ` since
`t < 1` (so `¬(1 < t)`). -/
def topSecRight : C(↑N, ↑(sub (leftPieceU x)ᶜ)) := by
  refine ⟨fun a => ⟨⟨(a, 1), ?_⟩, ?_⟩, ?_⟩
  · show (1 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (by simpa using ne_of_gt ht1)
  · show ¬ (((1 : unitInterval) : ℝ) < (x.2 : ℝ))
    simpa using not_lt.mpr ht1.le
  · exact Continuous.subtype_mk (Continuous.subtype_mk (continuous_id.prodMk continuous_const) _) _

theorem projRight_comp_topSecRight :
    (projRight x).comp (topSecRight x ht1) = ContinuousMap.id ↑N := rfl

/-- **The interval-contraction homotopy** on `sub((leftPieceU x)ᶜ)`: `H(q,u).2 = 1 − u·(1 − s)` —
straight-line to the top endpoint, endpoint-preserving (`1 − u(1−s) ≥ s > t`). `slice 0 =
topSecRight ∘ projRight`, `slice 1 = id`. -/
def rightHtpy : C(↑(sub (leftPieceU x)ᶜ) × unitInterval, ↑(sub (leftPieceU x)ᶜ)) := by
  refine ⟨fun p => ⟨⟨(p.1.1.1.1,
      ⟨1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ), ?_⟩), ?_⟩, ?_⟩, ?_⟩
  · -- ∈ unitInterval
    have hu0 : (0 : ℝ) ≤ (p.2 : ℝ) := unitInterval.nonneg p.2
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs0 : (0 : ℝ) ≤ ((p.1.1.1.2 : unitInterval) : ℝ) := unitInterval.nonneg p.1.1.1.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    constructor <;> nlinarith
  · -- ≠ x.2
    have hge : ¬ (((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)) := p.1.2
    have hne : (p.1.1.1.2 : unitInterval) ≠ x.2 := p.1.1.2
    have hneR : ((p.1.1.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hne (Subtype.ext h)
    have hgt : (x.2 : ℝ) < ((p.1.1.1.2 : unitInterval) : ℝ) := lt_of_le_of_ne (not_lt.mp hge) hneR.symm
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    have hval : (x.2 : ℝ) < 1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((p.1.1.1.2 : unitInterval) : ℝ))
        (by linarith : (0:ℝ) ≤ 1 - ((p.2 : unitInterval) : ℝ)), hgt]
    show (⟨1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ), _⟩ : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (ne_of_gt hval)
  · -- ∈ (leftPieceU x)ᶜ
    have hge : ¬ (((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)) := p.1.2
    have hne : (p.1.1.1.2 : unitInterval) ≠ x.2 := p.1.1.2
    have hneR : ((p.1.1.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hne (Subtype.ext h)
    have hgt : (x.2 : ℝ) < ((p.1.1.1.2 : unitInterval) : ℝ) := lt_of_le_of_ne (not_lt.mp hge) hneR.symm
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    show ¬ ((1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ)) < (x.2 : ℝ))
    have : (x.2 : ℝ) < 1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((p.1.1.1.2 : unitInterval) : ℝ))
        (by linarith : (0:ℝ) ≤ 1 - ((p.2 : unitInterval) : ℝ)), hgt]
    exact not_lt.mpr this.le
  · -- continuity
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ (Continuous.subtype_mk ?_ _)) _) _
    · exact continuous_fst.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_fst))
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_fst)))))

theorem slice_rightHtpy_zero :
    slice (rightHtpy x) 0 = (topSecRight x ht1).comp (projRight x) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  apply Subtype.ext
  show 1 - ((0 : unitInterval) : ℝ) + ((0 : unitInterval) : ℝ) * (q.1.1.2 : ℝ) = ((1 : unitInterval) : ℝ)
  norm_num

theorem slice_rightHtpy_one :
    slice (rightHtpy x) 1 = ContinuousMap.id ↑(sub (leftPieceU x)ᶜ) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  apply Subtype.ext
  show 1 - ((1 : unitInterval) : ℝ) + ((1 : unitInterval) : ℝ) * (q.1.1.2 : ℝ) = (q.1.1.2 : ℝ)
  norm_num

include ht1 in
/-- **The above-`t` half is a homology iso onto `M`** (positive degree): `H_{k+1}(sub((leftPieceU x)ᶜ))
→ H_{k+1}(M)` via the projection is bijective (interval contraction). -/
theorem rightHalfBij (k : ℕ) :
    Function.Bijective (Homology.map (projRight x) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (projRight x) (topSecRight x ht1)
    (rightHtpy x) (slice_rightHtpy_zero x ht1) (slice_rightHtpy_one x)
    (constHomotopy N)
    ((slice_constHomotopy N 0).trans (projRight_comp_topSecRight x ht1).symm)
    (slice_constHomotopy N 1) k

end RightHalf

/-! ## §3. The subspace split `H_{k+1}(sub(puncU x)) ≅ H_{k+1}(M)²` -/

section Assemble

variable (x : ↑(cyl N)) (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)

include ht0 ht1 in
/-- **The `puncU` subspace homology splits as `H_{k+1}(M)²`.** The clopen split (`splitHnEquiv`) of
`sub(puncU x)` into the two half-open pieces, each identified with `M` (`leftHalfBij`/`rightHalfBij`,
interval contraction). -/
noncomputable def puncUSubHomEquiv (k : ℕ) :
    Homology (sub (puncU x)) (k + 1) ≃ₗ[ZMod 2] Homology N (k + 1) × Homology N (k + 1) :=
  (splitHnEquiv (isClopen_leftPieceU x) (k + 1)).symm.trans
    (LinearEquiv.prodCongr
      (LinearEquiv.ofBijective (Homology.map (projLeft x) (k + 1)) (leftHalfBij x ht0 k))
      (LinearEquiv.ofBijective (Homology.map (projRight x) (k + 1)) (rightHalfBij x ht1 k)))

include ht0 ht1 in
theorem finrank_puncUSubHom (k : ℕ) [FiniteDimensional (ZMod 2) (Homology N (k + 1))] :
    Module.finrank (ZMod 2) (Homology (sub (puncU x)) (k + 1))
      = 2 * Module.finrank (ZMod 2) (Homology N (k + 1)) := by
  rw [(puncUSubHomEquiv x ht0 ht1 k).finrank_eq, Module.finrank_prod]; omega

include ht0 ht1 in
theorem finiteDimensional_puncUSubHom (k : ℕ) [FiniteDimensional (ZMod 2) (Homology N (k + 1))] :
    FiniteDimensional (ZMod 2) (Homology (sub (puncU x)) (k + 1)) :=
  (puncUSubHomEquiv x ht0 ht1 k).symm.finiteDimensional

/-! ## §4. `homIncl` surjectivity and the pair-LES finrank count -/

include ht0 in
/-- **The subspace inclusion is a homology surjection** (positive degree): `homIncl :
H_{k+1}(sub(puncU x)) → H_{k+1}(M×I)` is onto. The below-`t` half `sub(leftPieceU x)` maps by a
homology iso onto `M×I` (its projection composes to the collapse `prodFst`, both bijective), and that
inclusion factors through `sub(puncU x)`, so `homIncl` is onto — the `puncU` mirror of
`homIncl_boundary_surjective`. -/
theorem homIncl_puncU_surjective (k : ℕ) :
    Function.Surjective (homIncl (X := cyl N) (puncU x) (k + 1)) := by
  set ιU : C(↑(sub (leftPieceU x)), ↑(sub (puncU x))) := subInclCM (leftPieceU x) with hιU
  set ιS : C(↑(sub (puncU x)), ↑(cyl N)) := subInclCM (puncU x) with hιS
  have hcomp : (prodFst N (TopCat.of unitInterval)).comp (ιS.comp ιU) = projLeft x := by
    apply ContinuousMap.ext; intro q; rfl
  have hbij_prodFst : Function.Bijective
      (Homology.map (prodFst N (TopCat.of unitInterval)) (k + 1)) :=
    prodFst_homology_bijective N (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one k
  have hbij_projLeft : Function.Bijective (Homology.map (projLeft x) (k + 1)) := leftHalfBij x ht0 k
  have hbij_comp : Function.Bijective (Homology.map (ιS.comp ιU) (k + 1)) := by
    have hmapcomp :
        (Homology.map (prodFst N (TopCat.of unitInterval)) (k + 1)).comp
          (Homology.map (ιS.comp ιU) (k + 1)) = Homology.map (projLeft x) (k + 1) := by
      rw [← Homology.map_comp, hcomp]
    have hcompbij : Function.Bijective
        (⇑(Homology.map (prodFst N (TopCat.of unitInterval)) (k + 1))
          ∘ ⇑(Homology.map (ιS.comp ιU) (k + 1))) := by
      rw [← LinearMap.coe_comp, hmapcomp]; exact hbij_projLeft
    exact (hbij_prodFst.of_comp_iff' _).mp hcompbij
  have hdecomp : Homology.map (ιS.comp ιU) (k + 1)
      = (homIncl (puncU x) (k + 1)).comp (Homology.map ιU (k + 1)) := by
    rw [Homology.map_comp, homIncl_eq_map]
  have hsurj_comp : Function.Surjective (Homology.map (ιS.comp ιU) (k + 1)) := hbij_comp.surjective
  rw [hdecomp, LinearMap.coe_comp] at hsurj_comp
  exact hsurj_comp.of_comp

include ht0 ht1 in
/-- **The `puncU` pair-LES DIMENSION count** `dim H_{k+2}(M×I, M×(I∖t)) = dim H_{k+1}(M)`. The
pair-LES rank count (`finrank_relHom_of_homIncl_surj`, via `homIncl` surjectivity §4) gives
`dim H_{k+2}(M×I, puncU) = dim H_{k+1}(sub(puncU x)) − dim H_{k+1}(M×I)`; the split (§3) makes the
subspace `2·b_{k+1}` and the contractible-factor collapse makes `H_{k+1}(M×I) = b_{k+1}`, so the count
is `2·b − b = b`. This is the interval-suspension `puncU` input to the relative-MV LES. -/
theorem cylinder_puncU_relHom_finrank (k : ℕ)
    [FiniteDimensional (ZMod 2) (Homology N (k + 1))] :
    Module.finrank (ZMod 2) (RelativeHomology (X := cyl N) (puncU x) (k + 2))
      = Module.finrank (ZMod 2) (Homology N (k + 1)) := by
  have hcollapse : Module.finrank (ZMod 2) (Homology (cyl N) (k + 1))
      = Module.finrank (ZMod 2) (Homology N (k + 1)) :=
    (prodContractibleHomologyEquiv N (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one k).finrank_eq
  rw [finrank_relHom_of_homIncl_surj (X := cyl N) (puncU x) (k + 1)
      (finiteDimensional_puncUSubHom x ht0 ht1 k)
      (homIncl_puncU_surjective x ht0 k) (homIncl_puncU_surjective x ht0 (k + 1)),
    finrank_puncUSubHom x ht0 ht1 k, hcollapse]
  omega

end Assemble

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU
