/-
# Phase 5q.H (W-A arm 4) — the MV overlap SUBSPACE `H_k((M∖σ)×(I∖t)) ≅ H_k(M∖σ)²`

Route-B infrastructure for the punctured-product local homology. The overlap of the two MV cover
pieces of `{x}ᶜ` (`PoincareLefschetzRelFundClassCylinderPuncturedCover.puncU_inter_puncV`) is the
doubly-punctured product `puncU x ∩ puncV x = (M∖σ) × (I∖t)`. This module computes its **subspace**
homology — the input the relative-MV LES needs at the overlap corner — by **composing the two
mechanisms**:

* the interval clopen split (`belowT ⊔ aboveT`, exactly as `puncU`), giving a ⊔-decomposition, and
* the base-deletion `M∖σ = sub({x.1}ᶜ)` carried along untouched.

Each half `(M∖σ)×belowT` deformation-retracts (endpoint-preserving straight-line interval
contraction) onto the slice `(M∖σ)×{0}`, a copy of `M∖σ`; so, ⊔-additively,

  `H_k((M∖σ)×(I∖t)) ≅ H_k(M∖σ) × H_k(M∖σ)`,  hence  `dim H_k = 2·dim H_k(M∖σ)`.

This is the reusable overlap-subspace input to any route-B closure of the interior local-Künneth
nonvanishing. (The overlap **pair** `H_k(M×I, (M∖σ)×(I∖t))` itself is NOT computed here — the pair-LES
inclusion `H_k((M∖σ)×(I∖t)) → H_k(M×I)` is `(a,b) ↦ ι_*(a)+ι_*(b)`, genuinely `M`-local-homology
data (`ι_* : H(M∖σ) → H(M)`, not onto in top degree), which is the deep δ-content left to the closer.)

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the clopen split** of `sub(overlap)` into below/above-`t` halves (`leftPieceO`).
* **§2 — each half `≃ M∖σ`**: projection/slice interval-contraction homotopy equivalences.
* **§3 — the subspace split** `overlapSubHomEquiv : H_{k+1}(sub(overlap)) ≅ H_{k+1}(M∖σ)²` and its
  finrank `= 2·dim H_{k+1}(M∖σ)`.

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
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap

noncomputable section

variable {N : TopCat}

/-- **The overlap** `puncU x ∩ puncV x = (M∖σ)×(I∖t)` (the doubly-punctured product). -/
abbrev overlap (x : ↑(cyl N)) : Set ↑(cyl N) := puncU x ∩ puncV x

/-! ## §1. The clopen split of `sub(overlap x)` into the below-`t` / above-`t` halves -/

/-- **The "below `t`" half** of `sub(overlap x)`: interval coordinate `< t = x.2`. -/
def leftPieceO (x : ↑(cyl N)) : Set ↑(sub (overlap x)) :=
  {q | ((q.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)}

theorem continuous_coordO (x : ↑(cyl N)) :
    Continuous (fun q : ↑(sub (overlap x)) => ((q.1.2 : unitInterval) : ℝ)) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

theorem isOpen_leftPieceO (x : ↑(cyl N)) : IsOpen (leftPieceO x) :=
  isOpen_Iio.preimage (continuous_coordO x)

theorem leftPieceO_compl (x : ↑(cyl N)) :
    (leftPieceO x)ᶜ = (fun q : ↑(sub (overlap x)) => ((q.1.2 : unitInterval) : ℝ)) ⁻¹' Set.Ioi (x.2 : ℝ) := by
  ext q
  have hq : (q.1.2 : unitInterval) ≠ x.2 := q.2.1
  have hqR : ((q.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hq (Subtype.ext h)
  simp only [leftPieceO, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
  rcases lt_or_gt_of_ne hqR with h | h
  · simp [not_lt.mpr h.le, h]
  · simp [not_lt_of_gt h, h]

theorem isOpen_leftPieceO_compl (x : ↑(cyl N)) : IsOpen (leftPieceO x)ᶜ := by
  rw [leftPieceO_compl]; exact isOpen_Ioi.preimage (continuous_coordO x)

theorem isClopen_leftPieceO (x : ↑(cyl N)) : IsClopen (leftPieceO x) :=
  ⟨isOpen_compl_iff.mp (isOpen_leftPieceO_compl x), isOpen_leftPieceO x⟩

/-! ## §2a. The below-`t` half `≃ M∖σ` -/

section LeftHalf

variable (x : ↑(cyl N)) (ht0 : (0 : ℝ) < (x.2 : ℝ))

/-- **The projection** `sub(leftPieceO x) → M∖σ = sub({x.1}ᶜ)`, `q ↦ q.1.1.1` (base coordinate, which
avoids `σ = x.1` since the point is in `puncV`). -/
def projLeftO : C(↑(sub (leftPieceO x)), ↑(sub ({x.1}ᶜ : Set ↑N))) := by
  refine ⟨fun q => ⟨q.1.1.1, ?_⟩, ?_⟩
  · exact q.1.2.2
  · exact Continuous.subtype_mk (continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val)) _

/-- **The bottom slice** `M∖σ → sub(leftPieceO x)`, `⟨a,ha⟩ ↦ (a, 0)` — in the overlap since `a ≠ σ`
(`ha`) and `0 ≠ t` (`ht0`). -/
def botSecLeftO : C(↑(sub ({x.1}ᶜ : Set ↑N)), ↑(sub (leftPieceO x))) := by
  refine ⟨fun a => ⟨⟨(a.1, 0), ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · show (0 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (by simpa using ne_of_lt ht0)
  · show a.1 ≠ x.1
    exact a.2
  · show ((0 : unitInterval) : ℝ) < (x.2 : ℝ)
    simpa using ht0
  · have hc : Continuous (fun a : ↑(sub ({x.1}ᶜ : Set ↑N)) => (a.1 : ↑N)) := continuous_subtype_val
    exact Continuous.subtype_mk (Continuous.subtype_mk
      (hc.prodMk continuous_const) _) _

theorem projLeftO_comp_botSecLeftO :
    (projLeftO x).comp (botSecLeftO x ht0) = ContinuousMap.id ↑(sub ({x.1}ᶜ : Set ↑N)) := rfl

/-- **The interval-contraction homotopy** on `sub(leftPieceO x)`: `H(q,u).2 = u·s`, base coordinate
fixed. -/
def leftHtpyO : C(↑(sub (leftPieceO x)) × unitInterval, ↑(sub (leftPieceO x))) := by
  refine ⟨fun p => ⟨⟨(p.1.1.1.1, p.2 * p.1.1.1.2), ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · -- ≠ x.2 (puncU)
    have hlt : ((p.2 * p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ) := by
      have hs : ((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ) := p.1.2
      have hu : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
      have hsnn : (0 : ℝ) ≤ ((p.1.1.1.2 : unitInterval) : ℝ) := unitInterval.nonneg p.1.1.1.2
      show (p.2 : ℝ) * (p.1.1.1.2 : ℝ) < (x.2 : ℝ)
      nlinarith
    show (p.2 * p.1.1.1.2 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (ne_of_lt hlt)
  · -- ≠ x.1 (puncV, base coordinate unchanged)
    exact p.1.1.2.2
  · -- ∈ leftPieceO
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

theorem slice_leftHtpyO_zero :
    slice (leftHtpyO x) 0 = (botSecLeftO x ht0).comp (projLeftO x) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (0 : unitInterval) * q.1.1.2 = (0 : unitInterval)
  rw [zero_mul]

theorem slice_leftHtpyO_one :
    slice (leftHtpyO x) 1 = ContinuousMap.id ↑(sub (leftPieceO x)) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (1 : unitInterval) * q.1.1.2 = q.1.1.2
  rw [one_mul]

include ht0 in
theorem leftHalfBijO (k : ℕ) :
    Function.Bijective (Homology.map (projLeftO x) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (projLeftO x) (botSecLeftO x ht0)
    (leftHtpyO x) (slice_leftHtpyO_zero x ht0) (slice_leftHtpyO_one x)
    (constHomotopy (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))))
    ((slice_constHomotopy _ 0).trans (projLeftO_comp_botSecLeftO x ht0).symm)
    (slice_constHomotopy _ 1) k

end LeftHalf

/-! ## §2b. The above-`t` half `(leftPieceO x)ᶜ ≃ M∖σ` -/

section RightHalf

variable (x : ↑(cyl N)) (ht1 : (x.2 : ℝ) < 1)

def projRightO : C(↑(sub (leftPieceO x)ᶜ), ↑(sub ({x.1}ᶜ : Set ↑N))) := by
  refine ⟨fun q => ⟨q.1.1.1, ?_⟩, ?_⟩
  · exact q.1.2.2
  · exact Continuous.subtype_mk (continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val)) _

def topSecRightO : C(↑(sub ({x.1}ᶜ : Set ↑N)), ↑(sub (leftPieceO x)ᶜ)) := by
  refine ⟨fun a => ⟨⟨(a.1, 1), ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · show (1 : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (by simpa using ne_of_gt ht1)
  · show a.1 ≠ x.1
    exact a.2
  · show ¬ (((1 : unitInterval) : ℝ) < (x.2 : ℝ))
    simpa using not_lt.mpr ht1.le
  · have hc : Continuous (fun a : ↑(sub ({x.1}ᶜ : Set ↑N)) => (a.1 : ↑N)) := continuous_subtype_val
    exact Continuous.subtype_mk (Continuous.subtype_mk
      (hc.prodMk continuous_const) _) _

theorem projRightO_comp_topSecRightO :
    (projRightO x).comp (topSecRightO x ht1) = ContinuousMap.id ↑(sub ({x.1}ᶜ : Set ↑N)) := rfl

def rightHtpyO : C(↑(sub (leftPieceO x)ᶜ) × unitInterval, ↑(sub (leftPieceO x)ᶜ)) := by
  refine ⟨fun p => ⟨⟨(p.1.1.1.1,
      ⟨1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ), ?_⟩), ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · have hu0 : (0 : ℝ) ≤ (p.2 : ℝ) := unitInterval.nonneg p.2
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs0 : (0 : ℝ) ≤ ((p.1.1.1.2 : unitInterval) : ℝ) := unitInterval.nonneg p.1.1.1.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    constructor <;> nlinarith
  · -- ≠ x.2 (puncU)
    have hge : ¬ (((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)) := p.1.2
    have hne : (p.1.1.1.2 : unitInterval) ≠ x.2 := p.1.1.2.1
    have hneR : ((p.1.1.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hne (Subtype.ext h)
    have hgt : (x.2 : ℝ) < ((p.1.1.1.2 : unitInterval) : ℝ) := lt_of_le_of_ne (not_lt.mp hge) hneR.symm
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    have hval : (x.2 : ℝ) < 1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((p.1.1.1.2 : unitInterval) : ℝ))
        (by linarith : (0:ℝ) ≤ 1 - ((p.2 : unitInterval) : ℝ)), hgt]
    show (⟨1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ), _⟩ : unitInterval) ≠ x.2
    exact fun h => absurd (congrArg (fun y : unitInterval => (y : ℝ)) h) (ne_of_gt hval)
  · -- ≠ x.1 (puncV, base coordinate unchanged)
    exact p.1.1.2.2
  · -- ∈ (leftPieceO x)ᶜ
    have hge : ¬ (((p.1.1.1.2 : unitInterval) : ℝ) < (x.2 : ℝ)) := p.1.2
    have hne : (p.1.1.1.2 : unitInterval) ≠ x.2 := p.1.1.2.1
    have hneR : ((p.1.1.1.2 : unitInterval) : ℝ) ≠ (x.2 : ℝ) := fun h => hne (Subtype.ext h)
    have hgt : (x.2 : ℝ) < ((p.1.1.1.2 : unitInterval) : ℝ) := lt_of_le_of_ne (not_lt.mp hge) hneR.symm
    have hu1 : ((p.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hs1 : ((p.1.1.1.2 : unitInterval) : ℝ) ≤ 1 := unitInterval.le_one p.1.1.1.2
    show ¬ ((1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ)) < (x.2 : ℝ))
    have : (x.2 : ℝ) < 1 - (p.2 : ℝ) + (p.2 : ℝ) * (p.1.1.1.2 : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((p.1.1.1.2 : unitInterval) : ℝ))
        (by linarith : (0:ℝ) ≤ 1 - ((p.2 : unitInterval) : ℝ)), hgt]
    exact not_lt.mpr this.le
  · refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ (Continuous.subtype_mk ?_ _)) _) _
    · exact continuous_fst.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_fst))
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_fst)))))

theorem slice_rightHtpyO_zero :
    slice (rightHtpyO x) 0 = (topSecRightO x ht1).comp (projRightO x) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  apply Subtype.ext
  show 1 - ((0 : unitInterval) : ℝ) + ((0 : unitInterval) : ℝ) * (q.1.1.2 : ℝ) = ((1 : unitInterval) : ℝ)
  norm_num

theorem slice_rightHtpyO_one :
    slice (rightHtpyO x) 1 = ContinuousMap.id ↑(sub (leftPieceO x)ᶜ) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  apply Subtype.ext
  show 1 - ((1 : unitInterval) : ℝ) + ((1 : unitInterval) : ℝ) * (q.1.1.2 : ℝ) = (q.1.1.2 : ℝ)
  norm_num

include ht1 in
theorem rightHalfBijO (k : ℕ) :
    Function.Bijective (Homology.map (projRightO x) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (projRightO x) (topSecRightO x ht1)
    (rightHtpyO x) (slice_rightHtpyO_zero x ht1) (slice_rightHtpyO_one x)
    (constHomotopy (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))))
    ((slice_constHomotopy _ 0).trans (projRightO_comp_topSecRightO x ht1).symm)
    (slice_constHomotopy _ 1) k

end RightHalf

/-! ## §3. The overlap subspace split `H_{k+1}(sub(overlap x)) ≅ H_{k+1}(M∖σ)²` -/

section Assemble

variable (x : ↑(cyl N)) (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)

include ht0 ht1 in
/-- **The overlap subspace homology splits as `H_{k+1}(M∖σ)²`.** Clopen split of `sub(overlap x)`
into the two half-open pieces, each identified with `M∖σ = sub({x.1}ᶜ)` by the interval contraction. -/
noncomputable def overlapSubHomEquiv (k : ℕ) :
    Homology (sub (overlap x)) (k + 1) ≃ₗ[ZMod 2]
      Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1)
        × Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1) :=
  (splitHnEquiv (isClopen_leftPieceO x) (k + 1)).symm.trans
    (LinearEquiv.prodCongr
      (LinearEquiv.ofBijective (Homology.map (projLeftO x) (k + 1)) (leftHalfBijO x ht0 k))
      (LinearEquiv.ofBijective (Homology.map (projRightO x) (k + 1)) (rightHalfBijO x ht1 k)))

include ht0 ht1 in
/-- **The overlap subspace finrank** `dim H_{k+1}(sub(overlap x)) = 2·dim H_{k+1}(M∖σ)`. -/
theorem finrank_overlapSubHom (k : ℕ)
    [FiniteDimensional (ZMod 2) (Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1))] :
    Module.finrank (ZMod 2) (Homology (sub (overlap x)) (k + 1))
      = 2 * Module.finrank (ZMod 2) (Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1)) := by
  rw [(overlapSubHomEquiv x ht0 ht1 k).finrank_eq, Module.finrank_prod]; omega

include ht0 ht1 in
theorem finiteDimensional_overlapSubHom (k : ℕ)
    [FiniteDimensional (ZMod 2) (Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1))] :
    FiniteDimensional (ZMod 2) (Homology (sub (overlap x)) (k + 1)) :=
  (overlapSubHomEquiv x ht0 ht1 k).symm.finiteDimensional

end Assemble

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
