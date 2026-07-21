/-
# Phase 5q.H — K6′b Leg 15: the SEAM ↔ SEAM transition class (3,3)

Step 5 of the weld atlas is a 3×3 transition dispatch on the flat model `𝓔³ × ℝ`.
`KummerInteriorManifold` closed the two interior diagonals (1,1), (2,2) and the vacuous interior
off-diagonal (1,2). This module closes **(3,3)** — seam chart against seam chart — and records the
`symm` mirror **(2,1)** of the vacuous class.

**Why (3,3) needs no collar smoothness.** The seam chart is by construction

    seamChart c r₀ = (seamParamHomeo c).symm ≫ₕ ((chartAt 𝓔³ r₀).prod paramChart),

i.e. the *inverse* of an open embedding `ℝP³ × (−1/8, 1/2) ↪ K3` followed by a chart of the
**product manifold** `ℝP³ × (−1/8, 1/2)`. So for a fixed component `c` the two seam charts differ
only in their product-manifold chart, and

    (S.symm ≫ₕ A).symm ≫ₕ (S.symm ≫ₕ A')  =  A.symm ≫ₕ ((S ≫ₕ S.symm) ≫ₕ A')  ≈  A.symm ≫ₕ A'

because `S.source = univ` (`OpenPartialHomeomorph.self_trans_symm`). The right-hand side is a
coordinate change of the product manifold `ℝP³ × (−1/8, 1/2)`, hence `C^k` by
`StructureGroupoid.compatible` — the `ℝP³` factor from `KummerRP3Smooth.isManifold_rp3`, the
interval factor from the single-chart `paramChart` (§1). The model identification is
`ManifoldModelTransport.model_prod3Real_eq : (𝓡 3).prod 𝓘(ℝ,ℝ) = 𝓘(ℝ, 𝓔³ × ℝ)`.

**Distinct components (§3).** For `c ≠ c'` the transition is *vacuous*: the sixteen component
neighbourhoods are pairwise disjoint. The Q sides are collars of chart radius `< 5/8` around fixed
points that are `2` apart (`disjoint_qOpenCollarSet`, via `fixedSet_dist_ge` and the
`τ`-isometry step of `KummerSeamComponentOpen`); the E sides are distinct copies; and the only
cross identifications the weld makes are seam joins, which `seam_separation` pins to a single
component.

**Score after this module: 5 of the 9 ordered transition classes.** (1,1), (2,2), (1,2), (2,1),
(3,3). The four that remain — (1,3), (3,1), (2,3), (3,2), i.e. two up to `symm` — are exactly the
ones that need the *thickened* collar smoothness (`KummerSeamCollarSmooth` supplies its chart-level
product core; the inverse direction is not built). Nothing here is blocked on them.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamChart
import SKEFTHawking.ManifoldModelTransport
import SKEFTHawking.HalfSpaceInteriorFlatten
import SKEFTHawking.KummerInteriorManifold

namespace SKEFTHawking.KummerSeamTransition

open Set Topology
open scoped Manifold
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerResolutionPiece (RP3)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerRP3Smooth (E3)
open SKEFTHawking.KummerSeamChart
open SKEFTHawking.HalfSpaceInteriorFlatten (FModel)
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamOpenNbhd
open SKEFTHawking.KummerSeamComponentOpen

noncomputable section

variable {k : WithTop ℕ∞}

/-- The single-chart charted space on the open collar parameter interval. -/
local instance instChartedSpaceOpenParam : ChartedSpace ℝ ↥openParam :=
  paramChart.singletonChartedSpace rfl

theorem paramChart_mem_atlas : paramChart ∈ atlas ℝ ↥openParam := rfl

local instance instIsManifoldOpenParam (k : WithTop ℕ∞) : IsManifold 𝓘(ℝ, ℝ) k ↥openParam := by
  haveI := paramChart.singleton_hasGroupoid (rfl : paramChart.source = univ)
    (contDiffGroupoid k 𝓘(ℝ, ℝ))
  exact IsManifold.mk' _ _ _

/-- The seam chart's model block, as a chart of the product manifold `ℝP³ × (−1/8, 1/2)`. -/
def seamModelChart (r₀ : RP3) : OpenPartialHomeomorph (RP3 × ↥openParam) FModel :=
  (chartAt E3 r₀).prod paramChart

theorem seamChart_eq (c : EIndex) (r₀ : RP3) :
    seamChart c r₀ = (seamParamHomeo c).symm.trans (seamModelChart r₀) := rfl

theorem seamModelChart_mem_atlas (r₀ : RP3) :
    seamModelChart r₀ ∈ atlas (ModelProd E3 ℝ) (RP3 × ↥openParam) :=
  Set.mem_image2_of_mem (chart_mem_atlas E3 r₀) paramChart_mem_atlas

theorem mem_contDiffGroupoid_seamModelChart (r₀ r₀' : RP3) :
    ((seamModelChart r₀).symm.trans (seamModelChart r₀')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  haveI : IsManifold (𝓡 3) k RP3 := SKEFTHawking.KummerRP3Smooth.isManifold_rp3
  have h : ((seamModelChart r₀).symm.trans (seamModelChart r₀'))
      ∈ contDiffGroupoid k ((𝓡 3).prod 𝓘(ℝ, ℝ)) :=
    StructureGroupoid.compatible _ (seamModelChart_mem_atlas r₀) (seamModelChart_mem_atlas r₀')
  rwa [ManifoldModelTransport.model_prod3Real_eq] at h

theorem self_trans_symm_seamParamHomeo (c : EIndex) :
    (seamParamHomeo c).trans (seamParamHomeo c).symm
      ≈ OpenPartialHomeomorph.refl (RP3 × ↥openParam) :=
  (seamParamHomeo c).self_trans_symm

theorem eqOnSource_seamTransition (c : EIndex) (r₀ r₀' : RP3) :
    ((seamChart c r₀).symm.trans (seamChart c r₀'))
      ≈ ((seamModelChart r₀).symm.trans (seamModelChart r₀')) := by
  have key : (seamChart c r₀).symm.trans (seamChart c r₀')
      = (seamModelChart r₀).symm.trans
          (((seamParamHomeo c).trans (seamParamHomeo c).symm).trans (seamModelChart r₀')) := by
    rw [seamChart_eq, seamChart_eq, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc (seamParamHomeo c)]
  rw [key]
  refine OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _) ?_
  have h1 : ((seamParamHomeo c).trans (seamParamHomeo c).symm).trans (seamModelChart r₀')
      ≈ (OpenPartialHomeomorph.refl (RP3 × ↥openParam)).trans (seamModelChart r₀') :=
    OpenPartialHomeomorph.EqOnSource.trans' (self_trans_symm_seamParamHomeo c) (Setoid.refl _)
  rwa [OpenPartialHomeomorph.refl_trans] at h1

theorem mem_contDiffGroupoid_seamFam_same (c : EIndex) (r₀ r₀' : RP3) :
    ((seamChart c r₀).symm.trans (seamChart c r₀')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) :=
  (contDiffGroupoid k 𝓘(ℝ, FModel)).mem_of_eqOnSource
    (mem_contDiffGroupoid_seamModelChart r₀ r₀') (eqOnSource_seamTransition c r₀ r₀')

/-! ## §3. Distinct components have disjoint collars -/

theorem disjoint_qOpenCollarSet {c c' : EIndex} (h : c ≠ c') :
    Disjoint (qOpenCollarSet c) (qOpenCollarSet c') := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
  have hdc : dist (z : TorusFour) c.1 < 5 / 8 := dist_lt_of_mem_qOpenBall hz
  have hdc' : dist (z' : TorusFour) c'.1 < 5 / 8 := dist_lt_of_mem_qOpenBall hz'
  have hd : dist (z : TorusFour) c'.1 < 5 / 8 := by
    rcases (qmk_eq_iff z' z).mp hzz' with rfl | hτ
    · exact hdc'
    · have hzz : (z' : TorusFour) = torusFourInvolution (z : TorusFour) := by
        rw [hτ]; exact neg_one_smul_val z
      rw [hzz, dist_involution_fixed (eIndex_fixedSet c')] at hdc'
      exact hdc'
  have hsep : (2 : ℝ) ≤ dist c.1 c'.1 :=
    fixedSet_dist_ge (eIndex_fixedSet c) (eIndex_fixedSet c') (fun hc => h (Subtype.ext hc))
  have htri : dist c.1 c'.1 ≤ dist c.1 (z : TorusFour) + dist (z : TorusFour) c'.1 :=
    dist_triangle _ _ _
  rw [dist_comm c.1 (z : TorusFour)] at htri
  linarith

theorem disjoint_seamCompNbhd {c c' : EIndex} (h : c ≠ c') :
    Disjoint (seamCompNbhd c) (seamCompNbhd c') := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  rcases ha with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩ <;> rcases hb with ⟨q', hq', rfl⟩ | ⟨p', hp', rfl⟩
  · exact Set.disjoint_left.mp (disjoint_qOpenCollarSet h) hq
      (weldMk_inl_injective hab ▸ hq')
  · rcases Quotient.exact hab with he | ⟨_, _, h1, _⟩ | ⟨c₀, r₀, h1, h2⟩
    · exact absurd he (by simp)
    · exact absurd h1 (by simp)
    · have hq0 : q = qBdryMap c₀ r₀ := Sum.inl.inj h1
      have hc0 : p'.1 = c₀ := congrArg Prod.fst (Sum.inr.inj h2)
      exact h (((hp'.1 : p'.1 ∈ ({c'} : Set EIndex))).symm.trans
        (hc0.trans (seam_separation (hq0 ▸ hq)))).symm
  · rcases Quotient.exact hab with he | ⟨c₀, r₀, h1, h2⟩ | ⟨_, _, h1, _⟩
    · exact absurd he (by simp)
    · have hq0 : q' = qBdryMap c₀ r₀ := Sum.inl.inj h1
      have hc0 : p.1 = c₀ := congrArg Prod.fst (Sum.inr.inj h2)
      exact h ((hp.1 : p.1 ∈ ({c} : Set EIndex)).symm.trans
        (hc0.trans (seam_separation (hq0 ▸ hq'))))
    · exact absurd h1 (by simp)
  · have hpp : p' = p := weldMk_inr_injective hab
    exact h ((hp.1 : p.1 ∈ ({c} : Set EIndex)).symm.trans
      (congrArg Prod.fst hpp.symm ▸ (hp'.1 : p'.1 ∈ ({c'} : Set EIndex))))

/-! ## §4. Class (3,3) -/

theorem source_empty_seamFam_ne {c c' : EIndex} (h : c ≠ c') (r₀ r₀' : RP3) :
    ((seamChart c r₀).symm.trans (seamChart c' r₀')).source = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (seamChart c r₀).symm x ∈ (seamChart c r₀).source :=
    (seamChart c r₀).map_target hx1
  exact Set.disjoint_left.mp (disjoint_seamCompNbhd h)
    (seamChart_source_subset c r₀ h1) (seamChart_source_subset c' r₀' hx2)

/-- **CLASS (3,3) CLOSED** — any two seam charts of the weld atlas have a `C^k` transition on the
flat model `𝓔³ × ℝ`. -/
theorem mem_contDiffGroupoid_seamFam (c c' : EIndex) (r₀ r₀' : RP3) :
    ((seamChart c r₀).symm.trans (seamChart c' r₀')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  by_cases h : c = c'
  · subst h
    exact mem_contDiffGroupoid_seamFam_same c r₀ r₀'
  · exact SKEFTHawking.KummerInteriorManifold.mem_groupoid_of_source_empty
      (source_empty_seamFam_ne h r₀ r₀')

/-! ## §5. Class (2,1) — the mirror of the vacuous interior off-diagonal class -/

/-- **CLASS (2,1) CLOSED** — the mirror of `KummerInteriorManifold.mem_contDiffGroupoid_eFam_trans_qFam`.
A structure groupoid is closed under `symm`, and `(e.symm ≫ₕ f).symm = f.symm ≫ₕ e`; so the
Q-interior ↔ E-interior transition is `C^k` because the E-interior ↔ Q-interior one is. -/
theorem mem_contDiffGroupoid_qFam_trans_eFam (c : EIndex)
    (y : ↥SKEFTHawking.KummerWeldOpenPieces.interiorE)
    (y' : ↥SKEFTHawking.KummerWeldQInterior.interiorQ) :
    ((SKEFTHawking.KummerK3Chart.qFamChart y').symm.trans
      (SKEFTHawking.KummerK3Chart.eFamChart c y)) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  have h := (contDiffGroupoid k 𝓘(ℝ, FModel)).symm
    (SKEFTHawking.KummerInteriorManifold.mem_contDiffGroupoid_eFam_trans_qFam
      (k := k) c y y')
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] at h

end

end SKEFTHawking.KummerSeamTransition
