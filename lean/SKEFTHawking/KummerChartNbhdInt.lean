/-
# Phase 5q.H — the OPEN two-chart cover of `E`, and the chart-0 excision of the `b₂` residual

`KummerCollarPairSplitInt` reduced the `b₂` residual to two chart-local inputs about
`B = outerE ∪ chart1Set`. That `B` is the right *idea* but the wrong *set*: the two closed chart
regions `chart0Set`, `chart1Set` meet only along the base equator, so neither has the equator in its
interior and the excision hypothesis
`interior A ∪ interior B = univ` **fails** on the seam. Excision needs an honest open cover.

This module builds one. For a radius `r < 1`,

* `deepChart1 r = chart1 '' {‖z‖ ≤ r}` is the part of chart 1 strictly away from the seam. It is
  **closed** and — the load-bearing point — it is **saturated**: no chart-0 point lies in it, because
  a weld forces `‖z‖ = 1 > r` (`preimage_deepChart1`). Hence its `Quotient.mk` preimage is just
  `Sum.inr '' {‖z‖ ≤ r}` and closedness is inherited from the chart.
* `chartNbhd0 r = (deepChart1 r)ᶜ` and `chartNbhd1 r = (deepChart0 r)ᶜ` are therefore **open**, they
  contain the respective closed chart regions (`chart0Set_subset_chartNbhd0`), and they **cover**
  `E` (`chartNbhd_union`) because a point cannot be deep in both charts at once.

With `splitBOpen r := outerE ∪ chartNbhd1 r` the excision hypothesis now holds
(`splitBOpen_chartNbhd0_cover`), so `SingularExcisionIsoInt.excisionEquivInt` applies and §3
**discharges the excision step of input (C0)**:

> `relHomologyInt_splitBOpen_eq_zero_of_chart0` : `H₂(chartNbhd0 r, splitBOpen r ∩ chartNbhd0 r; ℤ) = 0`
>   ⟹ `H₂(E, splitBOpen r; ℤ) = 0`.

`chartNbhd0 r` is a `D² × D²` chart region fattened slightly past the equator — contractible — so its
pair group is an ordinary homotopy-type computation with **no extension problem in it**. That is the
whole point of routing through the charts: the undecidable bit of the pair LES
(`Ext¹(ℤ/2, ℤ) ≅ ℤ/2`) never appears on either chart.

`outerECyclic_of_chart_local` / `kummerK3_b2_target_of_chart_local` are the resulting reductions:
the `H₂(K3;ℤ) ≅ ℤ²²` headline now rests on

* **(C0′)** `H₂(chartNbhd0 r, splitBOpen r ∩ chartNbhd0 r; ℤ) = 0`, and
* **(C1′)** `H₂(splitBOpen r, outerE; ℤ)` cyclic,

both chart-local, both sign-free, both orientation-free.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerCollarPairSplitInt
import SKEFTHawking.SingularExcisionIsoInt

open SKEFTHawking.SingularRelHomologyInt (RelHomologyInt)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.KummerResolutionPiece (ResE ResChart resSetoid chart0 chart1 chart0_inj_iff
  chart1_inj_iff chart0_eq_chart1_iff)
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerPieceCollarInt (outerE)
open SKEFTHawking.KummerPieceCollarCyclicInt (OuterECyclic kummerK3_b2_target_of_outerE_cyclic)
open SKEFTHawking.KummerCollarPairSplitInt (chart0Set chart1Set chart0Set_union_chart1Set)
open SKEFTHawking.SingularRelativeTripleSurjInt (relHomologyInt_cyclic_of_triple)

namespace SKEFTHawking.KummerChartNbhdInt

noncomputable section

/-! ## §1. The deep chart cores and their open complements -/

/-- The base-disk core of radius `r` inside a chart. -/
def deepChartSet (r : ℝ) : Set ResChart := {p : ResChart | ‖(p.1 : ℂ)‖ ≤ r}

theorem isClosed_deepChartSet (r : ℝ) : IsClosed (deepChartSet r) :=
  isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const

/-- **The deep core of chart 0** — chart-0 points whose base coordinate has norm `≤ r`. For `r < 1`
these are strictly inside the chart, away from the equator where the weld happens. -/
def deepChart0 (r : ℝ) : Set ↑ResEtop := chart0 '' deepChartSet r

/-- **The deep core of chart 1.** -/
def deepChart1 (r : ℝ) : Set ↑ResEtop := chart1 '' deepChartSet r

/-- **The deep chart-1 core is saturated** (`r < 1`): its `Quotient.mk` preimage contains no chart-0
representative, because a weld forces the base norm to be `1`. This is what makes it closed in the
quotient. -/
theorem preimage_deepChart1 {r : ℝ} (hr : r < 1) :
    Quotient.mk resSetoid ⁻¹' deepChart1 r = Sum.inr '' deepChartSet r := by
  ext a
  simp only [Set.mem_preimage, deepChart1, Set.mem_image]
  constructor
  · rintro ⟨q, hq, hmk⟩
    cases a with
    | inl p =>
      exfalso
      obtain ⟨hseam, hq1, -⟩ := chart0_eq_chart1_iff.mp hmk.symm
      have : ‖(q.1 : ℂ)‖ = 1 := by rw [hq1, norm_inv, hseam, inv_one]
      have hqr : ‖(q.1 : ℂ)‖ ≤ r := hq
      rw [this] at hqr
      linarith
    | inr q' => exact ⟨q', (chart1_inj_iff.mp hmk) ▸ hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩

/-- The mirror for chart 0. -/
theorem preimage_deepChart0 {r : ℝ} (hr : r < 1) :
    Quotient.mk resSetoid ⁻¹' deepChart0 r = Sum.inl '' deepChartSet r := by
  ext a
  simp only [Set.mem_preimage, deepChart0, Set.mem_image]
  constructor
  · rintro ⟨p, hp, hmk⟩
    cases a with
    | inl p' => exact ⟨p', (chart0_inj_iff.mp hmk) ▸ hp, rfl⟩
    | inr q =>
      exfalso
      obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk
      have hpr : ‖(p.1 : ℂ)‖ ≤ r := hp
      rw [hseam] at hpr
      linarith
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem isClosed_deepChart1 {r : ℝ} (hr : r < 1) : IsClosed (deepChart1 r) := by
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isClosed_preimage.mp ?_
  rw [preimage_deepChart1 hr]
  exact isClosedMap_inr _ (isClosed_deepChartSet r)

theorem isClosed_deepChart0 {r : ℝ} (hr : r < 1) : IsClosed (deepChart0 r) := by
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isClosed_preimage.mp ?_
  rw [preimage_deepChart0 hr]
  exact isClosedMap_inl _ (isClosed_deepChartSet r)

/-- **The open chart-0 neighbourhood**: everything except the deep core of chart 1 — the chart-0
region fattened slightly past the base equator. -/
def chartNbhd0 (r : ℝ) : Set ↑ResEtop := (deepChart1 r)ᶜ

/-- **The open chart-1 neighbourhood.** -/
def chartNbhd1 (r : ℝ) : Set ↑ResEtop := (deepChart0 r)ᶜ

theorem isOpen_chartNbhd0 {r : ℝ} (hr : r < 1) : IsOpen (chartNbhd0 r) :=
  (isClosed_deepChart1 hr).isOpen_compl

theorem isOpen_chartNbhd1 {r : ℝ} (hr : r < 1) : IsOpen (chartNbhd1 r) :=
  (isClosed_deepChart0 hr).isOpen_compl

/-- The closed chart-0 region sits inside its open neighbourhood: a chart-0 point is never deep in
chart 1. -/
theorem chart0Set_subset_chartNbhd0 {r : ℝ} (hr : r < 1) : chart0Set ⊆ chartNbhd0 r := by
  rintro _ ⟨p, rfl⟩ ⟨q, hq, hmk⟩
  obtain ⟨hseam, hq1, -⟩ := chart0_eq_chart1_iff.mp hmk.symm
  have hone : ‖(q.1 : ℂ)‖ = 1 := by rw [hq1, norm_inv, hseam, inv_one]
  have hqr : ‖(q.1 : ℂ)‖ ≤ r := hq
  rw [hone] at hqr
  linarith

theorem chart1Set_subset_chartNbhd1 {r : ℝ} (hr : r < 1) : chart1Set ⊆ chartNbhd1 r := by
  rintro _ ⟨q, rfl⟩ ⟨p, hp, hmk⟩
  obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk
  have hpr : ‖(p.1 : ℂ)‖ ≤ r := hp
  rw [hseam] at hpr
  linarith

/-- **The two open neighbourhoods cover `E`** — the honest open cover the closed chart regions could
not supply. -/
theorem chartNbhd_union {r : ℝ} (hr : r < 1) :
    chartNbhd0 r ∪ chartNbhd1 r = (Set.univ : Set ↑ResEtop) := by
  refine Set.eq_univ_of_forall fun y => ?_
  rcases (Set.eq_univ_iff_forall.mp chart0Set_union_chart1Set y) with h0 | h1
  · exact Or.inl (chart0Set_subset_chartNbhd0 hr h0)
  · exact Or.inr (chart1Set_subset_chartNbhd1 hr h1)

/-! ## §2. The splitting subspace, now open-fattened -/

/-- **The splitting subspace** `B = outerE ∪ chartNbhd1 r`: the outer half-collar together with the
*open* chart-1 neighbourhood. Unlike `KummerCollarPairSplitInt.splitB` (which used the closed chart
region) this one has the seam in the interior of its second piece, so excision applies. -/
def splitBOpen (r : ℝ) : Set ↑ResEtop := outerE ∪ chartNbhd1 r

theorem outerE_subset_splitBOpen (r : ℝ) : outerE ⊆ splitBOpen r := Set.subset_union_left

/-- **The excision cover condition** for the pair `(splitBOpen r, chartNbhd0 r)`: the interiors
cover `E`. `chartNbhd1 r` is an open subset of `splitBOpen r`, so it lies in the latter's interior,
and `chartNbhd0 r` is open; together they cover by `chartNbhd_union`. -/
theorem splitBOpen_chartNbhd0_cover {r : ℝ} (hr : r < 1) :
    (⋃ U ∈ ({splitBOpen r, chartNbhd0 r} : Set (Set ↑ResEtop)), interior U) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  rcases (Set.eq_univ_iff_forall.mp (chartNbhd_union hr) y) with h0 | h1
  · refine Set.mem_biUnion (Set.mem_insert_of_mem _ rfl) ?_
    rwa [(isOpen_chartNbhd0 hr).interior_eq]
  · refine Set.mem_biUnion (Set.mem_insert _ _) ?_
    exact interior_maximal Set.subset_union_right (isOpen_chartNbhd1 hr) h1

/-! ## §3. The chart-0 excision: input (C0) becomes a chart-local vanishing -/

/-- **The excision isomorphism for the chart-0 pair.** `H₂(chartNbhd0 r, splitBOpen r ∩ chartNbhd0 r; ℤ)
≅ H₂(E, splitBOpen r; ℤ)` — the deep chart-1 core is excised. -/
def chart0ExcisionEquiv {r : ℝ} (hr : r < 1) :
    RelHomologyInt (restr (splitBOpen r) (chartNbhd0 r)) 2
      ≃ₗ[ℤ] RelHomologyInt (X := ResEtop) (splitBOpen r) 2 :=
  excisionEquivInt (splitBOpen r) (chartNbhd0 r) 1 (splitBOpen_chartNbhd0_cover hr)

/-- **Input (C0), discharged down to the chart.** Vanishing of the chart-0 pair group forces
vanishing of `H₂(E, splitBOpen r; ℤ)` — the hypothesis
`KummerCollarPairSplitInt`/`SingularRelativeTripleSurjInt` consume. `chartNbhd0 r` is a `D² × D²`
chart region fattened past the equator, so the remaining obligation is a contractibility
computation, with no extension problem in it. -/
theorem relHomologyInt_splitBOpen_eq_zero_of_chart0 {r : ℝ} (hr : r < 1)
    (h : ∀ y : RelHomologyInt (restr (splitBOpen r) (chartNbhd0 r)) 2, y = 0) :
    ∀ y : RelHomologyInt (X := ResEtop) (splitBOpen r) 2, y = 0 := by
  intro y
  obtain ⟨x, rfl⟩ := (chart0ExcisionEquiv hr).surjective y
  rw [h x, map_zero]

/-! ## §4. The `b₂` residual on two chart-local inputs -/

/-- **The chart-local reduction.** With `r < 1`:

* **(C0′)** `H₂(chartNbhd0 r, splitBOpen r ∩ chartNbhd0 r; ℤ) = 0`, and
* **(C1′)** `H₂(splitBOpen r, outerE; ℤ)` generated by one element,

give `OuterECyclic` — the `b₂` residual. Compared with
`KummerCollarPairSplitInt.outerECyclic_of_splitB`, the ambient-level hypothesis has been traded for
a genuinely chart-local one via excision (§3); the second hypothesis is unchanged in shape but now
lives over the *open* chart-1 neighbourhood. -/
theorem outerECyclic_of_chart_local {r : ℝ} (hr : r < 1)
    (h0 : ∀ y : RelHomologyInt (restr (splitBOpen r) (chartNbhd0 r)) 2, y = 0)
    (hcyc : ∃ a : RelHomologyInt (restr outerE (splitBOpen r)) 2,
      ∀ x : RelHomologyInt (restr outerE (splitBOpen r)) 2, ∃ k : ℤ, x = k • a) :
    OuterECyclic :=
  relHomologyInt_cyclic_of_triple outerE (splitBOpen r) (outerE_subset_splitBOpen r) 2
    (relHomologyInt_splitBOpen_eq_zero_of_chart0 hr h0) hcyc

/-- **The zero-section class is halvable from the two chart-local inputs.** -/
theorem zeroSectionClass_halved_of_chart_local {r : ℝ} (hr : r < 1)
    (h0 : ∀ y : RelHomologyInt (restr (splitBOpen r) (chartNbhd0 r)) 2, y = 0)
    (hcyc : ∃ a : RelHomologyInt (restr outerE (splitBOpen r)) 2,
      ∀ x : RelHomologyInt (restr outerE (splitBOpen r)) 2, ∃ k : ℤ, x = k • a) :
    ∃ x : SKEFTHawking.KummerCollarPairLESInt.CollarH2,
      (2 : ℤ) • x = SKEFTHawking.KummerCollarPairLESInt.zeroSectionClass :=
  SKEFTHawking.KummerCollarPairLESInt.outerECyclic_iff_zeroSectionClass_halved.mp
    (outerECyclic_of_chart_local hr h0 hcyc)

/-- **The headline consumer** — the two chart-local inputs close `kummerK3_b2_target`
(`H₂(K3;ℤ) ≅ ℤ²²`). -/
theorem kummerK3_b2_target_of_chart_local {r : ℝ} (hr : r < 1)
    (h0 : ∀ y : RelHomologyInt (restr (splitBOpen r) (chartNbhd0 r)) 2, y = 0)
    (hcyc : ∃ a : RelHomologyInt (restr outerE (splitBOpen r)) 2,
      ∀ x : RelHomologyInt (restr outerE (splitBOpen r)) 2, ∃ k : ℤ, x = k • a) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  kummerK3_b2_target_of_outerE_cyclic (outerECyclic_of_chart_local hr h0 hcyc)

/-! ## §5. Non-degeneracy of the open splitting -/

/-- **`splitBOpen r` is a proper subspace** (for `0 ≤ r`): the zero-section point over the chart-0
origin lies outside it — it has fiber norm `0` (so misses `outerE`) and it is deep in chart 0 (so
misses `chartNbhd1 r`). Without this the reduction would admit `B = Set.univ`, where both hypotheses
degenerate and nothing is proved. -/
theorem splitBOpen_ne_univ {r : ℝ} (hr : 0 ≤ r) :
    splitBOpen r ≠ (Set.univ : Set ↑ResEtop) := by
  intro h
  have hmem : chart0 (⟨0, by simp⟩, ⟨0, by simp⟩) ∈ splitBOpen r := by rw [h]; trivial
  rcases hmem with hout | hnb
  · have hz : (1 : ℝ) / 2 ≤ ‖((0 : ℂ))‖ := hout
    simp at hz
    norm_num at hz
  · exact hnb ⟨(⟨0, by simp⟩, ⟨0, by simp⟩), by show ‖((0 : ℂ))‖ ≤ r; simpa using hr, rfl⟩

end

end SKEFTHawking.KummerChartNbhdInt
