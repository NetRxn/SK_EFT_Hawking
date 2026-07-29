/-
# Phase 5q.H (N1 audit) — the bug-eyed interval: a compact non-Hausdorff C⁰ 1-manifold with
THREE boundary points

**Purpose (substrate audit — feeds `NonHausdorffBordismCollapse.lean`).** The project's `Bordism`
structure (`BordismGroup.lean`) requires the bordism manifold `W` to be a compact charted
`IsManifold` — but does **not** require `W` to be Hausdorff (only the *objects* of the structured
carriers carry `t2` fields). This module builds the classical witness that this omission is
load-bearing: the **bug-eyed interval** `B` — `[0,1]` with a doubled origin, i.e.
`(Bool × [0,1]) / ((i,t) ~ (j,t) for t ≠ 0)` — is a compact, non-Hausdorff, charted
(`EuclideanHalfSpace 1`) topological 1-manifold whose boundary consists of **three** points
`{0₁, 0₂, 1}`. Hence `M × B` is a compact bordism manifold with `∂(M × B) ≅ M ⊔ M ⊔ M` for every
closed `M` — an *odd* number of boundary copies, impossible for Hausdorff bordisms (mod-2
homology), and the seed of the bordism-relation collapse proved in the companion module.

Everything here is kernel-pure (`{propext, Classical.choice, Quot.sound}`); the charts are built by
transporting Mathlib's `IccLeftChart`/`IccRightChart` through explicit partial homeomorphisms, so
the boundary computation reuses Mathlib's `Icc` frontier lemmas verbatim. The `IsManifold (𝓡∂ 1) 0`
structure is the free C⁰ instance; note the chart transitions are in fact real-analytic
(identity / affine), so the same object obstructs at every smoothness — only a `T2Space W` field
excludes it.
-/
import Mathlib

namespace SKEFTHawking.NonHausdorffInterval

open scoped Manifold
open Set

noncomputable section

/-! ## §1. The doubled-origin quotient -/

/-- The doubling relation on `Bool × [0,1]`: two labelled points are identified iff their values
agree and either the labels agree or the value is nonzero. This is an equivalence relation (the
two copies of the interval are glued away from `0`, leaving a doubled origin). -/
def bugRel (p q : Bool × Set.Icc (0 : ℝ) 1) : Prop :=
  p.2 = q.2 ∧ (p.1 = q.1 ∨ (p.2 : ℝ) ≠ 0)

/-- **The bug-eyed interval**: `[0,1]` with a doubled origin — the classical compact non-Hausdorff
1-manifold-with-boundary. Its boundary has THREE points (`0₁`, `0₂`, `1`). -/
def BugInterval : Type := Quot bugRel

instance : TopologicalSpace BugInterval :=
  inferInstanceAs (TopologicalSpace (Quot bugRel))

/-- The class of a labelled point. -/
def bmk (i : Bool) (t : Set.Icc (0 : ℝ) 1) : BugInterval := Quot.mk bugRel (i, t)

theorem bmk_eq_of_ne_zero {t : Set.Icc (0 : ℝ) 1} (i j : Bool) (h : (t : ℝ) ≠ 0) :
    bmk i t = bmk j t :=
  Quot.sound ⟨rfl, Or.inr h⟩

theorem bugInterval_ind {P : BugInterval → Prop} (h : ∀ i t, P (bmk i t)) : ∀ z, P z :=
  Quot.ind fun p => h p.1 p.2

/-- The underlying value in `[0,1]` — well-defined (the relation preserves the value). -/
def bugVal : BugInterval → Set.Icc (0 : ℝ) 1 :=
  Quot.lift (fun p => p.2) (fun _ _ h => h.1)

@[simp] theorem bugVal_bmk (i : Bool) (t : Set.Icc (0 : ℝ) 1) : bugVal (bmk i t) = t := rfl

theorem continuous_bugVal : Continuous bugVal :=
  continuous_quot_lift _ continuous_snd

/-- Opens of the bug-eyed interval are detected on the labelled square (quotient topology). -/
theorem isOpen_bugInterval_iff {S : Set BugInterval} :
    IsOpen S ↔ IsOpen (Quot.mk bugRel ⁻¹' S) :=
  (isQuotientMap_quot_mk (r := bugRel)).isOpen_preimage.symm

/-- The origin label: `some i` at the doubled origin `0ᵢ`, `none` elsewhere — well-defined, and
the separating invariant for the two origins. -/
def bugZeroLabel : BugInterval → Option Bool :=
  Quot.lift (fun p => if (p.2 : ℝ) = 0 then some p.1 else none) (fun p q h => by
    obtain ⟨h2, h1⟩ := h
    show (if (p.2 : ℝ) = 0 then some p.1 else none) = (if (q.2 : ℝ) = 0 then some q.1 else none)
    by_cases h0 : (p.2 : ℝ) = 0
    · have hq0 : (q.2 : ℝ) = 0 := by rw [← h2]; exact h0
      rcases h1 with h1 | h1
      · rw [if_pos h0, if_pos hq0, h1]
      · exact absurd h0 h1
    · have hq0 : ¬(q.2 : ℝ) = 0 := by rw [← h2]; exact h0
      rw [if_neg h0, if_neg hq0])

theorem bugZeroLabel_bmk (i : Bool) (t : Set.Icc (0 : ℝ) 1) :
    bugZeroLabel (bmk i t) = if (t : ℝ) = 0 then some i else none := rfl

/-! ## §2. The three special points -/

/-- The doubled origin `0ᵢ`. -/
def origin (i : Bool) : BugInterval := bmk i ⟨0, by norm_num⟩

/-- The top endpoint `1` (a single point — the copies are glued there). -/
def btop : BugInterval := bmk false ⟨1, by norm_num⟩

theorem bugVal_origin (i : Bool) : (bugVal (origin i) : ℝ) = 0 := rfl

theorem bugVal_btop : (bugVal btop : ℝ) = 1 := rfl

theorem bugZeroLabel_origin (i : Bool) : bugZeroLabel (origin i) = some i := by
  rw [origin, bugZeroLabel_bmk, if_pos rfl]

theorem bmk_top_eq (j : Bool) : bmk j ⟨1, by norm_num⟩ = btop :=
  bmk_eq_of_ne_zero j false one_ne_zero

/-- The two origins are distinct (the origin label separates them). -/
theorem origin_ne : origin false ≠ origin true := fun h => by
  have := congrArg bugZeroLabel h
  rw [bugZeroLabel_origin, bugZeroLabel_origin] at this
  exact absurd (Option.some.inj this) (by decide)

/-- The origins differ from the top (the value separates them). -/
theorem origin_ne_btop (i : Bool) : origin i ≠ btop := fun h => by
  have := congrArg (fun z => (bugVal z : ℝ)) h
  rw [show (bugVal (origin i) : ℝ) = 0 from rfl] at this
  norm_num [btop] at this

/-! ## §3. The partial homeomorphisms to `[0,1]` -/

/-- The bottom partial homeomorphism at the origin `0ᵢ`: on classes of value `< 1` that avoid the
*other* origin, the value map to `[0,1]`, inverted by `t ↦ [(i,t)]`. -/
def bugToIccBot (i : Bool) : OpenPartialHomeomorph BugInterval (Set.Icc (0 : ℝ) 1) where
  source := {z | (bugVal z : ℝ) < 1 ∧ bugZeroLabel z ≠ some (!i)}
  target := {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1}
  toFun := bugVal
  invFun := fun t => bmk i t
  map_source' := fun _ hz => hz.1
  map_target' := by
    intro t ht
    refine ⟨ht, ?_⟩
    rw [bugZeroLabel_bmk]
    by_cases h0 : (t : ℝ) = 0
    · rw [if_pos h0]
      intro h
      have := Option.some.inj h
      cases i <;> simp at this
    · rw [if_neg h0]
      exact fun h => nomatch h
  left_inv' := by
    refine bugInterval_ind fun j t hz => ?_
    obtain ⟨-, hlab⟩ := hz
    show bmk i t = bmk j t
    by_cases h0 : (t : ℝ) = 0
    · rw [bugZeroLabel_bmk, if_pos h0] at hlab
      have hji : j ≠ !i := fun h => hlab (by rw [h])
      have : j = i := by cases i <;> cases j <;> simp_all
      rw [this]
    · exact bmk_eq_of_ne_zero i j h0
  right_inv' := fun t _ => rfl
  open_source := by
    have hsub : {p : Bool × Set.Icc (0 : ℝ) 1 |
        (p.2 : ℝ) < 1 ∧ (if (p.2 : ℝ) = 0 then some p.1 else none) ≠ some (!i)} =
        {p : Bool × Set.Icc (0 : ℝ) 1 | (p.2 : ℝ) < 1} ∩
          ({p : Bool × Set.Icc (0 : ℝ) 1 | (p.2 : ℝ) = 0 ∧ p.1 = !i})ᶜ := by
      ext ⟨j, t⟩
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hc => h2 ?_⟩
        rw [if_pos hc.1, hc.2]
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hc => h2 ?_⟩
        by_cases h0 : (t : ℝ) = 0
        · rw [if_pos h0] at hc
          exact ⟨h0, Option.some.inj hc⟩
        · rw [if_neg h0] at hc
          exact nomatch hc
    rw [isOpen_bugInterval_iff]
    show IsOpen {p : Bool × Set.Icc (0 : ℝ) 1 |
        (p.2 : ℝ) < 1 ∧ (if (p.2 : ℝ) = 0 then some p.1 else none) ≠ some (!i)}
    rw [hsub]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
    · exact ((isClosed_eq (continuous_subtype_val.comp continuous_snd) continuous_const).inter
        (isClosed_eq continuous_fst continuous_const)).isOpen_compl
  open_target := isOpen_lt continuous_subtype_val continuous_const
  continuousOn_toFun := continuous_bugVal.continuousOn
  continuousOn_invFun :=
    (continuous_quot_mk.comp (continuous_const.prodMk continuous_id)).continuousOn

/-- The top partial homeomorphism: on classes of positive value, the value map to `[0,1]`,
inverted by `t ↦ [(false,t)]`. -/
def bugToIccTop : OpenPartialHomeomorph BugInterval (Set.Icc (0 : ℝ) 1) where
  source := {z | 0 < (bugVal z : ℝ)}
  target := {t : Set.Icc (0 : ℝ) 1 | 0 < (t : ℝ)}
  toFun := bugVal
  invFun := fun t => bmk false t
  map_source' := fun _ hz => hz
  map_target' := fun t ht => ht
  left_inv' := by
    refine bugInterval_ind fun j t hz => ?_
    have hz' : (0 : ℝ) < (t : ℝ) := hz
    exact bmk_eq_of_ne_zero false j (ne_of_gt hz')
  right_inv' := fun t _ => rfl
  open_source := by
    rw [isOpen_bugInterval_iff]
    exact isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
  open_target := isOpen_lt continuous_const continuous_subtype_val
  continuousOn_toFun := continuous_bugVal.continuousOn
  continuousOn_invFun :=
    (continuous_quot_mk.comp (continuous_const.prodMk continuous_id)).continuousOn

/-! ## §4. The charts (into `EuclideanHalfSpace 1`) and the charted-space structure -/

/-- The bottom chart at the origin `0ᵢ`: the transported `IccLeftChart`. -/
def bugChartBot (i : Bool) : OpenPartialHomeomorph BugInterval (EuclideanHalfSpace 1) :=
  (bugToIccBot i).trans (IccLeftChart 0 1)

/-- The top chart at `1`: the transported `IccRightChart`. -/
def bugChartTop : OpenPartialHomeomorph BugInterval (EuclideanHalfSpace 1) :=
  bugToIccTop.trans (IccRightChart 0 1)

theorem mem_bugChartBot_source {z : BugInterval} (i : Bool) (h1 : (bugVal z : ℝ) < 1)
    (h2 : bugZeroLabel z ≠ some (!i)) : z ∈ (bugChartBot i).source := by
  rw [bugChartBot, OpenPartialHomeomorph.trans_source]
  exact ⟨⟨h1, h2⟩, h1⟩

theorem mem_bugChartTop_source {z : BugInterval} (h : 0 < (bugVal z : ℝ)) :
    z ∈ bugChartTop.source := by
  rw [bugChartTop, OpenPartialHomeomorph.trans_source]
  exact ⟨h, h⟩

/-- The charted-space structure on the bug-eyed interval: two bottom charts (one per origin) and
one top chart. -/
instance : ChartedSpace (EuclideanHalfSpace 1) BugInterval where
  atlas := {bugChartBot false, bugChartBot true, bugChartTop}
  chartAt z :=
    if (bugVal z : ℝ) = 0 then bugChartBot ((bugZeroLabel z).getD false)
    else if (bugVal z : ℝ) < 1 then bugChartBot false else bugChartTop
  mem_chart_source z := by
    by_cases h0 : (bugVal z : ℝ) = 0
    · rw [if_pos h0]
      induction z using bugInterval_ind with | h j t =>
      have ht0 : (t : ℝ) = 0 := h0
      have hlab : bugZeroLabel (bmk j t) = some j := by rw [bugZeroLabel_bmk, if_pos ht0]
      rw [hlab]
      refine mem_bugChartBot_source j (by rw [bugVal_bmk, ht0]; norm_num) ?_
      rw [hlab]
      intro h
      have := Option.some.inj h
      cases j <;> simp at this
    · rw [if_neg h0]
      have hpos : 0 < (bugVal z : ℝ) := lt_of_le_of_ne (bugVal z).2.1 (Ne.symm h0)
      by_cases h1 : (bugVal z : ℝ) < 1
      · rw [if_pos h1]
        refine mem_bugChartBot_source false h1 ?_
        induction z using bugInterval_ind with | h j t =>
        have h0' : ¬((t : ℝ) = 0) := h0
        rw [bugZeroLabel_bmk, if_neg h0']
        exact fun h => nomatch h
      · rw [if_neg h1]
        exact mem_bugChartTop_source hpos
  chart_mem_atlas z := by
    by_cases h0 : (bugVal z : ℝ) = 0
    · rw [if_pos h0]
      rcases (bugZeroLabel z).getD false with _ | _
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [if_neg h0]
      by_cases h1 : (bugVal z : ℝ) < 1
      · rw [if_pos h1]; exact Set.mem_insert _ _
      · rw [if_neg h1]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- The bug-eyed interval is compact (a quotient of `Bool × [0,1]`). -/
instance : CompactSpace BugInterval where
  isCompact_univ := by
    have h : (Set.univ : Set BugInterval) = Quot.mk bugRel '' Set.univ := by
      rw [Set.image_univ]
      exact (Set.range_eq_univ.mpr (Quot.ind fun p => ⟨p, rfl⟩)).symm
    rw [h]
    exact isCompact_univ.image continuous_quot_mk

/-! ## §5. The boundary: THREE points -/

/-- The chart at the origin `0ᵢ` is the bottom chart `bugChartBot i`. -/
theorem chartAt_origin (i : Bool) : chartAt (EuclideanHalfSpace 1) (origin i) = bugChartBot i := by
  show (if (bugVal (origin i) : ℝ) = 0 then bugChartBot ((bugZeroLabel (origin i)).getD false)
    else _) = bugChartBot i
  rw [if_pos (bugVal_origin i), bugZeroLabel_origin]
  rfl

/-- The chart at the top is the top chart. -/
theorem chartAt_btop : chartAt (EuclideanHalfSpace 1) btop = bugChartTop := by
  show (if (bugVal btop : ℝ) = 0 then _ else if (bugVal btop : ℝ) < 1 then _ else bugChartTop)
    = bugChartTop
  rw [bugVal_btop]
  norm_num

/-- The chart at an interior point (value in `(0,1)`) is the bottom-`false` chart. -/
theorem chartAt_middle {z : BugInterval} (h0 : (bugVal z : ℝ) ≠ 0) (h1 : (bugVal z : ℝ) < 1) :
    chartAt (EuclideanHalfSpace 1) z = bugChartBot false := by
  show (if (bugVal z : ℝ) = 0 then _ else if (bugVal z : ℝ) < 1 then bugChartBot false else _)
    = bugChartBot false
  rw [if_neg h0, if_pos h1]

/-- The two origins are boundary points (via Mathlib's `IccLeftChart` frontier computation). -/
theorem isBoundaryPoint_origin (i : Bool) : (𝓡∂ 1).IsBoundaryPoint (origin i) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt, chartAt_origin]
  have hval : (bugToIccBot i) (origin i) = (⊥ : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    rfl
  have heval : ((bugChartBot i).extend (𝓡∂ 1)) (origin i)
      = ((IccLeftChart 0 1).extend (𝓡∂ 1)) ⊥ := by
    rw [bugChartBot, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.trans_apply, hval]
  rw [heval]
  exact IccLeftChart_extend_bot_mem_frontier

/-- The top endpoint is a boundary point (via Mathlib's `IccRightChart` frontier computation). -/
theorem isBoundaryPoint_btop : (𝓡∂ 1).IsBoundaryPoint btop := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt, chartAt_btop]
  have hval : bugToIccTop btop = (⊤ : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    rfl
  have heval : (bugChartTop.extend (𝓡∂ 1)) btop = ((IccRightChart 0 1).extend (𝓡∂ 1)) ⊤ := by
    rw [bugChartTop, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.trans_apply, hval]
  rw [heval]
  exact IccRightChart_extend_top_mem_frontier

/-- Interior values give interior points (via Mathlib's `IccLeftChart` interior computation). -/
theorem isInteriorPoint_middle {z : BugInterval} (h0 : 0 < (bugVal z : ℝ))
    (h1 : (bugVal z : ℝ) < 1) : (𝓡∂ 1).IsInteriorPoint z := by
  rw [ModelWithCorners.IsInteriorPoint, extChartAt, chartAt_middle (ne_of_gt h0) h1]
  have heval : ((bugChartBot false).extend (𝓡∂ 1)) z
      = ((IccLeftChart 0 1).extend (𝓡∂ 1)) (bugVal z) := by
    rw [bugChartBot, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.trans_apply]
    rfl
  rw [heval, interior_range_modelWithCornersEuclideanHalfSpace]
  exact IccLeftChart_extend_interior_pos ⟨h0, h1⟩

/-- **The boundary of the bug-eyed interval is THREE points** — the doubled origin plus the top.
This is the odd boundary count impossible for Hausdorff compact 1-manifolds, and the engine of the
bordism-relation collapse. -/
theorem boundary_bugInterval :
    (𝓡∂ 1).boundary BugInterval = {origin false, origin true, btop} := by
  ext z
  induction z using bugInterval_ind with | h j t =>
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with h0 | h1 | hmid
  · have hz : bmk j t = origin j := by
      show bmk j t = bmk j _
      congr 1
      exact Subtype.ext h0
    rw [hz]
    refine iff_of_true (isBoundaryPoint_origin j) ?_
    cases j
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · have hz : bmk j t = btop := by
      rw [show t = ⟨1, by norm_num⟩ from Subtype.ext h1]
      exact bmk_top_eq j
    rw [hz]
    exact iff_of_true isBoundaryPoint_btop
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · refine iff_of_false ?_ ?_
    · intro hb
      have hbd : (𝓡∂ 1).IsBoundaryPoint (bmk j t) := hb
      rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint] at hbd
      exact hbd (isInteriorPoint_middle (z := bmk j t) hmid.1 hmid.2)
    · intro h
      rcases h with h | h | h
      · have hv : (t : ℝ) = 0 := congrArg (fun z => (bugVal z : ℝ)) h
        rw [hv] at hmid
        exact lt_irrefl (0 : ℝ) hmid.1
      · have hv : (t : ℝ) = 0 := congrArg (fun z => (bugVal z : ℝ)) h
        rw [hv] at hmid
        exact lt_irrefl (0 : ℝ) hmid.1
      · have hbt : bmk j t = btop := h
        have hv : (t : ℝ) = 1 := congrArg (fun z => (bugVal z : ℝ)) hbt
        rw [hv] at hmid
        exact lt_irrefl (1 : ℝ) hmid.2

/-- **The bug-eyed interval is NOT Hausdorff** — the two origins are topologically inseparable
(every open set containing one meets any open set containing the other, on the shared spine). -/
theorem not_t2Space_bugInterval : ¬T2Space BugInterval := by
  intro h
  obtain ⟨U, V, hU, hV, hoU, hoV, hUV⟩ := h.t2 origin_ne
  -- The preimages of U and V under t ↦ [(false,t)] and t ↦ [(true,t)] are open sets of [0,1]
  -- containing 0; they share a point t > 0, whose class lies in both U and V.
  have hcontF : Continuous fun t : Set.Icc (0 : ℝ) 1 => bmk false t :=
    continuous_quot_mk.comp (continuous_const.prodMk continuous_id)
  have hcontT : Continuous fun t : Set.Icc (0 : ℝ) 1 => bmk true t :=
    continuous_quot_mk.comp (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen ((fun t : Set.Icc (0 : ℝ) 1 => bmk false t) ⁻¹' U) := hU.preimage hcontF
  have hVopen : IsOpen ((fun t : Set.Icc (0 : ℝ) 1 => bmk true t) ⁻¹' V) := hV.preimage hcontT
  have h0U : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ _ ⁻¹' U := hoU
  have h0V : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ _ ⁻¹' V := hoV
  -- intersect the two neighborhoods of 0 in [0,1]: they contain a common point with value > 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hUopen.inter hVopen) _ ⟨h0U, h0V⟩
  set δ : ℝ := min (ε / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have htmem : (⟨δ, ⟨le_of_lt hδpos, hδle⟩⟩ : Set.Icc (0 : ℝ) 1) ∈
      Metric.ball (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have : |δ - 0| = δ := by rw [sub_zero]; exact abs_of_pos hδpos
    rw [this]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨htU, htV⟩ := hball htmem
  have hglue : bmk false (⟨δ, ⟨le_of_lt hδpos, hδle⟩⟩ : Set.Icc (0 : ℝ) 1)
      = bmk true ⟨δ, ⟨le_of_lt hδpos, hδle⟩⟩ :=
    bmk_eq_of_ne_zero false true (ne_of_gt hδpos)
  have htU' : bmk false ⟨δ, ⟨le_of_lt hδpos, hδle⟩⟩ ∈ U := htU
  have htV' : bmk true ⟨δ, ⟨le_of_lt hδpos, hδle⟩⟩ ∈ V := htV
  refine Set.disjoint_iff.mp hUV ⟨htU', ?_⟩
  rw [hglue]
  exact htV'

end

end SKEFTHawking.NonHausdorffInterval
