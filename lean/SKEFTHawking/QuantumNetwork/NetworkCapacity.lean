import SKEFTHawking.QuantumNetwork.PLOBRateBound

/-!
# Multipath entanglement-distribution network capacity (Phase 6AN, Wave 2)

Generalizes single-link / single-path repeaterless capacity to a **network**: a capacity-weighted
graph with a source and a sink. We formalize flows, cuts, and the core of max-flow / min-cut duality
here (weak duality + witnessed equality + path achievability); **full max-flow–min-cut strong duality
(`maxFlow_eq_minCut`, the unconditional equality of max-flow value and min-cut capacity) is proven in
the sibling module `NetworkCapacityStrongDuality.lean`** (built from scratch — Mathlib has no
network-flow theory):

* `flowValue_le_cutCap` — **weak duality (converse upper bound):** every feasible flow value is at
  most every cut capacity. Telescoping the conservation law across any source–sink cut, the flow is
  the net flux across the cut, bounded by the cut's total capacity. This is the kernel-pure converse
  that underlies every repeaterless network-capacity upper bound (the graph-level analogue of the
  PLOB link bound `plobBound`).
* `maxFlow_minCut_of_saturating` — **witnessed max-flow–min-cut equality:** if some feasible flow
  *saturates* some cut (`flowValue f = cutCap S`), then `f` is a maximum flow and `S` is a minimum
  cut simultaneously — the network capacity equals the min-cut, exhibited without assuming the
  (harder) strong-duality existence theorem.
* `path3_capacity_eq_bottleneck` — **achievable lower bound / single-path specialization:** on a
  two-hop path `s → m → t` with link capacities `c₁, c₂`, the bottleneck `min c₁ c₂` is both
  achievable (a saturating flow) and the min-cut, so the end-to-end capacity equals the bottleneck.
  Specialized to repeaterless link capacities (`plobBound η`) this is the network reading of the PLOB
  bound along a path.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **capacity-weighted flow network**: a nonnegative capacity on every ordered pair of nodes
(`0` encodes "no link"), with a distinguished source and sink. -/
structure FlowNetwork (V : Type*) [Fintype V] where
  cap : V → V → ℝ
  capNonneg : ∀ u v, 0 ≤ cap u v
  source : V
  sink : V

namespace FlowNetwork

/-- A **feasible flow**: nonnegative, capacity-respecting, and conserved at every interior node
(net out = net in for nodes other than source and sink). -/
def IsFeasibleFlow (N : FlowNetwork V) (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v ≤ N.cap u v) ∧
    (∀ u, u ≠ N.source → u ≠ N.sink → ∑ w, f u w = ∑ w, f w u)

/-- The **value** of a flow: net flow out of the source. -/
def flowValue (N : FlowNetwork V) (f : V → V → ℝ) : ℝ :=
  ∑ w, f N.source w - ∑ w, f w N.source

/-- A **source–sink cut**: a set of nodes containing the source but not the sink. -/
def IsCut (N : FlowNetwork V) (S : Finset V) : Prop := N.source ∈ S ∧ N.sink ∉ S

/-- The **capacity of a cut**: total capacity of links crossing from `S` to its complement. -/
def cutCap (N : FlowNetwork V) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-- **Weak duality (converse upper bound).** Any feasible flow value is at most any cut capacity:
`flowValue f ≤ cutCap S`. Proof: conservation collapses `∑_{u∈S}(out − in)` to the source excess
`flowValue f`; the within-`S` links cancel; the reverse cross-cut flow is dropped (nonneg); each
forward cross-cut flow is `≤` its capacity. -/
theorem flowValue_le_cutCap (N : FlowNetwork V) {f : V → V → ℝ}
    (hf : N.IsFeasibleFlow f) {S : Finset V} (hS : N.IsCut S) :
    N.flowValue f ≤ N.cutCap S := by
  obtain ⟨hf0, hfcap, hcons⟩ := hf
  obtain ⟨hsS, htS⟩ := hS
  -- The interior excess vanishes, so the value equals the total excess over `S`.
  have h0 : ∀ u ∈ S, u ≠ N.source → (∑ w, f u w - ∑ w, f w u) = 0 := by
    intro u huS hune
    have huni : u ≠ N.sink := fun h => htS (h ▸ huS)
    rw [hcons u hune huni, sub_self]
  have hval : N.flowValue f = ∑ u ∈ S, (∑ w, f u w - ∑ w, f w u) := by
    rw [Finset.sum_eq_single_of_mem N.source hsS h0]; rfl
  -- Split each interior sum across the cut and cancel the within-`S` block.
  have e1 : ∑ u ∈ S, ∑ w, f u w
      = ∑ u ∈ S, ∑ w ∈ S, f u w + ∑ u ∈ S, ∑ w ∈ Sᶜ, f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S (fun w => f u w)).symm
  have e2 : ∑ u ∈ S, ∑ w, f w u
      = ∑ u ∈ S, ∑ w ∈ S, f w u + ∑ u ∈ S, ∑ w ∈ Sᶜ, f w u := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S (fun w => f w u)).symm
  have ecomm : ∑ u ∈ S, ∑ w ∈ S, f u w = ∑ u ∈ S, ∑ w ∈ S, f w u := Finset.sum_comm
  have hcancel : ∑ u ∈ S, (∑ w, f u w - ∑ w, f w u)
      = ∑ u ∈ S, ∑ w ∈ Sᶜ, f u w - ∑ u ∈ S, ∑ w ∈ Sᶜ, f w u := by
    rw [Finset.sum_sub_distrib, e1, e2, ecomm]; ring
  have hrev_nonneg : 0 ≤ ∑ u ∈ S, ∑ w ∈ Sᶜ, f w u :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun w _ => hf0 w u
  have hbound : ∑ u ∈ S, ∑ w ∈ Sᶜ, f u w ≤ N.cutCap S :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => hfcap u w
  rw [hval, hcancel]
  linarith

/-- **Witnessed max-flow–min-cut equality.** If a feasible flow `f` saturates a cut `S`
(`flowValue f = cutCap S`), then `f` is a maximum flow and `S` is a minimum cut: no feasible flow
exceeds `flowValue f`, and no cut is cheaper than `cutCap S`. The network capacity *equals* the
min-cut, exhibited from weak duality alone. -/
theorem maxFlow_minCut_of_saturating (N : FlowNetwork V) {f : V → V → ℝ} {S : Finset V}
    (hf : N.IsFeasibleFlow f) (hS : N.IsCut S) (hsat : N.flowValue f = N.cutCap S) :
    (∀ f', N.IsFeasibleFlow f' → N.flowValue f' ≤ N.flowValue f)
      ∧ (∀ S', N.IsCut S' → N.cutCap S ≤ N.cutCap S') := by
  refine ⟨fun f' hf' => ?_, fun S' hS' => ?_⟩
  · rw [hsat]; exact N.flowValue_le_cutCap hf' hS
  · rw [← hsat]; exact N.flowValue_le_cutCap hf hS'

/-! ## Single-path specialization: bottleneck = min-cut = achievable capacity -/

/-- The **two-hop path network** `0 →(c₁) 1 →(c₂) 2`, source `0`, sink `2`. -/
noncomputable def path3 (c₁ c₂ : ℝ) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) : FlowNetwork (Fin 3) where
  cap u v := if u = 0 ∧ v = 1 then c₁ else if u = 1 ∧ v = 2 then c₂ else 0
  capNonneg u v := by split_ifs <;> first | exact h₁ | exact h₂ | exact le_refl 0
  source := 0
  sink := 2

/-- The bottleneck flow on the two-hop path: push `min c₁ c₂` along `0 → 1 → 2`. -/
noncomputable def path3Flow (c₁ c₂ : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun u v => if u = 0 ∧ v = 1 then min c₁ c₂ else if u = 1 ∧ v = 2 then min c₁ c₂ else 0

/-- **Single-path bottleneck capacity = min-cut.** On the two-hop path, the bottleneck `min c₁ c₂` is
achieved by a feasible flow and equals the capacity of a source–sink cut; hence (via
`maxFlow_minCut_of_saturating`) it is the network capacity. This is the network reading of the path
bottleneck — `composite = min-cut over a path`. -/
theorem path3_capacity_eq_bottleneck (c₁ c₂ : ℝ) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) :
    ∃ (f : Fin 3 → Fin 3 → ℝ) (S : Finset (Fin 3)),
      (path3 c₁ c₂ h₁ h₂).IsFeasibleFlow f ∧ (path3 c₁ c₂ h₁ h₂).IsCut S ∧
        (path3 c₁ c₂ h₁ h₂).flowValue f = min c₁ c₂ ∧
        (path3 c₁ c₂ h₁ h₂).cutCap S = min c₁ c₂ := by
  refine ⟨path3Flow c₁ c₂, ?_⟩
  have hmin1 : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hmin2 : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have hmin0 : 0 ≤ min c₁ c₂ := le_min h₁ h₂
  -- feasibility (independent of which link is the bottleneck)
  have hfeas : (path3 c₁ c₂ h₁ h₂).IsFeasibleFlow (path3Flow c₁ c₂) := by
    refine ⟨fun u v => ?_, fun u v => ?_, fun u hu0 hu2 => ?_⟩
    · simp only [path3Flow]; split_ifs <;> first | exact hmin0 | exact le_refl 0
    · simp only [path3Flow, path3]
      split_ifs <;> first | exact hmin1 | exact hmin2 | exact h₁ | exact h₂ | exact le_refl 0
    · fin_cases u
      · exact absurd rfl hu0
      · simp [path3Flow]
      · exact absurd rfl hu2
  -- value of the bottleneck flow is the bottleneck
  have hval : (path3 c₁ c₂ h₁ h₂).flowValue (path3Flow c₁ c₂) = min c₁ c₂ := by
    simp [FlowNetwork.flowValue, path3, path3Flow]
  -- pick the saturating cut by cases on which link is smaller
  rcases le_total c₁ c₂ with hle | hle
  · refine ⟨{0}, hfeas, by simp [FlowNetwork.IsCut, path3], hval, ?_⟩
    rw [min_eq_left hle]
    simp only [FlowNetwork.cutCap, path3]
    rw [Finset.sum_singleton, show ({0}ᶜ : Finset (Fin 3)) = {1, 2} from by decide,
      Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
    simp
  · refine ⟨{0, 1}, hfeas, by simp [FlowNetwork.IsCut, path3], hval, ?_⟩
    rw [min_eq_right hle]
    simp only [FlowNetwork.cutCap, path3]
    rw [show (({0, 1} : Finset (Fin 3))ᶜ) = {2} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
    simp

/-- **Repeaterless network reading of PLOB along a path.** With link capacities given by the
repeaterless secret-key bound `plobBound η = −log₂(1−η)`, a feasible flow on the two-hop path
*achieves* the bottleneck end-to-end rate `min (plobBound η₁) (plobBound η₂)` (the achievability
half; `path3_capacity_eq_bottleneck` additionally exhibits the matching min-cut). -/
theorem path3_repeaterless_bottleneck {η₁ η₂ : ℝ} (h₁0 : 0 ≤ η₁) (h₁1 : η₁ < 1)
    (h₂0 : 0 ≤ η₂) (h₂1 : η₂ < 1) :
    ∃ f : Fin 3 → Fin 3 → ℝ,
      (path3 (plobBound η₁) (plobBound η₂) (plobBound_nonneg h₁0 h₁1)
          (plobBound_nonneg h₂0 h₂1)).IsFeasibleFlow f ∧
        (path3 (plobBound η₁) (plobBound η₂) (plobBound_nonneg h₁0 h₁1)
          (plobBound_nonneg h₂0 h₂1)).flowValue f = min (plobBound η₁) (plobBound η₂) := by
  obtain ⟨f, _, hf, _, hval, _⟩ :=
    path3_capacity_eq_bottleneck (plobBound η₁) (plobBound η₂)
      (plobBound_nonneg h₁0 h₁1) (plobBound_nonneg h₂0 h₂1)
  exact ⟨f, hf, hval⟩

end FlowNetwork

end SKEFTHawking.QuantumNetwork
