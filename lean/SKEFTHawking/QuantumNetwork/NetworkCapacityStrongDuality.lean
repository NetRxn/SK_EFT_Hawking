import SKEFTHawking.QuantumNetwork.NetworkCapacity

/-!
# Max-flow–min-cut STRONG duality (Phase 6AN, Wave 2 — strengthening pass)

`NetworkCapacity.lean` shipped the *weak-duality* converse (`flowValue_le_cutCap`), the witnessed
equality (`maxFlow_minCut_of_saturating`), and path achievability. This file strengthens W2 toward
the FULL max-flow–min-cut theorem (strong duality): for any finite capacity-weighted network with
`source ≠ sink`, the maximum flow value *equals* the minimum cut capacity — i.e. a saturating
flow/cut pair always *exists* (Mathlib has no network-flow theory; this is built from scratch).

The two pillars:

* `maxFlow_exists` — **the maximum flow is attained.** The feasible-flow set is a closed subset of
  the compact capacity box `∏ [0, cap u v]`, hence compact; `flowValue` is continuous; the extreme
  value theorem gives a maximizing flow.
* `maxFlow_no_augmenting` — **the augmenting-path theorem.** A maximizing flow's residual graph cannot
  reach the sink (else `augment` would build a strictly larger feasible flow). Combined with
  `flowValue_eq_cutCap_residualReachable` (a maximizing flow saturates the cut induced by its
  residual-reachable set) and weak duality, this gives:
* `maxFlow_eq_minCut` — **full strong duality** (this file: DONE): for any finite network with
  `source ≠ sink`, the maximum flow value equals the minimum cut capacity.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace FlowNetwork

/-- The set of feasible flows of `N`, as a subset of `V → V → ℝ`. -/
def feasibleSet (N : FlowNetwork V) : Set (V → V → ℝ) := {f | N.IsFeasibleFlow f}

omit [DecidableEq V] in
/-- The zero flow is feasible. -/
theorem zero_isFeasibleFlow (N : FlowNetwork V) : N.IsFeasibleFlow (fun _ _ => 0) :=
  ⟨fun _ _ => le_refl 0, fun u v => N.capNonneg u v, fun _ _ _ => by simp⟩

omit [Fintype V] [DecidableEq V] in
/-- Each entry evaluation `f ↦ f u v` is continuous on `V → V → ℝ`. -/
private theorem continuous_entry (u v : V) : Continuous (fun f : V → V → ℝ => f u v) :=
  (continuous_apply v).comp (continuous_apply u)

omit [DecidableEq V] in
/-- **The feasible-flow set is compact.** It is a closed subset of the compact capacity box
`∏_{u,v} [0, cap u v]`. -/
theorem isCompact_feasibleSet (N : FlowNetwork V) : IsCompact N.feasibleSet := by
  have hbox : IsCompact (Set.univ.pi fun u => Set.univ.pi fun v => Set.Icc (0 : ℝ) (N.cap u v)) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun v => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · -- feasibleSet is closed: an intersection of closed coordinate conditions
    have hset : N.feasibleSet =
        (⋂ u, ⋂ v, {f : V → V → ℝ | 0 ≤ f u v}) ∩
        (⋂ u, ⋂ v, {f : V → V → ℝ | f u v ≤ N.cap u v}) ∩
        (⋂ u, ⋂ (_ : u ≠ N.source), ⋂ (_ : u ≠ N.sink),
          {f : V → V → ℝ | ∑ w, f u w = ∑ w, f w u}) := by
      ext f
      simp only [feasibleSet, IsFeasibleFlow, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [hset]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le continuous_const (continuous_entry u v)
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (continuous_entry u v) continuous_const
    · refine isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
      exact isClosed_eq (continuous_finset_sum _ fun w _ => continuous_entry u w)
        (continuous_finset_sum _ fun w _ => continuous_entry w u)
  · -- feasibleSet ⊆ box
    intro f hf
    obtain ⟨hf0, hfcap, _⟩ := hf
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
    exact fun u v => ⟨hf0 u v, hfcap u v⟩

omit [DecidableEq V] in
/-- `flowValue` is continuous in the flow. -/
theorem continuous_flowValue (N : FlowNetwork V) : Continuous N.flowValue := by
  unfold FlowNetwork.flowValue
  exact (continuous_finset_sum _ fun w _ => continuous_entry N.source w).sub
    (continuous_finset_sum _ fun w _ => continuous_entry w N.source)

omit [DecidableEq V] in
/-- **The maximum flow is attained.** There is a feasible flow `f` whose value is `≥` that of every
feasible flow — the extreme value theorem on the compact feasible-flow set. -/
theorem maxFlow_exists (N : FlowNetwork V) :
    ∃ f, N.IsFeasibleFlow f ∧ ∀ g, N.IsFeasibleFlow g → N.flowValue g ≤ N.flowValue f := by
  obtain ⟨f, hf_mem, hf_max⟩ :=
    N.isCompact_feasibleSet.exists_isMaxOn ⟨_, N.zero_isFeasibleFlow⟩
      N.continuous_flowValue.continuousOn
  exact ⟨f, hf_mem, fun g hg => hf_max hg⟩

/-! ## Residual reachability and the induced cut -/

/-- A **residual edge** `u → v` of flow `f`: either the forward link has slack (`f u v < cap u v`)
or there is backward flow to cancel (`0 < f v u`). Pushing flow is possible exactly along these. -/
def IsResidualEdge (N : FlowNetwork V) (f : V → V → ℝ) (a b : V) : Prop :=
  f a b < N.cap a b ∨ 0 < f b a

/-- The set of nodes reachable from the source through residual edges, as a `Finset` (every set in a
`Fintype` is finite). The source–sink cut it induces is the min cut when `f` is a maximum flow. -/
noncomputable def residualReachable (N : FlowNetwork V) (f : V → V → ℝ) : Finset V :=
  (Set.toFinite {v | Relation.ReflTransGen (N.IsResidualEdge f) N.source v}).toFinset

omit [DecidableEq V] in
theorem mem_residualReachable {N : FlowNetwork V} {f : V → V → ℝ} {v : V} :
    v ∈ N.residualReachable f ↔ Relation.ReflTransGen (N.IsResidualEdge f) N.source v := by
  simp [residualReachable, Set.Finite.mem_toFinset]

omit [DecidableEq V] in
theorem source_mem_residualReachable (N : FlowNetwork V) (f : V → V → ℝ) :
    N.source ∈ N.residualReachable f :=
  mem_residualReachable.mpr Relation.ReflTransGen.refl

/-- **Cross-cut flux identity.** For any feasible flow and any source–sink cut `S`, the flow value
equals the net flux across the cut: forward cross-cut flow minus backward cross-cut flow. (Same
conservation-telescoping as `flowValue_le_cutCap`, here kept as an exact equality.) -/
theorem flowValue_eq_cross_flux (N : FlowNetwork V) {f : V → V → ℝ}
    (hf : N.IsFeasibleFlow f) {S : Finset V} (hS : N.IsCut S) :
    N.flowValue f = (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) - ∑ u ∈ S, ∑ v ∈ Sᶜ, f v u := by
  obtain ⟨_, _, hcons⟩ := hf
  obtain ⟨hsS, htS⟩ := hS
  have h0 : ∀ u ∈ S, u ≠ N.source → (∑ w, f u w - ∑ w, f w u) = 0 := by
    intro u huS hune
    have huni : u ≠ N.sink := fun h => htS (h ▸ huS)
    rw [hcons u hune huni, sub_self]
  have hval : N.flowValue f = ∑ u ∈ S, (∑ w, f u w - ∑ w, f w u) := by
    rw [Finset.sum_eq_single_of_mem N.source hsS h0]; rfl
  have e1 : ∑ u ∈ S, ∑ w, f u w
      = ∑ u ∈ S, ∑ w ∈ S, f u w + ∑ u ∈ S, ∑ w ∈ Sᶜ, f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S (fun w => f u w)).symm
  have e2 : ∑ u ∈ S, ∑ w, f w u
      = ∑ u ∈ S, ∑ w ∈ S, f w u + ∑ u ∈ S, ∑ w ∈ Sᶜ, f w u := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S (fun w => f w u)).symm
  have ecomm : ∑ u ∈ S, ∑ w ∈ S, f u w = ∑ u ∈ S, ∑ w ∈ S, f w u := Finset.sum_comm
  rw [hval, Finset.sum_sub_distrib, e1, e2, ecomm]; ring

/-- **Saturation (easy direction).** If the sink is NOT residual-reachable from the source under a
feasible flow `f`, then the residual-reachable set is a source–sink cut that `f` *saturates*:
`flowValue f = cutCap (residualReachable f)`. Every forward cross-cut edge is filled to capacity and
every backward cross-cut edge carries no flow (else the far endpoint would be reachable). -/
theorem flowValue_eq_cutCap_residualReachable (N : FlowNetwork V) {f : V → V → ℝ}
    (hf : N.IsFeasibleFlow f) (hsink : N.sink ∉ N.residualReachable f) :
    N.IsCut (N.residualReachable f) ∧
      N.flowValue f = N.cutCap (N.residualReachable f) := by
  set S := N.residualReachable f with hSdef
  have hcut : N.IsCut S := ⟨N.source_mem_residualReachable f, hsink⟩
  refine ⟨hcut, ?_⟩
  have hf0 := hf.1
  have hfcap := hf.2.1
  -- For u ∈ S, v ∉ S: the forward edge is saturated and the backward edge is empty.
  have hsat : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = N.cap u v ∧ f v u = 0 := by
    intro u huS v hvSc
    rw [Finset.mem_compl] at hvSc
    have huR : Relation.ReflTransGen (N.IsResidualEdge f) N.source u := mem_residualReachable.mp huS
    -- if (u,v) were residual, v would be reachable — contradiction
    have hnres : ¬ N.IsResidualEdge f u v := by
      intro hres
      exact hvSc (mem_residualReachable.mpr (huR.tail hres))
    rw [IsResidualEdge, not_or, not_lt, not_lt] at hnres
    exact ⟨le_antisymm (hfcap u v) hnres.1, le_antisymm hnres.2 (hf0 v u)⟩
  rw [N.flowValue_eq_cross_flux hf hcut]
  have hfwd : ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v = N.cutCap S := by
    refine Finset.sum_congr rfl fun u huS => Finset.sum_congr rfl fun v hvSc => ?_
    exact (hsat u huS v hvSc).1
  have hbwd : ∑ u ∈ S, ∑ v ∈ Sᶜ, f v u = 0 := by
    refine Finset.sum_eq_zero fun u huS => Finset.sum_eq_zero fun v hvSc => ?_
    exact (hsat u huS v hvSc).2
  rw [hfwd, hbwd, sub_zero]

/-- **Conditional max-flow–min-cut equality.** A maximum flow whose residual-reachable set excludes
the sink achieves the min cut: it is a maximum flow, the residual set is a *minimum* cut, and the two
coincide (`flowValue (max) = cutCap (min cut)`). The only remaining ingredient for *unconditional*
strong duality is that a maximum flow always has this property — the augmenting-path theorem. -/
theorem maxFlow_eq_minCut_of_no_augmenting (N : FlowNetwork V) {f : V → V → ℝ}
    (hf : N.IsFeasibleFlow f)
    (hmax : ∀ g, N.IsFeasibleFlow g → N.flowValue g ≤ N.flowValue f)
    (hsink : N.sink ∉ N.residualReachable f) :
    N.IsCut (N.residualReachable f) ∧
      N.flowValue f = N.cutCap (N.residualReachable f) ∧
      (∀ g, N.IsFeasibleFlow g → N.flowValue g ≤ N.flowValue f) ∧
      (∀ S, N.IsCut S → N.cutCap (N.residualReachable f) ≤ N.cutCap S) := by
  obtain ⟨hcut, hsatur⟩ := N.flowValue_eq_cutCap_residualReachable hf hsink
  obtain ⟨_, hmincut⟩ := N.maxFlow_minCut_of_saturating hf hcut hsatur
  exact ⟨hcut, hsatur, hmax, hmincut⟩

/-! ## The augmenting-path theorem: a maximum flow has no residual path to the sink

The remaining ingredient for unconditional strong duality. We prove the contrapositive: a residual
`source ⇝ sink` path yields a strictly larger feasible flow, contradicting maximality. The
construction inducts along a *simple* residual path, pushing flow one fresh edge at a time
(local excess change), re-scaling the push amount by convexity of feasibility + linearity of excess.
-/

/-- Net inflow (excess) of a flow at a node: `∑_w f w x − ∑_w f x w`. -/
def exc (f : V → V → ℝ) (x : V) : ℝ := (∑ w, f w x) - ∑ w, f x w

omit [DecidableEq V] in
theorem flowValue_eq_neg_exc (N : FlowNetwork V) (f : V → V → ℝ) :
    N.flowValue f = - exc f N.source := by
  unfold FlowNetwork.flowValue exc; ring

omit [DecidableEq V] in
/-- A feasible flow has zero excess at every interior node. -/
theorem exc_interior_zero {N : FlowNetwork V} {f : V → V → ℝ} (hf : N.IsFeasibleFlow f)
    {x : V} (hxs : x ≠ N.source) (hxt : x ≠ N.sink) : exc f x = 0 := by
  have := hf.2.2 x hxs hxt; unfold exc; linarith

omit [DecidableEq V] in
/-- Excess is affine: it commutes with convex combinations of flows. -/
theorem exc_convex (f g : V → V → ℝ) (t : ℝ) (x : V) :
    exc (fun i j => (1 - t) * f i j + t * g i j) x
      = (1 - t) * exc f x + t * exc g x := by
  simp only [exc, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

omit [DecidableEq V] in
/-- A convex combination of two capacity-feasible flows is capacity-feasible. -/
theorem cap_convex {N : FlowNetwork V} {f g : V → V → ℝ}
    (hf : ∀ a b, 0 ≤ f a b ∧ f a b ≤ N.cap a b) (hg : ∀ a b, 0 ≤ g a b ∧ g a b ≤ N.cap a b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : V) :
    0 ≤ (1 - t) * f a b + t * g a b ∧ (1 - t) * f a b + t * g a b ≤ N.cap a b := by
  obtain ⟨hf0, hfc⟩ := hf a b
  obtain ⟨hg0, hgc⟩ := hg a b
  constructor
  · have h1 : 0 ≤ 1 - t := by linarith
    positivity
  · nlinarith [mul_le_mul_of_nonneg_left hfc (by linarith : (0:ℝ) ≤ 1 - t),
      mul_le_mul_of_nonneg_left hgc ht0]

/-- **Local excess change under a single forward push.** Adding `δ` to the single entry `(a, b)`
(`a ≠ b`) raises the excess at `b` by `δ`, lowers it at `a` by `δ`, and leaves all other nodes
unchanged. -/
theorem exc_push_forward (f : V → V → ℝ) (a b : V) (δ : ℝ) (x : V) :
    exc (fun i j => if i = a ∧ j = b then f i j + δ else f i j) x
      = exc f x + (if x = b then δ else 0) - (if x = a then δ else 0) := by
  have hin : (∑ w, if w = a ∧ x = b then f w x + δ else f w x)
      = (∑ w, f w x) + (if x = b then δ else 0) := by
    have hsplit : ∀ w, (if w = a ∧ x = b then f w x + δ else f w x)
        = f w x + (if w = a ∧ x = b then δ else 0) := fun w => by split <;> ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    by_cases hxb : x = b
    · simp [hxb, Finset.sum_ite_eq']
    · simp [hxb]
  have hout : (∑ w, if x = a ∧ w = b then f x w + δ else f x w)
      = (∑ w, f x w) + (if x = a then δ else 0) := by
    have hsplit : ∀ w, (if x = a ∧ w = b then f x w + δ else f x w)
        = f x w + (if x = a ∧ w = b then δ else 0) := fun w => by split <;> ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    by_cases hxa : x = a
    · simp [hxa, Finset.sum_ite_eq']
    · simp [hxa]
  simp only [exc, hin, hout]; ring

/-- **The augmenting construction (core induction).** Walking a simple residual path from a node `c`
(carrying a surplus `δ` against the source's deficit) to the sink, each fresh edge is pushed
(rescaling `δ` down by convexity when needed); reaching the sink yields a feasible flow of strictly
greater value. `hfresh` says the partial flow `g` still agrees with `f` on all edges incident to the
*unwalked* nodes `l`, which keeps each next edge's residual equal to `f`'s. -/
theorem aug_core {N : FlowNetwork V} {f : V → V → ℝ} (hf : N.IsFeasibleFlow f) :
    ∀ (l : List V) (c : V) (g : V → V → ℝ) (δ : ℝ),
      0 < δ → (∀ a b, 0 ≤ g a b ∧ g a b ≤ N.cap a b) →
      exc g c = exc f c + δ → exc g N.source = exc f N.source - δ →
      (∀ x, x ≠ N.source → x ≠ c → exc g x = exc f x) →
      List.IsChain (N.IsResidualEdge f) (c :: l) →
      (c :: l).getLast (List.cons_ne_nil _ _) = N.sink →
      (c :: l).Nodup → N.source ∉ c :: l →
      (∀ e ∈ l, ∀ y, g e y = f e y ∧ g y e = f y e) →
      ∃ g', N.IsFeasibleFlow g' ∧ N.flowValue f < N.flowValue g' := by
  intro l
  induction l with
  | nil =>
    intro c g δ hδ hcap hc hsrc hexc _hchain hlast _hnodup _hsrcnotin _hfresh
    have hcsink : c = N.sink := by simpa using hlast
    subst hcsink
    refine ⟨g, ⟨fun a b => (hcap a b).1, fun a b => (hcap a b).2, fun x hxs hxt => ?_⟩, ?_⟩
    · have hx : exc g x = 0 := by rw [hexc x hxs hxt]; exact exc_interior_zero hf hxs hxt
      unfold exc at hx; linarith
    · rw [N.flowValue_eq_neg_exc f, N.flowValue_eq_neg_exc g, hsrc]; linarith
  | cons d l' ih =>
    intro c g δ hδ hcap hc hsrc hexc hchain hlast hnodup hsrcnotin hfresh
    obtain ⟨hcd, hchain'⟩ := List.isChain_cons_cons.mp hchain
    -- structural facts from Nodup / source∉path
    have hcm : c ∉ d :: l' := (List.nodup_cons.mp hnodup).1
    have hcd_ne : c ≠ d := List.ne_of_not_mem_cons hcm
    have hdc : d ≠ c := hcd_ne.symm
    have hc_notin_l' : c ∉ l' := List.not_mem_of_not_mem_cons hcm
    have hnodup' : (d :: l').Nodup := (List.nodup_cons.mp hnodup).2
    have hd_notin_l' : d ∉ l' := (List.nodup_cons.mp hnodup').1
    have hsrc_ne_c : N.source ≠ c := List.ne_of_not_mem_cons hsrcnotin
    have hsrcnotin' : N.source ∉ d :: l' := List.not_mem_of_not_mem_cons hsrcnotin
    have hsrc_ne_d : N.source ≠ d := List.ne_of_not_mem_cons hsrcnotin'
    -- freshness on the next edge (c,d): g agrees with f there
    have hgdc : g d c = f d c := (hfresh d (List.mem_cons_self ..) c).1
    have hgcd : g c d = f c d := (hfresh d (List.mem_cons_self ..) c).2
    have hlast' : (d :: l').getLast (List.cons_ne_nil _ _) = N.sink := by
      rwa [List.getLast_cons (List.cons_ne_nil d l')] at hlast
    -- once we have the pushed flow with surplus δ' at d, recurse via the IH
    have finish : ∀ (g₂ : V → V → ℝ) (δ' : ℝ), 0 < δ' →
        (∀ a b, 0 ≤ g₂ a b ∧ g₂ a b ≤ N.cap a b) →
        exc g₂ d = exc f d + δ' → exc g₂ N.source = exc f N.source - δ' →
        (∀ x, x ≠ N.source → x ≠ d → exc g₂ x = exc f x) →
        (∀ e ∈ l', ∀ y, g₂ e y = f e y ∧ g₂ y e = f y e) →
        ∃ g', N.IsFeasibleFlow g' ∧ N.flowValue f < N.flowValue g' :=
      fun g₂ δ' hδ' hg₂cap hg₂d hg₂src hg₂else hg₂fresh =>
        ih d g₂ δ' hδ' hg₂cap hg₂d hg₂src hg₂else hchain' hlast' hnodup' hsrcnotin' hg₂fresh
    by_cases hfwd : f c d < N.cap c d
    · -- FORWARD residual edge: push δ' along (c,d)
      have hr_pos : (0:ℝ) < N.cap c d - f c d := by linarith
      set δ' := min δ (N.cap c d - f c d) with hδ'def
      have hδ'_pos : 0 < δ' := lt_min hδ hr_pos
      have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
      have hδ'_le_r : δ' ≤ N.cap c d - f c d := min_le_right _ _
      have ht0 : 0 ≤ δ' / δ := by positivity
      have ht1 : δ' / δ ≤ 1 := (div_le_one hδ).mpr hδ'_le_δ
      have htδ : δ' / δ * δ = δ' := by field_simp
      set g₁ : V → V → ℝ := fun i j => (1 - δ'/δ) * f i j + (δ'/δ) * g i j with hg₁def
      have hg₁cap : ∀ a b, 0 ≤ g₁ a b ∧ g₁ a b ≤ N.cap a b :=
        fun a b => hg₁def ▸ cap_convex (fun a b => ⟨hf.1 a b, hf.2.1 a b⟩) hcap ht0 ht1 a b
      have hg₁exc : ∀ x, exc g₁ x = (1 - δ'/δ) * exc f x + (δ'/δ) * exc g x :=
        fun x => hg₁def ▸ exc_convex f g (δ'/δ) x
      have hg₁cd : g₁ c d = f c d := by rw [hg₁def]; simp only [hgcd]; ring
      have hg₁c : exc g₁ c = exc f c + δ' := by
        rw [hg₁exc c, hc, show (1 - δ' / δ) * exc f c + δ' / δ * (exc f c + δ)
          = exc f c + δ' / δ * δ from by ring, htδ]
      have hg₁src : exc g₁ N.source = exc f N.source - δ' := by
        rw [hg₁exc, hsrc, show (1 - δ' / δ) * exc f N.source + δ' / δ * (exc f N.source - δ)
          = exc f N.source - δ' / δ * δ from by ring, htδ]
      have hg₁else : ∀ x, x ≠ N.source → x ≠ c → exc g₁ x = exc f x :=
        fun x hxs hxc => by rw [hg₁exc x, hexc x hxs hxc]; ring
      set g₂ : V → V → ℝ := fun i j => if i = c ∧ j = d then g₁ i j + δ' else g₁ i j with hg₂def
      have hg₂exc : ∀ x, exc g₂ x = exc g₁ x + (if x = d then δ' else 0) - (if x = c then δ' else 0) :=
        fun x => hg₂def ▸ exc_push_forward g₁ c d δ' x
      refine finish g₂ δ' hδ'_pos ?_ ?_ ?_ ?_ ?_
      · intro a b
        by_cases hab : a = c ∧ b = d
        · obtain ⟨rfl, rfl⟩ := hab
          rw [hg₂def]; simp only [and_self, if_true, hg₁cd]
          exact ⟨by linarith [hf.1 a b], by linarith⟩
        · rw [hg₂def]; simp only [hab, if_false]; exact hg₁cap a b
      · rw [hg₂exc d, if_pos rfl, if_neg hdc, hg₁exc d, hexc d hsrc_ne_d.symm hdc]; ring
      · rw [hg₂exc N.source, if_neg hsrc_ne_d, if_neg hsrc_ne_c, hg₁src]; ring
      · intro x hxs hxd
        rw [hg₂exc x, if_neg hxd]
        by_cases hxc : x = c
        · subst hxc; rw [if_pos rfl, hg₁c]; ring
        · rw [if_neg hxc, hg₁else x hxs hxc]; ring
      · intro e he y
        have hec : e ≠ c := fun h => hc_notin_l' (h ▸ he)
        have hed : e ≠ d := fun h => hd_notin_l' (h ▸ he)
        have hgey := hfresh e (List.mem_cons_of_mem d he) y
        refine ⟨?_, ?_⟩
        · rw [hg₂def]; simp only [if_neg (fun h : e = c ∧ y = d => hec h.1)]
          rw [hg₁def]; simp only [hgey.1]; ring
        · rw [hg₂def]; simp only [if_neg (fun h : y = c ∧ e = d => hed h.2)]
          rw [hg₁def]; simp only [hgey.2]; ring
    · -- BACKWARD residual edge: reduce reverse flow on (d,c)
      have hbwd : 0 < f d c := hcd.resolve_left hfwd
      set δ' := min δ (f d c) with hδ'def
      have hδ'_pos : 0 < δ' := lt_min hδ hbwd
      have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
      have hδ'_le_r : δ' ≤ f d c := min_le_right _ _
      have ht0 : 0 ≤ δ' / δ := by positivity
      have ht1 : δ' / δ ≤ 1 := (div_le_one hδ).mpr hδ'_le_δ
      have htδ : δ' / δ * δ = δ' := by field_simp
      set g₁ : V → V → ℝ := fun i j => (1 - δ'/δ) * f i j + (δ'/δ) * g i j with hg₁def
      have hg₁cap : ∀ a b, 0 ≤ g₁ a b ∧ g₁ a b ≤ N.cap a b :=
        fun a b => hg₁def ▸ cap_convex (fun a b => ⟨hf.1 a b, hf.2.1 a b⟩) hcap ht0 ht1 a b
      have hg₁exc : ∀ x, exc g₁ x = (1 - δ'/δ) * exc f x + (δ'/δ) * exc g x :=
        fun x => hg₁def ▸ exc_convex f g (δ'/δ) x
      have hg₁dc : g₁ d c = f d c := by rw [hg₁def]; simp only [hgdc]; ring
      have hg₁c : exc g₁ c = exc f c + δ' := by
        rw [hg₁exc c, hc, show (1 - δ' / δ) * exc f c + δ' / δ * (exc f c + δ)
          = exc f c + δ' / δ * δ from by ring, htδ]
      have hg₁src : exc g₁ N.source = exc f N.source - δ' := by
        rw [hg₁exc, hsrc, show (1 - δ' / δ) * exc f N.source + δ' / δ * (exc f N.source - δ)
          = exc f N.source - δ' / δ * δ from by ring, htδ]
      have hg₁else : ∀ x, x ≠ N.source → x ≠ c → exc g₁ x = exc f x :=
        fun x hxs hxc => by rw [hg₁exc x, hexc x hxs hxc]; ring
      set g₂ : V → V → ℝ := fun i j => if i = d ∧ j = c then g₁ i j + (-δ') else g₁ i j with hg₂def
      have hg₂exc : ∀ x,
          exc g₂ x = exc g₁ x + (if x = c then -δ' else 0) - (if x = d then -δ' else 0) :=
        fun x => hg₂def ▸ exc_push_forward g₁ d c (-δ') x
      refine finish g₂ δ' hδ'_pos ?_ ?_ ?_ ?_ ?_
      · intro a b
        by_cases hab : a = d ∧ b = c
        · obtain ⟨rfl, rfl⟩ := hab
          rw [hg₂def]; simp only [and_self, if_true, hg₁dc]
          exact ⟨by linarith, by linarith [hf.2.1 a b]⟩
        · rw [hg₂def]; simp only [hab, if_false]; exact hg₁cap a b
      · rw [hg₂exc d, if_neg hdc, if_pos rfl, hg₁exc d, hexc d hsrc_ne_d.symm hdc]; ring
      · rw [hg₂exc N.source, if_neg hsrc_ne_c, if_neg hsrc_ne_d, hg₁src]; ring
      · intro x hxs hxd
        rw [hg₂exc x, if_neg hxd]
        by_cases hxc : x = c
        · subst hxc; rw [if_pos rfl, hg₁c]; ring
        · rw [if_neg hxc, hg₁else x hxs hxc]; ring
      · intro e he y
        have hec : e ≠ c := fun h => hc_notin_l' (h ▸ he)
        have hed : e ≠ d := fun h => hd_notin_l' (h ▸ he)
        have hgey := hfresh e (List.mem_cons_of_mem d he) y
        refine ⟨?_, ?_⟩
        · rw [hg₂def]; simp only [if_neg (fun h : e = d ∧ y = c => hed h.1)]
          rw [hg₁def]; simp only [hgey.1]; ring
        · rw [hg₂def]; simp only [if_neg (fun h : y = d ∧ e = c => hec h.2)]
          rw [hg₁def]; simp only [hgey.2]; ring

omit [Fintype V] in
/-- **Simple-path extraction.** A reflexive-transitive-closure witness from `a` to `b` refines to a
*simple* (`Nodup`) chain with the same endpoints, whose vertices are among the original chain's. Cycle
removal by strong induction on the length: splice out a repeated head, or recurse on the tail. -/
theorem exists_nodup_chain {r : V → V → Prop} (a b : V) :
    ∀ (n : ℕ) (l : List V), l.length ≤ n → List.IsChain r (a :: l) →
      (a :: l).getLast (List.cons_ne_nil _ _) = b →
      ∃ l', List.IsChain r (a :: l') ∧
        (a :: l').getLast (List.cons_ne_nil _ _) = b ∧ (a :: l').Nodup ∧
        (∀ x ∈ a :: l', x ∈ a :: l) := by
  intro n
  induction n generalizing a with
  | zero =>
    intro l hlen hchain hlast
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hl
    exact ⟨[], hchain, hlast, by simp, fun x hx => hx⟩
  | succ n ih =>
    intro l hlen hchain hlast
    by_cases hnd : (a :: l).Nodup
    · exact ⟨l, hchain, hlast, hnd, fun x hx => hx⟩
    · by_cases ha : a ∈ l
      · -- `a` repeats: splice to the suffix `a :: t`
        obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
        have hsplit : a :: (s ++ a :: t) = (a :: s) ++ (a :: t) := by simp
        have hchain_at : List.IsChain r (a :: t) :=
          hchain.infix (hsplit ▸ (List.suffix_append (a :: s) (a :: t)).isInfix)
        have hlast_at : (a :: t).getLast (List.cons_ne_nil _ _) = b := by
          have key : (a :: t).getLast? = some b := by
            rw [← List.getLast?_append_cons (a :: s) a t, ← hsplit,
              List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _), hlast]
          rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)] at key
          exact Option.some.inj key
        have hlen_t : t.length ≤ n := by
          simp only [List.length_append, List.length_cons] at hlen; omega
        obtain ⟨l', hc', hlast', hnd', hsub'⟩ := ih a t hlen_t hchain_at hlast_at
        refine ⟨l', hc', hlast', hnd', fun x hx => ?_⟩
        rcases List.mem_cons.mp (hsub' x hx) with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append_right s (List.mem_cons_of_mem a h))
      · -- `a` is fresh; the cycle is inside `l = d :: l''`
        have hlnd : ¬ l.Nodup := fun h => hnd (List.nodup_cons.mpr ⟨ha, h⟩)
        cases l with
        | nil => exact absurd List.nodup_nil hlnd
        | cons d l'' =>
          obtain ⟨hrad, hchain''⟩ := List.isChain_cons_cons.mp hchain
          have hlast'' : (d :: l'').getLast (List.cons_ne_nil _ _) = b := by
            rwa [List.getLast_cons (List.cons_ne_nil d l'')] at hlast
          have hlen'' : l''.length ≤ n := by
            simp only [List.length_cons] at hlen; omega
          obtain ⟨l', hc', hlast', hnd', hsub'⟩ := ih d l'' hlen'' hchain'' hlast''
          refine ⟨d :: l', List.isChain_cons_cons.mpr ⟨hrad, hc'⟩, ?_, ?_, ?_⟩
          · rw [List.getLast_cons (List.cons_ne_nil d l')]; exact hlast'
          · refine List.nodup_cons.mpr ⟨fun hmem => ha ?_, hnd'⟩
            exact hsub' a hmem
          · intro x hx
            rcases List.mem_cons.mp hx with h | h
            · exact h ▸ List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (hsub' x h)

/-- **Augmenting flow.** A residual `source ⇝ sink` path yields a strictly larger feasible flow:
extract a simple residual path, push along its first edge to seed the surplus, then run `aug_core`. -/
theorem augment {N : FlowNetwork V} {f : V → V → ℝ} (hf : N.IsFeasibleFlow f)
    (hreach : Relation.ReflTransGen (N.IsResidualEdge f) N.source N.sink) (hst : N.source ≠ N.sink) :
    ∃ g, N.IsFeasibleFlow g ∧ N.flowValue f < N.flowValue g := by
  obtain ⟨l₀, hchain₀, hlast₀⟩ := List.exists_isChain_cons_of_relationReflTransGen hreach
  obtain ⟨l, hchain, hlast, hnodup, _⟩ :=
    exists_nodup_chain N.source N.sink l₀.length l₀ le_rfl hchain₀ hlast₀
  cases l with
  | nil => exact absurd (by simpa using hlast) hst
  | cons p₁ rest =>
    obtain ⟨hres, hchain'⟩ := List.isChain_cons_cons.mp hchain
    have hsrcnotin' : N.source ∉ p₁ :: rest := (List.nodup_cons.mp hnodup).1
    have hnodup' : (p₁ :: rest).Nodup := (List.nodup_cons.mp hnodup).2
    have hsp₁ : N.source ≠ p₁ := List.ne_of_not_mem_cons hsrcnotin'
    have hp₁s : p₁ ≠ N.source := hsp₁.symm
    have hsrc_notin_rest : N.source ∉ rest := List.not_mem_of_not_mem_cons hsrcnotin'
    have hp₁_notin_rest : p₁ ∉ rest := (List.nodup_cons.mp hnodup').1
    have hlast' : (p₁ :: rest).getLast (List.cons_ne_nil _ _) = N.sink := by
      rwa [List.getLast_cons (List.cons_ne_nil p₁ rest)] at hlast
    -- a pushed seed flow `g₁` with surplus `δ₁` at `p₁`, deficit at the source, fresh on `rest`
    suffices H : ∀ (g₁ : V → V → ℝ) (δ₁ : ℝ), 0 < δ₁ →
        (∀ a b, 0 ≤ g₁ a b ∧ g₁ a b ≤ N.cap a b) →
        exc g₁ p₁ = exc f p₁ + δ₁ → exc g₁ N.source = exc f N.source - δ₁ →
        (∀ x, x ≠ N.source → x ≠ p₁ → exc g₁ x = exc f x) →
        (∀ e ∈ rest, ∀ y, g₁ e y = f e y ∧ g₁ y e = f y e) →
        ∃ g, N.IsFeasibleFlow g ∧ N.flowValue f < N.flowValue g by
      have hfreshmk : ∀ (g₁ : V → V → ℝ),
          (∀ a b, (a ≠ N.source ∨ b ≠ p₁) → (a ≠ p₁ ∨ b ≠ N.source) → g₁ a b = f a b) →
          (∀ e ∈ rest, ∀ y, g₁ e y = f e y ∧ g₁ y e = f y e) := by
        intro g₁ hg e he y
        have hes : e ≠ N.source := fun h => hsrc_notin_rest (h ▸ he)
        have hep₁ : e ≠ p₁ := fun h => hp₁_notin_rest (h ▸ he)
        exact ⟨hg e y (Or.inl hes) (Or.inl hep₁), hg y e (Or.inr hep₁) (Or.inr hes)⟩
      rcases hres with hfwd | hbwd
      · -- forward seed edge: push δ₁ = cap - f on (source, p₁)
        set δ₁ := N.cap N.source p₁ - f N.source p₁ with hδ₁def
        have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; linarith
        set g₁ : V → V → ℝ :=
          fun i j => if i = N.source ∧ j = p₁ then f i j + δ₁ else f i j with hg₁def
        have hg₁exc : ∀ x, exc g₁ x = exc f x + (if x = p₁ then δ₁ else 0)
            - (if x = N.source then δ₁ else 0) := fun x => hg₁def ▸ exc_push_forward f N.source p₁ δ₁ x
        refine H g₁ δ₁ hδ₁ ?_ ?_ ?_ ?_ (hfreshmk g₁ ?_)
        · intro a b
          by_cases hab : a = N.source ∧ b = p₁
          · rw [hg₁def]; simp only [if_pos hab]; rw [hab.1, hab.2]
            exact ⟨by linarith [hf.1 N.source p₁], by rw [hδ₁def]; linarith⟩
          · rw [hg₁def]; simp only [hab, if_false]; exact ⟨hf.1 a b, hf.2.1 a b⟩
        · rw [hg₁exc p₁, if_pos rfl, if_neg hp₁s]; ring
        · rw [hg₁exc N.source, if_neg hsp₁, if_pos rfl]; ring
        · intro x hxs hxp; rw [hg₁exc x, if_neg hxp, if_neg hxs]; ring
        · intro a b hab _hab'
          have hne : ¬(a = N.source ∧ b = p₁) := by
            rintro ⟨rfl, rfl⟩; rcases hab with h1 | h1 <;> exact h1 rfl
          rw [hg₁def]; simp only [if_neg hne]
      · -- backward seed edge: reduce reverse flow δ₁ = f p₁ source on (p₁, source)
        set δ₁ := f p₁ N.source with hδ₁def
        have hδ₁ : 0 < δ₁ := hbwd
        set g₁ : V → V → ℝ :=
          fun i j => if i = p₁ ∧ j = N.source then f i j + (-δ₁) else f i j with hg₁def
        have hg₁exc : ∀ x, exc g₁ x = exc f x + (if x = N.source then -δ₁ else 0)
            - (if x = p₁ then -δ₁ else 0) := fun x => hg₁def ▸ exc_push_forward f p₁ N.source (-δ₁) x
        refine H g₁ δ₁ hδ₁ ?_ ?_ ?_ ?_ (hfreshmk g₁ ?_)
        · intro a b
          by_cases hab : a = p₁ ∧ b = N.source
          · rw [hg₁def]; simp only [if_pos hab]; rw [hab.1, hab.2]
            exact ⟨by rw [hδ₁def]; linarith, by linarith [hf.2.1 p₁ N.source]⟩
          · rw [hg₁def]; simp only [hab, if_false]; exact ⟨hf.1 a b, hf.2.1 a b⟩
        · rw [hg₁exc p₁, if_neg hp₁s, if_pos rfl]; ring
        · rw [hg₁exc N.source, if_pos rfl, if_neg hsp₁]; ring
        · intro x hxs hxp; rw [hg₁exc x, if_neg hxs, if_neg hxp]; ring
        · intro a b _hab hab'
          have hne : ¬(a = p₁ ∧ b = N.source) := by
            rintro ⟨rfl, rfl⟩; rcases hab' with h1 | h1 <;> exact h1 rfl
          rw [hg₁def]; simp only [if_neg hne]
    -- run the core induction from `p₁`
    intro g₁ δ₁ hδ₁ hg₁cap hg₁p₁ hg₁src hg₁else hg₁fresh
    exact aug_core hf rest p₁ g₁ δ₁ hδ₁ hg₁cap hg₁p₁ hg₁src hg₁else hchain' hlast' hnodup'
      hsrcnotin' hg₁fresh

/-- **Maximum flow has no augmenting path.** If `f` is a maximum flow then the sink is not
residual-reachable from the source (else `augment` would build a strictly larger feasible flow). -/
theorem maxFlow_no_augmenting {N : FlowNetwork V} {f : V → V → ℝ} (hf : N.IsFeasibleFlow f)
    (hmax : ∀ g, N.IsFeasibleFlow g → N.flowValue g ≤ N.flowValue f) (hst : N.source ≠ N.sink) :
    N.sink ∉ N.residualReachable f := by
  intro hsink
  obtain ⟨g, hg, hlt⟩ := augment hf (mem_residualReachable.mp hsink) hst
  exact absurd (hmax g hg) (not_le.mpr hlt)

/-- **Max-flow–min-cut (strong duality), unconditional.** For any finite capacity-weighted network
with `source ≠ sink`, there is a feasible flow `f` and a source–sink cut `S` with `flowValue f =
cutCap S`, where `f` is a maximum flow and `S` is a minimum cut. Hence the maximum flow value equals
the minimum cut capacity. -/
theorem maxFlow_eq_minCut (N : FlowNetwork V) (hst : N.source ≠ N.sink) :
    ∃ (f : V → V → ℝ) (S : Finset V), N.IsFeasibleFlow f ∧ N.IsCut S ∧
      N.flowValue f = N.cutCap S ∧
      (∀ g, N.IsFeasibleFlow g → N.flowValue g ≤ N.flowValue f) ∧
      (∀ S', N.IsCut S' → N.cutCap S ≤ N.cutCap S') := by
  obtain ⟨f, hf, hmax⟩ := N.maxFlow_exists
  have hsink := maxFlow_no_augmenting hf hmax hst
  obtain ⟨hcut, hsat, _, hmincut⟩ := N.maxFlow_eq_minCut_of_no_augmenting hf hmax hsink
  exact ⟨f, N.residualReachable f, hf, hcut, hsat, hmax, hmincut⟩

end FlowNetwork

end SKEFTHawking.QuantumNetwork
