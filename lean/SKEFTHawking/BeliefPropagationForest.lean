import SKEFTHawking.BeliefPropagation

/-!
# Constructive forest ranks for the actual all-pairs BP carrier

Ranks count the source component after deleting the outgoing edge, minus one.
Deleting a nonedge leaves the original component, so nonincident coordinates are
retained. The existing unnormalized full-assignment dynamics is unchanged.
-/

namespace SKEFTHawking.BeliefPropagation

open SimpleGraph

/-- Source-side vertices after deleting the outgoing unordered edge. This also
    defines the source component for nonincident outgoing coordinates. -/
noncomputable def forestBranch {U : Type*} [Fintype U]
    (G : SimpleGraph U) (x y : U) : Finset U := by
  classical
  exact Finset.univ.filter fun w => (G.deleteEdges {s(x, y)}).Reachable x w

/-- The source itself is always in its cut component. -/
theorem mem_forestBranch_self {U : Type*} [Fintype U]
    (G : SimpleGraph U) (x y : U) : x ∈ forestBranch G x y := by
  classical
  simp [forestBranch]

/-- The opposite endpoint is absent when the removed edge belongs to a forest. -/
theorem not_mem_forestBranch_of_adj {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x z : U} (hzx : G.Adj z x) :
    x ∉ forestBranch G z x := by
  classical
  simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and]
  exact SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG hzx

/-- Each incoming cut branch embeds in the outgoing source branch, including
    when the outgoing pair is a nonedge. -/
theorem forestBranch_subset_next {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x y z : U}
    (hzx : G.Adj z x) (hzy : z ≠ y) :
    forestBranch G z x ⊆ forestBranch G x y := by
  classical
  intro w hw
  simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with ⟨p⟩
  have hb : ¬(G.deleteEdges {s(z, x)}).Reachable z x :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG hzx
  have hx : x ∉ p.support := fun hx => hb (p.takeUntil x hx).reachable
  have q : (G.deleteEdges {s(x, y)}).Reachable z w := by
    refine ⟨p.transfer _ ?_⟩
    intro e he
    have hg := p.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at hg ⊢
    refine ⟨hg.1, ?_⟩
    intro heq
    have heq' : e = s(x, y) := heq
    subst e
    exact hx (p.fst_mem_support_of_mem_edges he)
  have ha : (G.deleteEdges {s(x, y)}).Adj x z := by
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨hzx.symm, ?_⟩
    simp [hzy, hzx.ne]
  exact ha.reachable.trans q

/-- The inclusion is strict because the outgoing source is missing from its
    incoming cut branch. -/
theorem forestBranch_ssubset_next {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x y z : U}
    (hzx : G.Adj z x) (hzy : z ≠ y) :
    forestBranch G z x ⊂ forestBranch G x y := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨forestBranch_subset_next G hG hzx hzy, ?_⟩
  intro he
  exact not_mem_forestBranch_of_adj G hG hzx
    (he.symm ▸ mem_forestBranch_self G x y)

/-- Cardinality-minus-one rank of the actual source cut component. -/
noncomputable def forestEdgeRank {U : Type*} [Fintype U]
    (G : SimpleGraph U) (x y : U) : ℕ := (forestBranch G x y).card - 1

/-- Component cardinality gives a strict rank for every actual dependency. -/
theorem forestEdgeRank_lt_next {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x y z : U}
    (hzx : G.Adj z x) (hzy : z ≠ y) :
    forestEdgeRank G z x < forestEdgeRank G x y := by
  classical
  have hlt := Finset.card_lt_card (forestBranch_ssubset_next G hG hzx hzy)
  have hpos := Finset.card_pos.mpr ⟨z, mem_forestBranch_self G z x⟩
  unfold forestEdgeRank
  omega

/-- A constructed rank on every existing message coordinate; no certificate is
    assumed and nonincident outgoing coordinates are retained. -/
noncomputable def forestMessageRank {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) : MsgEndpoint ν α → ℕ
  | Sum.inl (v, a) => forestEdgeRank (incidenceGraph G) (Sum.inl v) (Sum.inr a)
  | Sum.inr (a, v) => forestEdgeRank (incidenceGraph G) (Sum.inr a) (Sum.inl v)

/-- Genuine incidence acyclicity constructs both strict certificate fields. -/
noncomputable def bpRankCertForest {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) : BPRankCert G where
  rank := forestMessageRank G
  var_gt := by
    intro v a b hba hb
    exact forestEdgeRank_lt_next _ hG
      ((incidenceGraph_inl_inr_adj G v b).mpr hb).symm (by simpa using hba)
  fac_gt := by
    intro a v u huv hu
    exact forestEdgeRank_lt_next _ hG
      ((incidenceGraph_inl_inr_adj G u a).mpr hu) (by simpa using huv)

/-- Every cut-component rank is bounded by the actual finite vertex carrier. -/
theorem forestEdgeRank_add_one_le {U : Type*} [Fintype U]
    (G : SimpleGraph U) (x y : U) :
    forestEdgeRank G x y + 1 ≤ Fintype.card U := by
  classical
  have hpos := Finset.card_pos.mpr ⟨x, mem_forestBranch_self G x y⟩
  have hcard := Finset.card_le_univ (forestBranch G x y)
  unfold forestEdgeRank
  omega

/-- The constructed all-pairs certificate has a safe graph-size horizon.
    The maximum with one retains the source's empty-coordinate convention. -/
theorem convergenceHorizon_forest_le {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) :
    convergenceHorizon (forestMessageRank G) ≤ max 1 (Fintype.card ν + Fintype.card α) := by
  classical
  unfold convergenceHorizon
  apply Nat.succ_le_of_lt
  apply (Finset.sup_lt_iff (by exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))).mpr
  intro e _
  cases e with
  | inl va =>
    have h := forestEdgeRank_add_one_le (incidenceGraph G) (Sum.inl va.1) (Sum.inr va.2)
    simp only [Fintype.card_sum] at h
    change forestEdgeRank (incidenceGraph G) (Sum.inl va.1) (Sum.inr va.2) < _
    omega
  | inr av =>
    have h := forestEdgeRank_add_one_le (incidenceGraph G) (Sum.inr av.1) (Sum.inl av.2)
    simp only [Fintype.card_sum] at h
    change forestEdgeRank (incidenceGraph G) (Sum.inr av.1) (Sum.inl av.2) < _
    omega

/-- Acyclicity alone now gives full-array stabilization and a fixed point at
    the safe graph-size horizon for the actual existing BP update. -/
theorem bp_converges_on_forest {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (factorWeight : α → (ν → X) → ℝ) (m : BPMessages ν α G X) :
    (∀ n, max 1 (Fintype.card ν + Fintype.card α) ≤ n →
      (fun m' => bpUpdate m' factorWeight)^[n] m =
      (fun m' => bpUpdate m' factorWeight)^[max 1 (Fintype.card ν + Fintype.card α)] m) ∧
    IsBPFixedPoint
      ((fun m' => bpUpdate m' factorWeight)^[max 1 (Fintype.card ν + Fintype.card α)] m)
      factorWeight := by
  obtain ⟨hs, hf⟩ := bp_converges_on_ranked_acyclic (bpRankCertForest G hG) factorWeight m
  have hb := convergenceHorizon_forest_le G
  have he := hs _ hb
  refine ⟨fun n hn => (hs n (hb.trans hn)).trans he.symm, ?_⟩
  rw [he]
  exact hf

/-- Actual five-node incidence path v0-a0-v1-a1-v2. -/
def fiveNodePath : FactorGraph (Fin 3) (Fin 2) where
  incidence a v := if a = 0 then v = 0 ∨ v = 1 else v = 1 ∨ v = 2

/-- Explicit component-cardinality ranks on all twelve directed coordinates
    of the five-node path. In particular, nonedges have rank four. -/
def fiveNodePathRank : MsgEndpoint (Fin 3) (Fin 2) → ℕ
  | Sum.inl (v, a) =>
      if v = 0 then if a = 0 then 0 else 4
      else if v = 1 then 2 else if a = 0 then 4 else 0
  | Sum.inr (a, v) =>
      if a = 0 then if v = 0 then 3 else if v = 1 then 1 else 4
      else if v = 0 then 4 else if v = 1 then 1 else 3

/-- Both strict fields are exercised on the five-node path. -/
def bpRankCertFiveNodePath : BPRankCert fiveNodePath where
  rank := fiveNodePathRank
  var_gt := by
    intro v a b hba hb
    fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp_all [fiveNodePath, fiveNodePathRank]
  fac_gt := by
    intro a v u huv hu
    fin_cases a <;> fin_cases v <;> fin_cases u <;>
      simp_all [fiveNodePath, fiveNodePathRank]

/-- A genuine nonincident coordinate has rank four. -/
theorem fiveNodePath_nonincident_rank :
    bpRankCertFiveNodePath.rank (Sum.inl (2, 0)) = 4 := by decide +kernel

/-- The maximum includes nonincident coordinates, giving horizon five. -/
theorem fiveNodePath_horizon : convergenceHorizon bpRankCertFiveNodePath.rank = 5 := by
  decide +kernel

/-- Both variable and factor inequalities have actual incoming dependencies. -/
theorem fiveNodePath_two_strict_fields :
    bpRankCertFiveNodePath.rank (Sum.inr (0, 1)) <
      bpRankCertFiveNodePath.rank (Sum.inl (1, 1)) ∧
    bpRankCertFiveNodePath.rank (Sum.inl (0, 0)) <
      bpRankCertFiveNodePath.rank (Sum.inr (0, 1)) := by
  constructor
  · exact bpRankCertFiveNodePath.var_gt 1 1 0 (by decide) (by decide)
  · exact bpRankCertFiveNodePath.fac_gt 0 1 0 (by decide) (by decide)

/-- With singleton alphabet and unit factors, these five actual source updates
    form the dependency chain ending at the nonincident outgoing pair. -/
theorem fiveNodePath_update_chain
    (m : BPMessages (Fin 3) (Fin 2) fiveNodePath Unit) :
    (bpUpdate m (fun _ _ => 1)).varToFactor 0 0 () = 1 ∧
    (bpUpdate m (fun _ _ => 1)).factorToVar 0 1 () = m.varToFactor 0 0 () ∧
    (bpUpdate m (fun _ _ => 1)).varToFactor 1 1 () = m.factorToVar 0 1 () ∧
    (bpUpdate m (fun _ _ => 1)).factorToVar 1 2 () = m.varToFactor 1 1 () ∧
    (bpUpdate m (fun _ _ => 1)).varToFactor 2 0 () = m.factorToVar 1 2 () := by
  simp [bpUpdate, bpVariableUpdate, bpFactorUpdate, otherFactors, otherVars,
    fiveNodePath, Finset.prod_filter, Fin.prod_univ_succ]

/-- Initial values are two at every coordinate, including nonedges. -/
def fiveNodePathInitial : BPMessages (Fin 3) (Fin 2) fiveNodePath Unit where
  varToFactor _ _ _ := 2
  factorToVar _ _ _ := 2

/-- Actual iterates of the unchanged synchronous update. -/
noncomputable def fiveNodePathIterate (n : ℕ) :
    BPMessages (Fin 3) (Fin 2) fiveNodePath Unit :=
  (fun m => bpUpdate m (fun _ _ => 1))^[n] fiveNodePathInitial

/-- The nonincident message has not stabilized at graph diameter four. -/
theorem fiveNodePath_sweep_four :
    (fiveNodePathIterate 4).varToFactor 2 0 () = 2 := by
  simp [fiveNodePathIterate, Function.iterate_succ_apply',
    fiveNodePath_update_chain, fiveNodePathInitial]

/-- The same actual coordinate becomes one on sweep five. -/
theorem fiveNodePath_sweep_five :
    (fiveNodePathIterate 5).varToFactor 2 0 () = 1 := by
  simp only [fiveNodePathIterate, Function.iterate_succ_apply',
    fiveNodePath_update_chain, fiveNodePathInitial]

/-- The diameter-four whole-state fixed-point assertion is false for the actual
    all-pairs dynamics, as witnessed by this one nonincident coordinate. -/
theorem fiveNodePath_not_fixed_at_four :
    ¬ IsBPFixedPoint (fiveNodePathIterate 4) (fun _ _ => 1) := by
  intro h
  have he : fiveNodePathIterate 5 = fiveNodePathIterate 4 := by
    exact h
  have hc := congrArg (fun m : BPMessages (Fin 3) (Fin 2) fiveNodePath Unit =>
    m.varToFactor 2 0 ()) he
  rw [fiveNodePath_sweep_four, fiveNodePath_sweep_five] at hc
  norm_num at hc

/-- Extend a certificate rank to directed incidence-graph vertex pairs.
    Same-part pairs are unused by the adjacency-constrained cycle argument. -/
def bpVertexRank {ν α : Type*} {G : FactorGraph ν α} (cert : BPRankCert G) :
    (ν ⊕ α) → (ν ⊕ α) → ℕ
  | Sum.inl v, Sum.inr a => cert.rank (Sum.inl (v, a))
  | Sum.inr a, Sum.inl v => cert.rank (Sum.inr (a, v))
  | _, _ => 0

/-- Existing certificate fields increase ranks along every actual
    nonbacktracking incidence step. -/
theorem bpVertexRank_lt {ν α : Type*} {G : FactorGraph ν α}
    (cert : BPRankCert G) {x y z : ν ⊕ α}
    (hzx : (incidenceGraph G).Adj z x) (hxy : (incidenceGraph G).Adj x y)
    (hzy : z ≠ y) : bpVertexRank cert z x < bpVertexRank cert x y := by
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp_all [bpVertexRank, incidenceGraph, SimpleGraph.fromRel_adj]
  all_goals first | apply cert.var_gt <;> assumption | apply cert.fac_gt <;> assumption

/-- A natural rank that increases along actual nonbacktracking adjacent steps
    forbids every simple cycle, of arbitrary length. -/
theorem isAcyclic_of_strict_edgeRank {U : Type*} (G : SimpleGraph U)
    (r : U → U → ℕ)
    (hstep : ∀ {x y z}, G.Adj z x → G.Adj x y → z ≠ y → r z x < r x y) :
    G.IsAcyclic := by
  intro u p hp
  have hl := hp.three_le_length
  have hi : ∀ n, n + 1 < p.length →
      r (p.getVert n) (p.getVert (n + 1)) <
        r (p.getVert (n + 1)) (p.getVert (n + 2)) := by
    intro n hn
    apply hstep (p.adj_getVert_succ (by omega)) (p.adj_getVert_succ hn)
    have h := hp.getVert_sub_one_ne_getVert_add_one (i := n + 1) (by omega)
    simpa using h
  have hle : ∀ n, n < p.length →
      r (p.getVert 0) (p.getVert 1) ≤ r (p.getVert n) (p.getVert (n + 1)) := by
    intro n hn
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (ih (by omega)).trans (hi n (by omega)).le
  have hend := hle (p.length - 1) (by omega)
  have hlast : G.Adj (p.getVert (p.length - 1)) (p.getVert 0) := by
    simpa [show p.length - 1 + 1 = p.length by omega] using p.adj_getVert_succ (i := p.length - 1) (by omega)
  have hne : p.getVert (p.length - 1) ≠ p.getVert 1 := by
    intro he
    have h := hp.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega
  have hclose := hstep hlast (p.adj_getVert_succ (i := 0) (by omega)) hne
  simp only [show p.length - 1 + 1 = p.length by omega, SimpleGraph.Walk.getVert_length,
    SimpleGraph.Walk.getVert_zero, Nat.zero_add] at hend hclose
  omega

/-- A certificate forbids every actual incidence cycle, not merely four-cycles. -/
theorem isAcyclicFactorGraph_of_bpRankCert {ν α : Type*}
    {G : FactorGraph ν α} (cert : BPRankCert G) : IsAcyclicFactorGraph G := by
  exact isAcyclic_of_strict_edgeRank (incidenceGraph G) (bpVertexRank cert)
    (fun hzx hxy hzy => bpVertexRank_lt cert hzx hxy hzy)

/-- Actual incidence-cycle obstruction to the existence of a certificate. -/
theorem no_bpRankCert_of_incidence_cycle {ν α : Type*} (G : FactorGraph ν α)
    {u : ν ⊕ α} (p : (incidenceGraph G).Walk u u) (hp : p.IsCycle) :
    ¬ Nonempty (BPRankCert G) := by
  rintro ⟨cert⟩
  exact isAcyclicFactorGraph_of_bpRankCert cert p hp

/-- The actual all-pairs certificate exists exactly on finite forests. -/
theorem nonempty_bpRankCert_iff_acyclic {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) : Nonempty (BPRankCert G) ↔ IsAcyclicFactorGraph G := by
  exact ⟨fun ⟨cert⟩ => isAcyclicFactorGraph_of_bpRankCert cert,
    fun hG => ⟨bpRankCertForest G hG⟩⟩

/-- The five-node witness is a genuine forest; its certificate is not merely
    an assignment of ranks on a graph whose acyclicity was assumed. -/
theorem fiveNodePath_acyclic : IsAcyclicFactorGraph fiveNodePath :=
  isAcyclicFactorGraph_of_bpRankCert bpRankCertFiveNodePath

/-- For a nonedge, cutting the outgoing pair retains the complete original
    source component, exactly as required for all-pairs message semantics. -/
theorem forestBranch_of_not_adj {U : Type*} [Fintype U]
    (G : SimpleGraph U) [DecidableRel G.Reachable] {x y : U} (hxy : ¬ G.Adj x y) :
    forestBranch G x y = Finset.univ.filter (G.Reachable x) := by
  classical
  have he : G.deleteEdges {s(x, y)} = G := by
    simpa [SimpleGraph.deleteEdges_eq_self] using hxy
  simp [forestBranch, he]

/-- Every vertex of the actual five-node path is reachable from v2. -/
theorem fiveNodePath_reachable_from_right (w : Fin 3 ⊕ Fin 2) :
    (incidenceGraph fiveNodePath).Reachable (Sum.inl 2) w := by
  have h21 : (incidenceGraph fiveNodePath).Adj (Sum.inl 2) (Sum.inr 1) :=
    (incidenceGraph_inl_inr_adj _ _ _).mpr (by decide)
  have h11 : (incidenceGraph fiveNodePath).Adj (Sum.inl 1) (Sum.inr 1) :=
    (incidenceGraph_inl_inr_adj _ _ _).mpr (by decide)
  have h10 : (incidenceGraph fiveNodePath).Adj (Sum.inl 1) (Sum.inr 0) :=
    (incidenceGraph_inl_inr_adj _ _ _).mpr (by decide)
  have h00 : (incidenceGraph fiveNodePath).Adj (Sum.inl 0) (Sum.inr 0) :=
    (incidenceGraph_inl_inr_adj _ _ _).mpr (by decide)
  rcases w with v | a
  · fin_cases v
    · exact h21.reachable.trans (h11.symm.reachable.trans
        (h10.reachable.trans h00.symm.reachable))
    · exact h21.reachable.trans h11.symm.reachable
    · exact SimpleGraph.Reachable.rfl
  · fin_cases a
    · exact h21.reachable.trans (h11.symm.reachable.trans h10.reachable)
    · exact h21.reachable

/-- Rank four also belongs to the general component-cardinality construction,
    not only to the separately explicit path certificate. -/
theorem fiveNodePath_constructed_nonincident_rank :
    (bpRankCertForest fiveNodePath fiveNodePath_acyclic).rank (Sum.inl (2, 0)) = 4 := by
  classical
  change (forestBranch (incidenceGraph fiveNodePath) (Sum.inl 2) (Sum.inr 0)).card - 1 = 4
  rw [forestBranch_of_not_adj _ (by
    rw [incidenceGraph_inl_inr_adj]
    decide)]
  have he : Finset.univ.filter ((incidenceGraph fiveNodePath).Reachable (Sum.inl 2)) =
      (Finset.univ : Finset (Fin 3 ⊕ Fin 2)) := by
    ext w
    simp [fiveNodePath_reachable_from_right]
  rw [he]
  norm_num

/-- The general constructed certificate also attains horizon five on the path. -/
theorem fiveNodePath_constructed_horizon :
    convergenceHorizon (bpRankCertForest fiveNodePath fiveNodePath_acyclic).rank = 5 := by
  classical
  have hb := convergenceHorizon_forest_le fiveNodePath
  norm_num at hb
  have hl : 4 ≤ Finset.univ.sup (forestMessageRank fiveNodePath) := by
    rw [← fiveNodePath_constructed_nonincident_rank]
    exact Finset.le_sup (Finset.mem_univ (Sum.inl (2, 0)))
  change Finset.univ.sup (forestMessageRank fiveNodePath) + 1 = 5
  unfold convergenceHorizon at hb
  omega

/-- If either bipartite side is empty, the actual endpoint set is empty and
    the existing horizon convention is one, independently of the other side. -/
theorem convergenceHorizon_forest_empty_variables {α : Type*} [Fintype α]
    (G : FactorGraph (Fin 0) α) : convergenceHorizon (forestMessageRank G) = 1 := by
  simp [convergenceHorizon]

/-- The same empty-endpoint convention holds for an empty factor side. -/
theorem convergenceHorizon_forest_empty_factors {ν : Type*} [Fintype ν]
    (G : FactorGraph ν (Fin 0)) : convergenceHorizon (forestMessageRank G) = 1 := by
  simp [convergenceHorizon]

/-- All four nonincident directed path coordinates have rank four in the
    explicit certificate; this is a complete finite coordinate check. -/
theorem fiveNodePath_all_nonincident_ranks (v : Fin 3) (a : Fin 2)
    (h : fiveNodePath.incidence a v = false) :
    bpRankCertFiveNodePath.rank (Sum.inl (v, a)) = 4 ∧
    bpRankCertFiveNodePath.rank (Sum.inr (a, v)) = 4 := by
  fin_cases v <;> fin_cases a <;>
    simp_all [fiveNodePath, bpRankCertFiveNodePath, fiveNodePathRank]

/-- The actual source coordinate remains two at every sweep through four,
    rather than only at the final preconvergence sweep. -/
theorem fiveNodePath_sweeps_through_four (n : ℕ) (hn : n ≤ 4) :
    (fiveNodePathIterate n).varToFactor 2 0 () = 2 := by
  interval_cases n <;>
    simp [fiveNodePathIterate, Function.iterate_succ_apply',
      fiveNodePath_update_chain, fiveNodePathInitial]

end SKEFTHawking.BeliefPropagation
