import SKEFTHawking.BeliefPropagationForest

/-!
# Local finite probability semantics for the original BP update

The original update sums complete assignments. Scope restriction therefore
carries a positive alphabet-cardinality multiplicity. This module develops
that finite probability construction without changing the message carrier.
The general forest cavity/marginal bridge remains a separate proof target
until its component decompositions and recurrences have been derived.
-/

namespace SKEFTHawking.BeliefPropagation
namespace Probability

open scoped BigOperators

/-- Extend a genuine scope assignment, using an arbitrary background outside. -/
def extendScope {ν X : Type*} [DecidableEq ν]
    (s : Finset ν) (z : s → X) (background : ν → X) : ν → X :=
  fun v => if h : v ∈ s then z ⟨v, h⟩ else background v

/-- Scope locality of a full-assignment function, independent of the background. -/
def DependsOn {ν X : Type*} (s : Finset ν) (f : (ν → X) → ℝ) : Prop :=
  ∀ y z, (∀ v ∈ s, y v = z v) → f y = f z

/-- The actual incidence scope, including empty scopes of isolated factors. -/
def factorScope {ν α : Type*} [Fintype ν]
    (G : FactorGraph ν α) (a : α) : Finset ν :=
  Finset.univ.filter fun v => G.incidence a v = true

/-- Locality is an explicit condition on the original factor function. -/
def ScopeLocal {ν α X : Type*} [Fintype ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) : Prop :=
  ∀ a, DependsOn (factorScope G a) (f a)

/-- The joint unnormalized weight on actual complete assignments. -/
noncomputable def jointWeight {ν α X : Type*} [Fintype α]
    (f : α → (ν → X) → ℝ) (y : ν → X) : ℝ := ∏ a, f a y

/-- The true finite partition function, rather than a supplied normalization. -/
noncomputable def partition {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    (f : α → (ν → X) → ℝ) : ℝ := by
  classical
  exact ∑ y, jointWeight f y

/-- Actual complete-assignment numerator for a variable marginal. -/
noncomputable def marginalWeight {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq X]
    (f : α → (ν → X) → ℝ) (v : ν) (x : X) : ℝ := by
  classical
  exact ∑ y : ν → X with y v = x, jointWeight f y

/-- Exact number of extensions outside a scope, represented in the real field. -/
def extensionMultiplicity {ν X : Type*} [Fintype ν] [Fintype X]
    (s : Finset ν) : ℝ := (Fintype.card X : ℝ) ^ (Fintype.card ν - s.card)

/-- Summing a scope-local function over complete assignments repeats every
    actual scope assignment by exactly the number of outside assignments. -/
theorem sum_dependsOn_scope {ν X : Type*} [Fintype ν] [Fintype X] [DecidableEq ν]
    (s : Finset ν) (f : (ν → X) → ℝ) (hf : DependsOn s f) (background : ν → X) :
    ∑ y, f y = extensionMultiplicity (X := X) s * ∑ z : s → X, f (extendScope s z background) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun v : ν => v ∈ s) (fun _ => X)
  have h := Fintype.sum_equiv e f (fun p => f (extendScope s p.1 background)) (by
    intro y
    apply hf
    intro v hv
    simp [e, Equiv.piEquivPiSubtypeProd, extendScope, hv])
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp [extensionMultiplicity, Fintype.card_subtype_compl]

/-- Restriction with a fixed boundary keeps the same outside multiplicity;
    the boundary is inside the scope, so it must not be counted twice. -/
theorem sum_boundary_dependsOn_scope {ν X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    (s : Finset ν) (f : (ν → X) → ℝ) (hf : DependsOn s f)
    (background : ν → X) (v : ν) (hv : v ∈ s) (x : X) :
    (∑ y : ν → X with y v = x, f y) =
      extensionMultiplicity (X := X) s *
        ∑ z : s → X with z ⟨v, hv⟩ = x, f (extendScope s z background) := by
  classical
  have hg : DependsOn s (fun y => if y v = x then f y else 0) := by
    intro y z hyz
    change (if y v = x then f y else 0) = (if z v = x then f z else 0)
    rw [hyz v hv, hf y z hyz]
  have h := sum_dependsOn_scope s (fun y => if y v = x then f y else 0) hg background
  simpa only [Finset.sum_filter, extendScope, dif_pos hv] using h

/-- The actual factor summand ignores every variable outside the factor scope,
    because both the factor and all consumed incoming coordinates do so. -/
theorem factorSummand_dependsOn {ν α X : Type*}
    [Fintype ν] [DecidableEq ν] (G : FactorGraph ν α)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (m : BPMessages ν α G X) (a : α) (v : ν) :
    DependsOn (factorScope G a)
      (fun y => f a y * ∏ u ∈ otherVars G a v, m.varToFactor u a (y u)) := by
  intro y z hyz
  dsimp only
  rw [hf a y z hyz]
  congr 1
  apply Finset.prod_congr rfl
  intro u hu
  rw [hyz u (by simpa [factorScope] using (Finset.mem_filter.mp hu).2.2)]

/-- A local-table expression of the original factor update. The original full
    loop equals this expression multiplied by the exact outside cardinality. -/
theorem bpFactorUpdate_scope_reduction {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (m : BPMessages ν α G X) (a : α) (v : ν) (hv : v ∈ factorScope G a)
    (x : X) (background : ν → X) :
    bpFactorUpdate m f a v x = extensionMultiplicity (X := X) (factorScope G a) *
      ∑ z : factorScope G a → X with z ⟨v, hv⟩ = x,
        f a (extendScope (factorScope G a) z background) *
          ∏ u ∈ otherVars G a v,
            m.varToFactor u a (extendScope (factorScope G a) z background u) := by
  exact sum_boundary_dependsOn_scope (factorScope G a) _
    (factorSummand_dependsOn G f hf m a v) background v hv x

/-- A nonempty finite alphabet makes every outside-assignment multiplicity
    strictly positive, including an empty outside set. -/
theorem extensionMultiplicity_pos {ν X : Type*}
    [Fintype ν] [Fintype X] [Nonempty X] (s : Finset ν) :
    0 < extensionMultiplicity (X := X) s := by
  exact pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _

/-- Actual normalized joint marginal; a probability interpretation requires
    the true partition to be positive. -/
noncomputable def normalizedMarginal {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq X]
    (f : α → (ν → X) → ℝ) (v : ν) (x : X) : ℝ :=
  marginalWeight f v x / partition f

/-- Summing all actual marginal numerators recovers the full partition. -/
theorem sum_marginalWeight {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq X]
    (f : α → (ν → X) → ℝ) (v : ν) :
    ∑ x, marginalWeight f v x = partition f := by
  classical
  exact Finset.sum_fiberwise Finset.univ (fun y : ν → X => y v) (jointWeight f)

/-- The actual global marginal is normalized when the actual partition is
    positive. No assumption about BP or a putative correspondence is used. -/
theorem normalizedMarginal_sum_one {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq X]
    (f : α → (ν → X) → ℝ) (hZ : 0 < partition f) (v : ν) :
    ∑ x, normalizedMarginal f v x = 1 := by
  unfold normalizedMarginal
  rw [← Finset.sum_div, sum_marginalWeight, div_self (ne_of_gt hZ)]

/-- Nonnegative local factors give nonnegative true marginal numerators,
    allowing individual zeros without dividing by a cavity message. -/
theorem marginalWeight_nonneg {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq X]
    (f : α → (ν → X) → ℝ) (hf : ∀ a y, 0 ≤ f a y) (v : ν) (x : X) :
    0 ≤ marginalWeight f v x := by
  classical
  exact Finset.sum_nonneg (fun y _ => Finset.prod_nonneg (fun a _ => hf a y))

/-- Opposite sides of an actual forest edge have disjoint vertices. This is
    the separation needed to factor genuine cavity assignment sums. -/
theorem forestBranch_disjoint_opposite {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x y : U} (hxy : G.Adj x y) :
    Disjoint (forestBranch G x y) (forestBranch G y x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  have hyw : (G.deleteEdges {s(x, y)}).Reachable y w := by
    simpa only [Sym2.eq_swap] using hw'
  exact (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG hxy)
    (hw.trans hyw.symm)

/-- Distinct incoming branches at a node have disjoint vertex sets. This is
    derived from forest separation, rather than assumed as a cavity law. -/
theorem forestBranch_disjoint_incoming {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) {x y z : U}
    (hyx : G.Adj y x) (hzx : G.Adj z x) (hzy : z ≠ y) :
    Disjoint (forestBranch G z x) (forestBranch G y x) := by
  exact Finset.disjoint_of_subset_left (forestBranch_subset_next G hG hzx hzy)
    (forestBranch_disjoint_opposite G hG hyx.symm)

/-- The outgoing source component is exactly its source plus the incoming
    cut branches. This covers nonincident outgoing pairs as well. -/
theorem mem_forestBranch_iff_source_or_incoming {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) (x y w : U) :
    w ∈ forestBranch G x y ↔ w = x ∨
      ∃ z, G.Adj z x ∧ z ≠ y ∧ w ∈ forestBranch G z x := by
  classical
  constructor
  · intro hw
    simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨p⟩
    rcases p.toPath with ⟨q, hq⟩
    cases q with
    | nil => exact Or.inl rfl
    | @cons u z w h p =>
      right
      have hzx : G.Adj z x := h.1.symm
      have hzy : z ≠ y := by
        intro he
        subst z
        simp [SimpleGraph.deleteEdges_adj] at h
      refine ⟨z, hzx, hzy, ?_⟩
      simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨p.transfer _ ?_⟩
      intro e he
      have hg := p.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at hg ⊢
      refine ⟨hg.1, ?_⟩
      intro heq
      have heq' : e = s(z, x) := heq
      subst e
      have hn := (SimpleGraph.Walk.cons_isPath_iff h p).mp hq
      exact hn.2 (p.snd_mem_support_of_mem_edges he)
  · rintro (rfl | ⟨z, hzx, hzy, hw⟩)
    · exact mem_forestBranch_self _ _ _
    · exact forestBranch_subset_next G hG hzx hzy hw

/-- Every nonsource vertex of an outgoing branch belongs to exactly one
    incoming branch; both coverage and uniqueness are derived from the graph. -/
theorem existsUnique_incoming_branch {U : Type*} [Fintype U]
    (G : SimpleGraph U) (hG : G.IsAcyclic) (x y w : U)
    (hw : w ∈ forestBranch G x y) (hwx : w ≠ x) :
    ∃! z, G.Adj z x ∧ z ≠ y ∧ w ∈ forestBranch G z x := by
  classical
  rcases (mem_forestBranch_iff_source_or_incoming G hG x y w).mp hw with h | ⟨z, hz, hzy, hwz⟩
  · exact (hwx h).elim
  · refine ⟨z, ⟨hz, hzy, hwz⟩, ?_⟩
    intro z' hz'
    by_contra hne
    exact Finset.disjoint_left.mp (forestBranch_disjoint_incoming G hG hz hz'.1 hne)
      hz'.2.2 hwz

/-- A neighboring vertex stays in a cut component unless its edge is exactly
    the removed edge. This is a graph fact, independent of factor weights. -/
theorem adjacent_mem_branch_or_cut {U : Type*} [Fintype U]
    (G : SimpleGraph U) {x y z w : U} (hz : z ∈ forestBranch G x y)
    (hzw : G.Adj z w) :
    w ∈ forestBranch G x y ∨ s(z, w) = s(x, y) := by
  classical
  by_cases he : s(z, w) = s(x, y)
  · exact Or.inr he
  · left
    simp only [forestBranch, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    apply hz.trans
    have ha : (G.deleteEdges {s(x, y)}).Adj z w := by
      simp [SimpleGraph.deleteEdges_adj, hzw, he]
    exact ha.reachable

/-- Actual variables in a source-side cut component. -/
noncomputable def branchVariables {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (x y : ν ⊕ α) : Finset ν := by
  classical
  exact Finset.univ.filter fun v => Sum.inl v ∈ forestBranch (incidenceGraph G) x y

/-- Actual factors in a source-side cut component. -/
noncomputable def branchFactors {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (x y : ν ⊕ α) : Finset α := by
  classical
  exact Finset.univ.filter fun a => Sum.inr a ∈ forestBranch (incidenceGraph G) x y

/-- Any factor on either side of a variable-factor cut depends only on that
    side's variables and, possibly, the one fixed boundary variable. -/
theorem factorScope_subset_branch_boundary {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (x y : ν ⊕ α) (v : ν) (a b : α)
    (hcut : s(x, y) = s(Sum.inl v, Sum.inr a))
    (hb : b ∈ branchFactors G x y) :
    factorScope G b ⊆ insert v (branchVariables G x y) := by
  classical
  intro u hu
  have hb' : Sum.inr b ∈ forestBranch (incidenceGraph G) x y := by
    simpa [branchFactors] using hb
  have hbu : G.incidence b u = true := by
    simpa [factorScope] using hu
  rcases adjacent_mem_branch_or_cut (incidenceGraph G) hb'
    ((incidenceGraph_inl_inr_adj G u b).mpr hbu).symm with hin | he
  · simp [branchVariables, hin]
  · have hm : Sum.inl u ∈ (s(Sum.inl v, Sum.inr a) : Sym2 (ν ⊕ α)) := by
      rw [← hcut, ← he]
      simp
    have huv : u = v := by simpa using hm
    simp [huv]

/-- Restriction and gluing of genuine assignments for an actual finite
    partition of variables. The unique-cover proof is a graph obligation,
    not a supplied probability or cavity correspondence. -/
noncomputable def assignmentPartitionEquiv {U I X : Type*}
    (blocks : I → Finset U) (cover : ∀ u, ∃! i, u ∈ blocks i) :
    (U → X) ≃ ((i : I) → blocks i → X) := by
  classical
  exact
    { toFun := fun y i u => y u
      invFun := fun z u => z (Classical.choose (cover u))
        ⟨u, (Classical.choose_spec (cover u)).1⟩
      left_inv := fun y => by funext u; rfl
      right_inv := fun z => by
        funext i u
        rcases u with ⟨u, hu⟩
        have hi : i = Classical.choose (cover u) :=
          (Classical.choose_spec (cover u)).2 i hu
        subst i
        rfl }

/-- A genuinely disjoint variable partition factors the full sum of branch
    products into the product of the genuine branch sums. -/
theorem sum_prod_partition {U I X : Type*}
    [Fintype U] [Fintype I] [Fintype X] [DecidableEq U] [DecidableEq I]
    (blocks : I → Finset U) (cover : ∀ u, ∃! i, u ∈ blocks i)
    (f : (i : I) → (blocks i → X) → ℝ) :
    (∑ y : U → X, ∏ i, f i (fun u => y u)) =
      ∏ i, ∑ z : blocks i → X, f i z := by
  classical
  rw [Fintype.prod_sum]
  exact (assignmentPartitionEquiv blocks cover).sum_comp (fun z => ∏ i, f i (z i))

/-- The actual product of factors in one cut component. -/
noncomputable def branchWeight {ν α X : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ)
    (x y : ν ⊕ α) (z : ν → X) : ℝ := ∏ b ∈ branchFactors G x y, f b z

/-- The branch product is local to the actual side variables and the single
    possible boundary variable, by the cut-scope theorem. -/
theorem branchWeight_dependsOn_boundary {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (x y : ν ⊕ α) (v : ν) (a : α)
    (hcut : s(x, y) = s(Sum.inl v, Sum.inr a)) :
    DependsOn (insert v (branchVariables G x y)) (branchWeight G f x y) := by
  classical
  intro z z' hzz'
  apply Finset.prod_congr rfl
  intro b hb
  apply hf b
  intro u hu
  exact hzz' u (factorScope_subset_branch_boundary G x y v a b hcut hb hu)

/-- Genuine cavity sum: sum all actual side variables other than the fixed
    boundary once, and multiply exactly the factors in that cut component. -/
noncomputable def cavitySum {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ)
    (x y : ν ⊕ α) (v : ν) (ξ : X) (background : ν → X) : ℝ :=
  ∑ z : (branchVariables G x y).erase v → X,
    branchWeight G f x y
      (Function.update (extendScope ((branchVariables G x y).erase v) z background) v ξ)

/-- Scope locality and actual cut closure remove the arbitrary exterior
    background from the genuine cavity sum. -/
theorem cavitySum_background_independent {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (x y : ν ⊕ α) (v : ν) (a : α)
    (hcut : s(x, y) = s(Sum.inl v, Sum.inr a))
    (ξ : X) (background background' : ν → X) :
    cavitySum G f x y v ξ background = cavitySum G f x y v ξ background' := by
  classical
  apply Finset.sum_congr rfl
  intro z _
  apply branchWeight_dependsOn_boundary G f hf x y v a hcut
  intro u hu
  by_cases huv : u = v
  · subst u
    simp
  · have hum : u ∈ branchVariables G x y := by
      simpa [huv] using hu
    have hue : u ∈ (branchVariables G x y).erase v := by
      simp [huv, hum]
    simp [Function.update, extendScope, huv, hue]

/-- The actual factors on a variable side are exactly the union of its
    incoming factor branches. No recurrence or probability law is assumed. -/
theorem branchFactors_variable_eq_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) (a : α) :
    branchFactors G (Sum.inl v) (Sum.inr a) =
      (otherFactors G v a).biUnion fun b => branchFactors G (Sum.inr b) (Sum.inl v) := by
  classical
  ext b
  simp only [Finset.mem_biUnion, branchFactors, otherFactors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hb
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inl v) (Sum.inr a) (Sum.inr b)).mp hb with he | ⟨z, hz, hza, hbz⟩
    · cases he
    · rcases z with u | c
      · have hn : ¬(incidenceGraph G).Adj (Sum.inl u) (Sum.inl v) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
      · exact ⟨c, ⟨by simpa using hza,
          (incidenceGraph_inl_inr_adj G v c).mp hz.symm⟩, hbz⟩
  · rintro ⟨c, ⟨hca, hcv⟩, hbc⟩
    exact forestBranch_subset_next (incidenceGraph G) hG
      ((incidenceGraph_inl_inr_adj G v c).mpr hcv).symm
      (by simpa using hca) hbc

/-- The actual factor-side factors are its source factor and exactly the
    incoming variable branches. The identity includes empty neighbor sets. -/
theorem branchFactors_factor_eq_insert_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (a : α) (v : ν) :
    branchFactors G (Sum.inr a) (Sum.inl v) = insert a
      ((otherVars G a v).biUnion fun u => branchFactors G (Sum.inl u) (Sum.inr a)) := by
  classical
  ext b
  simp only [Finset.mem_insert, Finset.mem_biUnion, branchFactors, otherVars,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hb
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inr a) (Sum.inl v) (Sum.inr b)).mp hb with he | ⟨z, hz, hzv, hbz⟩
    · exact Or.inl (by simpa using he)
    · right
      rcases z with u | c
      · exact ⟨u, ⟨by simpa using hzv,
          (incidenceGraph_inl_inr_adj G u a).mp hz⟩, hbz⟩
      · have hn : ¬(incidenceGraph G).Adj (Sum.inr c) (Sum.inr a) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
  · rintro (rfl | ⟨u, ⟨huv, hau⟩, hbu⟩)
    · exact mem_forestBranch_self _ _ _
    · exact forestBranch_subset_next (incidenceGraph G) hG
        ((incidenceGraph_inl_inr_adj G u a).mpr hau)
        (by simpa using huv) hbu

/-- The variables on a variable side consist of its source and the complete
    incoming factor branches; no variable is dropped or duplicated. -/
theorem branchVariables_variable_eq_insert_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) (a : α) :
    branchVariables G (Sum.inl v) (Sum.inr a) = insert v
      ((otherFactors G v a).biUnion fun b => branchVariables G (Sum.inr b) (Sum.inl v)) := by
  classical
  ext u
  simp only [Finset.mem_insert, Finset.mem_biUnion, branchVariables, otherFactors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hu
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inl v) (Sum.inr a) (Sum.inl u)).mp hu with he | ⟨z, hz, hza, huz⟩
    · exact Or.inl (by simpa using he)
    · right
      rcases z with w | b
      · have hn : ¬(incidenceGraph G).Adj (Sum.inl w) (Sum.inl v) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
      · exact ⟨b, ⟨by simpa using hza,
          (incidenceGraph_inl_inr_adj G v b).mp hz.symm⟩, huz⟩
  · rintro (rfl | ⟨b, ⟨hba, hbv⟩, hub⟩)
    · exact mem_forestBranch_self _ _ _
    · exact forestBranch_subset_next (incidenceGraph G) hG
        ((incidenceGraph_inl_inr_adj G v b).mpr hbv).symm
        (by simpa using hba) hub

/-- Every actual factor-side variable belongs to an incoming variable branch;
    the factor itself adds no spurious alphabet-valued assignment coordinate. -/
theorem branchVariables_factor_eq_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (a : α) (v : ν) :
    branchVariables G (Sum.inr a) (Sum.inl v) =
      (otherVars G a v).biUnion fun u => branchVariables G (Sum.inl u) (Sum.inr a) := by
  classical
  ext w
  simp only [Finset.mem_biUnion, branchVariables, otherVars,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inr a) (Sum.inl v) (Sum.inl w)).mp hw with he | ⟨z, hz, hzv, hwz⟩
    · cases he
    · rcases z with u | c
      · exact ⟨u, ⟨by simpa using hzv,
          (incidenceGraph_inl_inr_adj G u a).mp hz⟩, hwz⟩
      · have hn : ¬(incidenceGraph G).Adj (Sum.inr c) (Sum.inr a) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
  · rintro ⟨u, ⟨huv, hau⟩, hwu⟩
    exact forestBranch_subset_next (incidenceGraph G) hG
      ((incidenceGraph_inl_inr_adj G u a).mpr hau)
      (by simpa using huv) hwu

/-- Distinct incoming cut branches have disjoint actual factor sets. -/
theorem branchFactors_disjoint_incoming {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) {x y z : ν ⊕ α}
    (hyx : (incidenceGraph G).Adj y x) (hzx : (incidenceGraph G).Adj z x)
    (hzy : z ≠ y) : Disjoint (branchFactors G z x) (branchFactors G y x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha ha'
  exact Finset.disjoint_left.mp (forestBranch_disjoint_incoming (incidenceGraph G) hG hyx hzx hzy)
    (by simpa [branchFactors] using ha) (by simpa [branchFactors] using ha')

/-- Product of the source algorithm's exact factor multiplicities over the
    actual source-side factors, not a supplied message correspondence. -/
noncomputable def branchMultiplier {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    (G : FactorGraph ν α) (x y : ν ⊕ α) : ℝ :=
  ∏ b ∈ branchFactors G x y, extensionMultiplicity (X := X) (factorScope G b)

/-- Every genuine source-side multiplicity product is positive on a nonempty
    alphabet, without assuming positivity of any individual message. -/
theorem branchMultiplier_pos {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [Nonempty X]
    (G : FactorGraph ν α) (x y : ν ⊕ α) :
    0 < branchMultiplier (X := X) G x y := by
  exact Finset.prod_pos (fun b _ => extensionMultiplicity_pos (factorScope G b))

/-- The actual source-side scaling constants obey the variable recurrence,
    by the derived disjoint factor cover. -/
theorem branchMultiplier_variable {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) (a : α) :
    branchMultiplier (X := X) G (Sum.inl v) (Sum.inr a) =
      ∏ b ∈ otherFactors G v a, branchMultiplier (X := X) G (Sum.inr b) (Sum.inl v) := by
  classical
  unfold branchMultiplier
  rw [branchFactors_variable_eq_biUnion G hG v a]
  apply Finset.prod_biUnion
  intro b hb c hc hbc
  have hbv := (Finset.mem_filter.mp hb).2.2
  have hcv := (Finset.mem_filter.mp hc).2.2
  exact branchFactors_disjoint_incoming G hG
    ((incidenceGraph_inl_inr_adj G v c).mpr hcv).symm
    ((incidenceGraph_inl_inr_adj G v b).mpr hbv).symm (by simpa using hbc)

/-- The actual full-assignment multiplicity of the source factor supplies
    exactly the extra factor in the factor-side constant recurrence. -/
theorem branchMultiplier_factor {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (a : α) (v : ν) :
    branchMultiplier (X := X) G (Sum.inr a) (Sum.inl v) =
      extensionMultiplicity (X := X) (factorScope G a) *
        ∏ u ∈ otherVars G a v, branchMultiplier (X := X) G (Sum.inl u) (Sum.inr a) := by
  classical
  have hn : a ∉ (otherVars G a v).biUnion
      (fun u => branchFactors G (Sum.inl u) (Sum.inr a)) := by
    intro ha
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
    have hinc : G.incidence a u = true := (Finset.mem_filter.mp hu).2.2
    exact not_mem_forestBranch_of_adj (incidenceGraph G) hG
      ((incidenceGraph_inl_inr_adj G u a).mpr hinc)
      (by simpa [branchFactors] using hau)
  unfold branchMultiplier
  rw [branchFactors_factor_eq_insert_biUnion G hG a v, Finset.prod_insert hn]
  congr 1
  apply Finset.prod_biUnion
  intro u hu w hw huw
  have hau : G.incidence a u = true := (Finset.mem_filter.mp hu).2.2
  have haw : G.incidence a w = true := (Finset.mem_filter.mp hw).2.2
  exact branchFactors_disjoint_incoming G hG
    ((incidenceGraph_inl_inr_adj G w a).mpr haw)
    ((incidenceGraph_inl_inr_adj G u a).mpr hau) (by simpa using huw)

/-- The actual variable-side product of original factors decomposes over the
    derived incoming factor branches, before taking any assignment sums. -/
theorem branchWeight_variable {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (v : ν) (a : α) (z : ν → X) :
    branchWeight G f (Sum.inl v) (Sum.inr a) z =
      ∏ b ∈ otherFactors G v a, branchWeight G f (Sum.inr b) (Sum.inl v) z := by
  classical
  unfold branchWeight
  rw [branchFactors_variable_eq_biUnion G hG v a]
  apply Finset.prod_biUnion
  intro b hb c hc hbc
  have hbv := (Finset.mem_filter.mp hb).2.2
  have hcv := (Finset.mem_filter.mp hc).2.2
  exact branchFactors_disjoint_incoming G hG
    ((incidenceGraph_inl_inr_adj G v c).mpr hcv).symm
    ((incidenceGraph_inl_inr_adj G v b).mpr hbv).symm (by simpa using hbc)

/-- The actual factor-side weight decomposes into its original source factor
    times all incoming variable-branch weights, with no normalization premise. -/
theorem branchWeight_factor {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (a : α) (v : ν) (z : ν → X) :
    branchWeight G f (Sum.inr a) (Sum.inl v) z = f a z *
      ∏ u ∈ otherVars G a v, branchWeight G f (Sum.inl u) (Sum.inr a) z := by
  classical
  have hn : a ∉ (otherVars G a v).biUnion
      (fun u => branchFactors G (Sum.inl u) (Sum.inr a)) := by
    intro ha
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
    have hinc : G.incidence a u = true := (Finset.mem_filter.mp hu).2.2
    exact not_mem_forestBranch_of_adj (incidenceGraph G) hG
      ((incidenceGraph_inl_inr_adj G u a).mpr hinc)
      (by simpa [branchFactors] using hau)
  unfold branchWeight
  rw [branchFactors_factor_eq_insert_biUnion G hG a v, Finset.prod_insert hn]
  congr 1
  apply Finset.prod_biUnion
  intro u hu w hw huw
  have hau : G.incidence a u = true := (Finset.mem_filter.mp hu).2.2
  have haw : G.incidence a w = true := (Finset.mem_filter.mp hw).2.2
  exact branchFactors_disjoint_incoming G hG
    ((incidenceGraph_inl_inr_adj G w a).mpr haw)
    ((incidenceGraph_inl_inr_adj G u a).mpr hau) (by simpa using huw)

/-- Restriction and gluing on a finite scope, with every coordinate owned by
    exactly one actual block. No exterior coordinates are counted. -/
noncomputable def scopePartitionEquiv {U I X : Type*}
    (s : Finset U) (blocks : I → Finset U)
    (sub : ∀ i, blocks i ⊆ s) (cover : ∀ u ∈ s, ∃! i, u ∈ blocks i) :
    (s → X) ≃ ((i : I) → blocks i → X) := by
  classical
  exact
    { toFun := fun y i u => y ⟨u, sub i u.property⟩
      invFun := fun z u => z (Classical.choose (cover u u.property))
        ⟨u, (Classical.choose_spec (cover u u.property)).1⟩
      left_inv := fun y => by funext u; rfl
      right_inv := fun z => by
        funext i u
        rcases u with ⟨u, hu⟩
        have hi : i = Classical.choose (cover u (sub i hu)) :=
          (Classical.choose_spec (cover u (sub i hu))).2 i hu
        dsimp only
        congr 1
        · exact hi.symm
        · have hblocks : blocks (Classical.choose (cover u (sub i hu))) = blocks i :=
            congrArg blocks hi.symm
          exact (Subtype.heq_iff_coe_eq (fun x => by rw [hblocks])).mpr rfl }

/-- Product-of-sums for an actual finite scope partition, with no multiplicity
    from variables outside the scope. -/
theorem sum_prod_scope_partition {U I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq U] [DecidableEq I]
    (s : Finset U) (blocks : I → Finset U)
    (sub : ∀ i, blocks i ⊆ s) (cover : ∀ u ∈ s, ∃! i, u ∈ blocks i)
    (f : (i : I) → (blocks i → X) → ℝ) :
    (∑ y : s → X, ∏ i, f i (fun u => y ⟨u, sub i u.property⟩)) =
      ∏ i, ∑ z : blocks i → X, f i z := by
  classical
  rw [Fintype.prod_sum]
  exact (scopePartitionEquiv s blocks sub cover).sum_comp (fun z => ∏ i, f i (z i))

/-- Actual boundary-conditioned sums factor over a genuine scope partition
    when each summand uses only its block and the shared fixed boundary. -/
theorem sum_prod_scope_boundary {U I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq U] [DecidableEq I]
    (s : Finset U) (blocks : I → Finset U)
    (sub : ∀ i, blocks i ⊆ s) (cover : ∀ u ∈ s, ∃! i, u ∈ blocks i)
    (F : I → (U → X) → ℝ) (v : U) (ξ : X) (background : U → X)
    (hF : ∀ i, DependsOn (insert v (blocks i)) (F i)) :
    (∑ y : s → X, ∏ i,
      F i (Function.update (extendScope s y background) v ξ)) =
      ∏ i, ∑ z : blocks i → X,
        F i (Function.update (extendScope (blocks i) z background) v ξ) := by
  classical
  rw [← sum_prod_scope_partition s blocks sub cover
    (fun i z => F i (Function.update (extendScope (blocks i) z background) v ξ))]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro i _
  apply hF i
  intro u hu
  rcases Finset.mem_insert.mp hu with huv | hub
  · subst u
    simp
  · by_cases huv : u = v <;>
      simp [Function.update, extendScope, huv, hub, sub i hub]

/-- Incoming branches own disjoint sets of actual variable coordinates. -/
theorem branchVariables_disjoint_incoming {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) {x y z : ν ⊕ α}
    (hyx : (incidenceGraph G).Adj y x) (hzx : (incidenceGraph G).Adj z x)
    (hzy : z ≠ y) : Disjoint (branchVariables G z x) (branchVariables G y x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u hu hu'
  exact Finset.disjoint_left.mp
    (forestBranch_disjoint_incoming (incidenceGraph G) hG hyx hzx hzy)
    (by simpa [branchVariables] using hu) (by simpa [branchVariables] using hu')

/-- Boundary-conditioned product-of-sums over a disjoint finite union of
    actual variable blocks. -/
theorem sum_prod_biUnion_boundary {U I X : Type*}
    [Fintype X] [DecidableEq U] [DecidableEq I]
    (s : Finset I) (blocks : I → Finset U)
    (hd : (s : Set I).PairwiseDisjoint blocks)
    (F : I → (U → X) → ℝ) (v : U) (ξ : X) (background : U → X)
    (hF : ∀ i ∈ s, DependsOn (insert v (blocks i)) (F i)) :
    (∑ y : s.biUnion blocks → X, ∏ i ∈ s,
      F i (Function.update (extendScope (s.biUnion blocks) y background) v ξ)) =
      ∏ i ∈ s, ∑ z : blocks i → X,
        F i (Function.update (extendScope (blocks i) z background) v ξ) := by
  classical
  let sub : ∀ i : s, blocks i ⊆ s.biUnion blocks :=
    fun i u hu => Finset.mem_biUnion.mpr ⟨i, i.property, hu⟩
  have cover : ∀ u ∈ s.biUnion blocks, ∃! i : s, u ∈ blocks i := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    refine ⟨⟨i, hi⟩, hui, ?_⟩
    intro j hj
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hd j.property hi hne) hj hui
  have h := sum_prod_scope_boundary (s.biUnion blocks) (fun i : s => blocks i)
    sub cover (fun i : s => F i) v ξ background (fun i => hF i i.property)
  have hp : ∀ y : s.biUnion blocks → X,
      (∏ i : s, F i (Function.update (extendScope (s.biUnion blocks) y background) v ξ)) =
        ∏ i ∈ s, F i (Function.update (extendScope (s.biUnion blocks) y background) v ξ) :=
    fun y => Finset.prod_coe_sort s
      (fun i => F i (Function.update (extendScope (s.biUnion blocks) y background) v ξ))
  have hq : (∏ i : s, ∑ z : blocks i → X,
      F i (Function.update (extendScope (blocks i) z background) v ξ)) =
        ∏ i ∈ s, ∑ z : blocks i → X,
          F i (Function.update (extendScope (blocks i) z background) v ξ) :=
    Finset.prod_coe_sort s (fun i => ∑ z : blocks i → X,
      F i (Function.update (extendScope (blocks i) z background) v ξ))
  simpa only [hp, hq] using h

/-- The genuine variable-to-factor cavity SUM recurrence, obtained by
    partitioning actual erased side assignments and using scope locality. -/
theorem cavitySum_variable {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (v : ν) (a : α) (ξ : X) (background : ν → X) :
    cavitySum G f (Sum.inl v) (Sum.inr a) v ξ background =
      ∏ b ∈ otherFactors G v a,
        cavitySum G f (Sum.inr b) (Sum.inl v) v ξ background := by
  classical
  unfold cavitySum
  simp_rw [branchWeight_variable G hG f v a]
  rw [branchVariables_variable_eq_insert_biUnion G hG v a,
    Finset.erase_insert_eq_erase, Finset.erase_biUnion]
  apply sum_prod_biUnion_boundary
  · intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro u hu hu'
    have h := branchVariables_disjoint_incoming G hG
      ((incidenceGraph_inl_inr_adj G v c).mpr (Finset.mem_filter.mp hc).2.2).symm
      ((incidenceGraph_inl_inr_adj G v b).mpr (Finset.mem_filter.mp hb).2.2).symm
      (by simpa using hbc)
    exact Finset.disjoint_left.mp h (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hu')
  · intro b hb z z' hz
    apply branchWeight_dependsOn_boundary G f hf (Sum.inr b) (Sum.inl v) v b Sym2.eq_swap z z'
    intro u hu
    apply hz
    by_cases huv : u = v <;> simp_all

/-- Separate a genuine branch assignment into its root value and all other
    coordinates. The root is counted once and the remainder is an erased scope. -/
noncomputable def scopeRootEquiv {U X : Type*} [DecidableEq U]
    (s : Finset U) (u : U) (hu : u ∈ s) :
    (s → X) ≃ X × (s.erase u → X) := by
  classical
  exact
    { toFun := fun y => (y ⟨u, hu⟩, fun w => y ⟨w, Finset.mem_of_mem_erase w.property⟩)
      invFun := fun p w => if h : (w : U) = u then p.1
        else p.2 ⟨w, Finset.mem_erase.mpr ⟨h, w.property⟩⟩
      left_inv := fun y => by
        funext w
        rcases w with ⟨w, hw⟩
        dsimp only
        split_ifs with h
        · subst w; rfl
        · rfl
      right_inv := fun p => by
        rcases p with ⟨x, z⟩
        exact Prod.ext (by simp)
          (by funext w; rcases w with ⟨w, hw⟩; simp [Finset.ne_of_mem_erase hw]) }

/-- A branch sum with its root value exposed is a genuine finite Fubini sum. -/
theorem sum_scope_root {U X : Type*} [Fintype X] [DecidableEq U]
    (s : Finset U) (u : U) (hu : u ∈ s) (F : (s → X) → ℝ) :
    (∑ y : s → X, F y) = ∑ x : X, ∑ z : s.erase u → X,
      F ((scopeRootEquiv s u hu).symm (x, z)) := by
  classical
  simpa only [Fintype.sum_prod_type] using ((scopeRootEquiv s u hu).symm.sum_comp F).symm

/-- Simultaneously split every actual branch assignment into its root state
    and its erased remainder, without dropping the joint root-state carrier. -/
noncomputable def rootAssignmentsEquiv {U I X : Type*} [DecidableEq U]
    (blocks : I → Finset U) (root : I → U) (hr : ∀ i, root i ∈ blocks i) :
    ((i : I) → blocks i → X) ≃
      (I → X) × ((i : I) → (blocks i).erase (root i) → X) := by
  classical
  exact
    { toFun := fun y =>
        (fun i => (scopeRootEquiv (blocks i) (root i) (hr i) (y i)).1,
         fun i => (scopeRootEquiv (blocks i) (root i) (hr i) (y i)).2)
      invFun := fun p i => (scopeRootEquiv (blocks i) (root i) (hr i)).symm (p.1 i, p.2 i)
      left_inv := fun y => by
        funext i
        exact (scopeRootEquiv (blocks i) (root i) (hr i)).symm_apply_apply (y i)
      right_inv := fun p => by
        rcases p with ⟨x, z⟩
        exact Prod.ext
          (funext fun i => congrArg Prod.fst
            ((scopeRootEquiv (blocks i) (root i) (hr i)).apply_symm_apply (x i, z i)))
          (funext fun i => congrArg Prod.snd
            ((scopeRootEquiv (blocks i) (root i) (hr i)).apply_symm_apply (x i, z i))) }

/-- Keep a coupled function of the incoming root states inside the outer
    sum while independently summing each branch's remaining coordinates. -/
theorem sum_prod_root_coupled {U I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq U] [DecidableEq I]
    (blocks : I → Finset U) (root : I → U) (hr : ∀ i, root i ∈ blocks i)
    (H : (I → X) → ℝ) (F : (i : I) → (blocks i → X) → ℝ) :
    (∑ y : (i : I) → blocks i → X,
      H (fun i => y i ⟨root i, hr i⟩) * ∏ i, F i (y i)) =
      ∑ x : I → X, H x * ∏ i, ∑ z : (blocks i).erase (root i) → X,
        F i ((scopeRootEquiv (blocks i) (root i) (hr i)).symm (x i, z)) := by
  classical
  let e := rootAssignmentsEquiv (X := X) blocks root hr
  have he := (e.symm.sum_comp
    (fun y => H (fun i => y i ⟨root i, hr i⟩) * ∏ i, F i (y i))).symm
  trans ∑ p : (I → X) × ((i : I) → (blocks i).erase (root i) → X),
    H p.1 * ∏ i, F i ((scopeRootEquiv (blocks i) (root i) (hr i)).symm (p.1 i, p.2 i))
  · simpa [e, rootAssignmentsEquiv, scopeRootEquiv] using he
  · rw [Fintype.sum_prod_type]
    simp_rw [Fintype.prod_sum, Finset.mul_sum]

/-- Every variable on a factor side avoids the external variable boundary
    of an actual edge. This makes boundary erasure exact, not a new count. -/
theorem boundary_not_mem_factor_branch {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (a : α) (v : ν)
    (hav : G.incidence a v = true) :
    v ∉ branchVariables G (Sum.inr a) (Sum.inl v) := by
  classical
  simpa [branchVariables] using not_mem_forestBranch_of_adj (incidenceGraph G) hG
    ((incidenceGraph_inl_inr_adj G v a).mpr hav).symm

/-- Recombining a root and its erased assignment is precisely the original
    finite-scope extension followed by one boundary update. -/
theorem extendScope_root_split {U X : Type*} [DecidableEq U]
    (s : Finset U) (u : U) (hu : u ∈ s) (x : X)
    (z : s.erase u → X) (background : U → X) :
    extendScope s ((scopeRootEquiv s u hu).symm (x, z)) background =
      Function.update (extendScope (s.erase u) z background) u x := by
  classical
  funext w
  by_cases hwu : w = u <;> by_cases hws : w ∈ s <;>
    simp_all [extendScope, scopeRootEquiv, Function.update]

/-- The complete finite-scope root-coupled sum identity. The source coupling
    stays inside the outer root-state sum; locality justifies only the inner
    independent branch sums. -/
theorem sum_prod_scope_root_coupled {U I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq U] [DecidableEq I]
    (s : Finset U) (blocks : I → Finset U)
    (sub : ∀ i, blocks i ⊆ s) (cover : ∀ u ∈ s, ∃! i, u ∈ blocks i)
    (root : I → U) (hr : ∀ i, root i ∈ blocks i)
    (H : (I → X) → ℝ) (F : I → (U → X) → ℝ)
    (hF : ∀ i, DependsOn (blocks i) (F i)) (background : U → X) :
    (∑ y : s → X, H (fun i => y ⟨root i, sub i (hr i)⟩) *
      ∏ i, F i (extendScope s y background)) =
      ∑ x : I → X, H x * ∏ i, ∑ z : (blocks i).erase (root i) → X,
        F i (Function.update (extendScope ((blocks i).erase (root i)) z background) (root i) (x i)) := by
  classical
  let g : (i : I) → (blocks i → X) → ℝ :=
    fun i z => F i (extendScope (blocks i) z background)
  have hloc : ∀ (y : s → X) i,
      F i (extendScope s y background) = g i (fun u => y ⟨u, sub i u.property⟩) := by
    intro y i
    apply hF i
    intro u hu
    simp [extendScope, hu, sub i hu]
  have he := (scopePartitionEquiv (X := X) s blocks sub cover).sum_comp
    (fun z => H (fun i => z i ⟨root i, hr i⟩) * ∏ i, g i (z i))
  have hleft : (∑ y : s → X, H (fun i => y ⟨root i, sub i (hr i)⟩) *
      ∏ i, F i (extendScope s y background)) =
        ∑ z : (i : I) → blocks i → X,
          H (fun i => z i ⟨root i, hr i⟩) * ∏ i, g i (z i) := by
    simp_rw [hloc]
    exact he
  rw [hleft, sum_prod_root_coupled blocks root hr H g]
  simp_rw [g, extendScope_root_split]

/-- A variable-side weight is local to its actual side variables: the source
    variable already belongs to that side. -/
theorem branchWeight_variable_dependsOn {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (u : ν) (a : α) :
    DependsOn (branchVariables G (Sum.inl u) (Sum.inr a))
      (branchWeight G f (Sum.inl u) (Sum.inr a)) := by
  classical
  have hu : u ∈ branchVariables G (Sum.inl u) (Sum.inr a) := by
    simpa [branchVariables] using mem_forestBranch_self (incidenceGraph G) (Sum.inl u) (Sum.inr a)
  simpa only [Finset.insert_eq_of_mem hu] using
    branchWeight_dependsOn_boundary G f hf (Sum.inl u) (Sum.inr a) u a rfl

/-- The genuine factor-to-variable cavity SUM recurrence. The original
    source factor remains coupled to all incoming root values. -/
theorem cavitySum_factor {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (a : α) (v : ν) (hav : G.incidence a v = true)
    (ξ : X) (background : ν → X) :
    cavitySum G f (Sum.inr a) (Sum.inl v) v ξ background =
      ∑ x : otherVars G a v → X,
        f a (Function.update (extendScope (otherVars G a v) x background) v ξ) *
          ∏ u : otherVars G a v,
            cavitySum G f (Sum.inl (u : ν)) (Sum.inr a) u (x u) background := by
  classical
  let S := branchVariables G (Sum.inr a) (Sum.inl v)
  let blocks : otherVars G a v → Finset ν :=
    fun u => branchVariables G (Sum.inl (u : ν)) (Sum.inr a)
  have sub : ∀ i, blocks i ⊆ S := by
    intro i w hw
    dsimp [S]
    rw [branchVariables_factor_eq_biUnion G hG a v]
    exact Finset.mem_biUnion.mpr ⟨i, i.property, hw⟩
  have cover : ∀ w ∈ S, ∃! i : otherVars G a v, w ∈ blocks i := by
    intro w hw
    have hw' : w ∈ (otherVars G a v).biUnion
        (fun u => branchVariables G (Sum.inl u) (Sum.inr a)) := by
      simpa only [S, branchVariables_factor_eq_biUnion G hG a v] using hw
    obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw'
    refine ⟨⟨i, hi⟩, hwi, ?_⟩
    intro j hj
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (branchVariables_disjoint_incoming G hG
      ((incidenceGraph_inl_inr_adj G i a).mpr (Finset.mem_filter.mp hi).2.2)
      ((incidenceGraph_inl_inr_adj G j a).mpr (Finset.mem_filter.mp j.property).2.2)
      (by simpa using hne)) hj hwi
  have hr : ∀ i : otherVars G a v, (i : ν) ∈ blocks i := by
    intro i
    simpa [blocks, branchVariables] using
      mem_forestBranch_self (incidenceGraph G) (Sum.inl (i : ν)) (Sum.inr a)
  let F : otherVars G a v → (ν → X) → ℝ :=
    fun u => branchWeight G f (Sum.inl (u : ν)) (Sum.inr a)
  let H : (otherVars G a v → X) → ℝ :=
    fun x => f a (Function.update (extendScope (otherVars G a v) x background) v ξ)
  have hF : ∀ i, DependsOn (blocks i) (F i) :=
    fun i => branchWeight_variable_dependsOn G f hf i a
  have hsource : ∀ y : S → X,
      f a (Function.update (extendScope S y background) v ξ) =
        H (fun i => y ⟨i, sub i (hr i)⟩) := by
    intro y
    apply hf a
    intro w hw
    by_cases hwv : w = v
    · subst w
      simp
    · have hwo : w ∈ otherVars G a v := by
        simp only [otherVars, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hwv, by simpa [factorScope] using hw⟩
      have hws := sub ⟨w, hwo⟩ (hr ⟨w, hwo⟩)
      simp [Function.update, extendScope, hwv, hwo, hws]
  have hterm : ∀ y : S → X,
      branchWeight G f (Sum.inr a) (Sum.inl v)
        (Function.update (extendScope S y background) v ξ) =
          H (fun i => y ⟨i, sub i (hr i)⟩) * ∏ i, F i (extendScope S y background) := by
    intro y
    rw [branchWeight_factor G hG f a v, hsource y]
    congr 1
    trans ∏ i : otherVars G a v, F i (Function.update (extendScope S y background) v ξ)
    · exact (Finset.prod_coe_sort (otherVars G a v) (fun u =>
        branchWeight G f (Sum.inl u) (Sum.inr a)
          (Function.update (extendScope S y background) v ξ))).symm
    · apply Finset.prod_congr rfl
      intro i _
      apply hF i
      intro w hw
      have hwv : w ≠ v := by
        intro h
        subst w
        exact boundary_not_mem_factor_branch G hG a v hav (sub i hw)
      simp [Function.update, hwv]
  have hsum := sum_prod_scope_root_coupled S blocks sub cover
    (fun i : otherVars G a v => (i : ν)) hr H F hF background
  rw [cavitySum, Finset.erase_eq_of_notMem (boundary_not_mem_factor_branch G hG a v hav)]
  change (∑ y : S → X, branchWeight G f (Sum.inr a) (Sum.inl v)
    (Function.update (extendScope S y background) v ξ)) = _
  simp_rw [hterm]
  exact hsum

/-- Fixing a root in an actual scope sum leaves exactly its erased assignment
    domain, with no extra alphabet or exterior multiplicity. -/
theorem sum_fixed_scope {U X : Type*} [Fintype X] [DecidableEq U] [DecidableEq X]
    (s : Finset U) (v : U) (hv : v ∈ s) (ξ : X)
    (F : (U → X) → ℝ) (background : U → X) :
    (∑ y : s → X with y ⟨v, hv⟩ = ξ, F (extendScope s y background)) =
      ∑ z : s.erase v → X,
        F (Function.update (extendScope (s.erase v) z background) v ξ) := by
  classical
  simp only [Finset.sum_filter]
  rw [sum_scope_root s v hv]
  simp_rw [extendScope_root_split]
  simp [scopeRootEquiv]

/-- The actual full-assignment factor update is its coupled incoming-root
    sum times the exact exterior-assignment multiplicity. -/
theorem bpFactorUpdate_root_reduction {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (m : BPMessages ν α G X) (a : α) (v : ν) (hav : G.incidence a v = true)
    (ξ : X) (background : ν → X) :
    bpFactorUpdate m f a v ξ = extensionMultiplicity (X := X) (factorScope G a) *
      ∑ z : otherVars G a v → X,
        f a (Function.update (extendScope (otherVars G a v) z background) v ξ) *
          ∏ u : otherVars G a v, m.varToFactor u a (z u) := by
  classical
  have hv : v ∈ factorScope G a := by simp [factorScope, hav]
  rw [bpFactorUpdate_scope_reduction G f hf m a v hv ξ background]
  rw [sum_fixed_scope (factorScope G a) v hv ξ
    (fun y => f a y * ∏ u ∈ otherVars G a v, m.varToFactor u a (y u)) background]
  have he : (factorScope G a).erase v = otherVars G a v := by
    ext u; simp [factorScope, otherVars]
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [← Finset.prod_coe_sort (otherVars G a v)]
  apply Finset.prod_congr rfl
  intro u _
  have huv : (u : ν) ≠ v := (Finset.mem_filter.mp u.property).2.1
  simp [Function.update, extendScope, huv, u.property]

/-- Explicit source-scaled cavity values on the unchanged all-pairs carrier.
    Cavity semantics will be asserted only on actual incident coordinates. -/
noncomputable def scaledCavityMessages {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (background : ν → X) :
    BPMessages ν α G X where
  varToFactor v a ξ := branchMultiplier (X := X) G (Sum.inl v) (Sum.inr a) *
    cavitySum G f (Sum.inl v) (Sum.inr a) v ξ background
  factorToVar a v ξ := branchMultiplier (X := X) G (Sum.inr a) (Sum.inl v) *
    cavitySum G f (Sum.inr a) (Sum.inl v) v ξ background

/-- The original variable update reproduces the explicit source-scaled cavity
    value by the two derived variable recurrences. -/
theorem scaledCavityMessages_variable_update {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (background : ν → X) (v : ν) (a : α) (ξ : X) :
    bpVariableUpdate (scaledCavityMessages G f background) v a ξ =
      (scaledCavityMessages G f background).varToFactor v a ξ := by
  classical
  simp only [bpVariableUpdate, scaledCavityMessages]
  rw [Finset.prod_mul_distrib, branchMultiplier_variable G hG v a,
    cavitySum_variable G hG f hf v a ξ background]

/-- The original complete-assignment factor update reproduces the source-scaled
    cavity value on an actual incident edge, including every exterior multiplicity. -/
theorem scaledCavityMessages_factor_update {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (background : ν → X) (a : α) (v : ν) (hav : G.incidence a v = true) (ξ : X) :
    bpFactorUpdate (scaledCavityMessages G f background) f a v ξ =
      (scaledCavityMessages G f background).factorToVar a v ξ := by
  classical
  rw [bpFactorUpdate_root_reduction G f hf _ a v hav ξ background]
  simp only [scaledCavityMessages, Finset.prod_mul_distrib]
  rw [branchMultiplier_factor G hG a v, cavitySum_factor G hG f hf a v hav ξ background]
  rw [← Finset.prod_coe_sort (otherVars G a v)
    (fun u => branchMultiplier (X := X) G (Sum.inl u) (Sum.inr a))]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Every coordinate consumed by the original update is incident, even when
    the outgoing coordinate itself is not incident. -/
theorem bpUpdate_congr_incident {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ)
    (m m' : BPMessages ν α G X)
    (hvar : ∀ v a, G.incidence a v = true → m.varToFactor v a = m'.varToFactor v a)
    (hfac : ∀ a v, G.incidence a v = true → m.factorToVar a v = m'.factorToVar a v) :
    bpUpdate m f = bpUpdate m' f := by
  apply flattenMsg_injective
  funext e ξ
  rcases e with ⟨v, a⟩ | ⟨a, v⟩
  · change bpVariableUpdate m v a ξ = bpVariableUpdate m' v a ξ
    apply Finset.prod_congr rfl
    intro b hb
    rw [hfac b v (Finset.mem_filter.mp hb).2.2]
  · change bpFactorUpdate m f a v ξ = bpFactorUpdate m' f a v ξ
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro u hu
    rw [hvar u a (Finset.mem_filter.mp hu).2.2]

/-- One actual source sweep supplies nonincident coordinates and gives a full
    fixed point; its incident coordinates retain the proved cavity values. -/
theorem scaledCavityMessages_update_fixed {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f) (background : ν → X) :
    IsBPFixedPoint (bpUpdate (scaledCavityMessages G f background) f) f := by
  unfold IsBPFixedPoint
  apply bpUpdate_congr_incident
  · intro v a _
    funext ξ
    exact scaledCavityMessages_variable_update G hG f hf background v a ξ
  · intro a v hav
    funext ξ
    exact scaledCavityMessages_factor_update G hG f hf background a v hav ξ

/-- Genuine rank induction makes the original full-array fixed point unique,
    independently of the initial messages or signs of the factor weights. -/
theorem bpFixedPoint_unique {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (cert : BPRankCert G) (f : α → (ν → X) → ℝ)
    (m m' : BPMessages ν α G X) (hm : IsBPFixedPoint m f) (hm' : IsBPFixedPoint m' f) :
    m = m' := by
  have hs : bpStep G f (flattenMsg m) = flattenMsg m := by rw [← flattenMsg_bpUpdate, hm]
  have hs' : bpStep G f (flattenMsg m') = flattenMsg m' := by rw [← flattenMsg_bpUpdate, hm']
  have key : ∀ r : ℕ, ∀ e : MsgEndpoint ν α,
      cert.rank e = r → flattenMsg m e = flattenMsg m' e := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro e he
      rw [← congrFun hs e, ← congrFun hs' e]
      apply bpStep_rankLocal cert f
      intro e' he'
      exact ih (cert.rank e') (by omega) e' rfl
  apply flattenMsg_injective
  funext e
  exact key (cert.rank e) e rfl

/-- Every arbitrary-initial actual iterate beyond the constructed forest
    horizon equals the explicitly constructed full source fixed point. -/
theorem bpIterate_eq_cavity_completion {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f) (background : ν → X)
    (m : BPMessages ν α G X) (n : ℕ)
    (hn : max 1 (Fintype.card ν + Fintype.card α) ≤ n) :
    (fun m' => bpUpdate m' f)^[n] m = bpUpdate (scaledCavityMessages G f background) f := by
  rw [(bp_converges_on_forest G hG f m).1 n hn]
  exact bpFixedPoint_unique G (bpRankCertForest G hG) f _ _
    (bp_converges_on_forest G hG f m).2 (scaledCavityMessages_update_fixed G hG f hf background)

/-- The actual variables in the connected component of a variable vertex.
    The diagonal cut deletes no incidence edge. -/
noncomputable def componentVariables {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (v : ν) : Finset ν :=
  branchVariables G (Sum.inl v) (Sum.inl v)

/-- The actual factor vertices in the same connected component. -/
noncomputable def componentFactors {ν α : Type*} [Fintype ν] [Fintype α]
    (G : FactorGraph ν α) (v : ν) : Finset α :=
  branchFactors G (Sum.inl v) (Sum.inl v)

/-- Every factor in a whole component has all of its actual scope there. -/
theorem factorScope_subset_component {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (v : ν) (a : α) (ha : a ∈ componentFactors G v) :
    factorScope G a ⊆ componentVariables G v := by
  classical
  intro u hu
  have ha' : Sum.inr a ∈ forestBranch (incidenceGraph G) (Sum.inl v) (Sum.inl v) := by
    simpa [componentFactors, branchFactors] using ha
  have hau : G.incidence a u = true := by simpa [factorScope] using hu
  rcases adjacent_mem_branch_or_cut (incidenceGraph G) ha'
    ((incidenceGraph_inl_inr_adj G u a).mpr hau).symm with hin | he
  · simpa [componentVariables, branchVariables] using hin
  · simp at he

/-- A factor outside the selected component cannot depend on any variable
    inside it; disconnected components remain genuine independent scopes. -/
theorem factorScope_subset_component_compl {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (v : ν) (a : α) (ha : a ∉ componentFactors G v) :
    factorScope G a ⊆ (componentVariables G v)ᶜ := by
  classical
  intro u hu
  simp only [Finset.mem_compl]
  intro hum
  have hu' : Sum.inl u ∈ forestBranch (incidenceGraph G) (Sum.inl v) (Sum.inl v) := by
    simpa [componentVariables, branchVariables] using hum
  have hau : G.incidence a u = true := by simpa [factorScope] using hu
  rcases adjacent_mem_branch_or_cut (incidenceGraph G) hu'
    ((incidenceGraph_inl_inr_adj G u a).mpr hau) with hin | he
  · exact ha (by simpa [componentFactors, branchFactors] using hin)
  · simp at he

/-- All factors of a variable's component are covered once by its genuine
    incoming incident branches, including an isolated variable's empty cover. -/
theorem componentFactors_eq_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) :
    componentFactors G v = (incidentFactors G v).biUnion
      (fun a => branchFactors G (Sum.inr a) (Sum.inl v)) := by
  classical
  ext b
  simp only [componentFactors, Finset.mem_biUnion, branchFactors, incidentFactors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hb
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inl v) (Sum.inl v) (Sum.inr b)).mp hb with he | ⟨z, hz, _, hbz⟩
    · cases he
    · rcases z with u | c
      · have hn : ¬(incidenceGraph G).Adj (Sum.inl u) (Sum.inl v) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
      · exact ⟨c, (incidenceGraph_inl_inr_adj G v c).mp hz.symm, hbz⟩
  · rintro ⟨c, hcv, hbc⟩
    exact forestBranch_subset_next (incidenceGraph G) hG
      ((incidenceGraph_inl_inr_adj G v c).mpr hcv).symm (by simp) hbc

/-- The selected variable and all incoming branch variables cover its entire
    component, with the source variable included exactly once after erasure. -/
theorem componentVariables_eq_insert_biUnion {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) :
    componentVariables G v = insert v ((incidentFactors G v).biUnion
      (fun a => branchVariables G (Sum.inr a) (Sum.inl v))) := by
  classical
  ext u
  simp only [componentVariables, Finset.mem_insert, Finset.mem_biUnion, branchVariables,
    incidentFactors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hu
    rcases (mem_forestBranch_iff_source_or_incoming (incidenceGraph G) hG
      (Sum.inl v) (Sum.inl v) (Sum.inl u)).mp hu with he | ⟨z, hz, _, huz⟩
    · exact Or.inl (by simpa using he)
    · right
      rcases z with w | a
      · have hn : ¬(incidenceGraph G).Adj (Sum.inl w) (Sum.inl v) := by
          simp [incidenceGraph, SimpleGraph.fromRel_adj]
        exact (hn hz).elim
      · exact ⟨a, (incidenceGraph_inl_inr_adj G v a).mp hz.symm, huz⟩
  · rintro (rfl | ⟨a, hav, hua⟩)
    · exact mem_forestBranch_self _ _ _
    · exact forestBranch_subset_next (incidenceGraph G) hG
        ((incidenceGraph_inl_inr_adj G v a).mpr hav).symm (by simp) hua

/-- Any genuine product over the component's factors splits over its
    disjoint incoming factor branches, without repeating a source factor. -/
theorem prod_componentFactors {ν α : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G) (v : ν) (w : α → ℝ) :
    (∏ b ∈ componentFactors G v, w b) =
      ∏ a ∈ incidentFactors G v, ∏ b ∈ branchFactors G (Sum.inr a) (Sum.inl v), w b := by
  classical
  rw [componentFactors_eq_biUnion G hG v]
  apply Finset.prod_biUnion
  intro a ha b hb hab
  have hav : G.incidence a v = true := (Finset.mem_filter.mp ha).2
  have hbv : G.incidence b v = true := (Finset.mem_filter.mp hb).2
  exact branchFactors_disjoint_incoming G hG
    ((incidenceGraph_inl_inr_adj G v b).mpr hbv).symm
    ((incidenceGraph_inl_inr_adj G v a).mpr hav).symm (by simpa using hab)

/-- Splitting all assignments of the selected component at its variable root
    gives precisely the product of its genuine incoming cavity sums. -/
theorem cavitySum_component {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (v : ν) (ξ : X) (background : ν → X) :
    cavitySum G f (Sum.inl v) (Sum.inl v) v ξ background =
      ∏ a ∈ incidentFactors G v,
        cavitySum G f (Sum.inr a) (Sum.inl v) v ξ background := by
  classical
  have hw : ∀ z : ν → X, branchWeight G f (Sum.inl v) (Sum.inl v) z =
      ∏ a ∈ incidentFactors G v, branchWeight G f (Sum.inr a) (Sum.inl v) z := by
    intro z
    exact prod_componentFactors G hG v (fun b => f b z)
  unfold cavitySum
  simp_rw [hw]
  change (∑ y : (componentVariables G v).erase v → X, ∏ a ∈ incidentFactors G v,
    branchWeight G f (Sum.inr a) (Sum.inl v)
      (Function.update (extendScope ((componentVariables G v).erase v) y background) v ξ)) = _
  rw [componentVariables_eq_insert_biUnion G hG v,
    Finset.erase_insert_eq_erase, Finset.erase_biUnion]
  apply sum_prod_biUnion_boundary
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro u hu hu'
    have h := branchVariables_disjoint_incoming G hG
      ((incidenceGraph_inl_inr_adj G v b).mpr (Finset.mem_filter.mp hb).2).symm
      ((incidenceGraph_inl_inr_adj G v a).mpr (Finset.mem_filter.mp ha).2).symm
      (by simpa using hab)
    exact Finset.disjoint_left.mp h (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hu')
  · intro a ha z z' hz
    apply branchWeight_dependsOn_boundary G f hf (Sum.inr a) (Sum.inl v) v a Sym2.eq_swap z z'
    intro u hu
    apply hz
    by_cases huv : u = v <;> simp_all

/-- Actual late-iterate beliefs equal the true whole-component numerator
    times the source's strictly positive component multiplicity, not an assumed normalization. -/
theorem variableBelief_iterate_component {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f) (background : ν → X)
    (m : BPMessages ν α G X) (n : ℕ)
    (hn : max 1 (Fintype.card ν + Fintype.card α) ≤ n) (v : ν) (ξ : X) :
    variableBelief ((fun m' => bpUpdate m' f)^[n] m) v ξ =
      branchMultiplier (X := X) G (Sum.inl v) (Sum.inl v) *
        cavitySum G f (Sum.inl v) (Sum.inl v) v ξ background := by
  classical
  rw [bpIterate_eq_cavity_completion G hG f hf background m n hn]
  unfold variableBelief
  trans ∏ a ∈ incidentFactors G v, (scaledCavityMessages G f background).factorToVar a v ξ
  · apply Finset.prod_congr rfl
    intro a ha
    exact scaledCavityMessages_factor_update G hG f hf background a v
      (Finset.mem_filter.mp ha).2 ξ
  · simp only [scaledCavityMessages, Finset.prod_mul_distrib]
    rw [← cavitySum_component G hG f hf v ξ background]
    congr 1
    exact (prod_componentFactors G hG v
      (fun b => extensionMultiplicity (X := X) (factorScope G b))).symm

/-- Restrict and glue actual assignments on a finite scope and its exact
    complement, retaining disconnected and empty assignment domains. -/
noncomputable def scopeComplementEquiv {U X : Type*} [Fintype U] [DecidableEq U]
    (s : Finset U) : (U → X) ≃ (s → X) × ((sᶜ : Finset U) → X) := by
  classical
  refine
    { toFun := fun y => (fun u => y u, fun u => y u)
      invFun := fun p u => if h : u ∈ s then p.1 ⟨u, h⟩ else p.2 ⟨u, Finset.mem_compl.mpr h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    funext u
    dsimp only
    split_ifs <;> rfl
  · intro p
    apply Prod.ext
    · funext u
      simp only [dif_pos u.property]
    · funext u
      have hu : (u : U) ∉ s := Finset.mem_compl.mp u.property
      simp [hu]

/-- Genuine finite-assignment factorization across a scope and its complement;
    neither side receives the other's exterior-assignment multiplicity. -/
theorem sum_mul_dependsOn_compl {U X : Type*}
    [Fintype U] [Fintype X] [DecidableEq U]
    (s : Finset U) (F H : (U → X) → ℝ)
    (hF : DependsOn s F) (hH : DependsOn sᶜ H) (background : U → X) :
    (∑ y : U → X, F y * H y) =
      (∑ z : s → X, F (extendScope s z background)) *
        ∑ w : (sᶜ : Finset U) → X, H (extendScope sᶜ w background) := by
  classical
  let e := scopeComplementEquiv (X := X) s
  have he := Fintype.sum_equiv e (fun y => F y * H y)
    (fun p => F (extendScope s p.1 background) * H (extendScope sᶜ p.2 background)) (by
      intro y
      apply congrArg₂ (· * ·)
      · apply hF
        intro u hu
        simp [e, scopeComplementEquiv, extendScope, hu]
      · apply hH
        intro u hu
        simp [e, scopeComplementEquiv, extendScope, hu])
  rw [he, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- The exact global fixed-root numerator factors into its component's
    erased-root sum and the full partition of the complementary variables. -/
theorem sum_boundary_mul_dependsOn_compl {U X : Type*}
    [Fintype U] [Fintype X] [DecidableEq U] [DecidableEq X]
    (s : Finset U) (F H : (U → X) → ℝ)
    (hF : DependsOn s F) (hH : DependsOn sᶜ H)
    (v : U) (hv : v ∈ s) (ξ : X) (background : U → X) :
    (∑ y : U → X with y v = ξ, F y * H y) =
      (∑ z : s.erase v → X,
        F (Function.update (extendScope (s.erase v) z background) v ξ)) *
          ∑ w : (sᶜ : Finset U) → X, H (extendScope sᶜ w background) := by
  classical
  have hg : DependsOn s (fun y => if y v = ξ then F y else 0) := by
    intro y z hyz
    change (if y v = ξ then F y else 0) = (if z v = ξ then F z else 0)
    rw [hyz v hv, hF y z hyz]
  have h := sum_mul_dependsOn_compl s (fun y => if y v = ξ then F y else 0) H hg hH background
  have ev : ∀ z : s → X, extendScope s z background v = z ⟨v, hv⟩ := by
    intro z; simp [extendScope, hv]
  simp only [ite_mul, zero_mul, ev] at h
  rw [← Finset.sum_filter, ← Finset.sum_filter, sum_fixed_scope] at h
  exact h

/-- Original factors outside the selected component, retaining isolated
    factors and every other connected component. -/
noncomputable def outsideWeight {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (v : ν) (y : ν → X) : ℝ :=
  ∏ a ∈ (componentFactors G v)ᶜ, f a y

/-- The actual component product depends only on its own variables. -/
theorem componentWeight_dependsOn {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f) (v : ν) :
    DependsOn (componentVariables G v) (branchWeight G f (Sum.inl v) (Sum.inl v)) := by
  classical
  intro y z hyz
  apply Finset.prod_congr rfl
  intro a ha
  apply hf a
  intro u hu
  exact hyz u (factorScope_subset_component G v a ha hu)

/-- Complementary factors depend only on complementary variables, so their
    partition cannot silently include a second copy of the selected component. -/
theorem outsideWeight_dependsOn {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f) (v : ν) :
    DependsOn (componentVariables G v)ᶜ (outsideWeight G f v) := by
  classical
  intro y z hyz
  apply Finset.prod_congr rfl
  intro a ha
  apply hf a
  intro u hu
  exact hyz u (factorScope_subset_component_compl G v a (Finset.mem_compl.mp ha) hu)

/-- The original joint weight factors into the selected component and all
    other components; isolated constant factors remain in the complement. -/
theorem jointWeight_component_mul_outside {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (v : ν) (y : ν → X) :
    jointWeight f y = branchWeight G f (Sum.inl v) (Sum.inl v) y * outsideWeight G f v y := by
  classical
  exact (Finset.prod_mul_prod_compl (componentFactors G v) (fun a => f a y)).symm

/-- Actual finite partition on the selected component's own variables. -/
noncomputable def componentPartition {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (v : ν) (background : ν → X) : ℝ :=
  ∑ z : componentVariables G v → X,
    branchWeight G f (Sum.inl v) (Sum.inl v) (extendScope (componentVariables G v) z background)

/-- Actual partition over exactly the complementary variables and factors. -/
noncomputable def outsidePartition {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (v : ν) (background : ν → X) : ℝ :=
  ∑ z : ((componentVariables G v)ᶜ : Finset ν) → X,
    outsideWeight G f v (extendScope (componentVariables G v)ᶜ z background)

/-- The true global partition factors over a selected component and every
    remaining component, with all assignment coordinates counted exactly once. -/
theorem partition_component_mul_outside {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (v : ν) (background : ν → X) :
    partition f = componentPartition G f v background * outsidePartition G f v background := by
  classical
  unfold partition
  simp_rw [jointWeight_component_mul_outside G f v]
  convert sum_mul_dependsOn_compl (componentVariables G v) _ _
    (componentWeight_dependsOn G f hf v) (outsideWeight_dependsOn G f hf v) background using 1 <;>
    congr 1
  ext y
  simp

/-- True global variable numerators retain the complete partition of every
    other component, including isolated variables and constant factors. -/
theorem marginalWeight_component_mul_outside {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (v : ν) (ξ : X) (background : ν → X) :
    marginalWeight f v ξ = cavitySum G f (Sum.inl v) (Sum.inl v) v ξ background *
      outsidePartition G f v background := by
  classical
  have hv : v ∈ componentVariables G v := by
    simpa [componentVariables, branchVariables] using
      mem_forestBranch_self (incidenceGraph G) (Sum.inl v) (Sum.inl v)
  unfold marginalWeight
  simp_rw [jointWeight_component_mul_outside G f v]
  convert sum_boundary_mul_dependsOn_compl (componentVariables G v) _ _
    (componentWeight_dependsOn G f hf v) (outsideWeight_dependsOn G f hf v)
    v hv ξ background using 1 <;> congr 1
  ext y
  simp

/-- Nonnegative original factors and a genuinely positive global partition
    force both actual component partitions positive, even with zero factor entries. -/
theorem componentPartitions_pos {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (hnonneg : ∀ a y, 0 ≤ f a y) (hZ : 0 < partition f)
    (v : ν) (background : ν → X) :
    0 < componentPartition G f v background ∧ 0 < outsidePartition G f v background := by
  classical
  have hc : 0 ≤ componentPartition G f v background :=
    Finset.sum_nonneg (fun z _ => Finset.prod_nonneg (fun a _ => hnonneg a _))
  have ho : 0 ≤ outsidePartition G f v background :=
    Finset.sum_nonneg (fun z _ => Finset.prod_nonneg (fun a _ => hnonneg a _))
  have hp : 0 < componentPartition G f v background * outsidePartition G f v background := by
    rw [← partition_component_mul_outside G f hf v background]
    exact hZ
  constructor
  · by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) hc
    rw [hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  · by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) ho
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp

/-- Summing the genuine component numerators over the root state gives
    exactly its true partition, with no division by individual messages. -/
theorem sum_cavitySum_component {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [DecidableEq ν]
    (G : FactorGraph ν α) (f : α → (ν → X) → ℝ) (v : ν) (background : ν → X) :
    (∑ ξ, cavitySum G f (Sum.inl v) (Sum.inl v) v ξ background) =
      componentPartition G f v background := by
  classical
  have hv : v ∈ componentVariables G v := by
    simpa [componentVariables, branchVariables] using
      mem_forestBranch_self (incidenceGraph G) (Sum.inl v) (Sum.inl v)
  symm
  unfold componentPartition
  rw [sum_scope_root (componentVariables G v) v hv]
  simp_rw [extendScope_root_split]
  rfl

/-- The actual late-iterate belief normalizer is positive from the genuine
    global partition and nonnegative factors, permitting individual zero messages. -/
theorem variableBelief_normalizer_pos {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [Nonempty X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (hnonneg : ∀ a y, 0 ≤ f a y) (hZ : 0 < partition f) (background : ν → X)
    (m : BPMessages ν α G X) (n : ℕ)
    (hn : max 1 (Fintype.card ν + Fintype.card α) ≤ n) (v : ν) :
    0 < ∑ ξ, variableBelief ((fun m' => bpUpdate m' f)^[n] m) v ξ := by
  classical
  simp_rw [variableBelief_iterate_component G hG f hf background m n hn v]
  rw [← Finset.mul_sum, sum_cavitySum_component]
  exact mul_pos (branchMultiplier_pos G (Sum.inl v) (Sum.inl v))
    (componentPartitions_pos G f hf hnonneg hZ v background).1

/-- Exact global marginal of the ORIGINAL complete-assignment BP algorithm
    on every finite forest, from arbitrary initial arrays beyond its proved horizon.
    Only actual global-partition positivity is assumed; individual messages may be zero. -/
theorem normalized_variableBelief_eq_global_marginal {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X] [Nonempty X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (hG : IsAcyclicFactorGraph G)
    (f : α → (ν → X) → ℝ) (hf : ScopeLocal G f)
    (hnonneg : ∀ a y, 0 ≤ f a y) (hZ : 0 < partition f)
    (m : BPMessages ν α G X) (n : ℕ)
    (hn : max 1 (Fintype.card ν + Fintype.card α) ≤ n) (v : ν) (ξ : X) :
    variableBelief ((fun m' => bpUpdate m' f)^[n] m) v ξ /
      (∑ η, variableBelief ((fun m' => bpUpdate m' f)^[n] m) v η) =
        normalizedMarginal f v ξ := by
  classical
  let background : ν → X := fun _ => Classical.choice (inferInstance : Nonempty X)
  have hC := branchMultiplier_pos (X := X) G (Sum.inl v) (Sum.inl v)
  obtain ⟨hc, ho⟩ := componentPartitions_pos G f hf hnonneg hZ v background
  simp_rw [variableBelief_iterate_component G hG f hf background m n hn v]
  rw [← Finset.mul_sum, sum_cavitySum_component]
  unfold normalizedMarginal
  rw [marginalWeight_component_mul_outside G f hf v ξ background,
    partition_component_mul_outside G f hf v background]
  field_simp [ne_of_gt hC, ne_of_gt hc, ne_of_gt ho]

/-- Native zero-partition control on the actual three-node source tree:
    neither the actual BP belief nor totalized real division supplies a probability law. -/
theorem zeroPartition_control
    (m : BPMessages (Fin 2) (Fin 1) starFactorGraph Bool) :
    partition (ν := Fin 2) (α := Fin 1) (X := Bool) (fun _ _ => 0) = 0 ∧
      (∑ ξ, variableBelief (bpUpdate m (fun _ _ => 0)) 0 ξ) = 0 ∧
      (∑ ξ, normalizedMarginal (ν := Fin 2) (α := Fin 1)
        (fun _ (_ : Fin 2 → Bool) => 0) 0 ξ) = 0 := by
  simp [partition, jointWeight, normalizedMarginal, marginalWeight,
    variableBelief, bpUpdate, bpFactorUpdate, incidentFactors, starFactorGraph]

/-- Actual four-node path u-a-v-b used to test the necessity of locality. -/
def nonlocalControlGraph : FactorGraph (Fin 2) (Fin 2) where
  incidence a v := if a = 0 then true else v = 1

/-- The second factor illegally reads u although its incidence scope is only v. -/
def nonlocalControlWeight (a : Fin 2) (y : Fin 2 → Bool) : ℝ :=
  if a = 0 then 1 else if y 0 = false then 1 else 0

/-- Explicit values for every original coordinate, including both nonedges. -/
def nonlocalControlMessages : BPMessages (Fin 2) (Fin 2) nonlocalControlGraph Bool where
  varToFactor _ a _ := if a = 0 then 1 else 2
  factorToVar a v ξ := if a = 0 then 2 else if v = 1 then 1 else if ξ = false then 4 else 0

/-- Both source certificate fields hold on the four-node path; no forest
    assumption is inserted into the nonlocal countercontrol. -/
def nonlocalControlCert : BPRankCert nonlocalControlGraph := by
  let r : MsgEndpoint (Fin 2) (Fin 2) → ℕ := fun e => match e with
    | Sum.inl (v, a) => if a = 0 then if v = 0 then 0 else 1 else if v = 0 then 3 else 2
    | Sum.inr (a, v) => if a = 0 then if v = 0 then 2 else 1 else if v = 0 then 3 else 0
  refine { rank := r, var_gt := ?_, fac_gt := ?_ }
  · intro v a b hba hb
    fin_cases v <;> fin_cases a <;> fin_cases b <;> simp_all [r, nonlocalControlGraph]
  · intro a v u huv hu
    fin_cases a <;> fin_cases v <;> fin_cases u <;> simp_all [r, nonlocalControlGraph]

/-- Exact four-assignment enumeration used only to check the native binary
    countercontrols against the original complete-assignment sums. -/
theorem sum_finTwo_bool [Fintype (Fin 2 → Bool)] (F : (Fin 2 → Bool) → ℝ) :
    (∑ y, F y) = F ![false, false] + F ![false, true] +
      F ![true, false] + F ![true, true] := by
  have h := ((finTwoArrowEquiv Bool).symm.sum_comp F).symm
  simpa [Fintype.sum_prod_type, finTwoArrowEquiv, add_comm, add_assoc] using h

/-- Kernel-checked fixed point of the actual complete-assignment update for
    the nonlocal factor model; its nonincident coordinates are included. -/
theorem nonlocalControl_fixed : IsBPFixedPoint nonlocalControlMessages nonlocalControlWeight := by
  unfold IsBPFixedPoint
  apply flattenMsg_injective
  funext e ξ
  rcases e with ⟨v, a⟩ | ⟨a, v⟩
  · fin_cases v <;> fin_cases a <;> cases ξ <;>
      norm_num [flattenMsg, bpUpdate, bpVariableUpdate, otherFactors,
        nonlocalControlGraph, nonlocalControlMessages, Finset.prod_filter, Fin.prod_univ_succ]
  · simp only [flattenMsg, bpUpdate, bpFactorUpdate, Finset.sum_filter]
    rw [sum_finTwo_bool]
    simp only [otherVars, Finset.prod_filter, Fin.prod_univ_succ]
    fin_cases a <;> fin_cases v <;> cases ξ <;>
      norm_num [nonlocalControlGraph, nonlocalControlMessages, nonlocalControlWeight]

/-- A genuine forest, nonnegative weights, positive partition and actual fixed
    point still fail marginal correctness if the necessary scope locality is removed. -/
theorem nonlocalControl_counterexample :
    IsAcyclicFactorGraph nonlocalControlGraph ∧
      (∀ a y, 0 ≤ nonlocalControlWeight a y) ∧
      0 < partition nonlocalControlWeight ∧
      IsBPFixedPoint nonlocalControlMessages nonlocalControlWeight ∧
      ¬ ScopeLocal nonlocalControlGraph nonlocalControlWeight ∧
      variableBelief nonlocalControlMessages 0 false /
        (∑ ξ, variableBelief nonlocalControlMessages 0 ξ) ≠
          normalizedMarginal nonlocalControlWeight 0 false := by
  classical
  have hz : partition nonlocalControlWeight = 2 := by
    unfold partition
    simp only [sum_finTwo_bool]
    norm_num [jointWeight, nonlocalControlWeight, Fin.prod_univ_succ]
  have hm : marginalWeight nonlocalControlWeight 0 false = 2 := by
    unfold marginalWeight
    simp only [Finset.sum_filter, sum_finTwo_bool]
    norm_num [jointWeight, nonlocalControlWeight, Fin.prod_univ_succ]
  have hb : ∀ ξ, variableBelief nonlocalControlMessages 0 ξ = 2 := by
    intro ξ
    simp only [variableBelief, incidentFactors, Finset.prod_filter, Fin.prod_univ_succ]
    norm_num [nonlocalControlGraph, nonlocalControlMessages]
  refine ⟨isAcyclicFactorGraph_of_bpRankCert nonlocalControlCert, ?_, ?_,
    nonlocalControl_fixed, ?_, ?_⟩
  · intro a y
    unfold nonlocalControlWeight
    split_ifs <;> norm_num
  · rw [hz]; norm_num
  · intro hl
    have he := hl 1 ![false, false] ![true, false] (by
      intro v hv
      fin_cases v <;> simp_all [factorScope, nonlocalControlGraph])
    norm_num [nonlocalControlWeight] at he
  · simp_rw [hb]
    norm_num [normalizedMarginal, hz, hm]

/-- One unary component, one isolated variable and one isolated constant factor. -/
def disconnectedControlGraph : FactorGraph (Fin 2) (Fin 2) where
  incidence a v := a = 0 ∧ v = 0

/-- A zero local entry is allowed; the isolated factor contributes five to Z. -/
def disconnectedControlWeight (a : Fin 2) (y : Fin 2 → Bool) : ℝ :=
  if a = 0 then if y 0 = false then 0 else 3 else 5

/-- Constructed all-pairs rank for the actual disconnected control graph. -/
def disconnectedControlCert : BPRankCert disconnectedControlGraph := by
  let r : MsgEndpoint (Fin 2) (Fin 2) → ℕ := fun e => match e with
    | Sum.inl (v, a) => if v = 0 ∧ a = 1 then 1 else 0
    | Sum.inr (a, v) => if a = 0 ∧ v = 1 then 1 else 0
  refine { rank := r, var_gt := ?_, fac_gt := ?_ }
  · intro v a b hba hb
    fin_cases v <;> fin_cases a <;> fin_cases b <;> simp_all [r, disconnectedControlGraph]
  · intro a v u huv hu
    fin_cases a <;> fin_cases v <;> fin_cases u <;> simp_all [r, disconnectedControlGraph]

/-- Positive native control with an isolated variable, an isolated factor,
    an individual zero message and source multiplicity two. All values refer
    to the actual global model and original update, from any initial messages. -/
theorem disconnectedControl_values
    (m : BPMessages (Fin 2) (Fin 2) disconnectedControlGraph Bool) :
    IsAcyclicFactorGraph disconnectedControlGraph ∧
      ScopeLocal disconnectedControlGraph disconnectedControlWeight ∧
      (∀ a y, 0 ≤ disconnectedControlWeight a y) ∧
      partition disconnectedControlWeight = 30 ∧
      extensionMultiplicity (X := Bool) (factorScope disconnectedControlGraph 0) = 2 ∧
      variableBelief (bpUpdate m disconnectedControlWeight) 0 false = 0 ∧
      (∑ ξ, variableBelief (bpUpdate m disconnectedControlWeight) 0 ξ) = 6 ∧
      (∀ ξ, variableBelief (bpUpdate m disconnectedControlWeight) 1 ξ = 1) ∧
      normalizedMarginal disconnectedControlWeight 0 true = 1 ∧
      normalizedMarginal disconnectedControlWeight 1 true = 1 / 2 := by
  classical
  have hz : partition disconnectedControlWeight = 30 := by
    unfold partition
    simp only [sum_finTwo_bool]
    norm_num [jointWeight, disconnectedControlWeight, Fin.prod_univ_succ]
  have hm0 : marginalWeight disconnectedControlWeight 0 true = 30 := by
    unfold marginalWeight
    simp only [Finset.sum_filter, sum_finTwo_bool]
    norm_num [jointWeight, disconnectedControlWeight, Fin.prod_univ_succ]
  have hm1 : marginalWeight disconnectedControlWeight 1 true = 15 := by
    unfold marginalWeight
    simp only [Finset.sum_filter, sum_finTwo_bool]
    norm_num [jointWeight, disconnectedControlWeight, Fin.prod_univ_succ]
  have hfac : ∀ ξ, bpFactorUpdate m disconnectedControlWeight 0 0 ξ = if ξ = false then 0 else 6 := by
    intro ξ
    simp only [bpFactorUpdate, Finset.sum_filter, sum_finTwo_bool,
      otherVars, Finset.prod_filter, Fin.prod_univ_succ]
    cases ξ <;> norm_num [disconnectedControlGraph, disconnectedControlWeight]
  have hb0 : ∀ ξ, variableBelief (bpUpdate m disconnectedControlWeight) 0 ξ =
      if ξ = false then 0 else 6 := by
    intro ξ
    simp only [variableBelief, incidentFactors, Finset.prod_filter, Fin.prod_univ_succ]
    simpa [disconnectedControlGraph, bpUpdate] using hfac ξ
  have hb1 : ∀ ξ, variableBelief (bpUpdate m disconnectedControlWeight) 1 ξ = 1 := by
    intro ξ
    simp [variableBelief, incidentFactors, disconnectedControlGraph]
  refine ⟨isAcyclicFactorGraph_of_bpRankCert disconnectedControlCert, ?_, ?_, hz,
    ?_, ?_, ?_, hb1, ?_, ?_⟩
  · intro a y z hyz
    fin_cases a
    · have h0 := hyz 0 (by simp [factorScope, disconnectedControlGraph])
      simp [disconnectedControlWeight, h0]
    · simp [disconnectedControlWeight]
  · intro a y
    unfold disconnectedControlWeight
    split_ifs <;> norm_num
  · have he : factorScope disconnectedControlGraph 0 = {0} := by
      ext u
      fin_cases u <;> simp [factorScope, disconnectedControlGraph]
    rw [he]
    norm_num [extensionMultiplicity]
  · simp [hb0]
  · simp_rw [hb0]; norm_num
  · norm_num [normalizedMarginal, hz, hm0]
  · norm_num [normalizedMarginal, hz, hm1]

end Probability
end SKEFTHawking.BeliefPropagation
