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

end Probability
end SKEFTHawking.BeliefPropagation
