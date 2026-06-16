import Mathlib
import SKEFTHawking.SingularDisjointUnion

/-!
# Mayer–Vietoris: the chain-level intersection, sum, and short exact sequence

Toward Mayer–Vietoris (the engine of the fundamental-class gluing, Hatcher 3.26). The two submodules
`subspaceChains A`, `subspaceChains B` of `Cₙ(X)` satisfy:

* `subspaceChains A ⊓ subspaceChains B = subspaceChains (A ∩ B)` — a chain supported on `A`-valued AND
  `B`-valued simplices is supported on `(A∩B)`-valued ones (a simplex with image in both `A` and `B`
  has image in `A ∩ B`);
* monotonicity `A ⊆ B ⟹ subspaceChains A ≤ subspaceChains B`.

These are the algebra underlying the **Mayer–Vietoris short exact sequence of chain complexes**
`0 → C(A∩B) →[Δ] C(A) ⊕ C(B) →[Σ] C(A) + C(B) → 0`, with `Δ c = (c, c)` (the diagonal) and
`Σ (a, b) = a + b` (the sum, landing in `smallChains {A, B} = C(A) ⊔ C(B)`). This module builds those two
maps (`mvDiag`, `mvSum`) and proves the three exactness conditions (`mvDiag` injective, `mvSum`
surjective, `range mvDiag = ker mvSum`) — the snake-lemma input for the MV connecting homomorphism
`δ : Hₙ(X) → Hₙ₋₁(A∩B)` and hence the `Hₙ(M | A)` compactness induction giving the fundamental class
`[M]`. Over `ℤ/2`, `a - b = a + b`, so the sum map (not a difference) already has `ker = im Δ`.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularMayerVietoris

/-- **Subspace chains are monotone**: `A ⊆ B ⟹ subspaceChains A ≤ subspaceChains B`. -/
theorem subspaceChains_mono {X : TopCat} {A B : Set ↑X} (h : A ⊆ B) (n : ℕ) :
    subspaceChains (S := A) n ≤ subspaceChains (S := B) n := by
  rintro c ⟨a, rfl⟩
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | single σ' x =>
      rw [chainIncl_single,
        show Finsupp.single (simplexIncl A n σ') x
          = x • Finsupp.single (simplexIncl A n σ') (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ x
        (single_mem_subspaceChains_of_subordinate ((range_realize_simplexIncl A σ').trans h))

/-- **The Mayer–Vietoris intersection identity**: `subspaceChains A ⊓ subspaceChains B =
subspaceChains (A ∩ B)`. -/
theorem subspaceChains_inf {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    subspaceChains (S := A) n ⊓ subspaceChains (S := B) n = subspaceChains (S := A ∩ B) n := by
  refine le_antisymm (fun c ⟨hcA, hcB⟩ => ?_)
    (le_inf (subspaceChains_mono Set.inter_subset_left n)
      (subspaceChains_mono Set.inter_subset_right n))
  -- every simplex in `support c` is `(A∩B)`-valued, so `c ∈ subspaceChains (A∩B)`
  rw [← Finsupp.sum_single c]
  refine Submodule.sum_mem _ fun τ hτ => ?_
  have hne : c τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
  have hτA : τ ∈ Set.range (simplexIncl A n) := by
    obtain ⟨a, rfl⟩ := hcA
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range a τ hnr)
  have hτB : τ ∈ Set.range (simplexIncl B n) := by
    obtain ⟨b, rfl⟩ := hcB
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range b τ hnr)
  obtain ⟨σA, rfl⟩ := hτA
  obtain ⟨σB, hσB⟩ := hτB
  rw [show Finsupp.single (simplexIncl A n σA) (c (simplexIncl A n σA))
      = c (simplexIncl A n σA) • Finsupp.single (simplexIncl A n σA) (1 : ZMod 2) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ (single_mem_subspaceChains_of_subordinate ?_)
  rw [Set.subset_inter_iff]
  exact ⟨range_realize_simplexIncl A σA, hσB ▸ range_realize_simplexIncl B σB⟩

/-! ## The Mayer–Vietoris short exact sequence of chain modules -/

/-- **The diagonal `Δ : C(A∩B) → C(A) ⊕ C(B)`**, `c ↦ (c, c)` — the two submodule inclusions
`C(A∩B) ≤ C(A)` and `C(A∩B) ≤ C(B)` (`subspaceChains_mono`) paired up. The first map of the MV SES. -/
noncomputable def mvDiag {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    ↥(subspaceChains (S := A ∩ B) n) →ₗ[ZMod 2]
      ↥(subspaceChains (S := A) n) × ↥(subspaceChains (S := B) n) :=
  (Submodule.inclusion (subspaceChains_mono Set.inter_subset_left n)).prod
    (Submodule.inclusion (subspaceChains_mono Set.inter_subset_right n))

@[simp] theorem mvDiag_apply {X : TopCat} (A B : Set ↑X) (n : ℕ) (c : ↥(subspaceChains (S := A ∩ B) n)) :
    ((mvDiag A B n c).1 : SingularChain X n) = (c : SingularChain X n)
      ∧ ((mvDiag A B n c).2 : SingularChain X n) = (c : SingularChain X n) :=
  ⟨rfl, rfl⟩

/-- **The sum `Σ : C(A) ⊕ C(B) → C(A) + C(B)`**, `(a, b) ↦ a + b`, landing in
`smallChains {A, B} = C(A) ⊔ C(B)` (`smallChains_two_eq`). The second map of the MV SES. -/
noncomputable def mvSum {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    ↥(subspaceChains (S := A) n) × ↥(subspaceChains (S := B) n) →ₗ[ZMod 2]
      ↥(smallChains {A, B} n) :=
  LinearMap.codRestrict _
    ((subspaceChains (S := A) n).subtype.coprod (subspaceChains (S := B) n).subtype)
    (fun p => by
      rw [smallChains_two_eq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left p.1.2) (Submodule.mem_sup_right p.2.2))

@[simp] theorem mvSum_apply {X : TopCat} (A B : Set ↑X) (n : ℕ)
    (p : ↥(subspaceChains (S := A) n) × ↥(subspaceChains (S := B) n)) :
    (mvSum A B n p : SingularChain X n) = (p.1 : SingularChain X n) + (p.2 : SingularChain X n) :=
  rfl

/-- `Δ` is **injective**: `(c, c) = 0` forces `c = 0` (read off the first component). -/
theorem mvDiag_injective {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    Function.Injective (mvDiag A B n) := by
  intro c c' h
  exact Subtype.ext (congrArg (Subtype.val ∘ Prod.fst) h)

/-- `Σ` is **surjective**: an element of `smallChains {A, B} = C(A) ⊔ C(B)` decomposes as `a + b`. -/
theorem mvSum_surjective {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    Function.Surjective (mvSum A B n) := by
  rintro ⟨z, hz⟩
  rw [smallChains_two_eq, Submodule.mem_sup] at hz
  obtain ⟨a, ha, b, hb, hab⟩ := hz
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

/-- **Exactness at the middle term** `range Δ = ker Σ`: a pair `(a, b)` with `a + b = 0` has `a = b`
(char 2), and then `a ∈ C(A) ⊓ C(B) = C(A∩B)`, so `(a, b) = Δ a`. Conversely `Σ (Δ c) = c + c = 0`. -/
theorem mvDiag_range_eq_mvSum_ker {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    LinearMap.range (mvDiag A B n) = LinearMap.ker (mvSum A B n) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [mvSum_apply]
    show (c : SingularChain X n) + (c : SingularChain X n) = 0
    exact ZModModule.add_self _
  · rintro ⟨a, b⟩ hab
    have h0 : (a : SingularChain X n) + (b : SingularChain X n) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hab)
    have hab' : (a : SingularChain X n) = (b : SingularChain X n) := by
      rw [← neg_eq_of_add_eq_zero_left h0]
      exact neg_eq_of_add_eq_zero_left (ZModModule.add_self (b : SingularChain X n))
    have haAB : (a : SingularChain X n) ∈ subspaceChains (S := A ∩ B) n := by
      rw [← subspaceChains_inf]
      exact ⟨a.2, hab' ▸ b.2⟩
    refine ⟨⟨(a : SingularChain X n), haAB⟩, ?_⟩
    apply Prod.ext
    · exact Subtype.ext rfl
    · exact Subtype.ext hab'

end SKEFTHawking.SingularMayerVietoris
