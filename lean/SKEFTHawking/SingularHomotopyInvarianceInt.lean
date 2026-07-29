import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularPrism
import SKEFTHawking.SingularHomotopyInvariance

/-!
# Homotopy invariance of singular **integral** homology (signed prism)

The mod-2 prism (`SKEFTHawking.SingularPrism`) proves the chain-homotopy identity
`∂P + P∂ = g_# + f_#` over `ℤ/2`, where the alternating signs `(-1)ⁱ` all collapse to `1`. This
file rebuilds the **signed** integral prism operator
`P : Cₙ(X;ℤ) → Cₙ₊₁(Y;ℤ)`, `single σ 1 ↦ ∑ᵢ (-1)ⁱ • single (prismSimplex H σ i) 1`,
and the genuine signed identity `∂P + P∂ = g_# - f_#`.

**All geometric lemmas are reused verbatim from `SingularPrism`** (`prismSimplex`, the
`face_prismSimplex_side_v/w`, `prism_internal_cancel`, `face_zero/last_prismSimplex_*`,
`endSimplex`, `face_endSimplex`) — they are coefficient-free statements about *simplices*. Only the
chain-level sign bookkeeping is redone here. This is the integral analogue of
`SingularHomotopyInvariance`, and the engine of integral acyclicity (`SingularEuclideanAcyclicInt`)
and the deformation-retract homology isomorphisms feeding the integral local class.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularCohomologyMod2 (face)

namespace SKEFTHawking.SingularHomotopyInvarianceInt

/-! ## §1. The signed integral prism operator -/

/-- The **signed** prism chain of a single simplex `σ`: `∑ᵢ (-1)ⁱ • single (prismSimplex H σ i) 1`,
the integral chain homotopy building block (the mod-2 `prismBasis` with the alternating signs
restored). -/
noncomputable def prismBasisInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) : SingularChainInt Y (n + 1) :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (prismSimplex H σ i) 1

/-- The **integral prism operator** `P : Cₙ(X;ℤ) → Cₙ₊₁(Y;ℤ)`, the ℤ-linear extension of
`prismBasisInt` off the basis simplices. -/
noncomputable def prismOpInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ) :
    SingularChainInt X n →ₗ[ℤ] SingularChainInt Y (n + 1) :=
  Finsupp.linearCombination ℤ (prismBasisInt H n)

@[simp] theorem prismOpInt_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    prismOpInt H n (Finsupp.single σ a) = a • prismBasisInt H n σ := by
  rw [prismOpInt, Finsupp.linearCombination_single]

/-- The **integral endpoint map** `endMapInt H r : Cₙ(X;ℤ) → Cₙ(Y;ℤ)`, `single σ a ↦
single (endSimplex H r σ) a` — the pushforward of the homotopy slice `H(·, r)` (the integral
analogue of `SingularPrism.endMap`). -/
noncomputable def endMapInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (n : ℕ) : SingularChainInt X n →ₗ[ℤ] SingularChainInt Y n :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (endSimplex H r σ) 1)

@[simp] theorem endMapInt_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    endMapInt H r n (Finsupp.single σ a) = Finsupp.single (endSimplex H r σ) a := by
  rw [endMapInt, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §2. The boundary-identity double sums (signed) -/

/-- `∂(prismBasisInt σ)` as a signed double sum of single faces of prism simplices:
`∑ᵢ (-1)ⁱ ∑ⱼ (-1)ʲ single (∂ⱼ(prism σ i))`. The integral analogue of `chainBoundary_prismBasis`. -/
theorem chainBoundary_prismBasisInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary Y (n + 1) (prismBasisInt H (n + 1) σ)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ j : Fin (n + 3),
          ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (face j (prismSimplex H σ i)) 1 := by
  rw [prismBasisInt, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, chainBoundary_single, boundaryBasis]
  rfl

/-- `prismOpInt(∂σ)` as a signed double sum of single prism simplices of faces:
`∑ₖ (-1)ᵏ ∑ᵢ' (-1)ⁱ' single (prism (∂ₖσ) i')`. The integral analogue of `prismOp_chainBoundary`. -/
theorem prismOpInt_chainBoundary {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    prismOpInt H n (chainBoundary X n (Finsupp.single σ 1))
      = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • ∑ i' : Fin (n + 1),
          ((-1 : ℤ) ^ (i' : ℕ)) • Finsupp.single (prismSimplex H (face k σ) i') 1 := by
  rw [chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, prismOpInt_single, one_smul, prismBasisInt]
  rfl

/-! ## §3. The signed diagonal telescope -/

/-- **The signed diagonal faces telescope to the endpoints** (integral analogue of
`prism_diagonal_telescope`): `∑_p (single (face p.castSucc (prism σ p)) - single (face p.succ
(prism σ p))) = single (end₁ σ) - single (end₀ σ)`. The `-single(∂_{p+1}(prism p))` (w-diagonal,
succ side) of prism `p` equals `+single(∂_p(prism p+1))` (v-diagonal, castSucc side) up to sign of
prism `p+1`, so the interior telescopes; only the two endpoint terms survive. -/
theorem prism_diagonal_telescopeInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    ∑ p : Fin (n + 2), (Finsupp.single (face p.castSucc (prismSimplex H σ p)) (1 : ℤ)
      - Finsupp.single (face p.succ (prismSimplex H σ p)) 1)
    = Finsupp.single (endSimplex H 1 σ) 1 - Finsupp.single (endSimplex H 0 σ) 1 := by
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_succ
      (fun p : Fin (n + 2) => Finsupp.single (face p.castSucc (prismSimplex H σ p)) (1 : ℤ)),
    Fin.sum_univ_castSucc
      (fun p : Fin (n + 2) => Finsupp.single (face p.succ (prismSimplex H σ p)) (1 : ℤ))]
  have hcancel : (∑ p : Fin (n + 1),
        Finsupp.single (face p.castSucc.succ (prismSimplex H σ p.castSucc)) (1 : ℤ))
      = ∑ p : Fin (n + 1),
        Finsupp.single (face p.succ.castSucc (prismSimplex H σ p.succ)) (1 : ℤ) :=
    Finset.sum_congr rfl
      (fun p _ => congrArg (Finsupp.single · (1 : ℤ)) (prism_internal_cancel H σ p))
  rw [Fin.castSucc_zero, face_zero_prismSimplex_zero]
  rw [show (Fin.last (n + 1)).succ = (Fin.last (n + 2) : Fin (n + 3)) from rfl]
  rw [show (Fin.last (n + 1) : Fin (n + 2)) = Fin.last (n + 1) from rfl, face_last_prismSimplex_last]
  rw [hcancel]
  abel

/-! ## §4. The signed diagonal/side split -/

/-- The signed inner face-sum of prism `i` splits into its two **diagonal** faces
(`j ∈ {i.castSucc, i.succ}`, extracted with their signs `+`/`-`) and the remaining **side** faces. -/
private theorem prism_face_sum_splitInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    ((-1 : ℤ) ^ (i : ℕ)) • ∑ j : Fin (n + 3),
        ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1))
      = (Finsupp.single (face i.castSucc (prismSimplex H σ i)) 1
          - Finsupp.single (face i.succ (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1))
        + ((-1 : ℤ) ^ (i : ℕ)) • ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
            ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1)) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (n + 3) => j = i.castSucc ∨ j = i.succ)
    (fun j => ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (face j (prismSimplex H σ i)) 1)]
  rw [smul_add]
  congr 1
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have hfilter : Finset.univ.filter (fun j : Fin (n + 3) => j = i.castSucc ∨ j = i.succ)
      = {i.castSucc, i.succ} := by
    rw [Finset.filter_or, Finset.filter_eq', Finset.filter_eq', if_pos (Finset.mem_univ _),
      if_pos (Finset.mem_univ _), Finset.singleton_union]
  rw [hfilter, Finset.sum_pair hne, smul_add, smul_smul, smul_smul, Fin.val_castSucc, Fin.val_succ,
    ← pow_add, ← pow_add]
  have hc : ((-1 : ℤ) ^ ((i : ℕ) + (i : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  have hs : ((-1 : ℤ) ^ ((i : ℕ) + ((i : ℕ) + 1))) = -1 := by
    rw [show (i : ℕ) + ((i : ℕ) + 1) = 2 * (i : ℕ) + 1 by ring, pow_succ, pow_mul]; simp
  rw [hc, hs, one_smul, neg_one_smul, sub_eq_add_neg]

/-- Splitting the signed `∂(prismBasisInt σ)` double sum into the diagonal sum (telescopes to
`g_# - f_#`) and the side sum (equals `prismOpInt(∂σ)`). -/
private theorem prism_boundary_diag_sideInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ j : Fin (n + 3),
        ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1)))
      = (∑ p : Fin (n + 2), (Finsupp.single (face p.castSucc (prismSimplex H σ p)) 1
          - Finsupp.single (face p.succ (prismSimplex H σ p)) 1))
        + ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
            ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => prism_face_sum_splitInt H σ i)

/-! ## §5. The signed side faces cancel the `P∂` term -/

/-- **The signed side faces are exactly `-prismOpInt(∂σ)`**: the reindexing bijection `(k, i') ↦
(i, j)` sends each prism-of-a-face simplex `prism (∂ₖσ) i'` to the matching side face of a prism,
and the signs on the two sides differ by exactly `-1` (v: `i = i'+1`; w: `j = k+1`), so the side
sum carries the opposite sign of `prismOpInt(∂σ)`. This makes `∂P + P∂ = g_# - f_#` (the extra `-`
that mod-2 lacks). -/
private theorem prism_prismOpInt_eq_sideInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
          ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1)))
      = - ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • ∑ i' : Fin (n + 1),
          ((-1 : ℤ) ^ (i' : ℕ)) • Finsupp.single (prismSimplex H (face k σ) i') 1 := by
  -- Flatten both sides to a single sum over a product Finset.
  have hLHS : (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
          ((-1 : ℤ) ^ (j : ℕ)) • (Finsupp.single (face j (prismSimplex H σ i)) 1 : SingularChainInt Y (n + 1)))
      = ∑ x ∈ (Finset.univ : Finset (Fin (n + 2) × Fin (n + 3))).filter
            (fun x => ¬ (x.2 = x.1.castSucc ∨ x.2 = x.1.succ)),
          ((-1 : ℤ) ^ (x.1 : ℕ)) • ((-1 : ℤ) ^ (x.2 : ℕ)) • Finsupp.single (face x.2 (prismSimplex H σ x.1)) 1 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.smul_sum, Finset.sum_filter]
  have hRHS : (∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • ∑ i' : Fin (n + 1),
          ((-1 : ℤ) ^ (i' : ℕ)) • (Finsupp.single (prismSimplex H (face k σ) i') 1 : SingularChainInt Y (n + 1)))
      = ∑ a ∈ (Finset.univ : Finset (Fin (n + 2) × Fin (n + 1))),
          ((-1 : ℤ) ^ (a.1 : ℕ)) • ((-1 : ℤ) ^ (a.2 : ℕ)) • Finsupp.single (prismSimplex H (face a.1 σ) a.2) 1 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.smul_sum]
  rw [hLHS, hRHS, ← Finset.sum_neg_distrib, eq_comm]
  refine Finset.sum_bij
    (fun (a : Fin (n + 2) × Fin (n + 1)) _ =>
      if a.1 ≤ a.2.castSucc then ((a.2.succ, a.1.castSucc) : Fin (n + 2) × Fin (n + 3))
      else (a.2.castSucc, a.1.succ)) ?_ ?_ ?_ ?_
  · intro a _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    split_ifs with h
    · simp only [Fin.le_def, Fin.val_castSucc] at h
      simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [not_le, Fin.lt_def, Fin.val_castSucc] at h
      simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
  · intro a₁ _ a₂ _ h
    obtain ⟨k₁, i₁⟩ := a₁
    obtain ⟨k₂, i₂⟩ := a₂
    dsimp only at h
    split_ifs at h with h1 h2 <;>
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.le_def, not_le, Fin.val_castSucc,
        Fin.val_succ] at * <;>
      omega
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨i, j⟩ := b
    obtain ⟨_, hb2⟩ := hb
    simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hb2
    have hilt : (i : ℕ) < n + 2 := i.isLt
    have hjlt : (j : ℕ) < n + 3 := j.isLt
    by_cases hreg : (j : ℕ) < (i : ℕ)
    · refine ⟨(⟨(j : ℕ), by omega⟩, ⟨(i : ℕ) - 1, by omega⟩), Finset.mem_univ _, ?_⟩
      dsimp only
      have hc : (⟨(j : ℕ), by omega⟩ : Fin (n + 2))
          ≤ (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]; omega
      rw [if_pos hc]
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, and_true]
      omega
    · refine ⟨(⟨(j : ℕ) - 1, by omega⟩, ⟨(i : ℕ), by omega⟩), Finset.mem_univ _, ?_⟩
      dsimp only
      have hc : ¬ (⟨(j : ℕ) - 1, by omega⟩ : Fin (n + 2))
          ≤ (⟨(i : ℕ), by omega⟩ : Fin (n + 1)).castSucc := by
        simp only [not_le, Fin.lt_def, Fin.val_castSucc]; omega
      rw [if_neg hc]
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, true_and]
      omega
  · intro a _
    split_ifs with h
    · -- v-case: (i,j) = (i'.succ, k.castSucc); i = k'.succ so sign flips.
      rw [face_prismSimplex_side_v H σ h, Fin.val_succ, Fin.val_castSucc, pow_succ,
        smul_smul, smul_smul, ← neg_smul]
      congr 1
      ring
    · rw [not_le] at h
      rw [face_prismSimplex_side_w H σ h, Fin.val_succ, Fin.val_castSucc, pow_succ,
        smul_smul, smul_smul, ← neg_smul]
      congr 1
      ring

/-! ## §6. The signed chain-homotopy identity `∂P + P∂ = g_# - f_#` -/

/-- **The signed chain-homotopy identity on a basis simplex**: `∂P + P∂ = g_# - f_#` at `single σ 1`.
The boundary `∂(prismBasisInt σ)` splits into diagonal faces (telescoping to `g_# - f_#`) and side
faces (which equal `-prismOpInt(∂σ)`), so `∂P + P∂ = g_# - f_#`. -/
theorem prism_chainHomotopyInt_single {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary Y (n + 1) (prismOpInt H (n + 1) (Finsupp.single σ 1))
        + prismOpInt H n (chainBoundary X n (Finsupp.single σ 1))
      = endMapInt H 1 (n + 1) (Finsupp.single σ 1) - endMapInt H 0 (n + 1) (Finsupp.single σ 1) := by
  rw [prismOpInt_single, one_smul, endMapInt_single, endMapInt_single,
    chainBoundary_prismBasisInt, prismOpInt_chainBoundary, prism_boundary_diag_sideInt,
    prism_prismOpInt_eq_sideInt]
  rw [add_assoc, neg_add_cancel, add_zero]
  exact prism_diagonal_telescopeInt H σ

/-- **The integral prism operator is a signed chain homotopy** witnessing `f_# ≃ g_#`: for any chain
`c`, `∂(Pc) + P(∂c) = g_#(c) - f_#(c)` over ℤ. Extends `prism_chainHomotopyInt_single` off the basis
by linearity. The engine of homotopy invariance of singular integral homology. -/
theorem prism_chainHomotopyInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) {n : ℕ}
    (c : SingularChainInt X (n + 1)) :
    chainBoundary Y (n + 1) (prismOpInt H (n + 1) c) + prismOpInt H n (chainBoundary X n c)
      = endMapInt H 1 (n + 1) c - endMapInt H 0 (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_add_add_comm, h₁, h₂, add_sub_add_comm]
  | single σ a =>
      have hsa : Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsa]
      simp only [map_smul, ← smul_add, ← smul_sub]
      exact congrArg (a • ·) (prism_chainHomotopyInt_single H σ)

/-! ## §7. The endpoint maps on the identity / constant slices -/

open SKEFTHawking.SingularHomotopyInvariance (constSimplex face_constSimplex slice)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_id)

/-- On the `slice H r = id` endpoint, `endMapInt H r = id`: each `endSimplex H r σ = mapSimplex id σ
= σ`. -/
theorem endMapInt_eq_self_of_slice_id {X : TopCat} (H : C(↑X × unitInterval, ↑X)) (r : unitInterval)
    (hr : slice H r = ContinuousMap.id ↑X) (n : ℕ) (c : SingularChainInt X n) :
    endMapInt H r n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]
  | single σ a =>
      rw [endMapInt_single, SingularHomotopyInvariance.endSimplex_eq_mapSimplex, hr, mapSimplex_id]

/-- On the `slice H r = const_b` endpoint, `endMapInt H r z = (Σ z) • single (constSimplex b n)` —
the constant chain at `b`. -/
theorem endMapInt_const_of_slice_const {X : TopCat} (H : C(↑X × unitInterval, ↑X)) (r : unitInterval)
    (b : ↑X) (hr : slice H r = ContinuousMap.const ↑X b) (n : ℕ) (c : SingularChainInt X n) :
    endMapInt H r n c = (c.sum fun _ a => a) • Finsupp.single (constSimplex b n) 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), add_smul]
  | single σ a =>
      rw [endMapInt_single, SingularHomotopyInvariance.endSimplex_eq_mapSimplex, hr,
        SingularHomotopyInvariance.mapSimplex_const, Finsupp.sum_single_index rfl,
        Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §8. The integral constant chain is a boundary (parity) -/

/-- The signed boundary of a single constant `(n+2)`-simplex: `∂(single (constSimplex b (n+2)) 1)
= (∑ⱼ (-1)ʲ) • single (constSimplex b (n+1)) 1`, since every face of a constant simplex is the
constant simplex one dimension down. -/
theorem chainBoundary_single_constSimplexInt {X : TopCat} (b : ↑X) (n : ℕ) :
    chainBoundary X n (Finsupp.single (constSimplex b (n + 1)) 1)
      = (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (constSimplex b n) 1 := by
  rw [chainBoundary_single, boundaryBasis, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show SingularCohomologyInt.face j (constSimplex b (n + 1)) = constSimplex b n from
    face_constSimplex b n j]

/-- The alternating sign sum over `Fin (k)` is `if Even k then 0 else 1`. -/
theorem alt_sum_fin (k : ℕ) : (∑ j : Fin k, (-1 : ℤ) ^ (j : ℕ)) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range, neg_one_geom_sum]

/-- **The integral constant chain `m · single (constSimplex b (n+1))` (in degree `n+1`) is a
boundary** when it is a cycle (`m · (∑ⱼ (-1)ʲ over Fin(n+2)) = 0`). If `n` is even the alternating
`(n+3)`-face-sum is `1` so the constant chain is directly `∂(constSimplex b (n+2))`; if `n` is odd
the `(n+2)`-cycle-sum is `1` so the cycle condition forces `m = 0`. Integral analogue of
`SingularHomotopyInvariance.single_constSimplex_mem_boundaries`. -/
theorem single_constSimplex_mem_boundariesInt {X : TopCat} (b : ↑X) (n : ℕ) (m : ℤ)
    (hcyc : m * (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ)) = 0) :
    Finsupp.single (constSimplex b (n + 1)) m ∈ boundaries X (n + 1) := by
  by_cases hpar : Even n
  · -- n even ⟺ Even (n+3) false ⟹ ∑_{Fin(n+3)} = 1 ⟹ single(constSimplex) = ∂(constSimplex(n+2)).
    have hne3 : ¬ Even (n + 3) := by
      rw [Nat.even_add]; simp only [show ¬ Even 3 by decide, iff_false, not_not]; exact hpar
    have hsum : (∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ)) = 1 := by rw [alt_sum_fin, if_neg hne3]
    have hb : Finsupp.single (constSimplex b (n + 1)) (1 : ℤ) ∈ boundaries X (n + 1) := by
      refine ⟨Finsupp.single (constSimplex b (n + 2)) 1, ?_⟩
      rw [chainBoundary_single_constSimplexInt, hsum, one_smul]
    rw [show Finsupp.single (constSimplex b (n + 1)) m
        = m • Finsupp.single (constSimplex b (n + 1)) (1 : ℤ) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    exact (boundaries X (n + 1)).smul_mem m hb
  · -- n odd ⟺ Even (n+2) false ⟹ ∑_{Fin(n+2)} = 1 ⟹ hcyc forces m = 0.
    have hne2 : ¬ Even (n + 2) := by
      rw [Nat.even_add]; simp only [show Even 2 by decide, iff_true]; exact hpar
    have hsum : (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ)) = 1 := by rw [alt_sum_fin, if_neg hne2]
    rw [hsum, mul_one] at hcyc
    rw [hcyc, Finsupp.single_zero]
    exact (boundaries X (n + 1)).zero_mem

/-- **The integral endpoint map `endMapInt H r` is a chain map**: `∂ ∘ endMapInt = endMapInt ∘ ∂`.
Uses the coefficient-free `face_endSimplex` (endpoint pushforward commutes with faces). -/
theorem chainBoundary_endMapInt {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (r : unitInterval) (c : SingularChainInt X (n + 1)) :
    chainBoundary Y n (endMapInt H r (n + 1) c) = endMapInt H r n (chainBoundary X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single σ a =>
      rw [endMapInt_single, chainBoundary_single_smul, chainBoundary_single_smul, boundaryBasis,
        boundaryBasis, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, endMapInt_single,
        show SingularCohomologyInt.face i (endSimplex H r σ)
          = endSimplex H r (SingularCohomologyInt.face i σ) from
            SingularPrism.face_endSimplex H r σ i,
        Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §9. Acyclicity of contractible spaces (integral) -/

/-- **Integral acyclicity from a contraction**: if `U` carries a contraction `H` (`H(·, 0) = id`,
`H(·, 1) = const_b`), then every cycle in degree `n + 1 ≥ 1` is a boundary — `Hₙ₊₁(U; ℤ) = 0`.
Contractible spaces are acyclic in positive degrees.

From the signed prism identity `∂(P z) = end₁(z) - end₀(z) = const_b#(z) - z` (using `∂z = 0`):
`z = const_b#(z) - ∂(P z)`. The first summand is the constant chain `(Σz)·c_b^{n+1}` (a boundary by
`single_constSimplex_mem_boundariesInt`; its cycle condition comes from `end₁` being a chain map),
the second is a boundary by definition. -/
theorem cycle_mem_boundaries_of_contractionInt {U : TopCat} {n : ℕ}
    (H : C(↑U × unitInterval, ↑U)) (b : ↑U) (h0 : slice H 0 = ContinuousMap.id ↑U)
    (h1 : slice H 1 = ContinuousMap.const ↑U b) (z : SingularChainInt U (n + 1))
    (hz : chainBoundary U n z = 0) : z ∈ boundaries U (n + 1) := by
  -- The chain-homotopy identity at z: ∂(Pz) + P(∂z) = end₁ z - end₀ z.
  have hkey := prism_chainHomotopyInt H z
  rw [hz, map_zero, add_zero, endMapInt_eq_self_of_slice_id H 0 h0,
    endMapInt_const_of_slice_const H 1 b h1] at hkey
  -- The cycle condition: (Σz)·(∑_{Fin(n+2)}(-1)ʲ) = 0, from ∂z = 0 ⟹ ∂(end₁ z) = 0.
  have hcyc : (z.sum fun _ a => a) * (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ)) = 0 := by
    have hend1 : chainBoundary U n ((z.sum fun _ a => a) • Finsupp.single (constSimplex b (n + 1)) 1)
        = 0 := by
      rw [← endMapInt_const_of_slice_const H 1 b h1, chainBoundary_endMapInt, hz, map_zero]
    rw [map_smul, chainBoundary_single_constSimplexInt, smul_smul] at hend1
    have := Finsupp.single_eq_zero.mp (by
      rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at hend1)
    exact this
  have hconst : ((z.sum fun _ a => a) • Finsupp.single (constSimplex b (n + 1)) 1)
      ∈ boundaries U (n + 1) := by
    rw [show ((z.sum fun _ a => a) • Finsupp.single (constSimplex b (n + 1)) 1)
        = Finsupp.single (constSimplex b (n + 1)) (z.sum fun _ a => a) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    exact single_constSimplex_mem_boundariesInt b n (z.sum fun _ a => a) hcyc
  -- z = end₁ z - ∂(Pz): the constant term is a boundary, ∂(Pz) is a boundary.
  have hz_eq : z = ((z.sum fun _ a => a) • Finsupp.single (constSimplex b (n + 1)) 1)
      - chainBoundary U (n + 1) (prismOpInt H (n + 1) z) := by
    rw [hkey]; abel
  rw [hz_eq]
  exact (boundaries U (n + 1)).sub_mem hconst ⟨prismOpInt H (n + 1) z, rfl⟩

end SKEFTHawking.SingularHomotopyInvarianceInt
