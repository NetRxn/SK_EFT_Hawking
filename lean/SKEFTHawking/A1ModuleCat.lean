/-
Phase 5q.T Wave T3 (a)+(b): the resolution as a complex of PROJECTIVE A(1)-MODULES

`A1Resolution.lean` holds the differentials as F₂-matrices and proves they commute with the
A(1)-action (`d1_a1_linear … d5_a1_linear`). That is a statement *about* matrices. Mathlib's
`Ext` consumes morphisms in `ModuleCat`, so this module carries the matrices across into
genuine module theory:

  * `A1op := A1subᵐᵒᵖ` — **which side, and why.** `A1Resolution` §4 establishes that the
    differentials are given by *left* multiplication, hence commute with the *right* action:
    `Pₙ` is a free **right** A(1)-module. `ModuleCat R` is *left* modules, and `Rmat` is an
    algebra **anti**-homomorphism (`R_c ∘ R_b = R_{bc}`), so `blockR` is a left action of
    `A1subᵐᵒᵖ`, not of `A1sub`. Right A(1)-modules = left A(1)ᵒᵖ-modules; this is the same
    convention `A1Resolution` §4 already documents, now made structural rather than prose.
  * `coeffL_mul_e` — `Rmat b` implements right multiplication by `e b` in Milnor
    coordinates. The base case is `decide`; the general case is span induction over `A1Span`.
  * `coordEquiv r : (Fin r → A1op) ≃ₗ[F2] (Fin (r*8) → F2)` — the coordinate system, and
    `coordEquiv_smul`, the **bridge**: it intertwines the module action with `blockR`. This is
    what makes the F₂-expanded matrices morphisms of A(1)-modules rather than of bare vector
    spaces. Index convention `k ↦ (k / 8, k % 8)` matches `A1Resolution`'s encoding exactly —
    `finProdFinEquiv (i, j) = j + 8*i`, checked by `rfl` in `finProdFinEquiv_val`.
  * `span_e_top` + `smul_of_basis` — an F₂-linear map commuting with each of the eight basis
    elements is A(1)ᵒᵖ-linear. This is what lets the existing eight-case `decide` linearity
    theorems discharge linearity over the whole algebra.
  * `ofMatrix` — **a certified F₂-matrix as a genuine morphism of free A(1)-modules**, given
    only the commutation hypothesis the existing theorems already supply.
  * `D1 … D5` — the five differentials, and `D_chain_complex`, `dₙ ∘ dₙ₊₁ = 0` as an identity
    of A(1)-module morphisms.
  * `P r` (`ModuleCat A1op`) and `Projective (P r)` — Wave T3 sub-task (b). Free ⟹ projective
    is immediate once the module is the honest `Fin r → A1op`.
  * `coordEquiv_finrank : dim_{F₂} A(1)^r = 8r` — pins `coordEquiv` to the right object.

Everything here is kernel-pure: `{propext, Classical.choice, Quot.sound}`.

**What remains for the rest of Wave T3** (recorded here so the next agent does not re-derive
it). `ProjectiveResolution` requires an ℕ-indexed complex exact in *every* degree, and the
A(1)-resolution of F₂ is genuinely infinite (the Ext ranks 1,2,2,2,3,4,4,4,5,6,… grow). The
six explicit terms therefore cannot be handed to `isoExt` directly. The route is to splice:
take `K := ker D5`, take any `Q : ProjectiveResolution K` from `EnoughProjectives`, and define
the complex by structural match — `X 0…5 := P 1,2,2,2,3,4`, `X (n+6) := Q.complex.X n`, with
`d 5 := Q.π.f 0 ≫ (K ↪ P 4)`. Exactness at degree 5 is epi-ness of `Q.π.f 0`, at degree 6 is
`Q`'s `exact₀` (using that `K ↪ P 4` is mono), and above that it is `Q`'s own; degrees 1–4 and
the augmentation come from `A1Exactness.resolution_is_exact`. Since `Extⁿ` sees only `dₙ` and
`dₙ₊₁`, that yields `Ext⁰ … Ext⁴` honestly; `Ext⁵` additionally needs an explicit `d₆`.

Roadmap: docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md (Wave T3).
-/

import SKEFTHawking.A1Algebra
import SKEFTHawking.A1Resolution

namespace SKEFTHawking.A1

open Matrix

/-- A(1) acting on the right = A(1)ᵒᵖ acting on the left. -/
abbrev A1op := (A1sub)ᵐᵒᵖ

/-- Basis case: right multiplication by `e b` acts on Milnor coordinates by `Rmat b`. -/
theorem Lmat_mul_col0 : ∀ a b k : Idx,
    (Lmat a * Lmat b) k 0 = ∑ j, Rmat b k j * Lmat a j 0 := by decide

/-- **`Rmat b` implements right multiplication by `e b` in Milnor coordinates.** -/
theorem coeffL_mul_e : ∀ M ∈ A1Span, ∀ b : Idx,
    coeffL (M * Lmat b) = (Rmat b).mulVec (coeffL M) := by
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro b; funext k
      simpa [coeffL, Matrix.mulVec, dotProduct] using Lmat_mul_col0 a b k
  | zero => intro b; simp
  | add x y _ _ hx hy =>
      intro b; rw [add_mul, map_add, map_add, hx, hy, Matrix.mulVec_add]
  | smul c x _ hx =>
      intro b; rw [smul_mul_assoc, map_smul, map_smul, hx, Matrix.mulVec_smul]

/-! ## The free module in Milnor coordinates -/

/-- `A(1)^r` in Milnor coordinates: index `k` means Milnor basis element `k % 8` of block
    `k / 8`, matching the F₂-expanded encoding of `A1Resolution`'s differentials. -/
noncomputable def coordEquiv (r : ℕ) : (Fin r → A1op) ≃ₗ[F2] (Fin (r * 8) → F2) :=
  (LinearEquiv.piCongrRight fun _ : Fin r =>
      (MulOpposite.opLinearEquiv F2 (M := A1sub)).symm.trans A1equiv).trans
    (((LinearEquiv.curry F2 F2 (Fin r) Idx).symm).trans
      (LinearEquiv.funCongrLeft F2 F2 finProdFinEquiv.symm))

/-- `dim_{F₂} A(1)^r = 8r` — `coordEquiv` really is a coordinate system for the free module. -/
theorem coordEquiv_finrank (r : ℕ) : Module.finrank F2 (Fin r → A1op) = 8 * r := by
  rw [(coordEquiv r).finrank_eq, Module.finrank_pi F2]
  simp [Nat.mul_comm]

/-- The rank-`r` free module over A(1) as an object of `ModuleCat`. -/
def P (r : ℕ) : ModuleCat A1op := ModuleCat.of A1op (Fin r → A1op)

instance (r : ℕ) : CategoryTheory.Projective (P r) := by
  dsimp [P]
  infer_instance

theorem coordEquiv_apply (r : ℕ) (v : Fin r → A1op) (i : Fin r) (j : Idx) :
    coordEquiv r v (finProdFinEquiv (i, j)) = (v i).unop.1 j 0 := by
  simp [coordEquiv, A1equiv, coeffL]

theorem finProdFinEquiv_val (r : ℕ) (i : Fin r) (j : Idx) :
    (finProdFinEquiv (i, j)).val = j.val + 8 * i.val := rfl

theorem fpfe_div (r : ℕ) (i : Fin r) (j : Idx) :
    (finProdFinEquiv (i, j)).val / 8 = i.val := by
  have := j.isLt; rw [finProdFinEquiv_val]; omega

theorem fpfe_mod (r : ℕ) (i : Fin r) (j : Idx) :
    (finProdFinEquiv (i, j)).val % 8 = j.val := by
  have := j.isLt; rw [finProdFinEquiv_val]; omega

/-- `blockR` in block coordinates: `Rmat b` on the diagonal blocks, zero off them. -/
theorem blockR_apply (r : ℕ) (b : Idx) (i i' : Fin r) (j j' : Idx) :
    blockR (r * 8) b (finProdFinEquiv (i, j)) (finProdFinEquiv (i', j'))
      = if i = i' then Rmat b j j' else 0 := by
  have hj := j.isLt; have hj' := j'.isLt
  by_cases h : i = i'
  · subst h
    simp only [blockR, Matrix.of_apply, finProdFinEquiv_val]
    rw [if_pos (by omega)]
    congr 1 <;> · apply Fin.ext; simp
  · have hv : i.val ≠ i'.val := fun hh => h (Fin.ext hh)
    simp only [blockR, Matrix.of_apply, finProdFinEquiv_val]
    rw [if_neg (by omega), if_neg h]

/-- **The coordinate system intertwines the A(1)ᵒᵖ-action with `blockR`.**

    This is the bridge that makes `A1Resolution`'s F₂-expanded matrices morphisms of genuine
    A(1)-modules: `blockR` is exactly the matrix of the module action in these coordinates. -/
theorem coordEquiv_smul (r : ℕ) (b : Idx) (v : Fin r → A1op) :
    coordEquiv r (MulOpposite.op (e b) • v) = (blockR (r * 8) b).mulVec (coordEquiv r v) := by
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hL : coordEquiv r (MulOpposite.op (e b) • v) (finProdFinEquiv (i, j))
      = ((v i).unop.1 * Lmat b) j 0 := by
    rw [coordEquiv_apply]; rfl
  rw [hL]
  have hmem : ((v i).unop : Matrix Idx Idx F2) ∈ A1Span := (v i).unop.2
  have hkey := congrFun (coeffL_mul_e _ hmem b) j
  simp only [coeffL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct] at hkey
  rw [hkey]
  rw [Matrix.mulVec, dotProduct, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun j' _ => by rw [blockR_apply, if_pos rfl, coordEquiv_apply]
  · exact fun i' _ hne => Finset.sum_eq_zero fun j' _ => by
      rw [blockR_apply, if_neg (Ne.symm hne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The Milnor basis spans A(1) over F₂ — so an F₂-linear map that commutes with each
    `e b` commutes with the whole algebra. -/
theorem span_e_top : Submodule.span F2 (Set.range e) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = ∑ a, (coeffL x.1 a) • e a := by
    apply Subtype.ext
    have h := ofCoeff_coeffL x.1 x.2
    show (x : Matrix Idx Idx F2) = ((∑ a, (coeffL x.1 a) • e a : A1sub) : Matrix Idx Idx F2)
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa [ofCoeff, e] using h.symm
  rw [hx]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- An F₂-linear map between free A(1)-modules that commutes with right multiplication by
    every Milnor basis element is A(1)ᵒᵖ-linear. -/
theorem smul_of_basis {r s : ℕ} (f : (Fin r → A1op) →ₗ[F2] (Fin s → A1op))
    (hb : ∀ (b : Idx) (v), f (MulOpposite.op (e b) • v) = MulOpposite.op (e b) • f v)
    (x : A1op) (v : Fin r → A1op) : f (x • v) = x • f v := by
  have key : ∀ y ∈ Submodule.span F2 (Set.range e),
      f (MulOpposite.op y • v) = MulOpposite.op y • f v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨b, rfl⟩ := hz; exact hb b v
    | zero => simp
    | add z w _ _ hz hw => rw [MulOpposite.op_add, add_smul, add_smul, map_add, hz, hw]
    | smul c z _ hz => rw [MulOpposite.op_smul, smul_assoc, smul_assoc, map_smul, hz]
  simpa using key x.unop (by rw [span_e_top]; trivial)

/-! ## Differentials as genuine A(1)-linear maps -/

/-- An F₂-expanded matrix, read in Milnor coordinates, as an F₂-linear map of free modules. -/
noncomputable def ofMatrixF2 {r s : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2) :
    (Fin r → A1op) →ₗ[F2] (Fin s → A1op) :=
  (coordEquiv s).symm.toLinearMap.comp
    ((Matrix.mulVecLin M).comp (coordEquiv r).toLinearMap)

theorem ofMatrixF2_apply {r s : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2)
    (v : Fin r → A1op) :
    ofMatrixF2 M v = (coordEquiv s).symm (M.mulVec (coordEquiv r v)) := rfl

/-- A matrix that commutes with the A(1)-action is A(1)ᵒᵖ-linear in Milnor coordinates. -/
theorem ofMatrixF2_smul {r s : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2)
    (hM : ∀ b : Idx, M * blockR (r * 8) b = blockR (s * 8) b * M)
    (x : A1op) (v : Fin r → A1op) : ofMatrixF2 M (x • v) = x • ofMatrixF2 M v := by
  refine smul_of_basis _ (fun b w => ?_) x v
  rw [ofMatrixF2_apply, ofMatrixF2_apply, coordEquiv_smul, Matrix.mulVec_mulVec, hM b,
    ← Matrix.mulVec_mulVec]
  apply (coordEquiv s).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_smul, LinearEquiv.apply_symm_apply]

/-- **A certified F₂-matrix as a genuine morphism of free A(1)-modules.** -/
noncomputable def ofMatrix {r s : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2)
    (hM : ∀ b : Idx, M * blockR (r * 8) b = blockR (s * 8) b * M) :
    (Fin r → A1op) →ₗ[A1op] (Fin s → A1op) where
  toFun := ofMatrixF2 M
  map_add' := (ofMatrixF2 M).map_add
  map_smul' := ofMatrixF2_smul M hM

theorem ofMatrix_comp {r s t : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2)
    (N : Matrix (Fin (t * 8)) (Fin (s * 8)) F2) (hM) (hN) (v : Fin r → A1op) :
    ofMatrix N hN (ofMatrix M hM v) = (coordEquiv t).symm ((N * M).mulVec (coordEquiv r v)) := by
  show ofMatrixF2 N (ofMatrixF2 M v) = _
  rw [ofMatrixF2_apply, ofMatrixF2_apply, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec]

/-- `d₁ : P₁ → P₀` as an A(1)-module morphism. -/
noncomputable def D1 : (Fin 2 → A1op) →ₗ[A1op] (Fin 1 → A1op) :=
  ofMatrix d1 (fun b => by
    have h : blockR (1 * 8) b = Rmat b := blockR_eight b
    rw [d1_a1_linear b, h])

/-- `d₂ : P₂ → P₁` as an A(1)-module morphism. -/
noncomputable def D2 : (Fin 2 → A1op) →ₗ[A1op] (Fin 2 → A1op) := ofMatrix d2 d2_a1_linear

/-- `d₃ : P₃ → P₂` as an A(1)-module morphism. -/
noncomputable def D3 : (Fin 2 → A1op) →ₗ[A1op] (Fin 2 → A1op) := ofMatrix d3 d3_a1_linear

/-- `d₄ : P₄ → P₃` as an A(1)-module morphism. -/
noncomputable def D4 : (Fin 3 → A1op) →ₗ[A1op] (Fin 2 → A1op) := ofMatrix d4 d4_a1_linear

/-- `d₅ : P₅ → P₄` as an A(1)-module morphism. -/
noncomputable def D5 : (Fin 4 → A1op) →ₗ[A1op] (Fin 3 → A1op) := ofMatrix d5 d5_a1_linear

theorem comp_zero_of_mul_zero {r s t : ℕ} (M : Matrix (Fin (s * 8)) (Fin (r * 8)) F2)
    (N : Matrix (Fin (t * 8)) (Fin (s * 8)) F2) (hM) (hN) (h : N * M = 0) :
    (ofMatrix N hN).comp (ofMatrix M hM) = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, ofMatrix_comp, h]
  simp

/-- **`P•` is a complex of free A(1)-modules**: every consecutive composite is zero, as
    morphisms of A(1)-modules — not merely as F₂-matrix products. -/
theorem D_chain_complex :
    D1.comp D2 = 0 ∧ D2.comp D3 = 0 ∧ D3.comp D4 = 0 ∧ D4.comp D5 = 0 :=
  ⟨comp_zero_of_mul_zero _ _ _ _ d1_d2_zero, comp_zero_of_mul_zero _ _ _ _ d2_d3_zero,
   comp_zero_of_mul_zero _ _ _ _ d3_d4_zero, comp_zero_of_mul_zero _ _ _ _ d4_d5_zero⟩

end SKEFTHawking.A1
