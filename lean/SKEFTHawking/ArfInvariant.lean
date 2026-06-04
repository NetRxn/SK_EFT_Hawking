/-
Phase 5q.B Wave B2 (seed): the Arf invariant of a quadratic refinement over F₂

This module begins the char-2 quadratic-form / Arf-invariant infrastructure that the
spectra-free Rokhlin route needs (Guillou–Marin / Freedman–Kirby: the signature mod 16
of a closed spin 4-manifold is controlled by the Arf invariant of the quadratic
refinement on the mod-2 homology of a characteristic surface). It is also the
foundation of the finite Milgram Gauss sum used in Wave B1.

Mathlib has general `QuadraticForm` but no char-2 quadratic-refinement / Arf theory.
We develop it from scratch. This seed treats the genus-1 case (the F₂-plane, whose
underlying set is exactly the four vectors `0, e₀, e₁, e₀+e₁`) and proves the classical
**democratic characterisation**: a quadratic form refining the symplectic form takes the
value `Arf q` on a strict majority of vectors — three zeros when `Arf q = 0`, one zero
when `Arf q = 1` (the genus-1 instance of `#{q = 0} = 2^{2g-1} + 2^{g-1}(-1)^{Arf}`).
Higher genus is a later increment.

Proof method: the refinement axiom determines `q` from `(q e₀, q e₁)`, reducing every
claim to a kernel-pure `decide` over `ZMod 2 × ZMod 2` (no `native_decide`, no decide over
a function space).

See docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md (Wave B2).
-/

import Mathlib

namespace SKEFTHawking.Arf

open Finset

/-- The F₂-plane, the genus-1 symplectic space (underlying set `{0, e₀, e₁, e₀+e₁}`). -/
abbrev V := Fin 2 → ZMod 2

/-- The standard symplectic (alternating bilinear) form on the F₂-plane:
    `B x y = x₀y₁ + x₁y₀`. -/
abbrev B (x y : V) : ZMod 2 := x 0 * y 1 + x 1 * y 0

/-- `q` is a quadratic refinement of `B`: `q 0 = 0` and
    `q (x + y) = q x + q y + B x y` (the defining property of a quadratic form whose
    associated bilinear form is `B`, in characteristic 2). -/
abbrev IsRefinement (q : V → ZMod 2) : Prop :=
  q 0 = 0 ∧ ∀ x y : V, q (x + y) = q x + q y + B x y

/-- First symplectic basis vector `e₀ = (1,0)`. -/
abbrev e0 : V := ![1, 0]
/-- Second symplectic basis vector `e₁ = (0,1)`. -/
abbrev e1 : V := ![0, 1]

/-- `e₀, e₁` are a symplectic pair: `B e₀ e₁ = 1`. -/
theorem B_e0_e1 : B e0 e1 = 1 := by decide

/-- The Arf invariant (genus 1): `Arf q = q e₀ · q e₁`. -/
abbrev arf (q : V → ZMod 2) : ZMod 2 := q e0 * q e1

/-- Number of zeros of `q` among the four vectors of the F₂-plane `{0, e₀, e₁, e₀+e₁}`
    (= `|{x ∈ V : q x = 0}|`, since these four are exactly `V`). -/
abbrev zeroCount (q : V → ZMod 2) : ℕ :=
  (if q 0 = 0 then 1 else 0) + (if q e0 = 0 then 1 else 0)
    + (if q e1 = 0 then 1 else 0) + (if q (e0 + e1) = 0 then 1 else 0)

/-- A refinement is determined on `e₀+e₁` by its values on the basis:
    `q (e₀+e₁) = q e₀ + q e₁ + 1`. -/
theorem refinement_on_sum (q : V → ZMod 2) (hq : IsRefinement q) :
    q (e0 + e1) = q e0 + q e1 + 1 := by
  have h := hq.2 e0 e1; rwa [B_e0_e1] at h

/-- **Democratic characterisation of the Arf invariant (genus 1).**
    For any quadratic refinement of the symplectic form, the value `Arf q` is the
    majority value of `q`: three zeros when `Arf q = 0`, one zero when `Arf q = 1`. -/
theorem arf_democratic (q : V → ZMod 2) (hq : IsRefinement q) :
    (arf q = 0 → zeroCount q = 3) ∧ (arf q = 1 → zeroCount q = 1) := by
  have h0 := hq.1
  have hsum := refinement_on_sum q hq
  unfold arf zeroCount
  rw [h0, hsum]
  generalize q e0 = a
  generalize q e1 = b
  revert a b
  decide

/-- The Arf invariant is genuinely non-trivial: both states are realised by honest
    refinements (`q x = x₀x₁` gives `Arf = 0`; `q x = x₀+x₁+x₀x₁` gives `Arf = 1`). -/
theorem arf_surjective :
    (∃ q : V → ZMod 2, IsRefinement q ∧ arf q = 0) ∧
    (∃ q : V → ZMod 2, IsRefinement q ∧ arf q = 1) := by
  refine ⟨⟨fun x => x 0 * x 1, ?_, ?_⟩, ⟨fun x => x 0 + x 1 + x 0 * x 1, ?_, ?_⟩⟩ <;> decide

/-- Enumeration of the F₂-plane: a sum over `V` is the sum over its four vectors
    `0, e₀, e₁, e₀+e₁`. (Via `finTwoArrowEquiv`, avoiding any `decide` over the function space.) -/
theorem sum_univ_V {M : Type*} [AddCommMonoid M] (f : V → M) :
    ∑ x, f x = f 0 + f e0 + f e1 + f (e0 + e1) := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (ZMod 2)).symm f, Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hne : (0 : ZMod 2) ≠ 1 := by decide
  simp only [huniv, Finset.sum_pair hne]
  have h00 : (![(0 : ZMod 2), 0] : V) = 0 := by decide
  have h01 : (![(0 : ZMod 2), 1] : V) = e1 := by decide
  have h10 : (![(1 : ZMod 2), 0] : V) = e0 := by decide
  have h11 : (![(1 : ZMod 2), 1] : V) = e0 + e1 := by decide
  rw [h00, h01, h10, h11]
  abel

/-! ## The Arf Gauss sum (genus-1 seed of the Milgram formula)

The integer character sum `∑_{x ∈ V} (-1)^{q x}` equals `√|V| · (-1)^{Arf q} = 2·(-1)^{Arf q}`.
This is the genus-1 instance of the Gauss-sum identity that powers the Milgram signature-mod-8
formula consumed by Wave B1 (there the codomain is ℤ/8 and the sum is `√|disc|·e^{2πiσ/8}`). -/

/-- The ±1 character of `ZMod 2`: `0 ↦ 1`, `1 ↦ -1`. -/
abbrev signZ (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- The integer Arf Gauss sum `∑_{x ∈ V} (-1)^{q x}` over the four vectors of the F₂-plane. -/
abbrev gaussSumZ (q : V → ZMod 2) : ℤ :=
  signZ (q 0) + signZ (q e0) + signZ (q e1) + signZ (q (e0 + e1))

/-- **Genus-1 Arf Gauss sum.** For any quadratic refinement,
    `∑_{x ∈ V} (-1)^{q x} = 2·(-1)^{Arf q}` (the `√|V| = 2` Gauss-sum identity). -/
theorem gaussSum_arf (q : V → ZMod 2) (hq : IsRefinement q) :
    gaussSumZ q = 2 * signZ (arf q) := by
  have h0 := hq.1
  have hsum := refinement_on_sum q hq
  unfold gaussSumZ arf signZ
  rw [h0, hsum]
  generalize q e0 = a
  generalize q e1 = b
  revert a b
  decide

/-! ## Multiplicativity of the Gauss sum over orthogonal sums

The engine that lifts the genus-1 identity to genus `g`: the ±1 Gauss sum of an F₂-valued
function over a finite type is multiplicative under the orthogonal (additive) combination
of two such functions, because `signZ` is a multiplicative character of `(ZMod 2, +)`.
For a quadratic refinement that splits as `q(x,y) = q₁ x + q₂ y` (an orthogonal direct sum,
where the cross bilinear term vanishes), this gives `G(q) = G(q₁)·G(q₂)`, so a genus-`g`
standard form has `G = 2^g·(-1)^{Arf}`. -/

/-- `signZ` is a multiplicative character of `(ZMod 2, +)`: `(-1)^{a+b} = (-1)^a (-1)^b`. -/
theorem signZ_add (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  revert a b; decide

/-- `signZ 0 = 1`. -/
theorem signZ_zero : signZ (0 : ZMod 2) = 1 := by decide

/-- The character extends to finite sums: `(-1)^{∑ fᵢ} = ∏ (-1)^{fᵢ}`. -/
theorem signZ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    signZ (∑ i ∈ s, f i) = ∏ i ∈ s, signZ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [signZ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ_add, ih]

/-- The generic ±1 Gauss sum of an F₂-valued function over a finite type. -/
def gaussSum {ι : Type*} [Fintype ι] (f : ι → ZMod 2) : ℤ := ∑ x, signZ (f x)

/-- **Gauss-sum multiplicativity over an orthogonal sum.** If the refinement on `ι × κ`
    splits additively as `(x,y) ↦ f x + g y`, its Gauss sum factorises:
    `G = G(f)·G(g)`. -/
theorem gaussSum_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ZMod 2) (g : κ → ZMod 2) :
    gaussSum (fun p : ι × κ => f p.1 + g p.2) = gaussSum f * gaussSum g := by
  unfold gaussSum
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => signZ_add _ _

/-- **Genus-`g` Gauss-sum factorisation.** If the refinement on `∀ i, V i` is the orthogonal
    sum `x ↦ ∑ i, qᵢ (x i)`, its Gauss sum is the product of the factor Gauss sums. Combined
    with the genus-1 value `gaussSum (per plane) = 2·(-1)^{Arf}`, a block-diagonal genus-`g`
    form has Gauss sum `2^g·(-1)^{∑ Arf}`. -/
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] (q : ∀ i, V i → ZMod 2) :
    gaussSum (fun x : (∀ i, V i) => ∑ i, q i (x i)) = ∏ i, gaussSum (q i) := by
  unfold gaussSum
  simp only [signZ_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The generic Gauss sum over the F₂-plane equals the explicit four-term sum. -/
theorem gaussSum_eq_gaussSumZ (q : V → ZMod 2) : gaussSum q = gaussSumZ q :=
  sum_univ_V (fun x => signZ (q x))

/-- Genus-1, unified form: `gaussSum q = 2·(-1)^{Arf q}` for the generic Gauss sum. -/
theorem gaussSum_arf' (q : V → ZMod 2) (hq : IsRefinement q) :
    gaussSum q = 2 * signZ (arf q) := by
  rw [gaussSum_eq_gaussSumZ]; exact gaussSum_arf q hq

/-- **Genus-`g` Arf Gauss sum.** For a block-diagonal refinement `x ↦ ∑ᵢ qᵢ(xᵢ)` on `Fin g → V`
    built from genus-1 refinements `qᵢ`, the Gauss sum is `2^g·(-1)^{∑ᵢ Arf qᵢ}`. This is the
    finite Milgram identity at the level of `𝔽₂`/Arf — the seed for the `σ mod 8` (Brown `ZMod 4`)
    refinement in Wave B1. -/
theorem gaussSum_genus_g {g : ℕ} (qfun : Fin g → (V → ZMod 2))
    (hq : ∀ i, IsRefinement (qfun i)) :
    gaussSum (fun x : Fin g → V => ∑ i, qfun i (x i)) = 2 ^ g * signZ (∑ i, arf (qfun i)) := by
  rw [gaussSum_pi, Finset.prod_congr rfl (fun i _ => gaussSum_arf' (qfun i) (hq i)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← signZ_sum]

end SKEFTHawking.Arf
