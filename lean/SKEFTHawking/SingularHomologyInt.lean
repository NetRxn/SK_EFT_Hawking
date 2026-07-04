/-
# Phase 5q.H · E1 — singular ℤ homology and the integral Kronecker pairing

Substrate-G foundation brick (Option-A from-scratch). The **integral dual** of
`SKEFTHawking/SingularCohomologyInt.lean`: that file builds singular ℤ *cochains*
(`ℤ`-valued functions on singular simplices) with the *signed* coboundary
`δf = ∑ᵢ (-1)ⁱ f(∂ᵢ·)`. This module builds the *chains* — finitely-supported ℤ-combinations of
singular simplices — with the **signed boundary** `∂c = ∑ᵢ (-1)ⁱ ∂ᵢ c` (the genuine integral
alternating sum, which the mod-2 file `SingularHomologyMod2` could drop since `+1 = -1` in char 2),
and the **integral Kronecker pairing** `⟨f, c⟩ = ∑ a · f σ` connecting integral cochains to integral
chains.

The pairing is the adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩`, which makes it descend to a genuine ℤ-bilinear
evaluation `Hⁿ(X;ℤ) × Hₙ(X;ℤ) → ℤ` on integral (co)homology. This `kroneckerHInt` is the missing
ℤ ingredient the `[M]` datum needs: given a fundamental class `[M] : Homology X 4`, the disclosed
`SingularCohomologyInt.IntFundamentalClass.eval` datum is discharged by
`eval := (kroneckerHInt 4).flip [M]` — exactly mirroring the mod-2
`PoincareDualityConstruct.fundamentalFunctional = kroneckerH.flip fundamentalClass`.

Bricks (mirroring `SingularHomologyMod2`, over ℤ with the genuine sign):
  1. the singular integral chain group `Cₙ(X;ℤ)`, the signed boundary `∂` (`∂² = 0` — the exact
     dual of `SingularCohomologyInt.coboundary_comp_coboundary`, opposite-sign cancellation), and
     integral homology `Hₙ(X;ℤ) = ker ∂ₙ / im ∂ₙ₊₁`;
  2. the integral Kronecker pairing `⟨·,·⟩ : Cⁿ × Cₙ → ℤ` (bilinear), the adjunction
     `⟨δf, c⟩ = ⟨f, ∂c⟩`, and the descended `kroneckerHInt : Hⁿ(X;ℤ) × Hₙ(X;ℤ) → ℤ`;
  3. the eval-bridge `intFundamentalClassOfHomology [M] : IntFundamentalClass X` with
     `eval := (kroneckerHInt 4).flip [M]`, reducing the `intFundamentalClass_eval_datum` to the
     single geometric input `[M] : Homology X 4` (+ orientation).

NOT this dispatch: the orientation class / the geometric construction of `[M]` (the community-scale
residual core — no mod-2 shortcut exists over ℤ). All proofs kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularIntersectionFormInt

namespace SKEFTHawking.SingularHomologyInt

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt

/-- **Singular `n`-chains** of a space `X` with **ℤ** coefficients: finitely-supported ℤ
combinations of the singular `n`-simplices `(TopCat.toSSet.obj X).obj (op [n])`. A genuine
ℤ-module (a `Finsupp` into the commutative ring `ℤ`). The dual of `SingularCochainInt`. -/
abbrev SingularChainInt (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) →₀ ℤ

/-- The **signed** boundary of a *single basis simplex* `σ` (an `(n+1)`-simplex):
`∂σ = ∑ᵢ (-1)ⁱ ∂ᵢσ` over ℤ, as the ℤ-chain `∑ᵢ (-1)ⁱ • single (face i σ) 1`. The genuine
alternating sign (dropped in the mod-2 file) is present here, dual to `coboundary`. -/
noncomputable def boundaryBasis (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) : SingularChainInt X n :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (face i σ) 1

/-- The **singular integral boundary** `∂ : Cₙ₊₁ →ₗ[ℤ] Cₙ`, the ℤ-linear extension of the signed
`σ ↦ ∑ᵢ (-1)ⁱ ∂ᵢσ` off the basis simplices (`Finsupp.linearCombination`). -/
noncomputable def chainBoundary (X : TopCat) (n : ℕ) :
    SingularChainInt X (n + 1) →ₗ[ℤ] SingularChainInt X n :=
  Finsupp.linearCombination ℤ (boundaryBasis X n)

/-- The boundary on a basis simplex: `∂(single σ 1) = ∑ᵢ (-1)ⁱ • single (∂ᵢσ) 1`. -/
theorem chainBoundary_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary X n (Finsupp.single σ 1) = boundaryBasis X n σ := by
  rw [chainBoundary, Finsupp.linearCombination_single, one_smul]

/-- The boundary on a scaled basis simplex: `∂(single σ a) = a • ∂σ`. -/
theorem chainBoundary_single_smul (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (a : ℤ) :
    chainBoundary X n (Finsupp.single σ a) = a • boundaryBasis X n σ := by
  rw [chainBoundary, Finsupp.linearCombination_single]

/-- The boundary applied to a *single basis simplex* `σ` (an `(n+2)`-simplex), twice: the signed
double sum `∑ᵢ∑ⱼ (-1)ⁱ (-1)ʲ • single (∂ⱼ∂ᵢσ) 1`, the head of the `∂² = 0` cancellation. -/
theorem chainBoundary_chainBoundary_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1 + 1)))) :
    chainBoundary X n (chainBoundary X (n + 1) (Finsupp.single σ 1))
      = ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
          ((-1 : ℤ) ^ (i : ℕ)) • (((-1 : ℤ) ^ (j : ℕ)) •
            Finsupp.single (face j (face i σ)) (1 : ℤ)) := by
  rw [chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, chainBoundary_single, boundaryBasis, Finset.smul_sum]

/-- **`∂² = 0` on a basis simplex.** The exact dual of `coboundary_comp_coboundary`: by `face_face`
each summand is `(-1)ⁱ (-1)ʲ • single` of the composite coface `δ j ≫ δ i`, and the cosimplicial
identity `δ_comp_δ` pairs the index set `Fin(n+3) × Fin(n+2)` into a fixed-point-free involution whose
two members carry OPPOSITE signs and equal `single` values, so the sum vanishes over ℤ. -/
theorem chainBoundary_chainBoundary_single_eq_zero (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1 + 1)))) :
    chainBoundary X n (chainBoundary X (n + 1) (Finsupp.single σ 1)) = 0 := by
  rw [chainBoundary_chainBoundary_single]
  simp only [face_face]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    ((-1 : ℤ) ^ (p.1 : ℕ)) • (((-1 : ℤ) ^ (p.2 : ℕ)) •
      Finsupp.single ((TopCat.toSSet.obj X).map (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1).op σ)
        (1 : ℤ)))]
  refine Finset.sum_involution
    (fun p _ => if h : p.2.castSucc < p.1
      then (p.2.castSucc, p.1.pred ((Fin.zero_le _).trans_lt h).ne')
      else (p.2.succ, p.1.castPred (by
        simp only [not_lt] at h
        rw [Fin.ne_iff_vne, Fin.val_last]; have := p.2.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ -
    simp only
    by_cases h : j.castSucc < i
    · rw [dif_pos h]
      have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have hle : j ≤ i.pred hne := by
        rw [Fin.le_def, Fin.val_pred]; rw [Fin.lt_def, Fin.val_castSucc] at h; omega
      have heq : SimplexCategory.δ j ≫ SimplexCategory.δ i
          = SimplexCategory.δ (i.pred hne) ≫ SimplexCategory.δ j.castSucc := by
        rw [← SimplexCategory.δ_comp_δ hle, Fin.succ_pred]
      rw [heq]
      simp only [Fin.val_castSucc, Fin.val_pred, smul_smul]
      have hi : (i : ℕ) = (i : ℕ) - 1 + 1 := by
        rw [Fin.lt_def, Fin.val_castSucc] at h; omega
      rw [show ((-1 : ℤ) ^ (i : ℕ)) = -(-1) ^ ((i : ℕ) - 1) by
        conv_lhs => rw [hi]
        rw [pow_succ]; ring]
      rw [← add_smul]; convert zero_smul ℤ _; ring
    · rw [dif_neg h]
      simp only [not_lt] at h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        rw [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega
      have hle : i.castPred hne ≤ j := by
        rw [Fin.le_def, Fin.coe_castPred]; rw [Fin.le_def, Fin.val_castSucc] at h; omega
      have heq : SimplexCategory.δ j ≫ SimplexCategory.δ i
          = SimplexCategory.δ (i.castPred hne) ≫ SimplexCategory.δ j.succ := by
        rw [SimplexCategory.δ_comp_δ hle, Fin.castSucc_castPred]
      rw [heq]
      simp only [Fin.val_succ, Fin.coe_castPred, smul_smul]
      rw [pow_succ]
      rw [← add_smul]; convert zero_smul ℤ _; ring
  · rintro ⟨i, j⟩ - _
    by_cases h : j.castSucc < i
    · simp only [dif_pos h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_castSucc] at hc
      simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
    · simp only [dif_neg h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_succ] at hc
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at h; omega
  · intro a _; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ -
    by_cases h : j.castSucc < i
    · have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have h2 : ¬ (i.pred hne).castSucc < j.castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_pred]
        simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
      simp only [dif_pos h, dif_neg h2, Fin.succ_pred, Fin.castPred_castSucc]
    · have hle : i ≤ j.castSucc := not_lt.mp h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        simp only [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      have h2 : i < j.succ := by
        simp only [Fin.lt_def, Fin.val_succ]
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      simp only [dif_neg h, Fin.castSucc_castPred, Fin.pred_succ, dif_pos h2]

/-- **`∂² = 0`** — the singular integral chain complex condition, as the composite linear map
`Cₙ₊₂ → Cₙ` (the dual of `coboundary_comp_coboundary`). Reduced to the basis-simplex case by
`Finsupp.lhom_ext`. -/
theorem chainBoundary_comp_chainBoundary (X : TopCat) (n : ℕ) :
    (chainBoundary X n).comp (chainBoundary X (n + 1)) = 0 := by
  refine Finsupp.lhom_ext (fun σ b => ?_)
  have hsingle : (Finsupp.single σ b) = b • Finsupp.single σ 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, hsingle, map_smul, map_smul,
    chainBoundary_chainBoundary_single_eq_zero, smul_zero]

/-- `∂² = 0` in applied form: `∂(∂ c) = 0` for every chain `c`. -/
theorem boundary_comp_boundary (X : TopCat) (n : ℕ) (c : SingularChainInt X (n + 1 + 1)) :
    chainBoundary X n (chainBoundary X (n + 1) c) = 0 := by
  have := chainBoundary_comp_chainBoundary X n
  rw [← LinearMap.comp_apply, this, LinearMap.zero_apply]

/-! ## §2. Singular integral homology `Hₙ(X; ℤ) = ker ∂ₙ / im ∂ₙ₊₁` -/

/-- The **`n`-cycles** `ker(∂ₙ : Cₙ → Cₙ₋₁)` — in degree `0` there is no `∂₀`, so every `0`-chain is
a cycle (`⊤`). -/
noncomputable def cycles (X : TopCat) (n : ℕ) : Submodule ℤ (SingularChainInt X n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (chainBoundary X m)

/-- The **`n`-boundaries** (image of the outgoing `∂ₙ₊₁ : Cₙ₊₁ → Cₙ`). -/
noncomputable def boundaries (X : TopCat) (n : ℕ) : Submodule ℤ (SingularChainInt X n) :=
  LinearMap.range (chainBoundary X n)

/-- Boundaries are cycles, `im ∂ₙ₊₁ ≤ ker ∂ₙ` — the well-definedness of homology, from `∂² = 0`. -/
theorem boundaries_le_cycles (X : TopCat) (n : ℕ) : boundaries X n ≤ cycles X n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (chainBoundary X (m + 1)) ≤ LinearMap.ker (chainBoundary X m)
    rw [LinearMap.range_le_ker_iff]
    exact chainBoundary_comp_chainBoundary X m

/-- **Singular integral homology** `Hₙ(X; ℤ) = ker ∂ₙ / im ∂ₙ₊₁` — a genuine quotient ℤ-module
(the integral homology of the topological space `X`, built from the singular chain complex). The
dual of `SingularCohomologyInt.Cohomology`. -/
def Homology (X : TopCat) (n : ℕ) : Type :=
  (cycles X n) ⧸ (boundaries X n).submoduleOf (cycles X n)

noncomputable instance (X : TopCat) (n : ℕ) : AddCommGroup (Homology X n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (X : TopCat) (n : ℕ) : Module ℤ (Homology X n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The homology class of a cycle. -/
noncomputable def Homology.mk (X : TopCat) (n : ℕ) (z : cycles X n) : Homology X n :=
  Submodule.Quotient.mk z

/-! ## §3. The integral Kronecker pairing `Cⁿ × Cₙ → ℤ` -/

/-- The **integral Kronecker pairing** `⟨f, c⟩ = ∑_σ a_σ · f σ` of a singular integral `n`-cochain
`f` against an integral `n`-chain `c = ∑ a_σ · σ` (the `Finsupp` sum). The evaluation of an integral
cohomology class against an integral homology cycle. -/
noncomputable def kronecker {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : ℤ :=
  c.sum (fun σ a => a * f σ)

@[simp] theorem kronecker_apply {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker f c = c.sum (fun σ a => a * f σ) := rfl

/-- The pairing is `Finsupp.linearCombination` of `f` (read as `α → ℤ`) — `a · f σ = a • f σ` in ℤ.
This identifies the chain-argument linearity with a `LinearMap`. -/
theorem kronecker_eq_linearCombination {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker f c = Finsupp.linearCombination ℤ f c := by
  rw [kronecker_apply, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr (fun σ _ => by rw [smul_eq_mul])

/-- The Kronecker pairing on a basis simplex: `⟨f, single σ a⟩ = a · f σ`. -/
@[simp] theorem kronecker_single {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    kronecker f (Finsupp.single σ a) = a * f σ := by
  rw [kronecker_eq_linearCombination, Finsupp.linearCombination_single, smul_eq_mul]

/-- The pairing is **left-additive** (in the cochain). -/
theorem kronecker_add_left {X : TopCat} {n : ℕ} (f g : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker (f + g) c = kronecker f c + kronecker g c := by
  simp only [kronecker_apply, Pi.add_apply, mul_add]
  rw [Finsupp.sum_add]

/-- The pairing is **left ℤ-linear in the scalar** (in the cochain). -/
theorem kronecker_smul_left {X : TopCat} {n : ℕ} (s : ℤ) (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker (s • f) c = s • kronecker f c := by
  simp only [kronecker_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr (fun σ _ => by ring)

/-- The pairing is **right-additive** (in the chain). -/
theorem kronecker_add_right {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c d : SingularChainInt X n) : kronecker f (c + d) = kronecker f c + kronecker f d := by
  rw [kronecker_eq_linearCombination, kronecker_eq_linearCombination, kronecker_eq_linearCombination,
    map_add]

/-- The pairing is **right ℤ-linear in the scalar** (in the chain). -/
theorem kronecker_smul_right {X : TopCat} {n : ℕ} (s : ℤ) (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker f (s • c) = s • kronecker f c := by
  rw [kronecker_eq_linearCombination, kronecker_eq_linearCombination, map_smul]

/-- The integral Kronecker pairing as a **ℤ-bilinear map** `Cⁿ →ₗ Cₙ →ₗ ℤ`. -/
noncomputable def kroneckerₗ {X : TopCat} (n : ℕ) :
    SingularCochainInt X n →ₗ[ℤ] SingularChainInt X n →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ kronecker kronecker_add_left kronecker_smul_left
    kronecker_add_right kronecker_smul_right

@[simp] theorem kroneckerₗ_apply {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kroneckerₗ n f c = kronecker f c := rfl

/-! ## §4. The adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩` -/

/-- The Kronecker pairing of a cochain `f` against a *single boundary basis* `∂σ`: with the genuine
sign, `⟨f, ∂σ⟩ = ∑ᵢ (-1)ⁱ f(∂ᵢσ) = (δf)(σ)`. The core of the adjunction, off the basis. -/
theorem kronecker_boundaryBasis {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    kronecker f (boundaryBasis X n σ) = coboundary X n f σ := by
  rw [boundaryBasis, coboundary_apply, kronecker_eq_linearCombination, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Finsupp.linearCombination_single]

/-- **The adjunction** `⟨δf, c⟩ = ⟨f, ∂c⟩` over ℤ: the singular coboundary `δ` and boundary `∂` are
adjoint under the integral Kronecker pairing. Both sides are linear in the `(n+1)`-chain `c`, so it
suffices to check on a basis simplex `σ`, where both reduce to `∑ᵢ (-1)ⁱ f(∂ᵢσ)`. This is what makes
the pairing descend to (co)homology. -/
theorem kronecker_coboundary_chainBoundary {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X (n + 1)) :
    kronecker (coboundary X n f) c = kronecker f (chainBoundary X n c) := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | single_add σ a c hσ ha ih =>
    rw [kronecker_add_right, ih, map_add, kronecker_add_right, kronecker_single,
      show coboundary X n f = coboundaryₗ X n f from rfl]
    congr 1
    rw [chainBoundary_single_smul, kronecker_smul_right, kronecker_boundaryBasis]
    rfl

/-! ## §5. Descent of the pairing to `Hⁿ × Hₙ → ℤ` -/

/-- **Cocycle ⊥ boundary**: a cocycle `f` (`δf = 0`) pairs to `0` with any boundary `∂d`. Immediate
from the adjunction. The first descent fact. -/
theorem kronecker_eq_zero_of_cocycle_boundary {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (hf : coboundaryₗ X n f = 0) (d : SingularChainInt X (n + 1)) :
    kronecker f (chainBoundary X n d) = 0 := by
  rw [← kronecker_coboundary_chainBoundary, show coboundary X n f = coboundaryₗ X n f from rfl, hf]
  simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]

/-- **Coboundary ⊥ cycle** (degree `m+1`): a coboundary `δg` pairs to `0` with any `(m+1)`-cycle `c`
(`∂c = 0`). From the adjunction. The second descent fact. -/
theorem kronecker_eq_zero_of_coboundary_cycle {X : TopCat} {m : ℕ} (g : SingularCochainInt X m)
    (c : SingularChainInt X (m + 1)) (hc : chainBoundary X m c = 0) :
    kronecker (coboundary X m g) c = 0 := by
  rw [kronecker_coboundary_chainBoundary, hc]
  simp only [kronecker_apply, Finsupp.sum_zero_index]

/-- For a fixed `n`-cocycle `fc`, the pairing `⟨fc, ·⟩` descends to a linear map `Hₙ(X;ℤ) → ℤ`. -/
noncomputable def kroneckerRightH {X : TopCat} {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n)) :
    Homology X n →ₗ[ℤ] ℤ :=
  Submodule.liftQ _
    ((kroneckerₗ n fc.1).comp (cycles X n).subtype)
    (by
      intro c hc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hc
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, kroneckerₗ_apply]
      show kronecker fc.1 c.1 = 0
      obtain ⟨d, hd⟩ := hc
      rw [← hd]
      exact kronecker_eq_zero_of_cocycle_boundary fc.1 (LinearMap.mem_ker.mp fc.2) d)

/-- The computation rule for `kroneckerRightH` on a representative cycle `c`. -/
theorem kroneckerRightH_apply_mk {X : TopCat} {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n))
    (c : cycles X n) :
    kroneckerRightH fc (Submodule.Quotient.mk c) = kronecker fc.1 c.1 := rfl

/-- The map `fc ↦ kroneckerRightH fc`, packaged as ℤ-linear in the cochain (before descending the
cohomology quotient). -/
noncomputable def kroneckerRightHₗ {X : TopCat} (n : ℕ) :
    LinearMap.ker (coboundaryₗ X n) →ₗ[ℤ] (Homology X n →ₗ[ℤ] ℤ) where
  toFun := kroneckerRightH
  map_add' fc fc' := by
    ext x
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.add_apply, kroneckerRightH_apply_mk]
    rw [show ((fc + fc').1 : SingularCochainInt X n) = fc.1 + fc'.1 from rfl, kronecker_add_left]
  map_smul' s fc := by
    ext x
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.smul_apply, RingHom.id_apply, kroneckerRightH_apply_mk]
    rw [show ((s • fc).1 : SingularCochainInt X n) = s • fc.1 from rfl, kronecker_smul_left]

/-- **The integral Kronecker pairing on `Hⁿ × Hₙ → ℤ`** — a genuine ℤ-bilinear map (the evaluation of
an integral cohomology class against an integral homology class). Well-defined by both descent facts.
The missing ℤ ingredient the `[M]` datum discharges through: `eval := (kroneckerHInt 4).flip [M]`. -/
noncomputable def kroneckerHInt {X : TopCat} (n : ℕ) :
    Cohomology X n →ₗ[ℤ] Homology X n →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ (kroneckerRightHₗ n)
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply]
      show kroneckerRightH fc (Submodule.Quotient.mk c) = 0
      rw [kroneckerRightH_apply_mk]
      cases n with
      | zero =>
        rw [show coboundaryRange X 0 = ⊥ from rfl, Submodule.mem_bot,
          ← ZeroMemClass.coe_zero (LinearMap.ker (coboundaryₗ X 0)), Subtype.coe_inj] at hfc
        rw [hfc, ZeroMemClass.coe_zero]
        simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
      | succ m =>
        rw [show coboundaryRange X (m + 1) = LinearMap.range (coboundaryₗ X m) from rfl] at hfc
        obtain ⟨g, hg⟩ := hfc
        rw [← hg]
        have hcyc : chainBoundary X m c.1 = 0 :=
          LinearMap.mem_ker.mp (c.2 : c.1 ∈ LinearMap.ker (chainBoundary X m))
        exact kronecker_eq_zero_of_coboundary_cycle g c.1 hcyc)

@[simp] theorem kroneckerHInt_mk_mk {X : TopCat} {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n))
    (c : cycles X n) :
    kroneckerHInt n (Submodule.Quotient.mk fc) (Submodule.Quotient.mk c) = kronecker fc.1 c.1 := rfl

/-! ## §6. The eval-bridge — discharging `intFundamentalClass_eval_datum` up to the geometric `[M]` -/

/-- **The eval-bridge.** Given a genuine integral fundamental class `[M] : Homology X 4`, the disclosed
`SingularCohomologyInt.IntFundamentalClass.eval` datum is realized by the integral Kronecker pairing
flipped against `[M]`: `eval := (kroneckerHInt 4).flip [M] = ⟨·, [M]⟩ : Cohomology X 4 →ₗ[ℤ] ℤ`.

This is the exact integral mirror of the mod-2
`PoincareDualityConstruct.fundamentalFunctional = (kroneckerH (m+2)).flip fundamentalClass`. It reduces
the disclosed `intFundamentalClass_eval_datum` (a whole integral evaluation functional) to the SINGLE
geometric input `[M] : Homology X 4` (+ orientation) — the community-scale residual core (no mod-2
shortcut over ℤ). Everything downstream of the datum (`interFormInt` + `interFormInt_symm`, kernel-pure)
holds for this concrete `eval`, so the intersection form is discharged the moment `[M]` is built. -/
noncomputable def intFundamentalClassOfHomology {X : TopCat} (zM : Homology X 4) :
    IntFundamentalClass X where
  eval := (kroneckerHInt 4).flip zM

/-- **The eval-bridge computes as `⟨·, [M]⟩`** — the `eval` of `intFundamentalClassOfHomology [M]` is
exactly the integral Kronecker pairing against `[M]`. Confirms the datum's `eval` is discharged by the
pair `(kroneckerHInt, [M])`. -/
@[simp] theorem intFundamentalClassOfHomology_eval {X : TopCat} (zM : Homology X 4)
    (ω : Cohomology X 4) :
    (intFundamentalClassOfHomology zM).eval ω = kroneckerHInt 4 ω zM :=
  rfl

end SKEFTHawking.SingularHomologyInt
