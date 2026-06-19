/-
# Phase 5q.F — singular ℤ/2 homology and the Kronecker pairing

The dual of `SKEFTHawking/SingularCohomologyMod2.lean`. That file builds singular ℤ/2 *cochains*
(`ℤ/2`-valued functions on singular simplices) with the coboundary `δ`. This module builds the
*chains* — finitely-supported `ℤ/2`-combinations of singular simplices — with the boundary `∂`
(the mod-2 alternating sum over faces, i.e. the plain sum), and the **Kronecker pairing**
`⟨f, c⟩ = ∑ a · f σ` connecting cochains to chains.

The pairing is the adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩`, which makes it descend to a perfect-pairing
candidate `Hⁿ(X; ℤ/2) × Hₙ(X; ℤ/2) → ℤ/2` on (co)homology. This is the algebraic substrate the
ABK β needs: an evaluation of cohomology classes against bordism cycles, built from the bordism
group's underlying `SingularManifold` spaces rather than supplied as a hypothesis.

Bricks: the singular chain group `Cₙ`, the boundary `∂` (`∂² = 0` from `SimplexCategory.δ_comp_δ`),
homology `Hₙ`, the Kronecker pairing `⟨·,·⟩` (bilinear), the adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩`, and
the descended pairing `Hⁿ × Hₙ → ℤ/2`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularHomologyMod2

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2

/-- **Singular `n`-chains** of a space `X` with `ℤ/2` coefficients: finitely-supported `ℤ/2`
combinations of the singular `n`-simplices `(TopCat.toSSet.obj X).obj (op [n])`. A genuine
`ℤ/2`-vector space (a `Finsupp` into the field `ZMod 2`). -/
abbrev SingularChain (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) →₀ ZMod 2

/-- The boundary of a *single basis simplex* `σ` (an `(n+1)`-simplex): `∂σ = ∑ᵢ ∂ᵢσ` over `ℤ/2`
(the alternating sign is `+1` mod 2), as a `ℤ/2`-chain `∑ᵢ single (face i σ) 1`. -/
noncomputable def boundaryBasis (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) : SingularChain X n :=
  ∑ i : Fin (n + 2), Finsupp.single (face i σ) 1

/-- The **singular boundary** `∂ : Cₙ₊₁ →ₗ[ZMod 2] Cₙ`, the `ℤ/2`-linear extension of
`σ ↦ ∑ᵢ ∂ᵢσ` off the basis simplices (`Finsupp.linearCombination`). -/
noncomputable def chainBoundary (X : TopCat) (n : ℕ) :
    SingularChain X (n + 1) →ₗ[ZMod 2] SingularChain X n :=
  Finsupp.linearCombination (ZMod 2) (boundaryBasis X n)

/-- The boundary on a basis simplex: `∂(single σ 1) = ∑ᵢ single (∂ᵢσ) 1`. -/
theorem chainBoundary_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary X n (Finsupp.single σ 1) = boundaryBasis X n σ := by
  rw [chainBoundary, Finsupp.linearCombination_single, one_smul]

/-- The boundary on a scaled basis simplex: `∂(single σ a) = a • ∂σ`. -/
theorem chainBoundary_single_smul (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (a : ZMod 2) :
    chainBoundary X n (Finsupp.single σ a) = a • boundaryBasis X n σ := by
  rw [chainBoundary, Finsupp.linearCombination_single]

/-- The boundary applied to a *single basis simplex* `σ` (an `(n+2)`-simplex), twice: this is the
double sum `∑ᵢ∑ⱼ single (∂ⱼ∂ᵢσ) 1`, the head of the `∂² = 0` cancellation. -/
theorem chainBoundary_chainBoundary_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1 + 1)))) :
    chainBoundary X n (chainBoundary X (n + 1) (Finsupp.single σ 1))
      = ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
          Finsupp.single (face j (face i σ)) (1 : ZMod 2) := by
  rw [chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [chainBoundary_single, boundaryBasis]

/-- **`∂² = 0` on a basis simplex.** `(∂²)(single σ 1) = ∑ᵢ∑ⱼ single (∂ⱼ∂ᵢσ) 1`; by `face_face` each
summand is `single` of the composite coface `δ j ≫ δ i`, and the cosimplicial identity `δ_comp_δ`
pairs the index set `Fin(n+3) × Fin(n+2)` into a fixed-point-free involution with equal `single`
values, so the sum vanishes over `ℤ/2`. The exact dual of `coboundary_comp_coboundary`. -/
theorem chainBoundary_chainBoundary_single_eq_zero (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1 + 1)))) :
    chainBoundary X n (chainBoundary X (n + 1) (Finsupp.single σ 1)) = 0 := by
  rw [chainBoundary_chainBoundary_single]
  simp only [face_face]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    Finsupp.single ((TopCat.toSSet.obj X).map (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1).op σ)
      (1 : ZMod 2))]
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
      rw [heq]; exact ZModModule.add_self _
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
      rw [heq]; exact ZModModule.add_self _
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

/-- **`∂² = 0`** — the singular chain complex condition, as the composite linear map
`Cₙ₊₂ → Cₙ` (the dual of `coboundary_comp_coboundary`). Reduced to the basis-simplex case
`chainBoundary_chainBoundary_single_eq_zero` by `Finsupp.lhom_ext`. -/
theorem chainBoundary_comp_chainBoundary (X : TopCat) (n : ℕ) :
    (chainBoundary X n).comp (chainBoundary X (n + 1)) = 0 := by
  refine Finsupp.lhom_ext (fun σ b => ?_)
  have hsingle : (Finsupp.single σ b) = b • Finsupp.single σ 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, hsingle, map_smul, map_smul,
    chainBoundary_chainBoundary_single_eq_zero, smul_zero]

/-- `∂² = 0` in applied form: `∂(∂ c) = 0` for every chain `c`. -/
theorem chainBoundary_chainBoundary_apply (X : TopCat) (n : ℕ) (c : SingularChain X (n + 1 + 1)) :
    chainBoundary X n (chainBoundary X (n + 1) c) = 0 := by
  have := chainBoundary_comp_chainBoundary X n
  rw [← LinearMap.comp_apply, this, LinearMap.zero_apply]

/-! ## §2. Singular homology `Hₙ(X; ℤ/2) = ker ∂ₙ / im ∂ₙ₊₁` -/

/-- The **`n`-cycles** `ker(∂ₙ : Cₙ → Cₙ₋₁)` — in degree `0` there is no `∂₀`, so every `0`-chain is
a cycle (`⊤`). -/
noncomputable def cycles (X : TopCat) (n : ℕ) : Submodule (ZMod 2) (SingularChain X n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (chainBoundary X m)

/-- The **`n`-boundaries** (image of the outgoing `∂ₙ₊₁ : Cₙ₊₁ → Cₙ`). -/
noncomputable def boundaries (X : TopCat) (n : ℕ) : Submodule (ZMod 2) (SingularChain X n) :=
  LinearMap.range (chainBoundary X n)

/-- Boundaries are cycles, `im ∂ₙ₊₁ ≤ ker ∂ₙ` — the well-definedness of homology, from `∂² = 0`. -/
theorem boundaries_le_cycles (X : TopCat) (n : ℕ) : boundaries X n ≤ cycles X n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (chainBoundary X (m + 1)) ≤ LinearMap.ker (chainBoundary X m)
    rw [LinearMap.range_le_ker_iff]
    exact chainBoundary_comp_chainBoundary X m

/-- **Singular `ℤ/2` homology** `Hₙ(X; ℤ/2) = ker ∂ₙ / im ∂ₙ₊₁` — a genuine quotient `ℤ/2`-vector
space (the homology of the topological space `X`, built from the singular chain complex). The
dual of `Cohomology`. -/
def Homology (X : TopCat) (n : ℕ) : Type :=
  (cycles X n) ⧸ (boundaries X n).submoduleOf (cycles X n)

noncomputable instance (X : TopCat) (n : ℕ) : AddCommGroup (Homology X n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (X : TopCat) (n : ℕ) : Module (ZMod 2) (Homology X n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The homology class of a cycle. -/
noncomputable def Homology.mk (X : TopCat) (n : ℕ) (z : cycles X n) : Homology X n :=
  Submodule.Quotient.mk z

/-! ## §3. The Kronecker pairing `Cⁿ × Cₙ → ℤ/2` -/

/-- The **Kronecker pairing** `⟨f, c⟩ = ∑_σ a_σ · f σ` of a singular `n`-cochain `f` against an
`n`-chain `c = ∑ a_σ · σ` (the `Finsupp` sum). The evaluation of a cohomology class against a
homology cycle. -/
noncomputable def kronecker {X : TopCat} {n : ℕ} (f : SingularCochain X n) (c : SingularChain X n) :
    ZMod 2 :=
  c.sum (fun σ a => a * f σ)

@[simp] theorem kronecker_apply {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (c : SingularChain X n) : kronecker f c = c.sum (fun σ a => a * f σ) := rfl

/-- The pairing is `Finsupp.linearCombination` of `f` (read as `α → ℤ/2`) — `a · f σ = a • f σ` in
`ℤ/2`. This identifies the chain-argument linearity with a `LinearMap`. -/
theorem kronecker_eq_linearCombination {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (c : SingularChain X n) : kronecker f c = Finsupp.linearCombination (ZMod 2) f c := by
  rw [kronecker_apply, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr (fun σ _ => by rw [smul_eq_mul])

/-- The Kronecker pairing on a basis simplex: `⟨f, single σ a⟩ = a · f σ`. -/
@[simp] theorem kronecker_single {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    kronecker f (Finsupp.single σ a) = a * f σ := by
  rw [kronecker_eq_linearCombination, Finsupp.linearCombination_single, smul_eq_mul]

/-- The pairing is **left-additive** (in the cochain). -/
theorem kronecker_add_left {X : TopCat} {n : ℕ} (f g : SingularCochain X n)
    (c : SingularChain X n) : kronecker (f + g) c = kronecker f c + kronecker g c := by
  simp only [kronecker_apply, Pi.add_apply, mul_add]
  rw [Finsupp.sum_add]

/-- The pairing is **left ℤ/2-linear in the scalar** (in the cochain). -/
theorem kronecker_smul_left {X : TopCat} {n : ℕ} (s : ZMod 2) (f : SingularCochain X n)
    (c : SingularChain X n) : kronecker (s • f) c = s • kronecker f c := by
  simp only [kronecker_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr (fun σ _ => by ring)

/-- The pairing is **right-additive** (in the chain). -/
theorem kronecker_add_right {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (c d : SingularChain X n) : kronecker f (c + d) = kronecker f c + kronecker f d := by
  rw [kronecker_eq_linearCombination, kronecker_eq_linearCombination, kronecker_eq_linearCombination,
    map_add]

/-- The pairing is **right ℤ/2-linear in the scalar** (in the chain). -/
theorem kronecker_smul_right {X : TopCat} {n : ℕ} (s : ZMod 2) (f : SingularCochain X n)
    (c : SingularChain X n) : kronecker f (s • c) = s • kronecker f c := by
  rw [kronecker_eq_linearCombination, kronecker_eq_linearCombination, map_smul]

/-- The Kronecker pairing as a **`ℤ/2`-bilinear map** `Cⁿ →ₗ Cₙ →ₗ ℤ/2`. -/
noncomputable def kroneckerₗ {X : TopCat} (n : ℕ) :
    SingularCochain X n →ₗ[ZMod 2] SingularChain X n →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) kronecker kronecker_add_left kronecker_smul_left
    kronecker_add_right kronecker_smul_right

@[simp] theorem kroneckerₗ_apply {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (c : SingularChain X n) : kroneckerₗ n f c = kronecker f c := rfl

/-! ## §4. The adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩` -/

/-- The Kronecker pairing of a cochain `f` against a *single boundary basis* `∂σ` (the boundary of an
`(n+1)`-simplex `σ`): `⟨f, ∂σ⟩ = ∑ᵢ f(∂ᵢσ) = (δf)(σ)`. The core of the adjunction, off the basis. -/
theorem kronecker_boundaryBasis {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    kronecker f (boundaryBasis X n σ) = coboundary X n f σ := by
  rw [boundaryBasis, coboundary_apply, kronecker_eq_linearCombination, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finsupp.linearCombination_single, smul_eq_mul, one_mul]

/-- **The adjunction** `⟨δf, c⟩ = ⟨f, ∂c⟩` (mod 2): the singular coboundary `δ` and boundary `∂` are
adjoint under the Kronecker pairing. Both sides are linear in the `(n+1)`-chain `c`, so it suffices
to check on a basis simplex `σ`, where both reduce to `∑ᵢ f(∂ᵢσ)`. This is what makes the pairing
descend to (co)homology: pairing a cocycle with a boundary, or a coboundary with a cycle, gives `0`. -/
theorem kronecker_coboundary_chainBoundary {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (c : SingularChain X (n + 1)) :
    kronecker (coboundary X n f) c = kronecker f (chainBoundary X n c) := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | single_add σ a c hσ ha ih =>
    rw [kronecker_add_right, ih, map_add, kronecker_add_right, kronecker_single,
      show coboundary X n f = coboundaryₗ X n f from rfl]
    congr 1
    rw [chainBoundary_single_smul, kronecker_smul_right, kronecker_boundaryBasis]
    rfl

/-! ## §5. Descent of the pairing to `Hⁿ × Hₙ → ℤ/2` -/

/-- **Cocycle ⊥ boundary**: a cocycle `f` (`δf = 0`) pairs to `0` with any boundary `∂d`. Immediate
from the adjunction: `⟨f, ∂d⟩ = ⟨δf, d⟩ = ⟨0, d⟩ = 0`. The first descent fact (kills the boundaries
in the chain argument of the pairing). -/
theorem kronecker_eq_zero_of_cocycle_boundary {X : TopCat} {n : ℕ} (f : SingularCochain X n)
    (hf : coboundaryₗ X n f = 0) (d : SingularChain X (n + 1)) :
    kronecker f (chainBoundary X n d) = 0 := by
  rw [← kronecker_coboundary_chainBoundary, show coboundary X n f = coboundaryₗ X n f from rfl, hf]
  simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]

/-- **Coboundary ⊥ cycle** (degree `m+1`): a coboundary `δg` pairs to `0` with any `(m+1)`-cycle `c`
(`∂c = 0`). From the adjunction `⟨δg, c⟩ = ⟨g, ∂c⟩ = ⟨g, 0⟩ = 0`. The second descent fact (kills the
coboundaries in the cochain argument). -/
theorem kronecker_eq_zero_of_coboundary_cycle {X : TopCat} {m : ℕ} (g : SingularCochain X m)
    (c : SingularChain X (m + 1)) (hc : chainBoundary X m c = 0) :
    kronecker (coboundary X m g) c = 0 := by
  rw [kronecker_coboundary_chainBoundary, hc]
  simp only [kronecker_apply, Finsupp.sum_zero_index]

/-- For a fixed `n`-cocycle `fc`, the pairing `⟨fc, ·⟩` descends to a linear map `Hₙ → ℤ/2`. It
kills `Hₙ`-boundaries because a cocycle pairs to `0` with a boundary (`kronecker_eq_zero_of_cocycle_boundary`,
via the adjunction). -/
noncomputable def kroneckerRightH {X : TopCat} {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n)) :
    Homology X n →ₗ[ZMod 2] ZMod 2 :=
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

/-- The map `fc ↦ kroneckerRightH fc`, packaged as `ℤ/2`-linear in the cochain (before descending the
cohomology quotient). -/
noncomputable def kroneckerRightHₗ {X : TopCat} (n : ℕ) :
    LinearMap.ker (coboundaryₗ X n) →ₗ[ZMod 2] (Homology X n →ₗ[ZMod 2] ZMod 2) where
  toFun := kroneckerRightH
  map_add' fc fc' := by
    ext x
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.add_apply, kroneckerRightH_apply_mk]
    rw [show ((fc + fc').1 : SingularCochain X n) = fc.1 + fc'.1 from rfl, kronecker_add_left]
  map_smul' s fc := by
    ext x
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.smul_apply, RingHom.id_apply, kroneckerRightH_apply_mk]
    rw [show ((s • fc).1 : SingularCochain X n) = s • fc.1 from rfl, kronecker_smul_left]

/-- **The Kronecker pairing on `Hⁿ × Hₙ → ℤ/2`** — a genuine `ℤ/2`-bilinear map (the evaluation of a
cohomology class against a homology class). Well-defined: a cocycle pairs to `0` with a boundary
(`kronecker_eq_zero_of_cocycle_boundary`, descending the homology quotient via `kroneckerRightH`), and
a coboundary pairs to `0` with a cycle (`kronecker_eq_zero_of_coboundary_cycle`, descending the
cohomology quotient). The algebraic substrate for the ABK invariant `β` built from the bordism group. -/
noncomputable def kroneckerH {X : TopCat} (n : ℕ) :
    Cohomology X n →ₗ[ZMod 2] Homology X n →ₗ[ZMod 2] ZMod 2 :=
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

@[simp] theorem kroneckerH_mk_mk {X : TopCat} {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n))
    (c : cycles X n) :
    kroneckerH n (Submodule.Quotient.mk fc) (Submodule.Quotient.mk c) = kronecker fc.1 c.1 := rfl

/-! ## §8. The cap product `⌢ : Cᵏ × Cₙ → Cₙ₋ₖ` — the cohomology–homology pairing

The cap product caps a `k`-cochain against an `n`-chain to land in `Cₙ₋ₖ`: on a basis `(k+m)`-simplex
`σ`, `a ⌢ σ = a(frontₖ σ) • [backₘ σ]` (evaluate `a` on the front `k`-face, scale the back `m`-face).
It is the homology-valued analogue of the cup product (same Alexander–Whitney front/back split), and the
substrate for Poincaré duality, whose duality map is the cap with the fundamental class, `[M] ⌢ ·`. -/

/-- The cap product of a `k`-cochain with a *single basis* `(k+m)`-simplex `σ`:
`a ⌢ σ = a(frontₖ σ) • [backₘ σ]`. A `ℤ/2`-chain in `Cₘ`. -/
noncomputable def capBasis {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) : SingularChain X m :=
  a (frontFace σ) • Finsupp.single (backFace σ) 1

/-- The **cap product** `⌢ : Cᵏ × Cₙ → Cₙ₋ₖ` (with `n = k + m`), the `ℤ/2`-linear extension of
`σ ↦ a(frontₖ σ) • [backₘ σ]` off the basis simplices (`Finsupp.linearCombination`). Connects
cohomology and homology — the substrate for Poincaré duality `[M] ⌢ ·`. -/
noncomputable def cap {X : TopCat} {k m : ℕ} (a : SingularCochain X k) :
    SingularChain X (k + m) →ₗ[ZMod 2] SingularChain X m :=
  Finsupp.linearCombination (ZMod 2) (capBasis a)

/-- The cap product on a basis simplex: `a ⌢ [σ] = a(frontₖ σ) • [backₘ σ]`. -/
theorem cap_single {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) :
    cap a (Finsupp.single σ 1) = capBasis a σ := by
  rw [cap, Finsupp.linearCombination_single, one_smul]

/-- The cap product on a scaled basis simplex. -/
theorem cap_single_smul {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) (s : ZMod 2) :
    cap a (Finsupp.single σ s) = s • capBasis a σ := by
  rw [cap, Finsupp.linearCombination_single]

/-- The cap product is `ℤ/2`-linear in the cochain argument (additivity). -/
theorem cap_add_cochain {X : TopCat} {k m : ℕ} (a b : SingularCochain X k)
    (c : SingularChain X (k + m)) : cap (a + b) c = cap a c + cap b c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd]; abel
  | single σ s =>
      rw [cap_single_smul, cap_single_smul, cap_single_smul, ← smul_add]
      congr 1
      simp only [capBasis, Pi.add_apply, add_smul]

/-- The cap product is `ℤ/2`-linear in the cochain argument (homogeneity). -/
theorem cap_smul_cochain {X : TopCat} {k m : ℕ} (s : ZMod 2) (a : SingularCochain X k)
    (c : SingularChain X (k + m)) : cap (s • a) c = s • cap a c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, smul_add]
  | single σ t =>
      rw [cap_single_smul, cap_single_smul, smul_comm]
      congr 1
      simp only [capBasis, Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The **cap product packaged as a `ℤ/2`-bilinear map** `Cᵏ →ₗ (Cₖ₊ₘ →ₗ Cₘ)` (linear in the cochain
by `cap_add_cochain`/`cap_smul_cochain`, in the chain since each `cap a` is already a `LinearMap`). The
degree-`(k,m)` cap operation; the substrate for Poincaré duality `[M] ⌢ ·`. -/
noncomputable def capₗ {X : TopCat} (k m : ℕ) :
    SingularCochain X k →ₗ[ZMod 2] SingularChain X (k + m) →ₗ[ZMod 2] SingularChain X m where
  toFun := cap
  map_add' a b := LinearMap.ext fun c => by rw [LinearMap.add_apply]; exact cap_add_cochain a b c
  map_smul' s a := LinearMap.ext fun c => by
    rw [LinearMap.smul_apply, RingHom.id_apply]; exact cap_smul_cochain s a c

@[simp] theorem capₗ_apply {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + m)) : capₗ k m a c = cap a c := rfl

/-! ### The cap Leibniz (boundary) rule `∂(a ⌢ c) = (δa) ⌢ c + a ⌢ (∂c)` (mod 2)

The homological analogue of the cup Leibniz `coboundary_cup`, stated cast-free at a basis
`(k+m+1)`-simplex `σ`. The cap is chain-valued, so the diagonal cancellation is between the
front-coboundary expansion `(δa)(frontBig σ) = ∑ⱼ a(face j (frontBig σ))` and the `i ≤ k` faces of
`∂σ`: both contribute the *same* sum `∑_{j≤k} a(face j (frontBig σ)) • [backBig σ]`, which cancels
over ℤ/2 (`x + x = 0`), leaving the diagonal `a(frontSmall σ) • [backBig σ]`. The `i > k` faces of
`∂σ` give `a(frontSmall σ) • [face (i-k) (backSmall σ)]`, matching the `j ≥ 1` part of `∂(a ⌢ σ)`. -/
theorem cap_leibniz_single {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) :
    chainBoundary X m (cap a (Finsupp.single σ 1))
      = coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) 1
        + cap a (boundaryBasis X (k + m) σ) := by
  have h : k + 1 + (m + 1) = k + m + 2 := by omega
  -- LHS: `∂(a ⌢ σ)` reaches the canonical middle form, peeling the zeroth back-face term.
  have hL : chainBoundary X m (cap a (Finsupp.single σ 1))
      = a (frontSmall σ) • Finsupp.single (backBig σ) 1
        + a (frontSmall σ) • ∑ l : Fin (m + 1), Finsupp.single (face l.succ (backSmall σ)) (1 : ZMod 2) := by
    rw [cap_single, capBasis, map_smul, chainBoundary_single]
    show a (frontSmall σ) • boundaryBasis X m (backSmall σ) = _
    rw [boundaryBasis, Fin.sum_univ_succ, face_zero_backSmall, smul_add]
  -- `a ⌢ ∂σ` splits `Fin (k+m+2)` at `k`: the `i ≤ k` faces carry `[backBig σ]` with the interior
  -- front faces; the `i > k` faces carry `[frontSmall σ]` with the interior back faces.
  have hcap : cap a (boundaryBasis X (k + m) σ)
      = (∑ j : Fin (k + 1), a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ZMod 2))
        + (∑ l : Fin (m + 1),
            a (frontSmall σ) • Finsupp.single (face l.succ (backSmall σ)) (1 : ZMod 2)) := by
    have hsum : cap a (boundaryBasis X (k + m) σ)
        = ∑ i : Fin (k + m + 2), capBasis a (face i σ) := by
      rw [boundaryBasis, map_sum]
      exact Finset.sum_congr rfl (fun i _ => cap_single a (face i σ))
    rw [hsum, ← Equiv.sum_comp (finCongr h) (fun i => capBasis a (face i σ)), Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      have hle : (finCongr h (Fin.castAdd (m + 1) j)).val ≤ k := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]; omega
      rw [capBasis, frontFace_face_of_le σ _ hle, backFace_face_of_le σ _ hle]
      have hidx : (⟨(finCongr h (Fin.castAdd (m + 1) j)).val, by omega⟩ : Fin (k + 2))
          = j.castSucc := by
        apply Fin.ext; simp [Fin.val_castSucc]
      rw [hidx]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      have hgt : k < (finCongr h (Fin.natAdd (k + 1) l)).val := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [capBasis, frontFace_face_of_gt σ _ hgt, backFace_face_of_gt σ _ hgt]
      have hidx : (⟨(finCongr h (Fin.natAdd (k + 1) l)).val - k, by have := l.isLt; omega⟩ : Fin (m + 2))
          = l.succ := by
        apply Fin.ext; simp only [Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [hidx]
  -- The front-coboundary term peels its last face into the diagonal `a(frontSmall σ)•[backBig σ]`.
  have hcobound : coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) (1 : ZMod 2)
      = (∑ j : Fin (k + 1), a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ZMod 2))
        + a (frontSmall σ) • Finsupp.single (backBig σ) (1 : ZMod 2) := by
    rw [coboundary_apply, Fin.sum_univ_castSucc, face_last_frontBig, add_smul, Finset.sum_smul]
  -- The two `∑_{j≤k}` front sums coincide and cancel over ℤ/2; what remains is M.
  have hSS : (∑ j : Fin (k + 1), a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ZMod 2))
        + (∑ j : Fin (k + 1), a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ZMod 2))
      = 0 := by rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [hL, hcap, hcobound, Finset.smul_sum, add_add_add_comm, hSS, zero_add]

/-- **A cocycle caps to a chain map** (mod 2): if `a` is a cocycle (`δa = 0`) then
`∂(a ⌢ c) = a ⌢ (∂c)` for every `(k+m+1)`-chain `c` — i.e. `a ⌢ ·` intertwines the chain boundaries.
Cast-free (the `(δa) ⌢ c` middle term of `cap_leibniz_single` vanishes), the homological analogue of
`cup_cocycle`: this is the descent fact that makes `a ⌢ ·` well-defined on homology for a cocycle `a`.
Proved by `Finsupp.induction_linear` reducing to the basis case `cap_leibniz_single`. -/
theorem cap_cocycle_chainMap {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (ha : coboundaryₗ X k a = 0) (c : SingularChain X (k + m + 1)) :
    chainBoundary X m (cap a c) = cap a (chainBoundary X (k + m) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd, map_add]
  | single σ s =>
      rw [cap_single_smul, map_smul, chainBoundary_single_smul, map_smul,
        show chainBoundary X m (capBasis a σ) = chainBoundary X m (cap a (Finsupp.single σ 1)) by
          rw [cap_single],
        cap_leibniz_single]
      have hδ : coboundary X k a (frontBig σ) = 0 := congrFun ha (frontBig σ)
      rw [hδ, zero_smul, zero_add]

/-- A degree cast of a singular simplex is the functorial image of the `eqToHom` of the degree equality
(the cast pushes through `(TopCat.toSSet.obj X).map`). The bridge that lets the cap Leibniz middle term
`(δa) ⌢ c` — capped at the shifted degree `(k+1)+m` — be evaluated cast-free. -/
theorem singularSimplex_cast_eq {X : TopCat} {d n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk d))) (h : d = n) :
    (h ▸ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
      = (TopCat.toSSet.obj X).map (eqToHom (by rw [h])).op σ := by
  subst h; simp

/-- Under the cast `k+m+1 → (k+1)+m`, the split-`(k+1, m)` front face of `σ` is the split-`(k, m)`
`frontBig σ` — both are the inclusion of the front `k+1` vertices. -/
theorem frontFace_cast {X : TopCat} {k m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (h : k + m + 1 = k + 1 + m) :
    (frontFace (h ▸ σ) : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + 1)))) = frontBig σ := by
  unfold frontFace frontBig
  rw [singularSimplex_cast_eq σ h, ← FunctorToTypes.map_comp_apply, ← op_comp]
  have hmor : (frontIncl (k + 1) m
      ≫ eqToHom (show SimplexCategory.mk (k + 1 + m) = SimplexCategory.mk (k + m + 1) by rw [h]))
      = frontBigIncl k m := by
    apply SimplexCategory.Hom.ext; ext x : 2; apply Fin.ext
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, frontIncl,
      frontBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, Fin.val_castLE]
    rw [SimplexCategory.eqToHom_toOrderHom]
    simp only [OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_castLE]
  rw [hmor]

/-- Under the cast `k+m+1 → (k+1)+m`, the split-`(k+1, m)` back face of `σ` is the split-`(k, m)`
`backBig σ` — both are the inclusion of the back `m` vertices. -/
theorem backFace_cast {X : TopCat} {k m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (h : k + m + 1 = k + 1 + m) :
    (backFace (h ▸ σ) : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk m))) = backBig σ := by
  unfold backFace backBig
  rw [singularSimplex_cast_eq σ h, ← FunctorToTypes.map_comp_apply, ← op_comp]
  have hmor : (backIncl (k + 1) m
      ≫ eqToHom (show SimplexCategory.mk (k + 1 + m) = SimplexCategory.mk (k + m + 1) by rw [h]))
      = backBigIncl k m := by
    apply SimplexCategory.Hom.ext; ext x : 2; apply Fin.ext
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, backIncl,
      backBigIncl, toOrderHom_mkHom, OrderHom.coe_mk]
    rw [SimplexCategory.eqToHom_toOrderHom]
    simp only [OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_natAdd]
  rw [hmor]

/-- A degree cast of a `Finsupp.single` of a simplex is the `single` of the cast simplex. -/
theorem singularChain_single_cast {X : TopCat} {d n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk d))) (s : ZMod 2) (h : d = n) :
    (h ▸ Finsupp.single σ s : SingularChain X n)
      = Finsupp.single (h ▸ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) s := by
  subst h; rfl

/-- The middle term `(δa) ⌢ σ` of the cap Leibniz rule, evaluated at the cast basis simplex `h ▸ σ`
(at the `cap (δa)` degree `(k+1)+m`), recovers the cast-free `(δa)(frontBig σ) • [backBig σ]`. -/
theorem cap_coboundary_single_cast {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (s : ZMod 2)
    (h : k + m + 1 = k + 1 + m) :
    cap (coboundary X k a) (h ▸ Finsupp.single σ s)
      = s • (coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) (1 : ZMod 2)) := by
  rw [singularChain_single_cast σ s h, cap_single_smul, capBasis, frontFace_cast σ h,
    backFace_cast σ h]

/-- A degree cast of singular chains is additive. -/
theorem singularChain_cast_add {X : TopCat} {d n : ℕ} (c d' : SingularChain X d) (h : d = n) :
    (h ▸ (c + d') : SingularChain X n) = (h ▸ c) + (h ▸ d') := by
  subst h; rfl

/-- A degree cast sends the zero chain to the zero chain. -/
theorem singularChain_cast_zero {X : TopCat} {d n : ℕ} (h : d = n) :
    (h ▸ (0 : SingularChain X d) : SingularChain X n) = 0 := by
  subst h; rfl

/-- **Cap Leibniz (boundary) rule** (mod 2): `∂(a ⌢ c) = (δa) ⌢ c + a ⌢ (∂c)`, the homological
analogue of the cup Leibniz `coboundary_cup`, for a `k`-cochain `a` and an arbitrary `(k+m+1)`-chain
`c`. The middle term `(δa) ⌢ c` caps the `(k+1)`-coboundary `δa` against `c` re-indexed to degree
`(k+1)+m` (propositionally `= k+m+1`; the `cast` is the homological counterpart of the degree shift
`coboundary_cup` absorbs via `frontBig`/`backBig`). Proved by `Finsupp.induction_linear` reducing to the
cast-free basis case `cap_leibniz_single`, with the cast discharged by `cap_coboundary_single_cast`. -/
theorem cap_leibniz {X : TopCat} {k m : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + m + 1)) (h : k + m + 1 = k + 1 + m) :
    chainBoundary X m (cap a c)
      = cap (coboundary X k a) (h ▸ c) + cap a (chainBoundary X (k + m) c) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [singularChain_cast_zero h]; simp
  | add c d hc hd =>
      rw [map_add, map_add, map_add, hc, hd, singularChain_cast_add c d h, map_add,
        add_add_add_comm, ← map_add, ← map_add]
  | single σ s =>
      rw [cap_single_smul, map_smul, chainBoundary_single_smul, map_smul,
        show chainBoundary X m (capBasis a σ) = chainBoundary X m (cap a (Finsupp.single σ 1)) by
          rw [cap_single],
        cap_leibniz_single, smul_add, cap_coboundary_single_cast a σ s h]

end SKEFTHawking.SingularHomologyMod2
