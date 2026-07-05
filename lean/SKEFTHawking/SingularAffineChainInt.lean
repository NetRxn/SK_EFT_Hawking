import Mathlib
import SKEFTHawking.SingularExcisionMod2
import SKEFTHawking.SingularSubdivisionConvex

/-!
# The signed **integral** affine chain engine `LCᵢₙₜ_n(Y)`

Integral (ℤ-coefficient, **signed**) mirror of the mod-2 affine subdivision engine
`SingularExcisionMod2` / `SingularSubdivisionConvex`. Where the mod-2 engine drops all signs
(`∂[v] = ∑ᵢ [∂ᵢv]`, `∂(b·c) = c + b·∂c`, `1 − Sd = 1 + Sd`), the integral engine carries the true
alternating signs (`∂[v] = ∑ᵢ (−1)ⁱ [∂ᵢv]`, `∂(b·c) = c − b·∂c`, `∂D + D∂ = 1 − Sd`). This is the
root foundation of integral singular excision and integral sphere homology — both Mathlib-absent and
both `ZMod 2`-only in this project's on-main substrate.

The whole engine is elementary/free-module algebra over ℤ; the geometric operators (`coneBasis`,
`barycenter`, `Fin.cons`, `Fin.succAbove`) are **shared** with the mod-2 engine (they are
coefficient-agnostic tuple manipulations), so only the *signed* linear-combination boundary /
subdivision / homotopy need re-deriving.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularAffineChainInt

open SKEFTHawking.SingularExcisionMod2 (barycenter
  cons_comp_zero_succAbove cons_comp_succ_succAbove)

variable {Y : Type*}

/-! ## §1. Signed affine chains and boundary -/

/-- **Signed integral affine `n`-chains** `LCᵢₙₜ_n(Y)`: free ℤ-module on vertex-tuples `Fin (n+1) → Y`. -/
abbrev LinChainInt (Y : Type*) (n : ℕ) : Type _ := (Fin (n + 1) → Y) →₀ ℤ

/-- The **signed** affine boundary of a single vertex-tuple `v`: `∂[v] = ∑ᵢ (−1)ⁱ [∂ᵢv]` over ℤ, where
`∂ᵢv = v ∘ Fin.succAbove i` drops the `i`-th vertex. -/
noncomputable def linBoundaryBasisInt (n : ℕ) (v : Fin (n + 1 + 1) → Y) : LinChainInt Y n :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (v ∘ i.succAbove) 1

/-- The **signed affine boundary** `∂ : LCᵢₙₜ_{n+1}(Y) → LCᵢₙₜ_n(Y)`, the ℤ-linear extension of
`[v] ↦ ∑ᵢ (−1)ⁱ [∂ᵢv]`. -/
noncomputable def linBoundaryInt (n : ℕ) : LinChainInt Y (n + 1) →ₗ[ℤ] LinChainInt Y n :=
  Finsupp.linearCombination ℤ (linBoundaryBasisInt n)

theorem linBoundaryInt_single (n : ℕ) (v : Fin (n + 1 + 1) → Y) :
    linBoundaryInt n (Finsupp.single v 1) = linBoundaryBasisInt n v := by
  rw [linBoundaryInt, Finsupp.linearCombination_single, one_smul]

theorem linBoundaryInt_single_smul (n : ℕ) (v : Fin (n + 1 + 1) → Y) (a : ℤ) :
    linBoundaryInt n (Finsupp.single v a) = a • linBoundaryBasisInt n v := by
  rw [linBoundaryInt, Finsupp.linearCombination_single]

/-- `∂²` on a single vertex-tuple `v` is the signed double sum `∑ᵢ∑ⱼ (−1)ⁱ(−1)ʲ [∂ⱼ∂ᵢv]`. -/
theorem linBoundaryInt_linBoundaryInt_single (n : ℕ) (v : Fin (n + 1 + 1 + 1) → Y) :
    linBoundaryInt n (linBoundaryInt (n + 1) (Finsupp.single v 1))
      = ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
          ((-1 : ℤ) ^ (i : ℕ)) • (((-1 : ℤ) ^ (j : ℕ)) •
            Finsupp.single ((v ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) := by
  rw [linBoundaryInt_single, linBoundaryBasisInt, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, linBoundaryInt_single, linBoundaryBasisInt]
  rw [Finset.smul_sum]

/-- **`∂² = 0` on a single vertex-tuple** — the signed cosimplicial `Fin.succAbove` involution: the
fixed-point-free pairing `(i,j) ↦ (j.castSucc, i.pred)` / `(j.succ, i.castPred)` identifies the
double-sum terms in pairs with EQUAL `single` values and OPPOSITE signs, so the sum vanishes over ℤ. -/
theorem linBoundaryInt_linBoundaryInt_single_eq_zero (n : ℕ) (v : Fin (n + 1 + 1 + 1) → Y) :
    linBoundaryInt n (linBoundaryInt (n + 1) (Finsupp.single v 1)) = 0 := by
  rw [linBoundaryInt_linBoundaryInt_single]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    ((-1 : ℤ) ^ (p.1 : ℕ)) • (((-1 : ℤ) ^ (p.2 : ℕ)) •
      Finsupp.single ((v ∘ p.1.succAbove) ∘ p.2.succAbove) (1 : ℤ)))]
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
      have hfin : ((v ∘ i.succAbove) ∘ j.succAbove)
          = ((v ∘ (j.castSucc).succAbove) ∘ (i.pred hne).succAbove) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        rw [← Fin.succAbove_succAbove_succAbove_predAbove i j k,
          Fin.succAbove_of_castSucc_lt i j h, Fin.predAbove_of_castSucc_lt j i h]
      rw [hfin]
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
      have hfin : ((v ∘ i.succAbove) ∘ j.succAbove)
          = ((v ∘ (j.succ).succAbove) ∘ (i.castPred hne).succAbove) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        rw [← Fin.succAbove_succAbove_succAbove_predAbove i j k,
          Fin.succAbove_of_le_castSucc i j h, Fin.predAbove_of_le_castSucc j i h]
      rw [hfin]
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

/-- **`∂² = 0`** on the signed integral affine chain complex (reduced to the single-tuple case). -/
theorem linBoundaryInt_comp_linBoundaryInt (n : ℕ) :
    (linBoundaryInt n (Y := Y)).comp (linBoundaryInt (n + 1)) = 0 := by
  refine Finsupp.lhom_ext (fun v b => ?_)
  have hsingle : (Finsupp.single v b) = b • Finsupp.single v 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, hsingle, map_smul, map_smul,
    linBoundaryInt_linBoundaryInt_single_eq_zero, smul_zero]

/-- `∂² = 0` in applied form. -/
theorem linBoundaryInt_linBoundaryInt_apply (n : ℕ) (c : LinChainInt Y (n + 1 + 1)) :
    linBoundaryInt n (linBoundaryInt (n + 1) c) = 0 := by
  rw [← LinearMap.comp_apply, linBoundaryInt_comp_linBoundaryInt, LinearMap.zero_apply]

/-! ## §2. The signed cone operator `b · (−)` and its boundary formula

The cone `b · [v₀,…,vₙ] = [b, v₀, …, vₙ]` (prepend apex `b`). Its **signed** boundary formula is
`∂(b·c) = c − b·(∂c)` (for `n ≥ 1`): the `∂₀` face drops the apex giving `+[v]`; the later faces
carry the shifted sign `(−1)^{i+1}`, i.e. `−b·(∂[v])`. -/

/-- The cone of a single affine simplex on apex `b`: `b·[v] = [b,v]` (prepend `b`), integral. -/
noncomputable def coneBasisInt (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) : LinChainInt Y (n + 1) :=
  Finsupp.single (Fin.cons b v) 1

/-- The **signed cone operator** `b · (−) : LCᵢₙₜ_n(Y) → LCᵢₙₜ_{n+1}(Y)`, the ℤ-linear extension of
`[v] ↦ [b,v]`. -/
noncomputable def coneInt (b : Y) (n : ℕ) : LinChainInt Y n →ₗ[ℤ] LinChainInt Y (n + 1) :=
  Finsupp.linearCombination ℤ (coneBasisInt b n)

theorem coneInt_single (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) :
    coneInt b n (Finsupp.single v 1) = Finsupp.single (Fin.cons b v) 1 := by
  rw [coneInt, Finsupp.linearCombination_single, one_smul, coneBasisInt]

theorem coneInt_single_smul (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) (a : ℤ) :
    coneInt b n (Finsupp.single v a) = a • Finsupp.single (Fin.cons b v) 1 := by
  rw [coneInt, Finsupp.linearCombination_single, coneBasisInt]

/-- **The signed cone boundary formula** (`n ≥ 1`): `∂(b·[v]) = [v] − b·(∂[v])` over ℤ. -/
theorem linBoundaryInt_coneBasisInt (b : Y) (n : ℕ) (v : Fin (n + 1 + 1) → Y) :
    linBoundaryInt (n + 1) (coneBasisInt b (n + 1) v)
      = Finsupp.single v 1 - coneInt b n (linBoundaryInt n (Finsupp.single v 1)) := by
  rw [coneBasisInt, linBoundaryInt_single, linBoundaryBasisInt,
    Fin.sum_univ_succ (f := fun i => ((-1 : ℤ) ^ (i : ℕ)) •
      Finsupp.single ((Fin.cons b v) ∘ i.succAbove) (1 : ℤ)),
    cons_comp_zero_succAbove, linBoundaryInt_single, linBoundaryBasisInt, map_sum]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  rw [show (∑ i : Fin (n + 2), ((-1 : ℤ) ^ ((i : ℕ) + 1)) •
        Finsupp.single ((Fin.cons b v) ∘ (i.succ).succAbove) (1 : ℤ))
      = - (∑ i : Fin (n + 2), coneInt b n (((-1 : ℤ) ^ (i : ℕ)) •
          Finsupp.single (v ∘ i.succAbove) (1 : ℤ))) from ?_]
  · abel
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, coneInt_single, cons_comp_succ_succAbove, pow_succ]
    rw [show ((-1 : ℤ) ^ (j : ℕ) * -1) = -((-1 : ℤ) ^ (j : ℕ)) by ring, neg_smul]

/-- **The signed cone boundary formula on a general chain** (`n ≥ 1`): `∂(b·c) = c − b·(∂c)`. -/
theorem linBoundaryInt_coneInt (b : Y) (n : ℕ) (c : LinChainInt Y (n + 1)) :
    linBoundaryInt (n + 1) (coneInt b (n + 1) c) = c - coneInt b n (linBoundaryInt n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]; abel
  | single v a =>
    rw [coneInt_single_smul, map_smul,
      show Finsupp.single (Fin.cons b v) (1 : ℤ) = coneBasisInt b (n + 1) v from rfl,
      linBoundaryInt_coneBasisInt, smul_sub]
    congr 1
    · rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    · rw [← map_smul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §3. The signed augmentation `ε` and the degree-0 cone formula -/

/-- The **augmentation** `ε : LCᵢₙₜ_0(Y) → ℤ`, the sum of coefficients. -/
noncomputable def linAugInt : LinChainInt Y 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

theorem linAugInt_single (w : Fin 1 → Y) (a : ℤ) : linAugInt (Finsupp.single w a) = a := by
  rw [linAugInt, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

/-- **The degree-0 cone boundary formula**: `∂(b·c) = c − (ε c)·[b]` over ℤ, where `[b]` is the
constant 0-simplex at the apex `b`. (The `∂₀` face drops the apex; the `∂₁` face is the constant `b`,
carrying sign `(−1)¹ = −1`.) -/
theorem linBoundaryInt_coneInt_zero (b : Y) (c : LinChainInt Y 0) :
    linBoundaryInt 0 (coneInt b 0 c) = c - (linAugInt c) • Finsupp.single (fun _ => b) 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, map_zero, zero_smul, sub_zero]
  | add c d hc hd => simp only [map_add, add_smul]; rw [hc, hd]; abel
  | single w a =>
    have h1 : (Fin.cons b w : Fin 2 → Y) ∘ (1 : Fin 2).succAbove = (fun _ => b) := by
      funext k
      rw [Function.comp_apply, show (1 : Fin 2).succAbove k = 0 from by fin_cases k; decide,
        Fin.cons_zero]
    rw [coneInt_single_smul, map_smul,
      show Finsupp.single (Fin.cons b w) (1 : ℤ) = coneBasisInt b 0 w from rfl, coneBasisInt,
      linBoundaryInt_single, linBoundaryBasisInt, Fin.sum_univ_two,
      cons_comp_zero_succAbove, h1, linAugInt_single]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul, smul_add,
      smul_neg, Finsupp.smul_single, smul_eq_mul, mul_one]
    abel

/-- The augmentation kills boundaries of `1`-chains (`ε ∂ = 0`): a `1`-simplex's boundary has two
faces with opposite signs, total coefficient `1 − 1 = 0` over ℤ. -/
theorem linAugInt_linBoundaryInt (c : LinChainInt Y 1) : linAugInt (linBoundaryInt 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single v a =>
    rw [linBoundaryInt_single_smul, map_smul, linBoundaryBasisInt, Fin.sum_univ_two, map_add,
      map_smul, map_smul, linAugInt_single, linAugInt_single]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
    rw [add_neg_cancel, smul_zero]

/-! ## §4. The signed barycentric subdivision `Sd`

`Sd[v₀,…,vₙ] = b_v · Sd(∂[v₀,…,vₙ])` — coning the subdivided (signed) boundary at the barycenter.
The recursion is the SAME as mod-2 (the sign lives entirely in `∂`); the chain-map property
`∂ ∘ Sd = Sd ∘ ∂` now uses the **signed** cone formula `∂(b·c) = c − b·∂c`. -/

section Subdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **signed barycentric subdivision** `Sd : LCᵢₙₜ_n(V) → LCᵢₙₜ_n(V)`, recursive:
`Sd[v] = b_v · Sd(∂[v])` (degree 0: `Sd = id`). Uses the shared `barycenter`. -/
noncomputable def linSubdivInt : (n : ℕ) → LinChainInt V n →ₗ[ℤ] LinChainInt V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ
      (fun v => coneInt (barycenter v) n (linSubdivInt n (linBoundaryInt n (Finsupp.single v 1))))

theorem linSubdivInt_zero (c : LinChainInt V 0) : linSubdivInt 0 c = c := rfl

theorem linSubdivInt_single (n : ℕ) (v : Fin (n + 1 + 1) → V) :
    linSubdivInt (n + 1) (Finsupp.single v 1)
      = coneInt (barycenter v) n (linSubdivInt n (linBoundaryInt n (Finsupp.single v 1))) := by
  rw [linSubdivInt, Finsupp.linearCombination_single, one_smul]

theorem linSubdivInt_single_smul (n : ℕ) (v : Fin (n + 1 + 1) → V) (a : ℤ) :
    linSubdivInt (n + 1) (Finsupp.single v a)
      = a • coneInt (barycenter v) n (linSubdivInt n (linBoundaryInt n (Finsupp.single v 1))) := by
  rw [linSubdivInt, Finsupp.linearCombination_single]

/-- **The subdivision is a chain map**: `∂ ∘ Sd = Sd ∘ ∂` over ℤ. Base case: the degree-0 signed cone
formula `∂(b·c) = c − (ε c)·[b]` + `ε∂ = 0`. Inductive step: the general signed cone formula
`∂(b·c) = c − b·∂c`, the IH, and `∂² = 0`. -/
theorem linBoundaryInt_linSubdivInt : ∀ (n : ℕ) (c : LinChainInt V (n + 1)),
    linBoundaryInt n (linSubdivInt (n + 1) c) = linSubdivInt n (linBoundaryInt n c)
  | 0, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [linSubdivInt_single_smul, linSubdivInt_zero, map_smul, linSubdivInt_zero,
        show (Finsupp.single v a : LinChainInt V 1) = a • Finsupp.single v 1 from by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul]
      congr 1
      rw [linBoundaryInt_coneInt_zero, linAugInt_linBoundaryInt, zero_smul, sub_zero]
  | n + 1, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [linSubdivInt_single_smul, map_smul, linBoundaryInt_coneInt, linBoundaryInt_linSubdivInt n,
        linBoundaryInt_linBoundaryInt_apply, map_zero, map_zero, sub_zero, linBoundaryInt_single,
        linBoundaryInt_single_smul, map_smul]

/-! ## §5. The signed subdivision chain homotopy `D` (`∂D + D∂ = 1 − Sd`) -/

/-- The **signed subdivision chain homotopy** `D : LCᵢₙₜ_n(V) → LCᵢₙₜ_{n+1}(V)`, recursive
`D[v] = b_v · ([v] − D(∂[v]))` (degree 0: `D = 0`). Witnesses `Sd ≃ id`. -/
noncomputable def linHomotopyInt : (n : ℕ) → LinChainInt V n →ₗ[ℤ] LinChainInt V (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ
      (fun v => coneInt (barycenter v) (n + 1)
        (Finsupp.single v 1 - linHomotopyInt n (linBoundaryInt n (Finsupp.single v 1))))

theorem linHomotopyInt_zero_map (c : LinChainInt V 0) : linHomotopyInt 0 c = 0 := rfl

theorem linHomotopyInt_single_smul (n : ℕ) (v : Fin (n + 1 + 1) → V) (a : ℤ) :
    linHomotopyInt (n + 1) (Finsupp.single v a)
      = a • coneInt (barycenter v) (n + 1)
          (Finsupp.single v 1 - linHomotopyInt n (linBoundaryInt n (Finsupp.single v 1))) := by
  rw [linHomotopyInt, Finsupp.linearCombination_single]

/-- **The chain-homotopy identity `∂D + D∂ = 1 − Sd`** over ℤ: the subdivision `Sd` is
chain-homotopic to the identity via `D`. By induction on `n`, using the signed cone formula and
`∂² = 0`. -/
theorem linBoundaryInt_linHomotopyInt : ∀ (n : ℕ) (c : LinChainInt V (n + 1)),
    linBoundaryInt (n + 1) (linHomotopyInt (n + 1) c) + linHomotopyInt n (linBoundaryInt n c)
      = c - linSubdivInt (n + 1) c
  | 0, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero, add_zero, sub_zero]
    | add c d hc hd => simp only [map_add]; rw [add_add_add_comm, hc, hd, sub_add_sub_comm]
    | single v a =>
      rw [linHomotopyInt_single_smul, linHomotopyInt_zero_map, sub_zero, linHomotopyInt_zero_map,
        add_zero, map_smul, linBoundaryInt_coneInt, linSubdivInt_single_smul, linSubdivInt_zero,
        show (Finsupp.single v a : LinChainInt V 1) = a • Finsupp.single v 1 from by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one], smul_sub]
  | n + 1, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero, add_zero, sub_zero]
    | add c d hc hd => simp only [map_add]; rw [add_add_add_comm, hc, hd, sub_add_sub_comm]
    | single v a =>
      have hIH := linBoundaryInt_linHomotopyInt n (linBoundaryInt (n + 1) (Finsupp.single v 1))
      rw [linBoundaryInt_linBoundaryInt_apply, map_zero, add_zero] at hIH
      have key : linBoundaryInt (n + 1) (Finsupp.single v 1
          - linHomotopyInt (n + 1) (linBoundaryInt (n + 1) (Finsupp.single v 1)))
          = linSubdivInt (n + 1) (linBoundaryInt (n + 1) (Finsupp.single v 1)) := by
        rw [map_sub, hIH, sub_sub_cancel]
      rw [linHomotopyInt_single_smul, map_smul, linBoundaryInt_coneInt, key,
        ← linSubdivInt_single (n + 1) v, linBoundaryInt_single_smul (n + 1) v a,
        ← linBoundaryInt_single (n + 1) v, map_smul (linHomotopyInt (n + 1)) a]
      simp only [show (Finsupp.single v a : LinChainInt V (n + 1 + 1)) = a • Finsupp.single v 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      rw [map_smul (linSubdivInt (n + 1 + 1)) a, ← smul_add, ← smul_sub]
      congr 1
      abel

end Subdivision

/-! ## §6. The convex-support submodule `chainsInInt` and its preservation lemmas

The submodule of chains supported on simplices with all vertices in a set `S`; preserved by `coneInt`
(apex in `S`), `linBoundaryInt` (faces drop vertices), and — for `S` convex — `linSubdivInt` and
`linHomotopyInt` (the new vertices are barycenters of old ones). The integral mirror of
`SingularSubdivisionConvex.chainsIn`. Uses the shared `barycenter_mem`. -/

section ChainsIn

open SKEFTHawking.SingularSubdivisionConvex (barycenter_mem)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- The submodule of integral affine `n`-chains whose every basis simplex has **all vertices in `S`**. -/
noncomputable def chainsInInt (S : Set V) (n : ℕ) : Submodule ℤ (LinChainInt V n) :=
  Submodule.span ℤ
    {c | ∃ v : Fin (n + 1) → V, (∀ j, v j ∈ S) ∧ c = Finsupp.single v 1}

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
theorem single_mem_chainsInInt {S : Set V} {n : ℕ} {v : Fin (n + 1) → V} (hv : ∀ j, v j ∈ S) :
    Finsupp.single v 1 ∈ chainsInInt S n :=
  Submodule.subset_span ⟨v, hv, rfl⟩

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- `coneInt` with apex `b ∈ S` preserves `chainsInInt S`. -/
theorem coneInt_mem_chainsInInt {S : Set V} {n : ℕ} {b : V} (hb : b ∈ S) {c : LinChainInt V n}
    (hc : c ∈ chainsInInt S n) : coneInt b n c ∈ chainsInInt S (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v, hv, rfl⟩
    rw [coneInt_single]
    refine single_mem_chainsInInt (fun j => ?_)
    exact Fin.cases hb (fun k => hv k) j
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- `linBoundaryInt` preserves `chainsInInt S`. -/
theorem linBoundaryInt_mem_chainsInInt {S : Set V} {n : ℕ} {c : LinChainInt V (n + 1)}
    (hc : c ∈ chainsInInt S (n + 1)) : linBoundaryInt n c ∈ chainsInInt S n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v, hv, rfl⟩
    rw [linBoundaryInt_single, linBoundaryBasisInt]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (single_mem_chainsInInt (fun j => ?_)))
    exact hv (i.succAbove j)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- **The barycentric subdivision stays in a convex set `S`** (integral). -/
theorem linSubdivInt_mem_chainsInInt {S : Set V} (hS : Convex ℝ S) :
    ∀ (n : ℕ) {c : LinChainInt V n}, c ∈ chainsInInt S n → linSubdivInt n c ∈ chainsInInt S n
  | 0, c, hc => by rw [linSubdivInt_zero]; exact hc
  | n + 1, c, hc => by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, hv, rfl⟩
      rw [linSubdivInt_single]
      refine coneInt_mem_chainsInInt (barycenter_mem hS hv) ?_
      exact linSubdivInt_mem_chainsInInt hS n
        (linBoundaryInt_mem_chainsInInt (single_mem_chainsInInt hv))
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- **The subdivision chain homotopy `D` stays in a convex set `S`** (integral). -/
theorem linHomotopyInt_mem_chainsInInt {S : Set V} (hS : Convex ℝ S) :
    ∀ (n : ℕ) {c : LinChainInt V n}, c ∈ chainsInInt S n → linHomotopyInt n c ∈ chainsInInt S (n + 1)
  | 0, c, hc => by rw [linHomotopyInt_zero_map]; exact Submodule.zero_mem _
  | n + 1, c, hc => by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, hv, rfl⟩
      rw [linHomotopyInt_single_smul, one_smul]
      refine coneInt_mem_chainsInInt (barycenter_mem hS hv) ?_
      refine Submodule.sub_mem _ (single_mem_chainsInInt hv) ?_
      exact linHomotopyInt_mem_chainsInInt hS n
        (linBoundaryInt_mem_chainsInInt (single_mem_chainsInInt hv))
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

end ChainsIn

end SKEFTHawking.SingularAffineChainInt
