import Mathlib

/-!
# Phase 6o′ Wave 1a′ C2 — the Witt algebra and the Virasoro 2-cocycle

The **Witt algebra** `W = Der(ℝ[t,t⁻¹]) ≅ Vect(S¹)` — the Lie algebra of polynomial vector fields
on the circle, the vector-field factor of the horizon BMS₃ algebra `Vect(S¹) ⋉ C∞(S¹)_ab`
(C0 verdict, `Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md`).

Built directly on the intended carrier: finitely-supported functions `ℤ →₀ ℝ` with basis `Lₙ`
and bracket `[Lₘ, Lₙ] = (m − n) L_{m+n}` extended bilinearly. Mathlib naming/style for future
upstreaming (Mathlib v4.29.1 has `LieAlgebra.Extension` but no named Witt/Virasoro/BMS —
re-verified in-tree). **Jacobi is the real content** (pure index algebra, no analysis).

The **Virasoro 2-cocycle** `c(Lₘ, Lₙ) = δ_{m+n,0}·(m³ − m)/12` (the unique — up to coboundary —
central extension of `W` to the Virasoro algebra) is built as a bilinear form with its
Chevalley–Eilenberg 2-cocycle identity proved on the basis (the load-bearing index algebra). Per
the C0 verdict, NO central-charge VALUE is claimed — only the cocycle and its cocycle property.

This module exports the Witt `LieRing`/`LieAlgebra` — i.e. the `Vect(S¹)` factor — as the seam a
C3 `Vect ⋉ functions` semidirect-product build consumes.
-/

noncomputable section

namespace SKEFTHawking.Carrollian

/-! ## §1. The Witt algebra carrier -/

/-- The **Witt algebra** carrier: finitely-supported functions `ℤ →₀ ℝ`, with basis `Lₙ`. -/
def WittAlgebra : Type := ℤ →₀ ℝ

namespace WittAlgebra

instance : AddCommGroup WittAlgebra := inferInstanceAs (AddCommGroup (ℤ →₀ ℝ))
instance : Module ℝ WittAlgebra := inferInstanceAs (Module ℝ (ℤ →₀ ℝ))

/-- The basis vector field `Lₙ` (the mode `−t^{n+1} d/dt`). -/
def L (n : ℤ) : WittAlgebra := Finsupp.single n 1

/-! ## §2. The bracket -/

/-- The Witt bracket as an ℝ-bilinear map on the underlying `ℤ →₀ ℝ`, determined on the basis by
`[Lₘ, Lₙ] = (m − n) L_{m+n}` and extended bilinearly via `Finsupp.lift`. -/
def wittBracketAux : (ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) :=
  Finsupp.lift ((ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ)) ℝ ℤ
    (fun m => Finsupp.lift (ℤ →₀ ℝ) ℝ ℤ (fun n => ((m : ℝ) - n) • Finsupp.single (m + n) 1))

instance : Bracket WittAlgebra WittAlgebra where
  bracket x y := wittBracketAux x y

theorem bracket_def (x y : WittAlgebra) : ⁅x, y⁆ = wittBracketAux x y := rfl

/-- The defining bracket relation on the basis: `[Lₘ, Lₙ] = (m − n) L_{m+n}`. -/
theorem lie_L (m n : ℤ) : ⁅L m, L n⁆ = ((m : ℝ) - n) • L (m + n) := by
  rw [bracket_def]
  show wittBracketAux (Finsupp.single m 1) (Finsupp.single n 1) = _
  have hOuter : wittBracketAux (Finsupp.single m 1)
      = Finsupp.lift (ℤ →₀ ℝ) ℝ ℤ (fun n => ((m : ℝ) - n) • Finsupp.single (m + n) 1) := by
    rw [wittBracketAux, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]
  rw [hOuter, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]
  rfl

/-- The bracket on the basis, phrased directly on `wittBracketAux`. -/
theorem wittBracketAux_L (m n : ℤ) :
    wittBracketAux (L m) (L n) = ((m : ℝ) - n) • L (m + n) := lie_L m n

/-- Finsupp-typed basis bracket (keeps all scalar pull-outs in the `ℤ →₀ ℝ` module, so `map_smul`
matches). -/
theorem wittBracketAux_single (m n : ℤ) :
    wittBracketAux (Finsupp.single m (1 : ℝ)) (Finsupp.single n 1)
      = ((m : ℝ) - n) • Finsupp.single (m + n) 1 := by
  have hOuter : wittBracketAux (Finsupp.single m (1 : ℝ))
      = Finsupp.lift (ℤ →₀ ℝ) ℝ ℤ (fun n => ((m : ℝ) - n) • Finsupp.single (m + n) 1) := by
    rw [wittBracketAux, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]
  rw [hOuter, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- A general single is a scalar multiple of a basis single: `single m a = a • single m 1`. -/
theorem single_smul (m : ℤ) (a : ℝ) :
    (Finsupp.single m a : ℤ →₀ ℝ) = a • Finsupp.single m 1 := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §3. LieRing / LieAlgebra instances (Jacobi is the real content) -/

/-- **Jacobi on the basis** (single–single–single): the pure index-algebra core. The scalar
identity `(n−p)(m−n−p) = (m−n)(m+n−p) + (m−p)(n−m−p)` (that closes it via `ring`) is exactly why
the Witt bracket satisfies Jacobi. -/
theorem leibniz_single (m n p : ℤ) :
    wittBracketAux (Finsupp.single m (1 : ℝ))
        (wittBracketAux (Finsupp.single n 1) (Finsupp.single p 1))
      = wittBracketAux (wittBracketAux (Finsupp.single m 1) (Finsupp.single n 1))
          (Finsupp.single p 1)
        + wittBracketAux (Finsupp.single n 1)
            (wittBracketAux (Finsupp.single m 1) (Finsupp.single p 1)) := by
  simp only [wittBracketAux_single, map_smul, LinearMap.smul_apply, smul_smul]
  have i1 : m + (n + p) = m + n + p := by ring
  have i2 : n + (m + p) = m + n + p := by ring
  rw [i1, i2, ← add_smul]
  congr 1
  push_cast
  ring

/-- Antisymmetry `[x,y] = -[y,x]`, reduced from the basis identity by bilinearity. -/
theorem wittBracket_skew (x y : ℤ →₀ ℝ) :
    wittBracketAux x y = - wittBracketAux y x := by
  induction x using Finsupp.induction_linear generalizing y with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
    abel
  | single m a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂]
      abel
    | single n b =>
      rw [single_smul m a, single_smul n b]
      simp only [map_smul, LinearMap.smul_apply, wittBracketAux_single, smul_smul]
      rw [add_comm n m, ← neg_smul]
      congr 1
      ring

theorem wittBracket_self (x : ℤ →₀ ℝ) : wittBracketAux x x = 0 := by
  have hsum : wittBracketAux x x + wittBracketAux x x = 0 := by
    nth_rewrite 2 [wittBracket_skew x x]
    exact add_neg_cancel _
  have h2 : (2 : ℝ) • wittBracketAux x x = 0 := by rw [two_smul]; exact hsum
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- **Jacobi (Leibniz form)** — the real content, pure index algebra. -/
theorem wittBracket_leibniz (x y z : ℤ →₀ ℝ) :
    wittBracketAux x (wittBracketAux y z)
      = wittBracketAux (wittBracketAux x y) z + wittBracketAux y (wittBracketAux x z) := by
  induction x using Finsupp.induction_linear generalizing y z with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
    abel
  | single m a =>
    induction y using Finsupp.induction_linear generalizing z with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂]
      abel
    | single n b =>
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z₁ z₂ h₁ h₂ =>
        simp only [map_add, h₁, h₂]
        abel
      | single p c =>
        rw [single_smul m a, single_smul n b, single_smul p c]
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [leibniz_single]
        module

instance : LieRing WittAlgebra where
  add_lie x y z := LinearMap.congr_fun (map_add wittBracketAux x y) z
  lie_add x y z := map_add (wittBracketAux x) y z
  lie_self x := wittBracket_self x
  leibniz_lie x y z := wittBracket_leibniz x y z

instance : LieAlgebra ℝ WittAlgebra where
  lie_smul c x y := map_smul (wittBracketAux x) c y

/-! ## §4. Non-vacuity: a specific bracket value -/

/-- `[L₁, L₋₁] = 2 L₀` — a concrete, falsifiable structure constant. -/
theorem lie_L_one_neg_one : ⁅L 1, L (-1)⁆ = (2 : ℝ) • L 0 := by
  rw [lie_L]; norm_num

/-! ## §5. The Virasoro 2-cocycle -/

/-- The standard Virasoro 2-cocycle `c(Lₘ, Lₙ) = δ_{m+n,0}·(m³ − m)/12`, as an ℝ-bilinear form
on the underlying `ℤ →₀ ℝ`. -/
def wittCocycleAux : (ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.lift ((ℤ →₀ ℝ) →ₗ[ℝ] ℝ) ℝ ℤ
    (fun m => Finsupp.lift ℝ ℝ ℤ (fun n => if m + n = 0 then ((m : ℝ) ^ 3 - m) / 12 else 0))

/-- The Virasoro 2-cocycle as an ℝ-bilinear form on `WittAlgebra`. -/
def wittCocycle : WittAlgebra →ₗ[ℝ] WittAlgebra →ₗ[ℝ] ℝ := wittCocycleAux

/-- The cocycle on the basis: `c(Lₘ, Lₙ) = δ_{m+n,0}·(m³ − m)/12`. -/
theorem cocycle_L (m n : ℤ) :
    wittCocycle (L m) (L n) = if m + n = 0 then ((m : ℝ) ^ 3 - m) / 12 else 0 := by
  show wittCocycleAux (Finsupp.single m 1) (Finsupp.single n 1) = _
  have hOuter : wittCocycleAux (Finsupp.single m 1)
      = Finsupp.lift ℝ ℝ ℤ (fun n => if m + n = 0 then ((m : ℝ) ^ 3 - m) / 12 else 0) := by
    rw [wittCocycleAux, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]
  rw [hOuter, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **Antisymmetry of the cocycle**: `c(Lₘ, Lₙ) = -c(Lₙ, Lₘ)`. -/
theorem cocycle_skew (m n : ℤ) :
    wittCocycle (L m) (L n) = - wittCocycle (L n) (L m) := by
  rw [cocycle_L, cocycle_L]
  by_cases h : m + n = 0
  · rw [if_pos h, if_pos (by omega : n + m = 0)]
    have hn : n = -m := by omega
    subst hn
    push_cast
    ring
  · rw [if_neg h, if_neg (by omega : ¬ (n + m = 0))]
    ring

/-- **The Chevalley–Eilenberg 2-cocycle identity** on the basis (pure index algebra):
`c([Lₘ,Lₙ],Lₚ) + c([Lₙ,Lₚ],Lₘ) + c([Lₚ,Lₘ],Lₙ) = 0`. This is the defining property of a
Lie-algebra 2-cocycle — the obstruction whose vanishing makes `ℝ ⊕ W` (with bracket twisted by
`c`) a Lie algebra (the Virasoro central extension). -/
theorem cocycle_isCocycle (m n p : ℤ) :
    wittCocycle ⁅L m, L n⁆ (L p) + wittCocycle ⁅L n, L p⁆ (L m)
      + wittCocycle ⁅L p, L m⁆ (L n) = 0 := by
  rw [lie_L, lie_L, lie_L]
  simp only [map_smul, LinearMap.smul_apply, cocycle_L, smul_eq_mul]
  by_cases h : m + n + p = 0
  · rw [if_pos (by omega : m + n + p = 0), if_pos (by omega : n + p + m = 0),
        if_pos (by omega : p + m + n = 0)]
    have hp : p = -m - n := by omega
    subst hp
    push_cast
    ring
  · rw [if_neg (by omega : ¬ (m + n + p = 0)), if_neg (by omega : ¬ (n + p + m = 0)),
        if_neg (by omega : ¬ (p + m + n = 0))]
    ring

end WittAlgebra

end SKEFTHawking.Carrollian
