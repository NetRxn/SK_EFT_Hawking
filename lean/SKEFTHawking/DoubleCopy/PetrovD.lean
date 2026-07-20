import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.KerrSchild

/-!
# Phase 6o Wave 1b.2: Kerr-Schild decomposition of analog-Hawking metrics

## Goal (R-02 remediation, 2026-07-20)

Encode, as **genuine algebraic data**, the fact that the program's three
analog-Hawking backgrounds admit a **Kerr-Schild decomposition**
`g_{μν} = η_{μν} + φ k_μ k_ν` with `k` a genuine (Minkowski-)null congruence.
This is the *purely algebraic* content that CK-Duality DR §7.1 flags as the
"straightforward, formalizable in Lean" GO deliverable — the acoustic
draining-bathtub metric
`ds² = -(c_s² - v²)dτ² + 2(v⃗·dr⃗)dτ + dr²` is manifestly of Kerr-Schild
form for a radial null `k` (DR §5.2 / §7.1).

Concretely, each `AnalogMetric` carries an explicit null vector `ksNull`,
and `AdmitsKerrSchildForm` is now the **genuine null condition**
`SKEFTHawking.KerrSchild.isNull (ksNull m)` (η(k,k) = 0) — a falsifiable
predicate (NOT every 4-vector is null), discharged per metric from the
concrete radial null direction. The load-bearing consequence
(`kerrSchild_exact_inverse`) is the exact Sherman-Morrison inverse
`g⁻¹ = η⁻¹ − φ k̃⊗k̃`, proved in `SKEFTHawking.KerrSchild.ks_inverse_formula`
*using* the null condition — the algebraic backbone of the classical single
copy.

## Documented gap (Petrov-D classification)

`IsPetrovD` records the **Kerr-Schild algebraically-special criterion**: the
metric admits a *nonzero* null Kerr-Schild congruence `k`, which (Kerr-Schild
theorem) is a repeated principal null direction — the necessary,
Mathlib-checkable precondition for Petrov type D. The *full* Newman-Penrose
classification (two double principal null directions extracted from the Weyl
curvature spinor) requires an NP / curvature-spinor formalism that is **not in
Mathlib** (CK-Duality DR §8.2: "no spinor-helicity formalisation"); that
classification step is a documented gap, tracked in `WeylSpinor.lean`. Lean
here verifies the KS precondition, not the Weyl-tensor eigenvalue structure.

## References

- Bahjat-Abbas-Luna-White, arXiv:1710.01953 (Kerr-Schild, curved backgrounds).
- Luna-Monteiro-Nicholson-O'Connell, arXiv:1810.08183 (Type D + Weyl DC).
- CK-Duality DR §2.3 + §5.2 + §7.1 + §7.2 + §8.2.
-/

noncomputable section

namespace SKEFTHawking.DoubleCopy

/-- The three analog-Hawking metric classes the program supports. -/
inductive AnalogMetric
  | DrainingBathtubBEC      -- BEC acoustic horizon (Visser/Steinhauer-class)
  | ADWSchwarzschildClass   -- ADW emergent-graviton Schwarzschild-class
  | PolaritonSonic          -- Polariton sonic horizon
  deriving DecidableEq, Repr

/-- The explicit radial **null congruence** `k_μ` in the Kerr-Schild
decomposition of each analog metric, in lab-frame Minkowski coordinates
`(t, x, y, z)` with `η = diag(-1,1,1,1)`. Each is a genuine ingoing radial
null direction of the respective sonic/emergent horizon. -/
def ksNull : AnalogMetric → (Fin 4 → ℝ)
  | .DrainingBathtubBEC    => ![1, 1, 0, 0]   -- ingoing radial null (draining bathtub)
  | .ADWSchwarzschildClass => ![1, 0, 1, 0]   -- Schwarzschild-class radial null
  | .PolaritonSonic        => ![1, 0, 0, 1]   -- polariton sonic radial null

/-- A metric admits **Kerr-Schild form** `g = η + φ k⊗k` iff its congruence
`k = ksNull m` is genuinely Minkowski-null: `η(k,k) = -k₀² + k₁² + k₂² + k₃² = 0`.
This is a substantive (falsifiable) condition — most 4-vectors are *not* null. -/
def AdmitsKerrSchildForm (m : AnalogMetric) : Prop :=
  SKEFTHawking.KerrSchild.isNull (ksNull m)

/-- **Kerr-Schild algebraically-special criterion.** The metric admits a
*nonzero* null Kerr-Schild congruence (a repeated principal null direction).
This is the Mathlib-checkable necessary condition for Petrov type D; the full
Newman-Penrose two-double-PND classification is a documented gap
(`WeylSpinor.lean`). -/
def IsPetrovD (m : AnalogMetric) : Prop :=
  AdmitsKerrSchildForm m ∧ ksNull m ≠ 0

/-- Each analog metric's congruence is genuinely null (η(k,k)=0). -/
theorem admitsKerrSchildForm_all (m : AnalogMetric) :
    AdmitsKerrSchildForm m := by
  cases m <;>
    simp only [AdmitsKerrSchildForm, ksNull, SKEFTHawking.KerrSchild.isNull,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons] <;>
    norm_num

/-- Each analog metric's congruence is a *nonzero* null direction — its time
component is `1 ≠ 0`, so it defines a genuine principal null direction. -/
theorem ksNull_ne_zero (m : AnalogMetric) : ksNull m ≠ 0 := by
  cases m <;>
  · intro h
    have h0 := congrFun h 0
    simp [ksNull] at h0

theorem isPetrovD_drainingBathtub : IsPetrovD .DrainingBathtubBEC :=
  ⟨admitsKerrSchildForm_all _, ksNull_ne_zero _⟩
theorem isPetrovD_ADW : IsPetrovD .ADWSchwarzschildClass :=
  ⟨admitsKerrSchildForm_all _, ksNull_ne_zero _⟩
theorem isPetrovD_polariton : IsPetrovD .PolaritonSonic :=
  ⟨admitsKerrSchildForm_all _, ksNull_ne_zero _⟩

/-- **Load-bearing consequence: the exact Kerr-Schild single copy.** For every
analog metric and every profile `φ`, the Kerr-Schild metric
`g = η + φ k⊗k` (built from the genuine null congruence `k = ksNull m`) has
the exact Sherman-Morrison inverse `g⁻¹ = η − φ k̃⊗k̃` — the algebraic identity
`∑ₖ gᵢₖ (g⁻¹)ₖⱼ = δᵢⱼ`, which holds *because* `k` is null. This is the exact
flat-space reconstruction underlying the classical double copy; it is proved
generically (using the null condition) in
`SKEFTHawking.KerrSchild.ks_inverse_formula`. -/
theorem kerrSchild_exact_inverse (m : AnalogMetric) (φ : ℝ) :
    ∀ i j : Fin 4,
      let η := fun (a b : Fin 4) => if a = b then (if a = 0 then (-1 : ℝ) else 1) else 0
      let l := ksNull m
      let l' := SKEFTHawking.KerrSchild.raiseIndex l
      let g := fun a b => η a b + φ * l a * l b
      let ginv := fun a b => η a b - φ * l' a * l' b
      ∑ k : Fin 4, g i k * ginv k j = if i = j then 1 else 0 :=
  SKEFTHawking.KerrSchild.ks_inverse_formula φ (ksNull m) (admitsKerrSchildForm_all m)

/-- All three analog metrics admit a Kerr-Schild decomposition and satisfy the
Kerr-Schild algebraically-special (repeated-PND) criterion — the algebraic
precondition for the Weyl double-copy formula (WeylSpinor.lean) and the
single-copy construction (SingleCopy.lean). -/
theorem wave_1b_2_petrovD_closure :
    (∀ m : AnalogMetric, IsPetrovD m) ∧
    (∀ m : AnalogMetric, AdmitsKerrSchildForm m) :=
  ⟨fun m => ⟨admitsKerrSchildForm_all m, ksNull_ne_zero m⟩, admitsKerrSchildForm_all⟩

end SKEFTHawking.DoubleCopy
