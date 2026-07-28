/-
# Phase 5q.H — the Euclidean descent for `PlaneReduction`

`UnitCancellationEichler` reduced the whole K8b interior brick (`UnitCancellation` →
`StableNegRank16Two` → the welded `K3`'s Gram) to ONE geometry-free statement:

    PlaneReduction : ∀ α β γ δ : ℤ, ∃ γ' δ', ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ')

where `PlaneStep` is the action of the four `U ⊕ U₁` Eichler transvections on the coordinate tuple
`(α, β, γ, δ) = (f₁·w', e₁·w', f₂·w', e₂·w')`. Every step is realised by an actual isometry
(`UnitCancellationEichler.planeStep_lift`), so this file owes no geometry at all — only integers.

## The move algebra (§1)

Specialising one of the two transvection parameters to `0` collapses the four moves to clean
elementary operations. Writing them out is the whole trick:

| move | effect |
|---|---|
| `m₁ p 0` | `α ↦ α − δp`, `γ ↦ γ + pβ` |
| `m₁ 0 q` | `β ↦ β − δq`, `γ ↦ γ + qα` |
| `m₂ p 0` | `α ↦ α − γp`, `δ ↦ δ + pβ` |
| `m₂ 0 q` | `β ↦ β − γq`, `δ ↦ δ + qα` |
| `m₃ p q` | `γ ↦ γ − pβ`, `δ ↦ δ − qβ` (and `α` moves) |
| `m₄ p q` | `γ ↦ γ − pα`, `δ ↦ δ − qα` (and `β` moves) |

Two consequences drive everything below:

* **`m₁` and `m₂` subtract arbitrary multiples of `δ` resp. `γ` from `α` and `β` INDEPENDENTLY.**
  So a single move closes the problem whenever `δ` (or `γ`) divides both `α` and `β` — §2.
* **`m₃` and `m₄` reduce `γ` and `δ` modulo `β` resp. `α`, independently.** So a single move plus
  `planeReduction_zero_tail` closes it whenever `β` (or `α`) divides both `γ` and `δ` — §3.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.UnitCancellationEichler

namespace SKEFTHawking

open Relation

/-! ## §1. The elementary specialisations of the four moves -/

/-- `m₁` at `q = 0`: subtract a multiple of `δ` from `α`, paying `pβ` into `γ`. -/
theorem planeStep_m₁_left (p α β γ δ : ℤ) :
    PlaneStep (α, β, γ, δ) (α - δ * p, β, γ + p * β, δ) := by
  have h := PlaneStep.m₁ p 0 α β γ δ
  simpa using h

/-- `m₁` at `p = 0`: subtract a multiple of `δ` from `β`, paying `qα` into `γ`. -/
theorem planeStep_m₁_right (q α β γ δ : ℤ) :
    PlaneStep (α, β, γ, δ) (α, β - δ * q, γ + q * α, δ) := by
  have h := PlaneStep.m₁ 0 q α β γ δ
  simpa using h

/-- `m₂` at `q = 0`: subtract a multiple of `γ` from `α`, paying `pβ` into `δ`. -/
theorem planeStep_m₂_left (p α β γ δ : ℤ) :
    PlaneStep (α, β, γ, δ) (α - γ * p, β, γ, δ + p * β) := by
  have h := PlaneStep.m₂ p 0 α β γ δ
  simpa using h

/-- `m₂` at `p = 0`: subtract a multiple of `γ` from `β`, paying `qα` into `δ`. -/
theorem planeStep_m₂_right (q α β γ δ : ℤ) :
    PlaneStep (α, β, γ, δ) (α, β - γ * q, γ, δ + q * α) := by
  have h := PlaneStep.m₂ 0 q α β γ δ
  simpa using h

/-! ## §2. One move closes it when `γ` or `δ` divides both `α` and `β` -/

/-- **`δ ∣ α` and `δ ∣ β` ⟹ done in ONE move.** `m₁` subtracts multiples of `δ` from `α` and `β`
independently, so it zeroes both at once. -/
theorem planeReduction_of_dvd_delta {α β γ δ : ℤ} (hα : δ ∣ α) (hβ : δ ∣ β) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨a, ha⟩ := hα
  obtain ⟨b, hb⟩ := hβ
  refine ⟨γ + (a * β + b * α) - a * b * δ, δ, ReflTransGen.single ?_⟩
  have h := PlaneStep.m₁ a b α β γ δ
  rwa [show α - δ * a = 0 by rw [ha]; ring, show β - δ * b = 0 by rw [hb]; ring] at h

/-- **`γ ∣ α` and `γ ∣ β` ⟹ done in ONE move**, the `m₂` twin of the previous lemma. -/
theorem planeReduction_of_dvd_gamma {α β γ δ : ℤ} (hα : γ ∣ α) (hβ : γ ∣ β) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨a, ha⟩ := hα
  obtain ⟨b, hb⟩ := hβ
  refine ⟨γ, δ + (a * β + b * α) - a * b * γ, ReflTransGen.single ?_⟩
  have h := PlaneStep.m₂ a b α β γ δ
  rwa [show α - γ * a = 0 by rw [ha]; ring, show β - γ * b = 0 by rw [hb]; ring] at h

/-! ## §3. One move plus the zero tail, when `β` or `α` divides both `γ` and `δ` -/

/-- **`β ∣ γ` and `β ∣ δ` ⟹ `m₃` lands on the zero tail.** `m₃` reduces `γ` and `δ` modulo `β`
independently, so it zeroes both; `planeReduction_zero_tail` then finishes. -/
theorem planeReduction_of_dvd_beta {α β γ δ : ℤ} (hγ : β ∣ γ) (hδ : β ∣ δ) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨c, hc⟩ := hγ
  obtain ⟨d, hd⟩ := hδ
  have h := PlaneStep.m₃ c d α β γ δ
  rw [show γ - c * β = 0 by rw [hc]; ring, show δ - d * β = 0 by rw [hd]; ring] at h
  obtain ⟨γ', δ', hchain⟩ :=
    planeReduction_zero_tail (α + (c * δ + d * γ) - c * d * β) β
  exact ⟨γ', δ', (ReflTransGen.single h).trans hchain⟩

/-- **`α ∣ γ` and `α ∣ δ` ⟹ `m₄` lands on the zero tail**, the mirror of the previous lemma under
the `α ↔ β` symmetry of the move set. -/
theorem planeReduction_of_dvd_alpha {α β γ δ : ℤ} (hγ : α ∣ γ) (hδ : α ∣ δ) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨c, hc⟩ := hγ
  obtain ⟨d, hd⟩ := hδ
  have h := PlaneStep.m₄ c d α β γ δ
  rw [show γ - c * α = 0 by rw [hc]; ring, show δ - d * α = 0 by rw [hd]; ring] at h
  obtain ⟨γ', δ', hchain⟩ :=
    planeReduction_zero_tail α (β + (c * δ + d * γ) - c * d * α)
  exact ⟨γ', δ', (ReflTransGen.single h).trans hchain⟩

/-! ## §4. The `gcd` closers on the two axes

At `β = 0` the moves `m₁ p 0` and `m₂ p 0` subtract multiples of `δ` resp. `γ` from `α` while
leaving **all three** of `β, γ, δ` fixed (the `pβ` payments vanish). So on that axis `α` is free to
move through `α + (γ, δ)ℤ`, and Bézout zeroes it as soon as `gcd(γ, δ) ∣ α`. This is strictly
stronger than §2 there, which needs `γ` or `δ` to divide `α` on its own. -/

/-- **On the `β = 0` axis, `gcd(γ, δ) ∣ α` closes it in two moves.** -/
theorem planeReduction_of_beta_zero {α γ δ : ℤ} (h : (Int.gcd γ δ : ℤ) ∣ α) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, 0, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨k, hk⟩ := h
  refine ⟨γ, δ, ?_⟩
  have h1 : PlaneStep (α, 0, γ, δ) (α - γ * (Int.gcdA γ δ * k), 0, γ, δ) := by
    have h := planeStep_m₂_left (Int.gcdA γ δ * k) α 0 γ δ
    simpa using h
  have h2 : PlaneStep (α - γ * (Int.gcdA γ δ * k), 0, γ, δ)
      (α - γ * (Int.gcdA γ δ * k) - δ * (Int.gcdB γ δ * k), 0, γ, δ) := by
    have h := planeStep_m₁_left (Int.gcdB γ δ * k) (α - γ * (Int.gcdA γ δ * k)) 0 γ δ
    simpa using h
  have hzero : α - γ * (Int.gcdA γ δ * k) - δ * (Int.gcdB γ δ * k) = 0 := by
    have hb : (Int.gcd γ δ : ℤ) = γ * Int.gcdA γ δ + δ * Int.gcdB γ δ := Int.gcd_eq_gcd_ab γ δ
    rw [hk, hb]; ring
  rw [hzero] at h2
  exact (ReflTransGen.single h1).tail h2

/-- **On the `α = 0` axis, `gcd(γ, δ) ∣ β` closes it in one move** — `m₄` at `α = 0` shifts `β` by
`pδ + qγ` with `γ` and `δ` untouched, so a single Bézout choice suffices. -/
theorem planeReduction_of_alpha_zero {β γ δ : ℤ} (h : (Int.gcd γ δ : ℤ) ∣ β) :
    ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (0, β, γ, δ) (0, 0, γ', δ') := by
  obtain ⟨k, hk⟩ := h
  refine ⟨γ, δ, ReflTransGen.single ?_⟩
  have h := PlaneStep.m₄ (-(Int.gcdB γ δ * k)) (-(Int.gcdA γ δ * k)) 0 β γ δ
  have hzero : β + ((-(Int.gcdB γ δ * k)) * δ + (-(Int.gcdA γ δ * k)) * γ)
      - (-(Int.gcdB γ δ * k)) * (-(Int.gcdA γ δ * k)) * 0 = 0 := by
    have hb : (Int.gcd γ δ : ℤ) = γ * Int.gcdA γ δ + δ * Int.gcdB γ δ := Int.gcd_eq_gcd_ab γ δ
    rw [hk, hb]; ring
  rw [hzero] at h
  simpa using h

/-! ## §5. The descent on `|β|`

`m₃` reduces `γ` and `δ` modulo `β` in one move; if both remainders vanish we are on the zero tail,
and otherwise a nonzero remainder `r` with `|r| < |β|` is available to reduce `β` modulo `r` by
`m₂ 0 _` (resp. `m₁ 0 _`), so `|β|` strictly drops. Iterating lands on the `β = 0` axis. -/

/-- `|a % b| < |b|` for `b ≠ 0`, in the `natAbs` form the descent measure needs. -/
theorem natAbs_emod_lt_natAbs {a b : ℤ} (hb : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  have h0 : 0 ≤ a % b := Int.emod_nonneg a hb
  have h1 : a % b < |b| := Int.emod_lt_abs a hb
  have h2 : |b| = (b.natAbs : ℤ) := Int.abs_eq_natAbs b
  omega

/-- **THE DESCENT.** `PlaneReduction` follows from its own restriction to the `β = 0` axis.

This is the whole 4-parameter statement reduced to a 3-parameter one: given that every tuple of the
shape `(α, 0, γ, δ)` reduces, so does every tuple. The induction is on `β.natAbs`; each round is one
`m₃` (reducing `γ, δ` modulo `β`) followed by one `m₂ 0 _` or `m₁ 0 _` (reducing `β` modulo the
surviving remainder), and the zero-remainder case lands on `planeReduction_zero_tail`. -/
theorem planeReduction_of_axis
    (haxis : ∀ a c d : ℤ, ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (a, 0, c, d) (0, 0, γ', δ')) :
    PlaneReduction := by
  have key : ∀ n : ℕ, ∀ α β γ δ : ℤ, β.natAbs ≤ n →
      ∃ γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ') := by
    intro n
    induction n with
    | zero =>
      intro α β γ δ hle
      have hβ : β = 0 := by
        have : β.natAbs = 0 := Nat.le_zero.mp hle
        exact Int.natAbs_eq_zero.mp this
      subst hβ; exact haxis α γ δ
    | succ n ih =>
      intro α β γ δ hle
      by_cases hβ : β = 0
      · subst hβ; exact haxis α γ δ
      · -- one `m₃`: reduce `γ` and `δ` modulo `β`
        set p : ℤ := γ / β with hp
        set q : ℤ := δ / β with hq
        set α₁ : ℤ := α + (p * δ + q * γ) - p * q * β with hα₁
        have hstep3 : PlaneStep (α, β, γ, δ) (α₁, β, γ % β, δ % β) := by
          have h := PlaneStep.m₃ p q α β γ δ
          rwa [show γ - p * β = γ % β by rw [hp, Int.emod_def]; ring,
            show δ - q * β = δ % β by rw [hq, Int.emod_def]; ring] at h
        by_cases hr1 : γ % β = 0
        · by_cases hr2 : δ % β = 0
          · -- both remainders vanish: the zero tail
            rw [hr1, hr2] at hstep3
            obtain ⟨γ', δ', hchain⟩ := planeReduction_zero_tail α₁ β
            exact ⟨γ', δ', (ReflTransGen.single hstep3).trans hchain⟩
          · -- reduce `β` modulo `δ % β` with `m₁ 0 _`
            have hstep1 : PlaneStep (α₁, β, γ % β, δ % β)
                (α₁, β - (δ % β) * (β / (δ % β)), γ % β + (β / (δ % β)) * α₁, δ % β) :=
              planeStep_m₁_right (β / (δ % β)) α₁ β (γ % β) (δ % β)
            have hmod : β - (δ % β) * (β / (δ % β)) = β % (δ % β) :=
              (Int.emod_def β (δ % β)).symm
            rw [hmod] at hstep1
            have hlt : (β % (δ % β)).natAbs < β.natAbs :=
              lt_trans (natAbs_emod_lt_natAbs hr2) (natAbs_emod_lt_natAbs hβ)
            obtain ⟨γ', δ', hchain⟩ :=
              ih α₁ (β % (δ % β)) (γ % β + (β / (δ % β)) * α₁) (δ % β) (by omega)
            exact ⟨γ', δ',
              ((ReflTransGen.single hstep3).tail hstep1).trans hchain⟩
        · -- reduce `β` modulo `γ % β` with `m₂ 0 _`
          have hstep2 : PlaneStep (α₁, β, γ % β, δ % β)
              (α₁, β - (γ % β) * (β / (γ % β)), γ % β, δ % β + (β / (γ % β)) * α₁) :=
            planeStep_m₂_right (β / (γ % β)) α₁ β (γ % β) (δ % β)
          have hmod : β - (γ % β) * (β / (γ % β)) = β % (γ % β) :=
            (Int.emod_def β (γ % β)).symm
          rw [hmod] at hstep2
          have hlt : (β % (γ % β)).natAbs < β.natAbs :=
            lt_trans (natAbs_emod_lt_natAbs hr1) (natAbs_emod_lt_natAbs hβ)
          obtain ⟨γ', δ', hchain⟩ :=
            ih α₁ (β % (γ % β)) (γ % β) (δ % β + (β / (γ % β)) * α₁) (by omega)
          exact ⟨γ', δ',
            ((ReflTransGen.single hstep3).tail hstep2).trans hchain⟩
  intro α β γ δ
  exact key β.natAbs α β γ δ le_rfl

end SKEFTHawking
