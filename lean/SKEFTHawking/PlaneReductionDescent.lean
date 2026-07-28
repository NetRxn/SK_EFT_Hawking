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

/-! ## §6. The two axis moves, and why `gcd(γ, δ)` is the axis measure

§5 leaves exactly the `β = 0` axis. There `γ` and `δ` are frozen by every move that fixes `β`, so
the only thing that happens is that `α` slides through its coset of the ideal `(γ, δ)` — that is
§4's `planeReduction_of_beta_zero`, which closes the axis when `gcd(γ, δ) ∣ α`.

When it does not, the axis must be left, and `m₄` is the only move that leaves it. The two lemmas
here are the two halves of one round trip, and together they say what the round trip BUYS:
`α` first drops below `e := gcd(γ, δ)` (`planeReduction_axis_shift`), and then one `m₄` drops both
`γ` and `δ` below that same `α` (`planeReduction_axis_escape`) — so the new `gcd(γ, δ)` is
strictly smaller than the old one. `gcd(γ, δ)` is therefore the axis-visit measure. -/

/-- **Sliding `α` along the ideal, on the axis.** For any `k` divisible by `gcd(γ, δ)`, one `m₃`
move sends `(α, 0, γ, δ)` to `(α - k, 0, γ, δ)` — `β`, `γ` and `δ` are all untouched, because at
`β = 0` every payment `m₃` makes into `γ` and `δ` is a multiple of `β`. -/
theorem planeReduction_axis_shift (α γ δ k : ℤ) (h : (Int.gcd γ δ : ℤ) ∣ k) :
    ReflTransGen PlaneStep (α, 0, γ, δ) (α - k, 0, γ, δ) := by
  obtain ⟨m, hm⟩ := h
  refine ReflTransGen.single ?_
  have h := PlaneStep.m₃ (-(Int.gcdB γ δ * m)) (-(Int.gcdA γ δ * m)) α 0 γ δ
  have hval : α + ((-(Int.gcdB γ δ * m)) * δ + (-(Int.gcdA γ δ * m)) * γ)
      - (-(Int.gcdB γ δ * m)) * (-(Int.gcdA γ δ * m)) * 0 = α - k := by
    have hb : (Int.gcd γ δ : ℤ) = γ * Int.gcdA γ δ + δ * Int.gcdB γ δ := Int.gcd_eq_gcd_ab γ δ
    rw [hm, hb]; ring
  rw [hval] at h
  simpa using h

/-- **On the axis, `α` may be taken below `gcd(γ, δ)`.** The `emod` normal form of the slide. -/
theorem planeReduction_axis_normalize (α γ δ : ℤ) :
    ReflTransGen PlaneStep (α, 0, γ, δ) (α % (Int.gcd γ δ : ℤ), 0, γ, δ) := by
  have h : (Int.gcd γ δ : ℤ) ∣ (α - α % (Int.gcd γ δ : ℤ)) := by
    rw [Int.emod_def]; exact ⟨α / (Int.gcd γ δ : ℤ), by ring⟩
  have := planeReduction_axis_shift α γ δ (α - α % (Int.gcd γ δ : ℤ)) h
  simpa using this

/-- **Leaving the axis buys a strictly smaller `gcd(γ, δ)`.** One `m₄` reduces `γ` and `δ` modulo
`α` simultaneously (they are independent), at the cost of `β` becoming nonzero — `m₄` is the only
move that can leave the axis at all, since every other one fixes `β = 0`.

Paired with `planeReduction_axis_normalize`, which first puts `0 ≤ α < e := gcd(γ, δ)`, the new
`γ` and `δ` both land strictly below `α`, hence strictly below `e`. So each axis visit strictly
decreases `gcd(γ, δ)`, which is what makes the axis lane well-founded. -/
theorem planeReduction_axis_escape (α γ δ : ℤ) :
    ReflTransGen PlaneStep (α, 0, γ, δ)
      (α, (γ / α) * δ + (δ / α) * γ - (γ / α) * (δ / α) * α, γ % α, δ % α) := by
  refine ReflTransGen.single ?_
  have h := PlaneStep.m₄ (γ / α) (δ / α) α 0 γ δ
  rwa [show γ - (γ / α) * α = γ % α by rw [Int.emod_def]; ring,
    show δ - (δ / α) * α = δ % α by rw [Int.emod_def]; ring, zero_add] at h

/-- **The axis measure, made explicit.** After normalising `α` below `e := gcd(γ, δ)` and then
escaping, both new plane-2 coordinates are `< α < e`, so the new `gcd` is `< e`. Stated on `natAbs`
because that is the form a well-founded recursion consumes. -/
theorem natAbs_gcd_lt_of_axis_round {α γ δ : ℤ}
    (hγ : (γ % α).natAbs < α.natAbs) (hδ : (δ % α).natAbs < α.natAbs) :
    Int.gcd (γ % α) (δ % α) < α.natAbs := by
  rcases eq_or_ne (γ % α) 0 with h | h
  · simpa [h, Int.gcd] using hδ
  · exact lt_of_le_of_lt (Nat.le_of_dvd (Int.natAbs_pos.mpr h)
      (Nat.gcd_dvd_left (γ % α).natAbs (δ % α).natAbs)) hγ

/-! ## §5b. ONE DESCENT ROUND, WITH THE PLANE-2 BOUND

§5's induction throws away everything about `γ` and `δ`. The interleaving with §6b's axis measure
needs one more fact about a round, and it comes from a feature of the moves that is easy to miss:

**the `β`-reducing step leaves one plane-2 coordinate completely alone.** `m₂ 0 _` reduces `β`
modulo `γ` and pays into `δ` — but `γ` itself is untouched; `m₁ 0 _` is the mirror, paying into `γ`
and leaving `δ`. So whichever coordinate served as the modulus survives the round verbatim, and the
new `gcd(γ, δ)` **divides** it. Since the preceding `m₃` had already put both plane-2 coordinates
below `|β|`, the round's output gcd is bounded by them — even though the *other* coordinate may have
grown by a multiple of `α`. -/

/-- **One descent round, carrying the plane-2 bound.** Either the round lands on the zero tail, or it
strictly drops `|β|` *and* bounds the new `gcd(γ, δ)` by the `m₃`-reduced coordinates. -/
theorem descent_round {α β γ δ : ℤ} (hβ : β ≠ 0) :
    (∃ a : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (a, β, 0, 0)) ∨
    (∃ α' β' γ' δ' : ℤ, ReflTransGen PlaneStep (α, β, γ, δ) (α', β', γ', δ') ∧
      β'.natAbs < β.natAbs ∧
      Int.gcd γ' δ' ≤ max (γ % β).natAbs (δ % β).natAbs) := by
  set p : ℤ := γ / β with hp
  set q : ℤ := δ / β with hq
  set α₁ : ℤ := α + (p * δ + q * γ) - p * q * β with hα₁
  have hstep3 : PlaneStep (α, β, γ, δ) (α₁, β, γ % β, δ % β) := by
    have h := PlaneStep.m₃ p q α β γ δ
    rwa [show γ - p * β = γ % β by rw [hp, Int.emod_def]; ring,
      show δ - q * β = δ % β by rw [hq, Int.emod_def]; ring] at h
  by_cases hr1 : γ % β = 0
  · by_cases hr2 : δ % β = 0
    · refine Or.inl ⟨α₁, ?_⟩
      rw [hr1, hr2] at hstep3
      exact ReflTransGen.single hstep3
    · -- `m₁ 0 _` : `δ` is the modulus and survives untouched
      refine Or.inr ⟨α₁, β % (δ % β), γ % β + (β / (δ % β)) * α₁, δ % β, ?_, ?_, ?_⟩
      · have hstep1 := planeStep_m₁_right (β / (δ % β)) α₁ β (γ % β) (δ % β)
        rw [show β - (δ % β) * (β / (δ % β)) = β % (δ % β) from (Int.emod_def β (δ % β)).symm]
          at hstep1
        exact (ReflTransGen.single hstep3).tail hstep1
      · exact lt_trans (natAbs_emod_lt_natAbs hr2) (natAbs_emod_lt_natAbs hβ)
      · exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hr2)
          (Nat.gcd_dvd_right _ (δ % β).natAbs)) (le_max_right _ _)
  · -- `m₂ 0 _` : `γ` is the modulus and survives untouched
    refine Or.inr ⟨α₁, β % (γ % β), γ % β, δ % β + (β / (γ % β)) * α₁, ?_, ?_, ?_⟩
    · have hstep2 := planeStep_m₂_right (β / (γ % β)) α₁ β (γ % β) (δ % β)
      rw [show β - (γ % β) * (β / (γ % β)) = β % (γ % β) from (Int.emod_def β (γ % β)).symm]
        at hstep2
      exact (ReflTransGen.single hstep3).tail hstep2
    · exact lt_trans (natAbs_emod_lt_natAbs hr1) (natAbs_emod_lt_natAbs hβ)
    · exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hr1)
        (Nat.gcd_dvd_left (γ % β).natAbs _)) (le_max_left _ _)

/-! ## §6b. THE AXIS ROUND — one visit strictly drops `gcd(γ, δ)` -/

/-- **THE AXIS ROUND.** From an axis state whose `gcd(γ, δ) =: e` is positive and does **not** divide
`α` — precisely the case `planeReduction_of_beta_zero` cannot close — there is a chain to a state
with strictly smaller `gcd(γ, δ)`.

Two moves: `planeReduction_axis_normalize` puts `α` into `(0, e)` (it is nonzero exactly because
`e ∤ α`), then `planeReduction_axis_escape` reduces `γ` and `δ` modulo that `α`, so both land below
`α < e`.

Since `gcd(α, β, γ, δ)` is invariant and divides `gcd(γ, δ)`, the sequence of axis-visit gcds is
strictly decreasing and bounded below by it — and at the bottom the gcd divides `α`, so the axis
closes. That is the termination argument for the axis lane. -/
theorem planeReduction_axis_round {α γ δ : ℤ} (he : 0 < Int.gcd γ δ)
    (hnd : ¬ ((Int.gcd γ δ : ℤ) ∣ α)) :
    ∃ α' β' γ' δ' : ℤ, ReflTransGen PlaneStep (α, 0, γ, δ) (α', β', γ', δ') ∧
      Int.gcd γ' δ' < Int.gcd γ δ := by
  have hepos : (0 : ℤ) < (Int.gcd γ δ : ℤ) := by exact_mod_cast he
  set a : ℤ := α % (Int.gcd γ δ : ℤ) with hadef
  have ha0 : 0 ≤ a := Int.emod_nonneg α (ne_of_gt hepos)
  have halt : a < (Int.gcd γ δ : ℤ) := Int.emod_lt_of_pos α hepos
  have hane : a ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero (hadef ▸ h))
  refine ⟨a, (γ / a) * δ + (δ / a) * γ - (γ / a) * (δ / a) * a, γ % a, δ % a,
    (planeReduction_axis_normalize α γ δ).trans (planeReduction_axis_escape a γ δ), ?_⟩
  have h3 : Int.gcd (γ % a) (δ % a) < a.natAbs :=
    natAbs_gcd_lt_of_axis_round (natAbs_emod_lt_natAbs hane) (natAbs_emod_lt_natAbs hane)
  have h4 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha0
  omega

/-! ## §7. THE CONSERVED QUANTITY

`N (α, β, γ, δ) := αβ + γδ` is invariant under **all four** moves. This is not a coincidence of the
formulas: the tuple is the list of pairings of `w'` with `e₁, f₁, e₂, f₂`, the form on `U ⊕ U₁` is
hyperbolic, and every `PlaneStep` is realised by an isometry
(`UnitCancellationEichler.planeStep_lift`) — so `2N` is the norm of `w'`'s `U ⊕ U₁` component and
has to be preserved. The formulas simply confirm it.

Two consequences worth having explicitly:

* it gives the system a genuine invariant, so no proof of `PlaneReduction` can move `N`;
* it pins the **endpoint**: reaching `(0, 0, γ', δ')` forces `γ' δ' = N`. So `PlaneReduction` is
  implicitly the assertion that `N` always admits a factorisation reachable by the moves — a real
  constraint, and the reason the naive "drive everything to zero" reading of the statement is wrong
  (the plane-2 coordinates cannot both be sent to `0` unless `N = 0`). -/

/-- The conserved quantity of the `PlaneStep` system: `αβ + γδ`, i.e. half the norm of `w'`'s
`U ⊕ U₁` component. -/
def planeNorm (t : ℤ × ℤ × ℤ × ℤ) : ℤ := t.1 * t.2.1 + t.2.2.1 * t.2.2.2

/-- **Every Eichler move preserves `αβ + γδ`.** Checked on all four constructors; in each case the
four cross terms cancel identically. -/
theorem planeStep_planeNorm {t t' : ℤ × ℤ × ℤ × ℤ} (h : PlaneStep t t') :
    planeNorm t' = planeNorm t := by
  cases h <;> simp only [planeNorm] <;> ring

/-- **…hence so does every chain.** -/
theorem planeChain_planeNorm {t t' : ℤ × ℤ × ℤ × ℤ} (h : ReflTransGen PlaneStep t t') :
    planeNorm t' = planeNorm t := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [planeStep_planeNorm hstep, ih]

/-- **THE ENDPOINT CONSTRAINT.** If `(α, β, γ, δ)` reduces to `(0, 0, γ', δ')` then
`γ' δ' = αβ + γδ`. So the plane-2 coordinates of any endpoint multiply to the conserved quantity —
in particular they can *both* vanish only when `αβ + γδ = 0`, which is why
`planeReduction_zero_tail` has to return a nonzero `γ'` in general. -/
theorem mul_eq_planeNorm_of_reduces {α β γ δ γ' δ' : ℤ}
    (h : ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ')) : γ' * δ' = α * β + γ * δ := by
  have := planeChain_planeNorm h
  simpa [planeNorm] using this

/-- **The `m₃` α-killing identity.** Choosing `m₃ p q` so that it sends `α` to `0` is *exactly*
choosing a factorisation of the conserved quantity: the two new plane-2 coordinates multiply to it.

This is the shape any two-move close must take — kill `α` with one `m₃`, then close on the `α = 0`
axis with `planeReduction_of_alpha_zero`, which needs `gcd(γ', δ') ∣ β`. So the remaining question
is sharply arithmetic: *which* factorisations of `αβ + γδ` are reachable, and can one be chosen with
`gcd` dividing `β`. -/
theorem mul_eq_planeNorm_of_alpha_kill {α β γ δ p q : ℤ}
    (h : α + (p * δ + q * γ) - p * q * β = 0) :
    (γ - p * β) * (δ - q * β) = α * β + γ * δ := by
  have hα : α = p * q * β - p * δ - q * γ := by linarith
  rw [hα]; ring

end SKEFTHawking
