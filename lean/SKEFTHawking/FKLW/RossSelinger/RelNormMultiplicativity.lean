/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 3 — Lemma C.19: †-decomposability over coprime factors

Ross–Selinger arXiv:1403.2975v3 **Lemma C.19**: if `ξ = αβ` with `α, β` coprime in `ℤ[√2]`,
then `ξ` is †-decomposable iff `α` and `β` are. The substantive direction takes
`s := gcd(t, α)` in `ℤ[ω]` (the new `EuclideanDomain ZOmega`) and shows `s·s† ~ α`.

**Bezout-only formalization** (no `GCDMonoid`/`normalize` plumbing):
  * `s·s† ∣ α²` (conj-transport of divisibility through the bundled `conjHom`; `α` is real);
  * `s·s† ∣ t·t† = α·β·(unit)`;
  * coprimality transports through the embedding (`IsCoprime.map` — Bezout survives ring homs),
    and `α = x·α² + y·(αβ)` kills the gcd: `s·s† ∣ α`;
  * conversely `s = t·p + α·q` (`EuclideanDomain.gcd_eq_gcd_ab`) expands
    `s·s† = p·p†·(t·t†) + α·(…)`, every term divisible by `α` (since `α ∣ t·t†`): `α ∣ s·s†`;
  * mutual divisibility between **conj-fixed** elements descends to an `ℤ[√2]`-unit
    (conj-fixed = image of `zsqrt2ToZOmega`, by coordinates), so `α ~ relNormZsqrt2 s` with an
    `ℤ[√2]`-unit — exactly `DaggerDecomposable α`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.5 (Lemmas C.18/C.19).
-/

import SKEFTHawking.FKLW.RossSelinger.RelNormSolvability

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### The bundled conjugation and conj-fixed descent -/

/-- Complex conjugation on `ℤ[ω]`, bundled as a ring homomorphism. -/
def conjHom : ZOmega →+* ZOmega where
  toFun := ZOmega.conj
  map_one' := ZOmega.conj_one
  map_mul' := ZOmega.conj_mul
  map_zero' := ZOmega.conj_zero
  map_add' := ZOmega.conj_add

@[simp] theorem conjHom_apply (z : ZOmega) : conjHom z = ZOmega.conj z := rfl

/-- Conj-fixed elements of `ℤ[ω]` are exactly the embedded `ℤ[√2]`-elements. -/
theorem exists_zsqrt2_of_conj_fixed {z : ZOmega} (h : ZOmega.conj z = z) :
    ∃ ξ : Zsqrtd 2, zsqrt2ToZOmega ξ = z := by
  refine ⟨⟨z.d, z.c⟩, ?_⟩
  have ha : -z.c = z.a := congrArg ZOmega.a h
  have hb : -z.b = z.b := congrArg ZOmega.b h
  ext
  · exact ha
  · show (0 : ℤ) = z.b
    omega
  · rfl
  · rfl

/-- The relative norm is multiplicative. -/
theorem relNormZsqrt2_mul (s t : ZOmega) :
    relNormZsqrt2 (s * t) = relNormZsqrt2 s * relNormZsqrt2 t := by
  apply zsqrt2ToZOmega_injective
  rw [map_mul, zsqrt2ToZOmega_relNormZsqrt2, zsqrt2ToZOmega_relNormZsqrt2,
    zsqrt2ToZOmega_relNormZsqrt2]
  exact ZOmega.normSq_mul s t

@[simp] theorem relNormZsqrt2_zero : relNormZsqrt2 (0 : ZOmega) = 0 := by
  apply zsqrt2ToZOmega_injective
  rw [zsqrt2ToZOmega_relNormZsqrt2, map_zero]
  exact ZOmega.normSq_zero

/-! ### The easy direction: products of †-decomposables -/

theorem DaggerDecomposable.mul {α β : Zsqrtd 2} (hα : DaggerDecomposable α)
    (hβ : DaggerDecomposable β) : DaggerDecomposable (α * β) := by
  obtain ⟨t₁, u₁, hu₁, h₁⟩ := hα
  obtain ⟨t₂, u₂, hu₂, h₂⟩ := hβ
  exact ⟨t₁ * t₂, u₁ * u₂, hu₁.mul hu₂, by rw [relNormZsqrt2_mul, ← h₁, ← h₂]; ring⟩

/-! ### The substantive direction -/

/-- **Lemma C.19, the substantive half**: if `αβ` is †-decomposable and `α, β` are coprime, then
`α` is †-decomposable — via `s = gcd(t, α)` in `ℤ[ω]` and the Bezout sandwich `s·s† ~ α`. -/
theorem DaggerDecomposable.left_of_mul {α β : Zsqrtd 2} (hco : IsCoprime α β)
    (h : DaggerDecomposable (α * β)) : DaggerDecomposable α := by
  obtain ⟨t, u, hu, heq⟩ := h
  set A : ZOmega := zsqrt2ToZOmega α with hA
  set B : ZOmega := zsqrt2ToZOmega β with hB
  have hAconj : ZOmega.conj A = A := conj_zsqrt2ToZOmega α
  have heqZ : zsqrt2ToZOmega u * ZOmega.normSq t = A * B := by
    rw [← zsqrt2ToZOmega_relNormZsqrt2 t, ← map_mul, heq, map_mul]
  -- α divides t·t† (the embedded unit is invertible)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvu : zsqrt2ToZOmega v * zsqrt2ToZOmega u = 1 := by
    rw [← map_mul, mul_comm v u, hv, map_one]
  have hnormSq_eq : ZOmega.normSq t = A * (B * zsqrt2ToZOmega v) := by
    calc ZOmega.normSq t
        = (zsqrt2ToZOmega v * zsqrt2ToZOmega u) * ZOmega.normSq t := by rw [hvu, one_mul]
      _ = zsqrt2ToZOmega v * (zsqrt2ToZOmega u * ZOmega.normSq t) := by ring
      _ = zsqrt2ToZOmega v * (A * B) := by rw [heqZ]
      _ = A * (B * zsqrt2ToZOmega v) := by ring
  have hAdvd : A ∣ ZOmega.normSq t := ⟨B * zsqrt2ToZOmega v, hnormSq_eq⟩
  -- the α = 0 edge case
  by_cases hα0 : α = 0
  · exact ⟨0, 1, isUnit_one, by rw [relNormZsqrt2_zero, mul_zero, hα0]⟩
  have hAne : A ≠ 0 := by
    rw [hA]
    intro h0
    exact hα0 (zsqrt2ToZOmega_injective (by rw [h0, map_zero]))
  -- the gcd and its relative norm d = s·s†
  set s : ZOmega := EuclideanDomain.gcd t A with hs
  have hsA : s ∣ A := EuclideanDomain.gcd_dvd_right t A
  have hsT : s ∣ t := EuclideanDomain.gcd_dvd_left t A
  set d : ZOmega := s * ZOmega.conj s with hd
  have hdconj : ZOmega.conj d = d := by
    rw [hd, ZOmega.conj_mul, ZOmega.conj_conj, mul_comm]
  -- d ∣ α²
  have hdvd1 : d ∣ A * A := by
    refine mul_dvd_mul hsA ?_
    have hc := map_dvd conjHom hsA
    simpa [hAconj] using hc
  -- d ∣ α·β  (d ∣ t·t† = normSq t, and normSq t ∣ A·B via the unit)
  have hdvd2 : d ∣ A * B := by
    have hdn : d ∣ ZOmega.normSq t := by
      have := mul_dvd_mul hsT (map_dvd conjHom hsT)
      simpa [ZOmega.normSq] using this
    have hnAB : ZOmega.normSq t ∣ A * B := ⟨zsqrt2ToZOmega u, by rw [← heqZ]; ring⟩
    exact dvd_trans hdn hnAB
  -- Bezout kill: d ∣ α
  have hcoZ : IsCoprime A B := hco.map zsqrt2ToZOmega
  obtain ⟨x, y, hxy⟩ := hcoZ
  have hdA : d ∣ A := by
    have hAeq : A = x * (A * A) + y * (A * B) := by linear_combination A * hxy.symm
    rw [hAeq]
    exact dvd_add (Dvd.dvd.mul_left hdvd1 x) (Dvd.dvd.mul_left hdvd2 y)
  -- the reverse: α ∣ d via the Bezout expansion of the gcd
  have hsd : s = t * EuclideanDomain.gcdA t A + A * EuclideanDomain.gcdB t A := by
    rw [hs]
    exact EuclideanDomain.gcd_eq_gcd_ab t A
  set p : ZOmega := EuclideanDomain.gcdA t A with hp
  set q : ZOmega := EuclideanDomain.gcdB t A with hq
  have hAd : A ∣ d := by
    have hconjs : ZOmega.conj s
        = ZOmega.conj t * ZOmega.conj p + A * ZOmega.conj q := by
      rw [hsd, ZOmega.conj_add, ZOmega.conj_mul, ZOmega.conj_mul, hAconj]
    have hexp : d = (p * ZOmega.conj p) * ZOmega.normSq t
        + A * (t * p * ZOmega.conj q + ZOmega.conj t * ZOmega.conj p * q
          + A * (q * ZOmega.conj q)) := by
      rw [hd, hconjs, hsd, ZOmega.normSq]
      ring
    rw [hexp]
    exact dvd_add (Dvd.dvd.mul_left hAdvd _) (Dvd.intro _ rfl)
  -- mutual divisibility between conj-fixed elements ⟹ ℤ[√2]-unit relation
  obtain ⟨c, hc⟩ := hdA
  obtain ⟨e, he⟩ := hAd
  have hdne : d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc
    exact hAne hc
  have hce : c * e = 1 := by
    have h1 : d * (c * e) = d * 1 := by
      rw [mul_one, ← mul_assoc, ← hc, ← he]
    exact mul_left_cancel₀ hdne h1
  have hcconj : ZOmega.conj c = c := by
    have h1 : A = d * ZOmega.conj c := by
      have h2 := congrArg ZOmega.conj hc
      rwa [hAconj, ZOmega.conj_mul, hdconj] at h2
    have h3 : d * c = d * ZOmega.conj c := by rw [← hc, ← h1]
    exact (mul_left_cancel₀ hdne h3).symm
  have heconj : ZOmega.conj e = e := by
    have h1 : d = A * ZOmega.conj e := by
      have h2 := congrArg ZOmega.conj he
      rwa [hdconj, ZOmega.conj_mul, hAconj] at h2
    have h3 : A * e = A * ZOmega.conj e := by rw [← he, ← h1]
    exact (mul_left_cancel₀ hAne h3).symm
  obtain ⟨γ, hγ⟩ := exists_zsqrt2_of_conj_fixed hcconj
  obtain ⟨ε, hε⟩ := exists_zsqrt2_of_conj_fixed heconj
  have hγε : γ * ε = 1 := by
    apply zsqrt2ToZOmega_injective
    rw [map_mul, map_one, hγ, hε, hce]
  refine ⟨s, γ, IsUnit.of_mul_eq_one ε hγε, ?_⟩
  apply zsqrt2ToZOmega_injective
  rw [map_mul, zsqrt2ToZOmega_relNormZsqrt2, hγ]
  show c * ZOmega.normSq s = A
  rw [hc, hd]
  show c * (s * ZOmega.conj s) = s * ZOmega.conj s * c
  ring

/-- The symmetric half. -/
theorem DaggerDecomposable.right_of_mul {α β : Zsqrtd 2} (hco : IsCoprime α β)
    (h : DaggerDecomposable (α * β)) : DaggerDecomposable β :=
  DaggerDecomposable.left_of_mul hco.symm (by rwa [mul_comm] at h)

/-- **Lemma C.19** (Ross–Selinger arXiv:1403.2975v3): for coprime `α, β ∈ ℤ[√2]`, the product
`αβ` is †-decomposable iff `α` and `β` both are. -/
theorem daggerDecomposable_mul_iff {α β : Zsqrtd 2} (hco : IsCoprime α β) :
    DaggerDecomposable (α * β) ↔ DaggerDecomposable α ∧ DaggerDecomposable β :=
  ⟨fun h => ⟨h.left_of_mul hco, h.right_of_mul hco⟩, fun ⟨hα, hβ⟩ => hα.mul hβ⟩

end SKEFTHawking.RossSelinger
