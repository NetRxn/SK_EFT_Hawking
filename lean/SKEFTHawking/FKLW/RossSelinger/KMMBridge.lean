/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge (native_decide core)

The MA coverage recursion (`MACoverage.lean`) consumes the bridge

  `bridge : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → kSO3 M ≤ 3`

— the quantitative `sde ↔ k_SO3` relationship of Giles-Selinger Cor 7.11 — as
one of its two remaining hypotheses (the other is the Clifford base). This file
ships the finite computational core of the bridge.

## The M-structure reduction

By `column0_cleared_bounded`, a `μ(M) ≤ 3` unitary clears column 0 at exponent
`2`: `√2²·M₀₀ = of x`, `√2²·M₁₀ = of y` with `(|x|²).d ≤ 4`, `(|y|²).d ≤ 4`
(so each `ℤ[ω]` coordinate of `x, y` is bounded by `2`). By `realizable_col1`,
column 1 is determined: `M₀₁ = -(ωᵏ·conj M₁₀)`, `M₁₁ = ωᵏ·conj M₀₀`. Hence

  `M = reconstruct x y k = !![mk x 2, -(ωᵏ·conj (mk y 2)); mk y 2, ωᵏ·conj (mk x 2)]`.

So `kSO3 M = kSO3 (reconstruct x y k)`, a function of the *bounded integer data*
`(x, y, k)`. The unitarity forces `|x|² + |y|² = 2² = ⟨0,0,0,4⟩` (column-0 norm,
scaled by `√2⁴`), and `μ ≤ 3` is exactly `√2 ∣ |x|²` (`= gde(|x|²) ≥ 1`, since
`μ = denExp(|M₀₀|²) = 4 − gde(|x|²)`).

## The finite check

`bridgeBoxOk` ranges `(x, y)` over the explicit `5⁴`-coordinate box `[-2,2]⁴`,
filters to the necessary conditions `|x|² + |y|² = ⟨0,0,0,4⟩` and
`dividesSqrt2 |x|²`, and over `k ∈ {0,…,7}` checks `kSO3 (reconstruct x y k) ≤ 3`.

  * **Validated** (`scripts/bridge_superset_validation.py`, 2026-05-29): the
    filtered box is *exactly* the `1664` realizable `μ ≤ 3` matrices (208 `(x,y)`
    pairs × 8 phases); `max kSO3 = 3`; `0` failures. (Without the `dividesSqrt2`
    filter the superset leaks 512 `μ = 4` tuples with `kSO3 = 4` — the filter is
    the exact `μ ≤ 3` condition, not slack.)

`bridge_box_core : bridgeBoxOk = true` is `native_decide` (the `1664`-tuple
check; the unfiltered `5⁴ × 5⁴` pairs are cheap, `kSO3` runs only on the `1664`
that pass). The connecting lemmas (`M = reconstruct x y k`, coordinate bounds,
`List.all` extraction) and the abstract `bridge` theorem follow in a companion
increment, mirroring the `ma_step` core → `ma_step_exists` split.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — Cor 7.11 (`sde ↔ k_SO3`).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) — Theorem 1 (column structure).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `native_decide`).
- **#15** (no new project-local axioms): respected (`native_decide` carries the
  tracked `Lean.ofReduceBool` axiom, allowed alongside the kernel three).

-/

import SKEFTHawking.FKLW.RossSelinger.BlochMap
import SKEFTHawking.FKLW.RossSelinger.KMMForm
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2
import SKEFTHawking.FKLW.RossSelinger.KMMBaseCoverage
import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
import SKEFTHawking.FKLW.RossSelinger.UnitColumnCongruence

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **The KMM Theorem 1 reconstruction** of a realizable `μ ≤ 3` matrix from its
column-0 `ℤ[ω]` numerators `x, y` (cleared at exponent `2`) and the global phase
`k`: column 1 is `column-0`-determined (`realizable_col1`). -/
def reconstruct (x y : ZOmega) (k : ℕ) : Mat2 :=
  !![mk x 2, -(ωS ^ k * conj (mk y 2)); mk y 2, ωS ^ k * conj (mk x 2)]

/-- The explicit coordinate range `[-2, 2]` for each `ℤ[ω]` component (the
`(|x|²).d ≤ 4` sum-of-squares bound forces `|coord| ≤ 2`). -/
def intBox : List ℤ := [-2, -1, 0, 1, 2]

/-- The explicit `5⁴ = 625`-element `ℤ[ω]` box `[-2, 2]⁴`. -/
def zomBox : List ZOmega :=
  intBox.flatMap (fun a => intBox.flatMap (fun b =>
    intBox.flatMap (fun c => intBox.map (fun d => ⟨a, b, c, d⟩))))

/-- **The finite bridge check**: over the `ℤ[ω]` box, for every `(x, y)` meeting
the unitarity necessary condition `|x|² + |y|² = ⟨0,0,0,4⟩` and the `μ ≤ 3`
condition `√2 ∣ |x|²`, and every phase `k ∈ {0,…,7}`, the reconstructed matrix
has `kSO3 ≤ 3`. -/
def bridgeBoxOk : Bool :=
  zomBox.all (fun x => zomBox.all (fun y =>
    if ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega)
        ∧ ZOmega.dividesSqrt2 (ZOmega.normSq x)
    then (List.range 8).all (fun k => kSO3 (reconstruct x y k) ≤ 3)
    else true))

set_option maxRecDepth 8000 in
/-- **The bridge native_decide core**: the `1664`-tuple finite check passes.
`kSO3 (reconstruct x y k) ≤ 3` for every `(x, y, k)` in the filtered box (= the
`μ ≤ 3` realizable matrices). Validated `0`-failure in
`scripts/bridge_superset_validation.py`. -/
theorem bridge_box_core : bridgeBoxOk = true := by native_decide

/-! ## Connecting lemmas: from the abstract `M` to the box -/

/-- **`√2` is a unit, so column clearing inverts**: `√2^k · z = of w ⟹ z = mk w k`. -/
theorem eq_mk_of_sqrt2_pow_mul {z : ZOmegaSqrt2} {w : ZOmega} {k : ℕ}
    (h : (sqrt2 : ZOmegaSqrt2) ^ k * z = of w) : z = mk w k := by
  have hunit : mk (1 : ZOmega) k * (sqrt2 : ZOmegaSqrt2) ^ k = 1 := by
    rw [sqrt2_pow_eq, mk_mul, one_def, mk_eq_mk_iff]; ring
  calc z = mk (1 : ZOmega) k * ((sqrt2 : ZOmegaSqrt2) ^ k * z) := by
            rw [← mul_assoc, hunit, one_mul]
    _ = mk (1 : ZOmega) k * of w := by rw [h]
    _ = mk w k := by rw [of_def, mk_mul, one_mul, Nat.add_zero]

/-- `of` is injective (`√2` non-zero-divisor at exponent 0). -/
theorem of_inj : Function.Injective ZOmegaSqrt2.of := fun _ _ h => by
  rwa [of_def, of_def, mk_eq_mk_iff, pow_zero, mul_one, mul_one] at h

/-- `ωS^8 = 1` (`ω^8 = 1` in `ℤ[ω]`, `decide`; `of` is a ring hom). -/
theorem omegaS_pow_eight : ωS ^ 8 = 1 := by
  show (of ZOmega.ω) ^ 8 = 1
  rw [← ofRingHom_apply, ← map_pow, show ZOmega.ω ^ 8 = 1 from by decide, map_one]

/-- `ωS^k = ωS^(k % 8)` (phase periodicity). -/
theorem omegaS_pow_mod (k : ℕ) : ωS ^ k = ωS ^ (k % 8) := by
  conv_lhs => rw [← Nat.div_add_mod k 8, pow_add, pow_mul, omegaS_pow_eight, one_pow, one_mul]

/-- `reconstruct x y k = reconstruct x y (k % 8)` (phase periodicity). -/
theorem reconstruct_mod (x y : ZOmega) (k : ℕ) :
    reconstruct x y k = reconstruct x y (k % 8) := by
  unfold reconstruct; rw [omegaS_pow_mod k]

/-- **Coordinate bound ⟹ box membership**: `(|x|²).d = a²+b²+c²+d² ≤ 4` forces every
`ℤ[ω]` coordinate into `[-2,2]`, hence `x ∈ zomBox`. -/
theorem mem_zomBox {x : ZOmega} (h : (ZOmega.normSq x).d ≤ 4) : x ∈ zomBox := by
  rw [ZOmega.normSq_d] at h
  have hmem : ∀ t : ℤ, t ^ 2 ≤ 4 → t ∈ intBox := by
    intro t ht
    simp only [intBox, List.mem_cons, List.not_mem_nil, or_false]
    have h1 : -2 ≤ t := by nlinarith [sq_nonneg (t + 2)]
    have h2 : t ≤ 2 := by nlinarith [sq_nonneg (t - 2)]
    omega
  have ha : x.a ∈ intBox := hmem x.a (by nlinarith [sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d])
  have hb : x.b ∈ intBox := hmem x.b (by nlinarith [sq_nonneg x.a, sq_nonneg x.c, sq_nonneg x.d])
  have hc : x.c ∈ intBox := hmem x.c (by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.d])
  have hd : x.d ∈ intBox := hmem x.d (by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c])
  simp only [zomBox, List.mem_flatMap, List.mem_map]
  exact ⟨x.a, ha, x.b, hb, x.c, hc, x.d, hd, rfl⟩

/-! ## The bridge -/

/-- **The `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge** (Giles-Selinger Cor 7.11): every realizable
matrix with squared-modulus sde `μ(M) ≤ 3` has SO(3) Bloch least-denominator
exponent (= Matsumoto-Amano T-count) `kSO3 M ≤ 3`. The proof rewrites `M` as
`reconstruct x y k` (column 0 cleared at exponent 2; column 1 `realizable_col1`-
determined), shows the bounded integer data `(x, y)` lies in the filtered box, and
applies the `bridge_box_core` `native_decide`. This discharges one of the two
remaining `MACoverage` hypotheses (the other is the Clifford base). -/
theorem bridge (M : Mat2) (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    kSO3 M ≤ 3 := by
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := hM; exact interp_isUnitaryT gs
  obtain ⟨x, y, hx, hy, hxd, hyd⟩ := column0_cleared_bounded hu hμ
  obtain ⟨k, hcol01, hcol11⟩ := realizable_col1 hM
  have h00 : M 0 0 = mk x 2 := eq_mk_of_sqrt2_pow_mul hx
  have h10 : M 1 0 = mk y 2 := eq_mk_of_sqrt2_pow_mul hy
  -- M = reconstruct x y k
  have hMrec : M = reconstruct x y k := by
    rw [Matrix.eta_fin_two M, hcol01, hcol11, h00, h10]; rfl
  -- filter fact 1: |x|² + |y|² = ⟨0,0,0,4⟩  (cleared unit-column norm at s = 2)
  have hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) := by
    have := clearedCol_normSq_sum hx hy (unitary_col0_normSq hu)
    rwa [show ZOmega.sqrt2 ^ (2 * 2) = (⟨0, 0, 0, 4⟩ : ZOmega) from by decide] at this
  -- filter fact 2: √2 ∣ |x|²  (= the μ ≤ 3 condition)
  have hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (show denExp (normSq (M 0 0)) ≤ 3 from hμ)
    have hns : ZOmega.normSq x = ZOmega.sqrt2 * w := by
      apply of_inj
      rw [of_mul, ← (sqrt2_pow_normSq_clearing hx), show 2 * 2 = 1 + 3 from rfl,
        pow_add, mul_assoc, hw, pow_one]
      simp only [sqrt2_def, of_def]
    exact (ZOmega.dividesSqrt2_iff_dvd _).mpr ⟨w, hns⟩
  -- extract from the native_decide core
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hbox : kSO3 (reconstruct x y (k % 8)) ≤ 3 := by
    have h1 := List.all_eq_true.mp bridge_box_core x (mem_zomBox hxd)
    have h2 := List.all_eq_true.mp h1 y (mem_zomBox hyd)
    rw [if_pos ⟨hsum, hdvd⟩] at h2
    exact of_decide_eq_true (List.all_eq_true.mp h2 (k % 8) (List.mem_range.mpr hk8))
  rw [hMrec, reconstruct_mod]
  exact hbox

end KMM

end SKEFTHawking.RossSelinger
