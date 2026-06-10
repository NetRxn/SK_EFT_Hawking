/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — KMM reconstruction substrate for the `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge

The MA coverage recursion (`MACoverage.lean`) consumes the bridge

  `bridge : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → kSO3 M ≤ 3`

— the quantitative `sde ↔ k_SO3` relationship of Giles-Selinger Cor 7.11. This
file ships the *substrate*: the KMM Theorem 1 reconstruction, the coordinate
box (still consumed by `CliffordBase.lean`), the connecting lemmas, and the
reverse bound `μ ≤ kSO3 + 2`. The bridge theorem itself lives in
`BridgeStructural.lean`, proved **structurally** (Phase 6AO Track 3): the
former `native_decide` core (`bridgeBoxOk`/`bridge_box_core`, a `1664`-tuple
boxed sweep) was eliminated 2026-06-09 in favor of the parity/δ-divisibility
calculus of `BridgeParity.lean` + the nine per-entry `denExp` bounds of
`BridgeStructural.lean`, which need no box enumeration at all.

## The M-structure reduction

By `column0_cleared_bounded`, a `μ(M) ≤ 3` unitary clears column 0 at exponent
`2`: `√2²·M₀₀ = of x`, `√2²·M₁₀ = of y` with `(|x|²).d ≤ 4`, `(|y|²).d ≤ 4`
(so each `ℤ[ω]` coordinate of `x, y` is bounded by `2`). By `realizable_col1`,
column 1 is determined: `M₀₁ = -(ωᵏ·conj M₁₀)`, `M₁₁ = ωᵏ·conj M₀₀`. Hence

  `M = reconstruct x y k = !![mk x 2, -(ωᵏ·conj (mk y 2)); mk y 2, ωᵏ·conj (mk x 2)]`.

So `kSO3 M = kSO3 (reconstruct x y k)`, a function of the integer data
`(x, y, k)`. The unitarity forces `|x|² + |y|² = 2² = ⟨0,0,0,4⟩` (column-0 norm,
scaled by `√2⁴`), and `μ ≤ 3` is exactly `√2 ∣ |x|²` (`= gde(|x|²) ≥ 1`, since
`μ = denExp(|M₀₀|²) = 4 − gde(|x|²)`). `BridgeStructural.lean` shows these two
conditions alone force `denExp (blochEntry (reconstruct x y k) i j) ≤ 3` for all
nine Bloch entries — no coordinate bound or enumeration needed.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — Cor 7.11 (`sde ↔ k_SO3`).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) — Theorem 1 (column structure).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure:
  `propext`, `Classical.choice`, `Quot.sound` only).

-/

import SKEFTHawking.FKLW.RossSelinger.BlochMap
import SKEFTHawking.FKLW.RossSelinger.KMMForm
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2
import SKEFTHawking.FKLW.RossSelinger.KMMBaseCoverage
import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
import SKEFTHawking.FKLW.RossSelinger.UnitColumnCongruence
import SKEFTHawking.FKLW.RossSelinger.MAStepDecrease
import SKEFTHawking.FKLW.RossSelinger.MuDecrease

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **`ZOmegaSqrt2` is right-cancellative for `+`** (it is an `AddGroup`, but the
hand-rolled quotient `CommRing` instance does not expose the `IsRightCancelAdd`
mixin to `linear_combination`'s `ring1` closer — providing it explicitly unblocks
`linear_combination` over this ring). -/
instance : IsRightCancelAdd ZOmegaSqrt2 where
  add_right_cancel a b c h := by
    have h2 := congrArg (· + (-a)) h
    simpa only [add_neg_cancel_right] using h2

namespace ZOmegaSqrt2

/-- `normSq` is conjugation-invariant: `normSq (conj x) = normSq x`. -/
theorem normSq_conj' (x : ZOmegaSqrt2) : normSq (conj x) = normSq x := by
  rw [normSq, conj_conj, mul_comm, ← normSq]

/-- `normSq` is negation-invariant: `normSq (-x) = normSq x`. -/
theorem normSq_neg' (x : ZOmegaSqrt2) : normSq (-x) = normSq x := by
  have cn : conj (-x) = -conj x := by
    have h := conj_add x (-x); rw [add_neg_cancel, conj_zero] at h; linear_combination -h
  rw [normSq, normSq, cn]; ring

end ZOmegaSqrt2

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
def coordBox : List ℤ := [-2, -1, 0, 1, 2]

/-- The explicit `5⁴ = 625`-element `ℤ[ω]` box `[-2, 2]⁴`. -/
def zomBox : List ZOmega :=
  coordBox.flatMap (fun a => coordBox.flatMap (fun b =>
    coordBox.flatMap (fun c => coordBox.map (fun d => ⟨a, b, c, d⟩))))

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
  have hmem : ∀ t : ℤ, t ^ 2 ≤ 4 → t ∈ coordBox := by
    intro t ht
    simp only [coordBox, List.mem_cons, List.not_mem_nil, or_false]
    have h1 : -2 ≤ t := by nlinarith [sq_nonneg (t + 2)]
    have h2 : t ≤ 2 := by nlinarith [sq_nonneg (t - 2)]
    omega
  have ha : x.a ∈ coordBox := hmem x.a (by nlinarith [sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d])
  have hb : x.b ∈ coordBox := hmem x.b (by nlinarith [sq_nonneg x.a, sq_nonneg x.c, sq_nonneg x.d])
  have hc : x.c ∈ coordBox := hmem x.c (by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.d])
  have hd : x.d ∈ coordBox := hmem x.d (by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c])
  simp only [zomBox, List.mem_flatMap, List.mem_map]
  exact ⟨x.a, ha, x.b, hb, x.c, hc, x.d, hd, rfl⟩

/-! ## The reverse bound `μ ≤ kSO3 + 2` (for the Clifford base) -/

/-- **`muMeasure M ≤ kSO3 M + 2`** for a realizable `M` (a clean structural
bound). The `(z,z)` Bloch entry is `R(M)₂₂ = 2·|M₀₀|² − 1` for a unitary
(`realizable_col1` gives `|M₁₁|²=|M₀₀|²`, `|M₀₁|²=|M₁₀|²`, so the trace collapses), hence
`normSq M₀₀ = (R(M)₂₂ + 1)·½`. `denExp` is sub-multiplicative and `denExp ½ = 2`, so
`μ(M) = denExp(normSq M₀₀) ≤ denExp(R(M)₂₂) + 2 ≤ kSO3 M + 2`. In particular
`kSO3 M = 0 ⟹ μ(M) ≤ 2 ≤ 3`, which lets the Clifford base reuse `column0_cleared_bounded`. -/
theorem muMeasure_le_kSO3_add_two {M : Mat2} (hM : IsCliffordTRealizable M) :
    muMeasure M ≤ kSO3 M + 2 := by
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := hM; exact interp_isUnitaryT gs
  have hbloch : blochEntry M 2 2 = half * (normSq (M 0 0) - normSq (M 0 1)
      - normSq (M 1 0) + normSq (M 1 1)) := by
    simp only [blochEntry, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, normSq]
    ring
  have hc0 := unitary_col0_normSq hu
  obtain ⟨k, h01, h11⟩ := realizable_col1 hM
  have hr11 : normSq (M 1 1) = normSq (M 0 0) := by
    rw [h11, normSq_mul, show ωS = of ZOmega.ω from rfl, normSq_omega_pow, one_mul, normSq_conj']
  have hr01 : normSq (M 0 1) = normSq (M 1 0) := by
    rw [h01, normSq_neg', normSq_mul, show ωS = of ZOmega.ω from rfl, normSq_omega_pow, one_mul,
      normSq_conj']
  have hhalf : half + half = 1 := by rw [half, mk_add, one_def, mk_eq_mk_iff]; decide
  have hc' : normSq (M 1 0) = 1 - normSq (M 0 0) := by linear_combination hc0
  have hid : normSq (M 0 0) = (blochEntry M 2 2 + 1) * half := by
    rw [hbloch, hr11, hr01, hc']
    linear_combination (half - normSq (M 0 0) - 2 * normSq (M 0 0) * half) * hhalf
  unfold muMeasure
  rw [hid]
  have h2 : denExp half = 2 := by rw [half, denExp_mk]; decide
  calc denExp ((blochEntry M 2 2 + 1) * half)
      ≤ denExp (blochEntry M 2 2 + 1) + denExp half := denExp_mul_le _ _
    _ ≤ denExp (blochEntry M 2 2) + 2 := by
        have := denExp_add_le (blochEntry M 2 2) 1
        rw [denExp_one] at this; rw [h2]; omega
    _ ≤ kSO3 M + 2 := by have := denExp_blochEntry_le_kSO3 M 2 2; omega

end KMM

end SKEFTHawking.RossSelinger
