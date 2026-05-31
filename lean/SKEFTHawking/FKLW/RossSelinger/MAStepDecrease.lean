/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `kSO3`-decrease of a syllable strip (mod-2 condition)

The `ma_step` crux: for a realizable `M` with `kSO3 M = n ≥ 1`, the residue-selected
syllable strip lowers `kSO3` by 1. By `bloch_stripMat`,
`R(stripMat s M) = R((sylMat s)†)·R(M)`, so — writing `n = kSO3 M`,
`bᵢⱼ := √2ⁿ·R(M)ᵢⱼ` (cleared Bloch numerators) and `c^s := √2·R((sylMat s)†)`
(CONCRETE, cleared, since each syllable has `kSO3 = 1`) — one computes

  `√2^(n-1) · R(stripMat s M)ᵢⱼ = (∑ₖ c^s_ik · b_kj) / 2`,

so the decrease is governed by the clean **mod-2 condition**
`∀ i,j: ∑ₖ c^s_ik · b_kj ≡ 0 (mod 2)` on the (15-class) Bloch parity residue of `M`
(`scripts/kmm_ma_step_residue.py`).

This file ships the concrete `c^s` constants (`sylBlochNum`) and the clearing
identity `of (c^s_ik) = √2 · R((sylMat s)†)ᵢₖ` — the foundation of the decrease.
The full decrease lemma + the 15-class `decide` build on top.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — the SO(3)/Bloch picture of MA reduction.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MAStep

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The cleared syllable rotation** `c^s := √2 · R((sylMat s)†)` as a `ZOmega`
`3×3` matrix (each syllable has `kSO3 = 1`, so `√2·R((sylMat s)†)` is `ZOmega`-valued).
Values computed + cross-checked in `scripts/kmm_ma_step_residue.py`. -/
def sylBlochNum : Syllable → Matrix (Fin 3) (Fin 3) ZOmega
  | .T   => !![1, 1, 0; -1, 1, 0; 0, 0, ZOmega.sqrt2]
  | .HT  => !![0, -1, 1; 0, -1, -1; ZOmega.sqrt2, 0, 0]
  | .SHT => !![1, 0, 1; 1, 0, -1; 0, ZOmega.sqrt2, 0]

set_option maxRecDepth 8000 in
/-- **Clearing identity** `of (c^s_ik) = √2 · R((sylMat s)†)ᵢₖ`: the concrete
`sylBlochNum` equals `√2` times the SO(3) Bloch image of the syllable's adjoint.
Kernel-checked (`decide`). -/
theorem sylBlochNum_clearing (s : Syllable) :
    ∀ i k : Fin 3,
      ZOmegaSqrt2.of (sylBlochNum s i k)
        = sqrt2 * blochEntry (ZOmegaSqrt2.adjoint (sylMat s)) i k := by
  cases s <;> decide

/-! ## The cleared Bloch numerators `b = √2^kSO3 · R(M)` -/

/-- **Each Bloch entry's denominator exponent is ≤ `kSO3`** (`kSO3` is their `sup`).
Proved via `Finset.le_sup` on the `∀ p` (variable-index) form — instantiating at the
literal `(i,j)` last keeps the unifier from `whnf`-reducing the heavy `blochEntry`. -/
theorem denExp_blochEntry_le_kSO3 (M : Mat2) (i j : Fin 3) :
    ZOmegaSqrt2.denExp (blochEntry M i j) ≤ kSO3 M := by
  have key : ∀ p : Fin 3 × Fin 3,
      ZOmegaSqrt2.denExp (blochEntry M p.1 p.2) ≤ kSO3 M := by
    intro p
    rw [show kSO3 M
        = Finset.univ.sup (fun q : Fin 3 × Fin 3 => ZOmegaSqrt2.denExp (blochEntry M q.1 q.2))
        from rfl]
    exact Finset.le_sup
      (f := fun q : Fin 3 × Fin 3 => ZOmegaSqrt2.denExp (blochEntry M q.1 q.2))
      (Finset.mem_univ p)
  exact key (i, j)

/-- **The cleared Bloch numerator** `b_ij := √2^kSO3 · R(M)ᵢⱼ` as a `ZOmega`
element. Since `denExp R(M)ᵢⱼ ≤ kSO3 M`, multiplying by `√2^kSO3` clears the
denominator (`blochNum_spec`). Noncomputable (`Classical.choose`); used only in the
existence proof of `ma_step`. The mod-2 condition for the `kSO3`-decrease is on these
`b_ij` (the 15-class Bloch parity residue). -/
noncomputable def blochNum (M : Mat2) (i j : Fin 3) : ZOmega :=
  Classical.choose (ZOmegaSqrt2.denExp_le_iff.mp (denExp_blochEntry_le_kSO3 M i j))

/-- **Clearing spec for `blochNum`**: `√2^kSO3 · R(M)ᵢⱼ = of (b_ij)`. -/
theorem blochNum_spec (M : Mat2) (i j : Fin 3) :
    (sqrt2) ^ (kSO3 M) * blochEntry M i j = ZOmegaSqrt2.of (blochNum M i j) :=
  Classical.choose_spec (ZOmegaSqrt2.denExp_le_iff.mp (denExp_blochEntry_le_kSO3 M i j))

/-! ## The `kSO3`-decrease of a syllable strip (mod-2 condition) -/

/-- **The stripped Bloch numerator** `S_ij := ∑ₖ c^s_ik · b_kj` (the cleared
numerator of `√2^(kSO3+1)·R(stripMat s M)ᵢⱼ`). The `kSO3`-decrease is governed by
its parity (the 15-class Bloch residue). -/
noncomputable def blochStripNum (s : Syllable) (M : Mat2) (i j : Fin 3) : ZOmega :=
  ∑ k : Fin 3, sylBlochNum s i k * blochNum M k j

/-- **Core clearing identity** `√2^(kSO3 M + 1) · R(stripMat s M)ᵢⱼ = of(S_ij)`:
combines `bloch_stripMat` (`R(stripMat s M) = R((sylMat s)†)·R(M)`), the syllable
clearing (`sylBlochNum_clearing`), and the M-side clearing (`blochNum_spec`). -/
theorem sqrt2_pow_blochEntry_stripMat {M : Mat2} (hM : ZOmegaSqrt2.IsUnitaryT M)
    (s : Syllable) (i j : Fin 3) :
    sqrt2 ^ (kSO3 M + 1) * blochEntry (stripMat s M) i j
      = ZOmegaSqrt2.of (blochStripNum s M i j) := by
  unfold blochStripNum
  rw [bloch_stripMat hM, Fin.sum_univ_three, Fin.sum_univ_three,
      ZOmegaSqrt2.of_add, ZOmegaSqrt2.of_add, ZOmegaSqrt2.of_mul, ZOmegaSqrt2.of_mul,
      ZOmegaSqrt2.of_mul, sylBlochNum_clearing s i 0, sylBlochNum_clearing s i 1,
      sylBlochNum_clearing s i 2, ← blochNum_spec M 0 j, ← blochNum_spec M 1 j,
      ← blochNum_spec M 2 j]
  ring

/-- **Per-entry decrease** from the mod-2 condition: if `2 ∣ S_ij` then
`denExp R(stripMat s M)ᵢⱼ ≤ kSO3 M − 1`. (Since `√2^(n+1)·R = of(S) = √2²·of(w)`
when `S = 2w`, cancelling `√2²` (a unit) gives `√2^(n-1)·R = of(w)`.) -/
theorem denExp_blochEntry_stripMat_le {M : Mat2} (hM : ZOmegaSqrt2.IsUnitaryT M)
    (s : Syllable) (hn : 1 ≤ kSO3 M) (i j : Fin 3)
    (hdvd : (2 : ZOmega) ∣ blochStripNum s M i j) :
    ZOmegaSqrt2.denExp (blochEntry (stripMat s M) i j) ≤ kSO3 M - 1 := by
  obtain ⟨w, hw⟩ := hdvd
  have hid := sqrt2_pow_blochEntry_stripMat hM s i j
  rw [hw, ZOmegaSqrt2.of_mul, show ZOmegaSqrt2.of (2 : ZOmega) = sqrt2 ^ 2 from by decide,
      show kSO3 M + 1 = (kSO3 M - 1) + 2 from by omega, pow_add] at hid
  have hu : (invSqrt2 : ZOmegaSqrt2) ^ 2 * sqrt2 ^ 2 = 1 := by decide
  apply ZOmegaSqrt2.denExp_le_of_smul_eq_of (w := w)
  calc sqrt2 ^ (kSO3 M - 1) * blochEntry (stripMat s M) i j
      = invSqrt2 ^ 2 * (sqrt2 ^ (kSO3 M - 1) * sqrt2 ^ 2 * blochEntry (stripMat s M) i j) := by
        rw [show sqrt2 ^ (kSO3 M - 1) * sqrt2 ^ 2 * blochEntry (stripMat s M) i j
            = sqrt2 ^ 2 * (sqrt2 ^ (kSO3 M - 1) * blochEntry (stripMat s M) i j) from by ring,
            ← mul_assoc, hu, one_mul]
    _ = invSqrt2 ^ 2 * (sqrt2 ^ 2 * ZOmegaSqrt2.of w) := by rw [hid]
    _ = ZOmegaSqrt2.of w := by rw [← mul_assoc, hu, one_mul]

/-- **The `kSO3`-decrease** (the analytic core of `ma_step`): for a unitary `M`
with `kSO3 M ≥ 1`, if the mod-2 condition `∀ i,j: 2 ∣ S_ij` holds (the syllable `s`
is the residue-correct one), then `kSO3 (stripMat s M) < kSO3 M`. -/
theorem kSO3_stripMat_lt {M : Mat2} (hM : ZOmegaSqrt2.IsUnitaryT M) (s : Syllable)
    (hn : 1 ≤ kSO3 M) (hdvd : ∀ i j, (2 : ZOmega) ∣ blochStripNum s M i j) :
    kSO3 (stripMat s M) < kSO3 M := by
  have hle : kSO3 (stripMat s M) ≤ kSO3 M - 1 := by
    rw [show kSO3 (stripMat s M)
        = Finset.univ.sup (fun p : Fin 3 × Fin 3 =>
            ZOmegaSqrt2.denExp (blochEntry (stripMat s M) p.1 p.2)) from rfl]
    apply Finset.sup_le
    intro p _
    exact denExp_blochEntry_stripMat_le hM s hn p.1 p.2 (hdvd p.1 p.2)
  omega

end KMM

end SKEFTHawking.RossSelinger
