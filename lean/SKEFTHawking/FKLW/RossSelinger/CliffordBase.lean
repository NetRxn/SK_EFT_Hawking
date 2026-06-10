/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Clifford base (`kSO3 = 0 ⟹ ∃ ≤ 6-gate word`)

The MA coverage recursion (`MACoverage.lean`) bottoms out at `kSO3 M = 0`, where
`M` is a single-qubit Clifford (up to global phase `ωᵏ`) — one of the 192 matrices
`⟨H, S, X, Y, Z, ω⟩`. `cliffordBase` supplies the `≤ 6`-gate Clifford word for each.

## Structure (mirrors the bridge)

`muMeasure_le_kSO3_add_two` gives `kSO3 M = 0 ⟹ μ(M) ≤ 2 ≤ 3`, so
`column0_cleared_bounded` + `realizable_col1` rewrite `M = reconstruct x y k`
(`KMMBridge`). The word is a finite `(x, y, k)`-keyed lookup `cliffordWordOf` into the
explicit 192-entry `cliffordTable` (BFS-minimal Clifford words, gens `{H,S,X,Y,Z,ω}`,
all length `≤ 6`; emitted by `scripts/emit_clifford_table.py`, untrusted scaffolding).
**STRUCTURAL coverage (Phase 6AO Track 3, 2026-06-10)**: the former `native_decide` box
sweep (`cliffordBase_box_core`) was ELIMINATED — the `kSO3 = 0` quantization
(`CliffordBaseStructural` + `ZOmegaTorsion`) pins every key to a torsion class
(`(0, 2ωᵇ)`, `(√2ωᵃ, √2ωᵇ)`, `(2ωᵃ, 0)`), and three per-class kernel `decide +kernel`
checks (`cliffordCover_{y2,mid,x2}`, 640 torsion tuples total) verify the table words.

## Validated

`scripts/clifford_base_validation.py`: the `kSO3 = 0` subset is exactly
192 Cliffords (`μ ∈ {0,1,2}`), each reachable by a `≤ 6`-gate Clifford word.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only).
- **#15** (no new project-local axioms): respected. No `native_decide` —
  kernel-pure `{propext, Classical.choice, Quot.sound}`.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMBridge
import SKEFTHawking.FKLW.RossSelinger.BridgeStructural
import SKEFTHawking.FKLW.RossSelinger.CliffordBaseStructural
import SKEFTHawking.FKLW.RossSelinger.MACoverage

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **Reconstruction data of a realizable `μ ≤ 3` matrix**: `M = reconstruct x y k` with
the unit-column equation and the `μ ≤ 3` divisibility. Packages the
`column0_cleared_bounded` + `realizable_col1` extraction shared with the bridge. -/
theorem reconstruct_box_data {M : Mat2} (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    ∃ (x y : ZOmega) (k : ℕ), M = reconstruct x y k ∧
      ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) ∧
      ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := hM; exact interp_isUnitaryT gs
  obtain ⟨x, y, hx, hy, -, -⟩ := column0_cleared_bounded hu hμ
  obtain ⟨k, hcol01, hcol11⟩ := realizable_col1 hM
  have h00 : M 0 0 = mk x 2 := eq_mk_of_sqrt2_pow_mul hx
  have h10 : M 1 0 = mk y 2 := eq_mk_of_sqrt2_pow_mul hy
  have hMrec : M = reconstruct x y k := by
    rw [Matrix.eta_fin_two M, hcol01, hcol11, h00, h10]; rfl
  have hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) := by
    have := clearedCol_normSq_sum hx hy (unitary_col0_normSq hu)
    rwa [show ZOmega.sqrt2 ^ (2 * 2) = (⟨0, 0, 0, 4⟩ : ZOmega) from by decide] at this
  have hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (show denExp (normSq (M 0 0)) ≤ 3 from hμ)
    have hns : ZOmega.normSq x = ZOmega.sqrt2 * w := by
      apply of_inj
      rw [of_mul, ← (sqrt2_pow_normSq_clearing hx), show 2 * 2 = 1 + 3 from rfl,
        pow_add, mul_assoc, hw, pow_one]
      simp only [sqrt2_def, of_def]
    exact (ZOmega.dividesSqrt2_iff_dvd _).mpr ⟨w, hns⟩
  exact ⟨x, y, k, hMrec, hsum, hdvd⟩

-- 192 entries; max word length 6
def cliffordTable : List (ZOmega × ZOmega × ℕ × List CliffordTGate) := [
  (⟨-2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.S, .X, .Z, .Y, .omega]),
  (⟨-2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.Y, .X, .omega]),
  (⟨-2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.S, .Y, .X, .omega]),
  (⟨-2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.X, .Z, .Y, .omega]),
  (⟨0, -2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.Y, .X]),
  (⟨0, -2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.S, .Y, .X]),
  (⟨0, -2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.X, .Z, .Y]),
  (⟨0, -2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.S, .X, .Z, .Y]),
  (⟨0, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.S, .X, .Z, .X, .omega]),
  (⟨0, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.H, .Y, .H, .Y, .omega]),
  (⟨0, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.X, .S, .Y, .omega]),
  (⟨0, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.X, .Z, .X, .omega]),
  (⟨0, 0, 0, -2⟩, ⟨0, 0, 0, 0⟩, 0, [.H, .Y, .H, .Y]),
  (⟨0, 0, 0, -2⟩, ⟨0, 0, 0, 0⟩, 2, [.X, .S, .Y]),
  (⟨0, 0, 0, -2⟩, ⟨0, 0, 0, 0⟩, 4, [.X, .Z, .X]),
  (⟨0, 0, 0, -2⟩, ⟨0, 0, 0, 0⟩, 6, [.S, .X, .Z, .X]),
  (⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 0⟩, 0, []),
  (⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 0⟩, 2, [.S]),
  (⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 0⟩, 4, [.Z]),
  (⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 0⟩, 6, [.S, .Z]),
  (⟨0, 0, 2, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.S, .Z, .omega]),
  (⟨0, 0, 2, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.omega]),
  (⟨0, 0, 2, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.S, .omega]),
  (⟨0, 0, 2, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.Z, .omega]),
  (⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.X, .Y]),
  (⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.S, .X, .Y]),
  (⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.omega, .omega]),
  (⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.S, .omega, .omega]),
  (⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0, [.S, .omega, .omega, .omega]),
  (⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 2, [.X, .Y, .omega]),
  (⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 4, [.S, .X, .Y, .omega]),
  (⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 6, [.omega, .omega, .omega]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 0, [.H, .X, .Z, .Y]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 2, [.H, .S, .X, .Z, .Y]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 4, [.H, .Y, .X]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 6, [.H, .S, .Y, .X]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 0, [.H, .S, .Y, .H, .omega]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 2, [.S, .H, .X, .Z, .Y]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 4, [.H, .S, .H, .Z, .Y, .omega]),
  (⟨-1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 6, [.S, .H, .Y, .X]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 0, [.S, .H, .S, .Z, .X]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 2, [.S, .Y, .H]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 4, [.S, .Y, .H, .S]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 6, [.S, .H, .Z, .Y]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 0, [.Y, .H]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 2, [.Y, .H, .S]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 4, [.H, .Z, .Y]),
  (⟨-1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 6, [.H, .S, .Z, .X]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 0, [.S, .H, .S, .Z, .Y]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 2, [.S, .H, .X]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 4, [.S, .H, .X, .S]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 6, [.S, .H, .X, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 0, [.H, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 2, [.H, .S, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 4, [.H]),
  (⟨-1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 6, [.H, .S]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 0, [.H, .X]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 2, [.H, .X, .S]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 4, [.H, .X, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 6, [.H, .S, .Z, .Y]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 0, [.S, .H, .S]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 2, [.S, .H, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 4, [.S, .H, .S, .Z]),
  (⟨-1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 6, [.S, .H]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 0, [.H, .X, .S, .Y, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 2, [.H, .X, .Z, .X, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 4, [.H, .S, .X, .Z, .X, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 6, [.Y, .H, .Y, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 0, [.H, .S, .Y, .H, .S]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 2, [.H, .S, .H, .Z, .Y]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 4, [.H, .S, .H, .S, .Z, .X]),
  (⟨0, -1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 6, [.H, .S, .Y, .H]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 0, [.S, .H, .Z, .X, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 2, [.H, .S, .Y, .H, .Y]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 4, [.H, .S, .H, .X, .S, .Y]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 6, [.Y, .H, .S, .H]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 0, [.H, .S, .Y, .Z, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 2, [.H, .Y, .X, .Y, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 4, [.H, .S, .Y, .omega]),
  (⟨0, -1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 6, [.H, .Z, .X, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 0, [.S, .H, .Z, .Y, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 2, [.H, .S, .H, .Y, .X]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 4, [.S, .Y, .H, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 6, [.S, .Y, .H, .S, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 0, [.H, .S, .Y, .X, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 2, [.H, .X, .Z, .Y, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 4, [.H, .S, .X, .Z, .Y, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 6, [.H, .Y, .X, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 0, [.H, .S, .Z, .X, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 2, [.Y, .H, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 4, [.Y, .H, .S, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 6, [.H, .Z, .Y, .omega]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 0, [.H, .S, .H, .X, .S]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 2, [.H, .S, .H, .X, .Z]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 4, [.H, .S, .H, .S, .Z, .Y]),
  (⟨0, -1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 6, [.H, .S, .H, .X]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 0, [.H, .S, .H, .S, .Y]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 2, [.H, .S, .H, .Z, .X]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 4, [.S, .H, .omega, .omega, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, -1⟩, 6, [.H, .S, .H, .Y, .X, .Y]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 0, [.H, .S, .X, .Z, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 2, [.H, .Y, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 4, [.H, .S, .X, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, 6, [.H, .Y, .Z, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 0, [.H, .S, .X, .Y, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 2, [.H, .omega, .omega, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 4, [.H, .S, .omega, .omega, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, -1⟩, 6, [.H, .X, .Y, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 0, [.S, .H, .Y, .Z, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 2, [.H, .S, .H, .X, .Y]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 4, [.S, .H, .Y, .omega]),
  (⟨0, 1, 0, -1⟩, ⟨0, 1, 0, 1⟩, 6, [.H, .S, .H, .omega, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 0, [.H, .S, .Z, .Y, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 2, [.H, .X, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 4, [.H, .X, .S, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, -1⟩, 6, [.H, .X, .Z, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 0, [.H, .S, .H, .S, .Z]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 2, [.H, .S, .H]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 4, [.H, .S, .H, .S]),
  (⟨0, 1, 0, 1⟩, ⟨0, -1, 0, 1⟩, 6, [.H, .S, .H, .Z]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 0, [.S, .H, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 2, [.S, .H, .S, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 4, [.S, .H, .Z, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, -1⟩, 6, [.H, .S, .H, .Y]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 0, [.H, .S, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 2, [.H, .Z, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 4, [.H, .S, .Z, .omega]),
  (⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩, 6, [.H, .omega]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 0, [.S, .H, .X, .S, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 2, [.H, .Y, .H, .S, .H]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 4, [.H, .S, .H, .Z, .X, .omega]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, -1, 0⟩, 6, [.S, .Y, .H, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 0, [.H, .Y, .X, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 2, [.H, .S, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 4, [.H, .Z, .X]),
  (⟨1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, 6, [.H, .S, .Y, .Z]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 0, [.H, .X, .Z, .X]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 2, [.H, .S, .X, .Z, .X]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 4, [.Y, .H, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, 6, [.H, .X, .S, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 0, [.S, .H, .S, .Y, .Z]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 2, [.S, .H, .Y, .X, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 4, [.S, .H, .S, .Y]),
  (⟨1, 0, -1, 0⟩, ⟨1, 0, 1, 0⟩, 6, [.S, .H, .Z, .X]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 0, [.H, .Y]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 2, [.H, .S, .X]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 4, [.H, .Y, .Z]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, 6, [.H, .S, .X, .Z]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 0, [.H, .S, .H, .Z, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 2, [.S, .H, .Y]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 4, [.H, .S, .H, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨-1, 0, 1, 0⟩, 6, [.S, .H, .Y, .Z]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 0, [.H, .S, .H, .Y, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 2, [.S, .H, .omega, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 4, [.S, .H, .S, .omega, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, 6, [.S, .H, .X, .Y]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 0, [.H, .omega, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 2, [.H, .S, .omega, .omega]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 4, [.H, .X, .Y]),
  (⟨1, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, 6, [.H, .S, .X, .Y]),
  (⟨0, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩, 0, [.H, .Y, .H, .S, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩, 2, [.Z, .Y, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩, 4, [.S, .Z, .X, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩, 6, [.H, .Y, .H, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, -2, 0, 0⟩, 0, [.Z, .Y]),
  (⟨0, 0, 0, 0⟩, ⟨0, -2, 0, 0⟩, 2, [.S, .Z, .X]),
  (⟨0, 0, 0, 0⟩, ⟨0, -2, 0, 0⟩, 4, [.H, .Y, .H]),
  (⟨0, 0, 0, 0⟩, ⟨0, -2, 0, 0⟩, 6, [.H, .Y, .H, .S]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, -2, 0⟩, 0, [.S, .Y, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, -2, 0⟩, 2, [.Z, .X, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, -2, 0⟩, 4, [.S, .Y, .Z, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, -2, 0⟩, 6, [.Y, .X, .Y, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -2⟩, 0, [.Z, .X]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -2⟩, 2, [.S, .Y, .Z]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -2⟩, 4, [.Y, .X, .Y]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -2⟩, 6, [.S, .Y]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, 0, [.X, .Z]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, 2, [.S, .Z, .Y]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, 4, [.X]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, 6, [.X, .S]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 2, 0⟩, 0, [.X, .S, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 2, 0⟩, 2, [.X, .Z, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 2, 0⟩, 4, [.S, .Z, .Y, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 0, 2, 0⟩, 6, [.X, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, 0, [.Y, .Z]),
  (⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, 2, [.S, .X, .Z]),
  (⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, 4, [.Y]),
  (⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, 6, [.S, .X]),
  (⟨0, 0, 0, 0⟩, ⟨2, 0, 0, 0⟩, 0, [.S, .X, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨2, 0, 0, 0⟩, 2, [.Y, .Z, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨2, 0, 0, 0⟩, 4, [.S, .X, .Z, .omega]),
  (⟨0, 0, 0, 0⟩, ⟨2, 0, 0, 0⟩, 6, [.Y, .omega])
]

/-- **The Clifford word lookup**: the `≤ 6`-gate word for `reconstruct x y k`, or `[]`
if absent (only the `kSO3 = 0` keys are present). -/
def cliffordWordOf (x y : ZOmega) (k : ℕ) : List CliffordTGate :=
  ((cliffordTable.find? (fun e => decide (e.1 = x ∧ e.2.1 = y ∧ e.2.2.1 = k))).map
    (·.2.2.2)).getD []

/-! ## The per-class coverage checks (kernel `decide` — no box sweep)

By `normSq_quantized` + the `ZOmegaTorsion` classes, every `kSO3 = 0` reconstruction key is
`(0, 2ωᵇ)`, `(√2ωᵃ, √2ωᵇ)`, or `(2ωᵃ, 0)` with torsion exponents `< 8` and phase `k < 8`.
The three finite checks below verify, per class, that the looked-up `cliffordTable` word
reconstructs the matrix and has length `≤ 6` whenever `kSO3 = 0`. Kernel-pure
(`decide +kernel`); the former `native_decide` box sweep (`bridgeBox`-style `5⁴`-coordinate
enumeration) is gone — the quantization replaces it with `8·8 + 8·8·8 + 8·8 = 640` torsion
tuples. -/

set_option maxRecDepth 8000 in
/-- Coverage, class `x = 0` (`y = 2ωᵇ`): the table word is correct on every `kSO3 = 0` key. -/
theorem cliffordCover_y2 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct 0 (2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf 0 (2 * ZOmega.ω ^ b) k) = reconstruct 0 (2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf 0 (2 * ZOmega.ω ^ b) k).length ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, class `y = 0` (`x = 2ωᵃ`). -/
theorem cliffordCover_x2 : ∀ a < 8, ∀ k < 8,
    kSO3 (reconstruct (2 * ZOmega.ω ^ a) 0 k) = 0 →
    interp (cliffordWordOf (2 * ZOmega.ω ^ a) 0 k) = reconstruct (2 * ZOmega.ω ^ a) 0 k ∧
      (cliffordWordOf (2 * ZOmega.ω ^ a) 0 k).length ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 0` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_0 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 0) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 0) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 0) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 0) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 1` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_1 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 1) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 1) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 1) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 1) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 2` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_2 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 2) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 2) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 2) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 2) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 3` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_3 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 3) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 3) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 3) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 3) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 4` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_4 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 4) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 4) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 4) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 4) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 5` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_5 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 5) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 5) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 5) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 5) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 6` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_6 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 6) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 6) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 6) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 6) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- Coverage, middle class, chunk `a = 7` (64 tuples — sized to the kernel budget). -/
theorem cliffordCover_mid_7 : ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 7) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 7) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ 7) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ 7) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  decide +kernel

/-- Coverage, middle class (`x = √2ωᵃ`, `y = √2ωᵇ`) — dispatcher over the 8 per-`a`
kernel chunks (a single 512-tuple `decide +kernel` exceeds the heartbeat budget;
64-tuple chunks match the passing class sizes). -/
theorem cliffordCover_mid : ∀ a < 8, ∀ b < 8, ∀ k < 8,
    kSO3 (reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ a) (ZOmega.sqrt2 * ZOmega.ω ^ b) k) = 0 →
    interp (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ a) (ZOmega.sqrt2 * ZOmega.ω ^ b) k)
        = reconstruct (ZOmega.sqrt2 * ZOmega.ω ^ a) (ZOmega.sqrt2 * ZOmega.ω ^ b) k ∧
      (cliffordWordOf (ZOmega.sqrt2 * ZOmega.ω ^ a) (ZOmega.sqrt2 * ZOmega.ω ^ b) k).length
        ≤ 6 := by
  intro a ha b hb k hk h0
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cliffordCover_mid_0 b hb k hk h0
  · exact cliffordCover_mid_1 b hb k hk h0
  · exact cliffordCover_mid_2 b hb k hk h0
  · exact cliffordCover_mid_3 b hb k hk h0
  · exact cliffordCover_mid_4 b hb k hk h0
  · exact cliffordCover_mid_5 b hb k hk h0
  · exact cliffordCover_mid_6 b hb k hk h0
  · exact cliffordCover_mid_7 b hb k hk h0

/-- **The Clifford base** (`MACoverage`'s second remaining hypothesis): a realizable
`M` with `kSO3 M = 0` (i.e. a single-qubit Clifford up to phase) has a `≤ 6`-gate word.
STRUCTURAL (Phase 6AO Track 3): `muMeasure_le_kSO3_add_two` gives `μ ≤ 2 ≤ 3`;
`reconstruct_box_data` rewrites `M = reconstruct x y k`; the `kSO3 = 0` quantization
(`four_dvd_normSq_sub_of_kSO3_eq_zero` + `normSq_quantized` + the `ZOmegaTorsion` classes)
pins `(x, y)` to a torsion class, and the per-class kernel coverage check supplies and
verifies the word. No box enumeration, no `native_decide`. -/
theorem cliffordBase (M : Mat2) (hM : IsCliffordTRealizable M) (hk0 : kSO3 M = 0) :
    ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6 := by
  have hμ : muMeasure M ≤ 3 := by have := muMeasure_le_kSO3_add_two hM; omega
  obtain ⟨x, y, k, hMrec, hsum, hdvd⟩ := reconstruct_box_data hM hμ
  have hk0' : kSO3 (reconstruct x y (k % 8)) = 0 := by rw [← reconstruct_mod, ← hMrec]; exact hk0
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hZZ := four_dvd_normSq_sub_of_kSO3_eq_zero hk0'
  rcases normSq_quantized hsum hZZ with ⟨hx0, hy4⟩ | ⟨hx2, hy2⟩ | ⟨hx4, hy0⟩
  · obtain ⟨b, hb, rfl⟩ := ZOmega.two_torsion_of_normSq_eq_four hy4
    subst hx0
    obtain ⟨hint, hlen⟩ := cliffordCover_y2 b hb (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k], hlen⟩
  · obtain ⟨a, ha, rfl⟩ := ZOmega.sqrt2_torsion_of_normSq_eq_two hx2
    obtain ⟨b, hb, rfl⟩ := ZOmega.sqrt2_torsion_of_normSq_eq_two hy2
    obtain ⟨hint, hlen⟩ := cliffordCover_mid a ha b hb (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k], hlen⟩
  · obtain ⟨a, ha, rfl⟩ := ZOmega.two_torsion_of_normSq_eq_four hx4
    subst hy0
    obtain ⟨hint, hlen⟩ := cliffordCover_x2 a ha (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k], hlen⟩

/-! ## The unconditional KMM reduction (orphan #2 substrate, fully discharged) -/

/-- **`Nonempty KMMReduction`, UNCONDITIONAL** — the capstone of the MA-coverage arc.
Both hypotheses of `nonempty_kmmReduction_of_clifford_bridge` are now theorems:
`cliffordBase` (this file) and `bridge` (`BridgeStructural`, fully structural). No axiom, no open hypothesis
(Inv #15). This is the exact-synthesis substrate that closes Phase 6x orphan #2 at
the deterministic-branch level (feeds Item G). -/
theorem nonempty_kmmReduction : Nonempty KMMReduction :=
  nonempty_kmmReduction_of_clifford_bridge cliffordBase bridge

end KMM

end SKEFTHawking.RossSelinger
