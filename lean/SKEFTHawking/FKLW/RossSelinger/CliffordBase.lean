/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Clifford base (`kSO3 = 0 ⟹ ∃ ≤ 6-gate word`)

The MA coverage recursion (`MACoverage.lean`) bottoms out at `kSO3 M = 0`, where
`M` is a single-qubit Clifford (up to global phase `ωᵏ`) — one of the 192 matrices
`⟨H, S, X, Y, Z, ω⟩`. `cliffordBase` supplies the `≤ 6`-gate Clifford word for each.

## Structure (mirrors the bridge)

`muMeasure_le_kSO3_add_two` gives `kSO3 M = 0 ⟹ μ(M) ≤ 2 ≤ 3`, so
`column0_cleared_bounded` + `realizable_col1` rewrite `M = reconstruct x y k` with
bounded `(x, y)` (`KMMBridge`). The word is then a finite `(x, y, k)`-keyed lookup
`cliffordWordOf` into the explicit 192-entry `cliffordTable` (BFS-minimal Clifford
words, gens `{H,S,X,Y,Z,ω}`, all length `≤ 6`). The `native_decide`
`cliffordBase_box_core` re-verifies, for every `kSO3 = 0` tuple in the bridge box,
that `interp (cliffordWordOf x y k) = reconstruct x y k` and the word length is `≤ 6`
— so the table is untrusted scaffolding (`scripts/emit_clifford_table.py`).

## Validated

`scripts/clifford_base_validation.py`: the `kSO3 = 0` subset of the box is exactly
192 Cliffords (`μ ∈ {0,1,2}`), each reachable by a `≤ 6`-gate Clifford word.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only).
- **#15** (no new project-local axioms): respected (`native_decide` carries the
  tracked `Lean.ofReduceBool` axiom).

-/

import SKEFTHawking.FKLW.RossSelinger.KMMBridge
import SKEFTHawking.FKLW.RossSelinger.MACoverage

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **Box data of a realizable `μ ≤ 3` matrix**: `M = reconstruct x y k` with `(x, y)`
in the coordinate box and meeting the filter conditions. Packages the
`column0_cleared_bounded` + `realizable_col1` extraction shared with the bridge. -/
theorem reconstruct_box_data {M : Mat2} (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    ∃ (x y : ZOmega) (k : ℕ), M = reconstruct x y k ∧
      ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) ∧
      ZOmega.dividesSqrt2 (ZOmega.normSq x) ∧
      (ZOmega.normSq x).d ≤ 4 ∧ (ZOmega.normSq y).d ≤ 4 := by
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := hM; exact interp_isUnitaryT gs
  obtain ⟨x, y, hx, hy, hxd, hyd⟩ := column0_cleared_bounded hu hμ
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
  exact ⟨x, y, k, hMrec, hsum, hdvd, hxd, hyd⟩

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

/-- **The finite Clifford-base check**: for every `(x, y, k)` in the bridge box with
`kSO3 (reconstruct x y k) = 0`, the looked-up word reconstructs `M` and has length `≤ 6`. -/
def cliffordBaseBoxOk : Bool :=
  zomBox.all (fun x => zomBox.all (fun y =>
    if ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega)
        ∧ ZOmega.dividesSqrt2 (ZOmega.normSq x)
    then (List.range 8).all (fun k =>
      !decide (kSO3 (reconstruct x y k) = 0) ||
        (decide (interp (cliffordWordOf x y k) = reconstruct x y k)
          && decide ((cliffordWordOf x y k).length ≤ 6)))
    else true))

set_option maxRecDepth 8000 in
/-- **The Clifford-base native_decide core**: every `kSO3 = 0` tuple's looked-up word
is correct and `≤ 6` gates. Re-verifies the (untrusted) `cliffordTable`. -/
theorem cliffordBase_box_core : cliffordBaseBoxOk = true := by native_decide

/-- **The Clifford base** (`MACoverage`'s second remaining hypothesis): a realizable
`M` with `kSO3 M = 0` (i.e. a single-qubit Clifford up to phase) has a `≤ 6`-gate word.
Via `muMeasure_le_kSO3_add_two` (`kSO3 = 0 ⟹ μ ≤ 2 ≤ 3`), `reconstruct_box_data`
rewrites `M = reconstruct x y k`; `cliffordBase_box_core` then supplies and verifies
the word `cliffordWordOf x y (k % 8)`. -/
theorem cliffordBase (M : Mat2) (hM : IsCliffordTRealizable M) (hk0 : kSO3 M = 0) :
    ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6 := by
  have hμ : muMeasure M ≤ 3 := by have := muMeasure_le_kSO3_add_two hM; omega
  obtain ⟨x, y, k, hMrec, hsum, hdvd, hxd, hyd⟩ := reconstruct_box_data hM hμ
  have hk0' : kSO3 (reconstruct x y (k % 8)) = 0 := by rw [← reconstruct_mod, ← hMrec]; exact hk0
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp cliffordBase_box_core x (mem_zomBox hxd))
    y (mem_zomBox hyd)
  rw [if_pos ⟨hsum, hdvd⟩] at h2
  have h3 := List.all_eq_true.mp h2 (k % 8) (List.mem_range.mpr hk8)
  rw [decide_eq_true_eq.mpr hk0', Bool.not_true, Bool.false_or, Bool.and_eq_true] at h3
  refine ⟨cliffordWordOf x y (k % 8), ?_, of_decide_eq_true h3.2⟩
  rw [of_decide_eq_true h3.1, hMrec]; exact (reconstruct_mod x y k).symm

/-! ## The unconditional KMM reduction (orphan #2 substrate, fully discharged) -/

/-- **`Nonempty KMMReduction`, UNCONDITIONAL** — the capstone of the MA-coverage arc.
Both hypotheses of `nonempty_kmmReduction_of_clifford_bridge` are now theorems:
`cliffordBase` (this file) and `bridge` (`KMMBridge`). No axiom, no open hypothesis
(Inv #15). This is the exact-synthesis substrate that closes Phase 6x orphan #2 at
the deterministic-branch level (feeds Item G). -/
theorem nonempty_kmmReduction : Nonempty KMMReduction :=
  nonempty_kmmReduction_of_clifford_bridge cliffordBase bridge

end KMM

end SKEFTHawking.RossSelinger
