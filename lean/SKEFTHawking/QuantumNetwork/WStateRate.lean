import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Basic

/-!
# W-state random-party distillation yield (Phase 6AA, Wave 3)

The Fortescue–Lo finite-round random-pair distillation yield from `|W₃⟩`
(PRL 98, 260501 (2007), Eq. (13); exact-formulas DR §3):

`⟨E_D⟩ = D / (D + 1)`  EPR pairs per `|W₃⟩` after a `D`-round protocol.

This is the **protocol output formula** (cited, not derived here — formalizing the
full LOCC protocol is out of scope). Per the DR we formalize the finite-round
yield and its load-bearing properties **only**; the asymptotic equality
`E_t^∞(W₃) = 1` is an **open conjecture** and is deliberately NOT formalized.

The substantive falsifiable content is `fortescueLoYield_gt_two_thirds`: the
protocol surpasses the single-copy specified-pair bound `2/3` for `D ≥ 3`.

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Fortescue–Lo finite-round random-pair yield from `|W₃⟩`: `⟨E_D⟩ = D/(D+1)`. -/
noncomputable def fortescueLoYield (D : ℕ) : ℝ := (D : ℝ) / (D + 1)

/-- The finite-round yield is strictly below 1 (it approaches the conjectured-optimal
asymptotic value 1 from below; the `= 1` equality is an open conjecture, not claimed). -/
theorem fortescueLoYield_lt_one (D : ℕ) : fortescueLoYield D < 1 := by
  unfold fortescueLoYield
  rw [div_lt_one (by positivity)]
  linarith

/-- The yield is monotone non-decreasing in the number of rounds. -/
theorem fortescueLoYield_mono {D D' : ℕ} (h : D ≤ D') :
    fortescueLoYield D ≤ fortescueLoYield D' := by
  unfold fortescueLoYield
  have hD : (D : ℝ) ≤ (D' : ℝ) := by exact_mod_cast h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hD]

/-- **Surpasses the single-copy specified-pair bound `2/3` for `D ≥ 3`** (Fortescue–Lo
Eq. (13)): `⟨E_3⟩ = 3/4 > 2/3`, and the yield is monotone. The falsifiable headline. -/
theorem fortescueLoYield_gt_two_thirds {D : ℕ} (h : 3 ≤ D) :
    (2 : ℝ) / 3 < fortescueLoYield D :=
  calc (2 : ℝ) / 3 < 3 / 4 := by norm_num
    _ = fortescueLoYield 3 := by unfold fortescueLoYield; norm_num
    _ ≤ fortescueLoYield D := fortescueLoYield_mono h

end SKEFTHawking.QuantumNetwork
