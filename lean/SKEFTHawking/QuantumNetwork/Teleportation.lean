import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.RepeaterChain

/-!
# Horodecki teleportation fidelity over a shared resource (Phase 6AC, Wave 3)

The Horodecki average teleportation fidelity (PRA 60, 1888 (1999), Eq. (24);
exact-formulas DR §4): a qubit resource state with fully-entangled fraction
`F = max⟨Φ|ρ|Φ⟩` gives optimal average teleportation fidelity

`f_avg = (2F + 1) / 3`.

## Probe-gated analytic content (tracked hypothesis, NOT an axiom)

The `1/3` in Horodecki's formula is the value of the **Haar–Pauli quadratic
integral** `∫_{S²} (⟨ψ|σ_k|ψ⟩)² dμ = 1/3` (the single analytic step of the proof,
DR §4b step 4). Mathlib at our pin (v4.29.1 / `5e932f97`) provides the sphere-Haar
machinery (`MeasureTheory.Measure.toSphere`, `integral_fun_norm_addHaar`) but **not**
this specific spherical integral; deriving it (Bloch-vector quadratic → spherical
normalization) is a substantial measure-theory development off this phase's critical
path. Per the phase's probe-gate discipline we therefore **do not** prove the `1/3`
and we **do not** introduce a project-local axiom for it. Instead the constant enters
as an explicit hypothesis `HaarPauliConstant c` (`c = 1/3`) in every theorem below, so
no result silently assumes it. The structural decomposition

`teleportAvgFidelity F c = F + (1 − F)·c`

is the algebraic skeleton (resource averages to a depolarizing channel with the
`k=0` Pauli contributing `1` and the three `k≠0` Paulis each contributing the Haar
constant `c`); with `c = 1/3` it collapses to Horodecki's `(2F+1)/3`.

Invariants (Phase 6AC): kernel-pure, zero sorry, **zero project-local axioms**
(the Haar value is a discharged hypothesis), no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- The Haar–Pauli quadratic integral constant `∫_{S²}(⟨ψ|σ_k|ψ⟩)² dμ = 1/3`
(Horodecki PRA 60, 1888 (1999) §III, step 4). This analytic value is NOT proved
here — Mathlib at our pin lacks the spherical-integral lemma — so it appears as an
explicit hypothesis in every theorem, never as a project axiom. -/
def HaarPauliConstant (c : ℝ) : Prop := c = 1 / 3

/-- **Algebraic skeleton of the Horodecki teleportation fidelity.** Given a resource
with fully-entangled fraction `F` and the Haar–Pauli constant `c`, the average
teleportation fidelity is `F + (1 − F)·c` — the `U⊗U*`-twirled resource acts as a
depolarizing channel whose identity (`k=0`) Pauli contributes weight `1` and whose
three nontrivial Paulis each contribute the Haar constant `c`. -/
noncomputable def teleportAvgFidelity (F c : ℝ) : ℝ := F + (1 - F) * c

/-- **Horodecki qubit formula** `f_avg = (2F + 1)/3`, recovered from the skeleton
under the tracked Haar hypothesis `c = 1/3`. The `1/3` is a discharged hypothesis,
not an axiom. -/
theorem teleportAvgFidelity_horodecki (F : ℝ) {c : ℝ} (hc : HaarPauliConstant c) :
    teleportAvgFidelity F c = (2 * F + 1) / 3 := by
  unfold teleportAvgFidelity HaarPauliConstant at *
  rw [hc]; ring

/-- Perfect resource (`F = 1`) ⇒ perfect teleportation (`f_avg = 1`), independent of
the Haar constant. -/
theorem teleportAvgFidelity_one (c : ℝ) : teleportAvgFidelity 1 c = 1 := by
  unfold teleportAvgFidelity; ring

/-- At the entanglement threshold `F = 1/2` the fidelity hits the **classical bound
`2/3`** (Massar–Popescu PRL 74, 1259 (1995)) — the best achievable without entanglement. -/
theorem teleportAvgFidelity_classical_at_half {c : ℝ} (hc : HaarPauliConstant c) :
    teleportAvgFidelity (1 / 2) c = 2 / 3 := by
  unfold teleportAvgFidelity HaarPauliConstant at *
  rw [hc]; norm_num

/-- **`f_avg` is strictly increasing in the fully-entangled fraction** (the Haar
constant satisfies `c < 1`): a better resource gives strictly better teleportation. -/
theorem teleportAvgFidelity_strictMono {c : ℝ} (hc : HaarPauliConstant c) :
    StrictMono (fun F => teleportAvgFidelity F c) := by
  unfold HaarPauliConstant at hc
  intro a b hab
  simp only [teleportAvgFidelity]
  rw [hc]; linarith

/-- **Entanglement-utility threshold (Horodecki / Massar–Popescu).** The average
teleportation fidelity beats the classical bound `2/3` **iff** the fully-entangled
fraction exceeds `1/2`, i.e. iff the resource is entangled-useful. Headline of W3. -/
theorem teleport_beats_classical_iff (F : ℝ) {c : ℝ} (hc : HaarPauliConstant c) :
    2 / 3 < teleportAvgFidelity F c ↔ 1 / 2 < F := by
  unfold teleportAvgFidelity HaarPauliConstant at *
  rw [hc]; constructor <;> intro h <;> linarith

/-- **Teleportation usefulness over the repeater chain.** Using the `k`-swap Werner
end-to-end state (Phase 6AB) as the teleportation resource, the average teleportation
fidelity beats the classical `2/3` **iff** the `k`-fold Werner parameter exceeds `1/3`
— composing this wave's threshold with the shipped `endToEnd_teleportation_useful`. -/
theorem teleport_useful_over_chain (F : ℝ) (k : ℕ) {c : ℝ} (hc : HaarPauliConstant c) :
    2 / 3 < teleportAvgFidelity (endToEndFidelity F k) c ↔ 1 / 3 < (wernerParam F) ^ k := by
  rw [teleport_beats_classical_iff _ hc, endToEnd_teleportation_useful]

end SKEFTHawking.QuantumNetwork
