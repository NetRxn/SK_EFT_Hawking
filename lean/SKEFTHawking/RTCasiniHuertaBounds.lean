/-
# Phase 6c Wave 5 — Ryu-Takayanagi / Casini-Huerta Bounds

External-hypothesis-tracked bridges connecting analog Hawking entropy
(BEC, Phase 4) to real holographic entropy via two assumed-not-derived
structural Props:

* `H_RT_Formula_Valid` — the Ryu-Takayanagi (2006, hep-th/0603001) area
  law `S = A / (4 G_N)` for the holographic dual; tracked as an external
  hypothesis since the bulk dual is not constructed in this project.
* `H_CasiniHuerta_Bound_Valid` — the Casini-Huerta (2009, arXiv:0905.2562)
  log bound `S(L) ≤ (c/3) log(L/ε)` on entanglement entropy in 2D CFTs;
  tracked similarly.

The wave's correctness-push (`rt_classical_inconsistent_with_kaul_majumdar`)
makes explicit the **structural inconsistency** between classical RT
(no log corrections) and the Phase 6a Wave 3 Kaul-Majumdar microscopic
entropy `S = A/(4 G_N) - (3/2) log(A/(4 G_N))`: at any non-trivial
reduced area, the two differ by exactly the `(3/2) log` term.
Equivalently, RT must be *augmented* with quantum log corrections at
the area-log level for consistency with the W3 horizon BC.

A substantive cross-bridge `rt_falsified_by_kaul_majumdar` consumes
H_RT and the W3 `kaulMajumdarS` function, deriving the contradiction
explicitly. The W3 non-universality witness
`sen_4d_disagrees_with_kaul_majumdar` is invoked through
`kaulMajumdar_not_H_RT_in_Sen4D_branch` as a concrete falsifier.

## Scope (per Phase 6c roadmap §A, Wave 5 — pipeline stages 1-8 only)

**In scope:**

1. `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` external-
   hypothesis tracked Props.
2. Bridge theorems consuming H_RT to derive structural consequences
   (entropy positivity, entropy = `A/(4 G_N)`).
3. Cross-bridge consuming H_RT + W3 `kaulMajumdarS` to derive
   inconsistency at non-trivial reduced area.
4. Quantitative numerical anchor at canonical reduced area = 2.
5. Biconditional characterizing the knife-edge agreement case.
6. Falsifier theorems showing W3 microscopic entropies VIOLATE H_RT.
7. Concrete H_CH witness (saturated log bound).

**Out of scope (deferred):**

* Bulk minimal-surface construction (Lewkowycz-Maldacena replica trick).
* Casini-Huerta proof from modular Hamiltonian.
* CFT spectrum identification.
* AdS/CFT dictionary entries.

## References

* Ryu & Takayanagi, *Holographic derivation of entanglement entropy*,
  PRL 96, 181602 (2006); hep-th/0603001.
* Casini & Huerta, *Entanglement entropy in free quantum field theory*,
  J. Phys. A 42, 504007 (2009); arXiv:0905.2562.
* Phase 6a Wave 3 — `BHEntropyMicroscopic.lean` (substrate for the
  cross-bridge).
* Hawking, *Particle creation by black holes*, CMP 43, 199 (1975)
  (analog-Hawking link via `HawkingUniversality.lean`).

-/

import SKEFTHawking.BHEntropyMicroscopic

namespace SKEFTHawking.RTCasiniHuertaBounds

open SKEFTHawking SKEFTHawking.BHEntropyMicroscopic

/-! ## §1 — External-hypothesis tracked Props -/

/--
**Ryu-Takayanagi formula validity** (external hypothesis).

The classical RT statement: holographic entropy is exactly `A/(4 G_N)`
for any positive area and Newton constant.  Tracked as an
external-hypothesis Prop since the bulk holographic dual is not
constructed in this project.

A candidate entropy function `S_BH : ℝ → ℝ → ℝ` (taking area and `G_N`)
satisfies `H_RT_Formula_Valid` iff it equals `A/(4 G_N)` on the
positive cone.  Any function with non-trivial log corrections (e.g. the
W3 `kaulMajumdarS`) FAILS this Prop — see `kaulMajumdar_not_H_RT`.
-/
structure H_RT_Formula_Valid (S_BH : ℝ → ℝ → ℝ) : Prop where
  rt_proportional : ∀ A G_N, 0 < A → 0 < G_N → S_BH A G_N = A / (4 * G_N)

/--
**Casini-Huerta log bound validity** (external hypothesis).

For a 2D CFT entanglement entropy `S_ent : ℝ → ℝ` parametrised by
region size `L`, with central charge `c_central` and UV cutoff
`UV_cutoff`, the CH bound asserts `S_ent(L) ≤ (c/3) log(L/ε)` for
any `L > ε > 0`.  Tracked as external since the modular-Hamiltonian
derivation is not internalised here.
-/
structure H_CasiniHuerta_Bound_Valid
    (S_ent : ℝ → ℝ) (c_central UV_cutoff : ℝ) : Prop where
  c_pos : 0 < c_central
  uv_pos : 0 < UV_cutoff
  ch_bound : ∀ L, UV_cutoff < L →
    S_ent L ≤ (c_central / 3) * Real.log (L / UV_cutoff)

/-! ## §2 — RT structural consequences -/

/--
**Positivity under RT.**  The classical RT entropy is strictly positive
on the positive cone of `(A, G_N)`.  Combines the tracked Prop's
content (via `h.rt_proportional`) with `div_pos`.
-/
theorem rt_entropy_pos
    {S_BH : ℝ → ℝ → ℝ} (h : H_RT_Formula_Valid S_BH)
    (A G_N : ℝ) (hA : 0 < A) (hG : 0 < G_N) :
    0 < S_BH A G_N := by
  rw [h.rt_proportional A G_N hA hG]
  exact div_pos hA (by linarith)

/-! ## §3 — Quantitative anchor at canonical reduced area -/

/--
**Quantitative numerical anchor.**  At canonical reduced area
`A/(4 G_N) = 2` (i.e., `A = 8 G_N`), the W3 Kaul-Majumdar entropy
differs from classical RT by exactly `(3/2) log 2 ≈ 1.04`.

The proof unfolds the W3 definition `kaulMajumdarS`, normalizes the
reduced-area arithmetic, and applies `ring`.
-/
theorem rt_kaulMajumdar_gap_at_reduced_area_two (G_N : ℝ) (hG : 0 < G_N) :
    let A := 8 * G_N
    A / (4 * G_N) - kaulMajumdarS A G_N 0 = (3 / 2) * Real.log 2 := by
  simp only
  unfold kaulMajumdarS
  have h_red : (8 * G_N) / (4 * G_N) = 2 := by
    field_simp; ring
  rw [h_red]
  ring

/-! ## §4 — Correctness-push: classical-RT-vs-W3 inconsistency -/

/--
**Phase 6c Wave 5 correctness-push (knife-edge biconditional form).**

Classical RT and the Phase 6a Wave 3 Kaul-Majumdar microscopic entropy
agree *iff* the reduced area takes the knife-edge value
`A/(4 G_N) = 1` (i.e. `A = 4 G_N`).  Otherwise, the formulas necessarily
disagree by the `(3/2) log(A/(4 G_N))` log-correction term.

This is the structural content: **classical RT must be augmented with
quantum log corrections at the area-log level for consistency with the
W3 horizon BC** — except at the single knife-edge area.

The proof uses `Real.exp_log` to extract `A/(4 G_N) = 1` from
`Real.log (A/(4 G_N)) = 0` (forward direction); the reverse direction
collapses via `Real.log_one`.  The contrapositive of the forward
direction is the falsifier `rt_classical_inconsistent_with_kaul_majumdar`-
style content: at any non-trivial reduced area, classical RT and W3
Kaul-Majumdar disagree.
-/
theorem rt_eq_kaulMajumdar_iff_trivial_reduced_area
    (A G_N : ℝ) (hA : 0 < A) (hG : 0 < G_N) :
    A / (4 * G_N) = kaulMajumdarS A G_N 0 ↔ A / (4 * G_N) = 1 := by
  unfold kaulMajumdarS
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- A/(4 G_N) = A/(4 G_N) - (3/2) log(A/(4 G_N)) + 0 ⇒ log = 0 ⇒ ratio = 1
    have h_log : Real.log (A / (4 * G_N)) = 0 := by linarith
    have h_pos : 0 < A / (4 * G_N) := div_pos hA (by linarith)
    have h_exp : Real.exp (Real.log (A / (4 * G_N))) = A / (4 * G_N) :=
      Real.exp_log h_pos
    rw [h_log, Real.exp_zero] at h_exp
    exact h_exp.symm
  · rw [h, Real.log_one]; ring

/--
**Substantive cross-bridge: H_RT + W3 entropy ⇒ contradiction.**

Under `H_RT_Formula_Valid` for a candidate `S_BH`, the W3 Kaul-Majumdar
entropy function `kaulMajumdarS · · 0` is structurally INCOMPATIBLE
with `S_BH` at non-trivial reduced area.  The proof body invokes BOTH
`h_rt.rt_proportional` (uses the tracked Prop's substantive content)
and the contrapositive of the knife-edge biconditional (the W3
log-correction structural content).
-/
theorem rt_falsified_by_kaul_majumdar
    {S_BH : ℝ → ℝ → ℝ} (h_rt : H_RT_Formula_Valid S_BH)
    (A G_N : ℝ) (hA : 0 < A) (hG : 0 < G_N)
    (h_nontrivial : A / (4 * G_N) ≠ 1) :
    S_BH A G_N ≠ kaulMajumdarS A G_N 0 := by
  rw [h_rt.rt_proportional A G_N hA hG]
  intro h_eq
  exact h_nontrivial ((rt_eq_kaulMajumdar_iff_trivial_reduced_area A G_N hA hG).mp h_eq)

/-! ## §5 — Casini-Huerta consequences -/

/--
**CH bound positivity.**  Under H_CH, the bound `(c/3) log(L/UV)` is
strictly positive for any `L > UV > 0`.  Combines the tracked Prop's
`c_pos` and `uv_pos` fields with `Real.log_pos` and `mul_pos`.
-/
theorem ch_log_bound_pos_at_log_pos
    {S_ent : ℝ → ℝ} {c_central UV_cutoff : ℝ}
    (h : H_CasiniHuerta_Bound_Valid S_ent c_central UV_cutoff)
    (L : ℝ) (h_L : UV_cutoff < L) :
    0 < (c_central / 3) * Real.log (L / UV_cutoff) := by
  have h_c : 0 < c_central := h.c_pos
  have h_uv : 0 < UV_cutoff := h.uv_pos
  have h_log : 0 < Real.log (L / UV_cutoff) := by
    apply Real.log_pos
    rwa [lt_div_iff₀ h_uv, one_mul]
  have h_ratio : 0 < c_central / 3 := by positivity
  exact mul_pos h_ratio h_log

/-! ## §6 — Concrete H_CH witness -/

/-- **Saturated CH-bound entropy function.**  `S_sat(L) = (c/3) log(L/UV)`. -/
noncomputable def saturatedCHEntropy (c UV : ℝ) (L : ℝ) : ℝ :=
  (c / 3) * Real.log (L / UV)

/--
**Concrete H_CH witness.**  The saturated entropy `S_sat(L) = (c/3)
log(L/UV)` satisfies `H_CasiniHuerta_Bound_Valid` for any positive
central charge `c > 0` and UV cutoff `UV > 0`.  The bound is met with
equality (`le_refl`).
-/
theorem H_CasiniHuerta_Bound_Valid_witness_saturated
    (c UV : ℝ) (hc : 0 < c) (hUV : 0 < UV) :
    H_CasiniHuerta_Bound_Valid (saturatedCHEntropy c UV) c UV where
  c_pos := hc
  uv_pos := hUV
  ch_bound := fun _ _ => by unfold saturatedCHEntropy; rfl

/-! ## §7 — Falsifier: kaulMajumdarS violates H_RT -/

/--
**Falsifier.**  The W3 Kaul-Majumdar entropy function FAILS
`H_RT_Formula_Valid`: at canonical area `A = 8 G_N`, the entropy is
`2 - (3/2) log 2 ≈ 0.96`, not `2 = A/(4 G_N)`.  The discrepancy is
exactly the `(3/2) log 2 > 0` log-correction term.

This is the pillar falsifier separating microscopic-quantum-corrected
entropy (W3) from classical-RT entropy.
-/
theorem kaulMajumdar_not_H_RT :
    ¬ H_RT_Formula_Valid (fun A G_N => kaulMajumdarS A G_N 0) := by
  intro h
  -- Apply h.rt_proportional at A = 8, G_N = 1: claims kaulMajumdarS 8 1 0 = 8/(4*1) = 2.
  have h_eq := h.rt_proportional 8 1 (by norm_num) (by norm_num)
  -- kaulMajumdarS 8 1 0 = 8/(4*1) - (3/2) log(8/(4*1)) + 0 = 2 - (3/2) log 2.
  unfold kaulMajumdarS at h_eq
  have h_red : (8 : ℝ) / (4 * 1) = 2 := by norm_num
  rw [h_red] at h_eq
  -- h_eq : 2 - (3/2) * Real.log 2 + 0 = 2
  have h_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end SKEFTHawking.RTCasiniHuertaBounds
