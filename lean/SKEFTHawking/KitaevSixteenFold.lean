/-
# Phase 5q.E Wave 1 — The Kitaev 16-fold way: genuine chiral-central-charge arithmetic

This module ships the **algebraic heart** of the Kitaev "16-fold way" facet of the
so-called "16 convergence" (see `docs/SIXTEEN_CONVERGENCE_STATUS.md`). It supersedes
*in content* (not by deletion) the previously-vacuous placeholders in `Z16Classification.lean`
(`sixteen_fold_way_DEFINITIONAL : (16 : ℕ) = 16`,
`svec_sixteen_extensions : Fintype.card (Fin 16) = 16`,
`svec_extension_central_charge : ∀ N : Fin 16, ↑N + 1 ≤ 16`) — those remain there only as
documented-vacuous cardinality witnesses (annotated to point here; do not double-count). The
genuine, falsifiable content they gesture at is:

  * the chiral central charge of the ν-th phase is `c₋(ν) = ν/2`
    (`ν` Majorana edge modes / the `SO(ν)₁` edge WZW theory, Kitaev AIP 1134 (2009));
  * **faithfulness** — the 16 central charges `c₋(0), …, c₋(15)` are pairwise distinct
    **mod 8** (`kitaevCentralCharge_faithful`). This is the actual "16-fold" statement:
    the topological central charge mod 8, equivalently the Gauss-sum anomaly phase
    `e^{2πiν/16} ∈ μ₁₆`, is a complete invariant separating the 16 phases. A typo making
    the period 8 (rather than 16) or `c₋ = ν/4` would falsify it; the old placeholders
    `(16:ℕ)=16` / `card (Fin 16)=16` would not.

## What this is, and what it is NOT (honesty — load-bearing, keep in any paper)

This is the **algebraic shadow** of the Kitaev facet, not a bordism-theoretic
identification of it with the other 16s. The faithful ℤ₁₆ here is the additive group
of phase labels with its central-charge character; tying it to the Rokhlin signature
ℤ₁₆ and the Dai–Freed anomaly ℤ₁₆ requires the *Smith homomorphism* and computed
`Ω₄^{Pin⁺}/Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆`, which are Mathlib-absent (Phase 5q.E roadmap §"Walls").
A shared ℤ₁₆ **constrains, it does not derive**. `§4` below gives the one honest
cross-facet bridge buildable now: the Rokhlin→Kitaev *anomaly-inflow shadow*, carried
through the gravitational-anomaly index relation `c₋ = σ/2` as an **explicit named
hypothesis** — the relation's bulk-boundary justification is itself the documented wall,
so the theorem is honestly conditional.

The 3-generation physics headline (`generation_constraint_iff`) is independent of all
of this and does not import this module.

## References
  - Kitaev, AIP Conf. Proc. 1134, 22 (2009) — the 16-fold way.
  - Bruillard–Galindo–Ng–Plavnik–Rowell–Wang, J. Math. Phys. 58, 041704 (2017) —
    super-modular minimal modular extensions as a ℤ₁₆-torsor.
  - `WangBridge.lean::weyl_central_charge` — `c₋(n) = n/2` for `n` Weyl fermions.
  - `Z16AnomalyComputation.lean` — the SM ℤ₁₆ anomaly arithmetic.
  - `docs/SIXTEEN_CONVERGENCE_STATUS.md`, `docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md`.
-/

import Mathlib
import SKEFTHawking.WangBridge
import SKEFTHawking.SMFermionData

namespace SKEFTHawking.Kitaev16

/-! ## §1. The chiral central charge of the ν-th Kitaev phase -/

/-- Chiral central charge of the ν-th Kitaev phase: `c₋(ν) = ν/2`.

Modeling input (per Kitaev 2009): `ν` counts the chiral Majorana edge modes (the
`SO(ν)₁` edge theory), each contributing `1/2` to the chiral central charge — the same
`n ↦ n/2` convention as `WangBridge.weyl_central_charge`. The substantive content of
this module lives in the theorems below (faithfulness, periodicity, the bosonic/fermionic
split), not in this definition. -/
def kitaevCentralCharge (ν : ℤ) : ℚ := (ν : ℚ) / 2

/-- The ℤ₁₆ class of the ν-th phase: the doubled central charge `2·c₋(ν) = ν` reduced
mod 16 — equivalently the Gauss-sum anomaly phase `e^{2πiν/16}` read as an element of
`ℤ/16`. (`2 · kitaevCentralCharge ν = ν`, a definitional `ring` identity, is why this
records the doubled charge.) -/
def kitaevClass (ν : ℤ) : ZMod 16 := (ν : ZMod 16)

/-- **Mod-8 periodicity**: `c₋(ν + 16) = c₋(ν) + 8`, i.e. the central charge is invariant
mod 8 under `ν ↦ ν + 16` (`SO(ν+16)₁` and `SO(ν)₁` agree mod 8). Paired with
`kitaevCentralCharge_faithful` (the 16 values are distinct mod 8) this pins the period at
**exactly** 16 — the "16" of the 16-fold way. -/
theorem kitaevCentralCharge_period16 (ν : ℤ) :
    kitaevCentralCharge (ν + 16) = kitaevCentralCharge ν + 8 := by
  unfold kitaevCentralCharge; push_cast; ring

/-- **Faithfulness — the heart of the 16-fold way.** For `ν, μ ∈ {0, …, 15}`, the central
charges agree mod 8 (`∃ k, c₋(ν) − c₋(μ) = 8k`) **iff** `ν = μ`. So the 16 phases carry 16
genuinely distinct central charges mod 8; the topological central charge mod 8 is a complete
invariant. Falsifiable: a wrong central-charge slope or a period below 16 would break it. -/
theorem kitaevCentralCharge_faithful (ν μ : ℤ)
    (hν : 0 ≤ ν) (hν' : ν < 16) (hμ : 0 ≤ μ) (hμ' : μ < 16) :
    (∃ k : ℤ, kitaevCentralCharge ν - kitaevCentralCharge μ = 8 * k) ↔ ν = μ := by
  unfold kitaevCentralCharge
  constructor
  · rintro ⟨k, hk⟩
    have h2 : (ν : ℚ) - (μ : ℚ) = 16 * (k : ℚ) := by linear_combination 2 * hk
    have h3 : ν - μ = 16 * k := by exact_mod_cast h2
    omega
  · rintro rfl; exact ⟨0, by ring⟩

/-! ## §2. The bosonic/fermionic split — the "8 doubled to 16" shadow -/

/-- A Kitaev phase has **integer** central charge iff its label `ν` is even. The even-`ν`
phases are the *bosonic* (non-spin) sector; the odd-`ν` phases are genuinely fermionic
(half-integer `c₋`). This is the algebraic shadow of the KO/Bott "period 8 → 16" doubling
by the spin structure (the KO-theoretic *origin* is the Mathlib-absent wall, Phase 5q.E
roadmap). -/
theorem kitaev_integral_charge_iff_even (ν : ℤ) :
    (∃ m : ℤ, kitaevCentralCharge ν = (m : ℚ)) ↔ Even ν := by
  unfold kitaevCentralCharge
  constructor
  · rintro ⟨m, hm⟩
    have h2 : (ν : ℚ) = 2 * (m : ℚ) := by linear_combination 2 * hm
    have hz : ν = 2 * m := by exact_mod_cast h2
    exact ⟨m, by omega⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-- **Exactly 8 of the 16 phases are bosonic.** The integer-central-charge (even-`ν`)
classes form the unique index-2 subgroup `2·(ℤ/16) ≅ ℤ/8` — the "8" sitting inside the
"16". Decidable over `ZMod 16`. -/
theorem kitaev_eight_bosonic_phases :
    (Finset.univ.filter (fun ν : ZMod 16 => ∃ m : ZMod 16, ν = 2 * m)).card = 8 := by
  decide

/-! ## §3. Honest bridge to the SM facet -/

/-- **The SM realizes the trivial Kitaev class.** The Standard Model's
`∑ components = 16` Weyl fermions per generation (`total_components_with_nu_R`) give chiral
central charge `c₋ = 8 = c₋(16)` (the `SO(16)₁` value), whose Kitaev ℤ₁₆ class is
`16 ≡ 0` — the SM sits at the *anomaly-free* element of the very ℤ₁₆ whose 16 elements
`kitaevCentralCharge_faithful` shows are genuinely distinct. This is the **explicit
central-charge map** `c ↦ 2c mod 16`, not a bordism identification (that is the wall). -/
theorem sm_realizes_trivial_kitaev_class :
    weyl_central_charge (∑ f : SMFermion, components f) = kitaevCentralCharge 16
      ∧ kitaevClass 16 = 0 := by
  have hcount : (∑ f : SMFermion, components f) = 16 := total_components_with_nu_R
  refine ⟨?_, by decide⟩
  rw [hcount]; unfold weyl_central_charge kitaevCentralCharge; norm_num

/-- For `N_f` complete generations (each `16` Weyl with `ν_R`), the Kitaev class is
`16·N_f ≡ 0`: every complete-generation count lands on the trivial element. This is the
same arithmetic as `RokhlinBridge.z16_anomaly_always_cancels_with_nu_R` (the SM ℤ₁₆
anomaly cancellation), now read through the Kitaev central-charge map. -/
theorem sm_kitaev_class_eq_anomaly_cancellation (N_f : ℕ) :
    kitaevClass (16 * N_f) = 0 := by
  unfold kitaevClass
  push_cast
  rw [show (16 : ZMod 16) = 0 from by decide]
  ring

/-! ## §4. Honest anomaly-inflow shadow: Rokhlin → bosonic boundary -/

/-- **Rokhlin forces a bosonic boundary (conditional anomaly-inflow shadow).** Given the
gravitational-anomaly index relation `c₋ = σ/2` (Atiyah–Singer; supplied here as an
**explicit hypothesis** — its bulk-boundary justification is the Mathlib-absent
identification, the documented wall) together with Rokhlin's `16 ∣ σ` for a smooth-spin
bulk, the boundary central charge lands in the bosonic index-8 subgroup `8ℤ`. I.e. a
smooth-spin 4-manifold bulk can host only the *even* (bosonic) Kitaev phases at its
boundary. Both hypotheses are load-bearing: drop `16 ∣ σ` and `c₋` may be any half-integer. -/
theorem rokhlin_forces_bosonic_boundary (σ : ℤ) (c : ℚ)
    (h_index : c = (σ : ℚ) / 2) (h_rokhlin : (16 : ℤ) ∣ σ) :
    ∃ m : ℤ, c = 8 * m := by
  obtain ⟨t, ht⟩ := h_rokhlin
  exact ⟨t, by rw [h_index, ht]; push_cast; ring⟩

/-! ## §5. Module summary

Genuine Kitaev-16-fold content (supersedes *in content* the documented-vacuous
`Z16Classification` placeholders — which remain there as annotated cardinality witnesses):
  - `kitaevCentralCharge ν = ν/2`, `kitaevClass ν = ν mod 16` (the doubled charge).
  - `kitaevCentralCharge_period16` — central charge invariant mod 8 under `ν ↦ ν+16`.
  - `kitaevCentralCharge_faithful` — the 16 charges are pairwise distinct mod 8 (THE 16-fold).
  - `kitaev_integral_charge_iff_even` + `kitaev_eight_bosonic_phases` — the bosonic index-8
    sub-sector (the "8 doubled to 16" shadow).
  - `sm_realizes_trivial_kitaev_class`, `sm_kitaev_class_eq_anomaly_cancellation` — the SM
    lands on the trivial ℤ₁₆ element via the explicit central-charge map.
  - `rokhlin_forces_bosonic_boundary` — honest conditional inflow shadow (Rokhlin → bosonic),
    with the index relation as an explicit hypothesis and the bulk-boundary map flagged as a wall.

All kernel-pure (`propext`, `Classical.choice`, `Quot.sound`); no axiom / sorry / native_decide.
-/

end SKEFTHawking.Kitaev16
