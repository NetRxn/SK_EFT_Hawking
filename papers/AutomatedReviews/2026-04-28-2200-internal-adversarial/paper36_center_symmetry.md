---
paper: paper36_center_symmetry
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper36_center_symmetry

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`CenterSymmetryConfinement.lean` ships 20 substantive theorems with
load-bearing bodies; the `KSS_BOUND` bracket [0.07, 0.08] is a true
mathematical theorem (uses `Real.pi_gt_d4` and `Real.pi_lt_d4` to
derive a 12%-wide bracket — outside the within-own-tolerance regime).
Class 1 cache-skip on all seven bibitems. One REQUIRED issue: the
paper claims `\nu_{\mathrm{Potts}} = 0.5` "reflects the mean-field-like /
weakly-first-order nature of the 3D 3-state Potts transition," but
the 3D 3-state Potts transition is *first-order* (not weakly), so a
correlation-length critical exponent ν is not strictly defined for it
— ν = 0.5 is a *placeholder mean-field value*, not a measured exponent.
This is a parameter-provenance / narrative issue: prose treats it as a
literature-anchored value when it is in fact a placeholder. Two
RECOMMENDED issues on `centerPhase_Z2_eq_neg_one` (already substantive)
and the `0 < 4 * π` proof that's correct but trivially close to
within-tolerance.

## Findings

### 5.1 — 🟡 REQUIRED — 3D 3-state Potts transition is first-order; ν = 0.5 is not a measured exponent

- **Gate:** ParameterProvenance (Gate 3) / NarrativeGrounding (Gate 7)
- **Location:** `paper36_center_symmetry/paper_draft.tex:155-160, 230-232`; `lean/SKEFTHawking/CenterSymmetryConfinement.lean:218-225`
- **Observed:** Paper §IV: "ν_Potts = 0.5 ... reflects the mean-field-like / weakly-first-order nature of the 3D 3-state Potts transition." The 3D 3-state Potts transition is *first-order* (not weakly first-order); the standard physics literature (e.g., Wu 1982 Rev. Mod. Phys. 54, 235; Janke & Villanova 1997) treats it as discontinuous, with a small but non-zero latent heat. A correlation-length critical exponent ν is not a measured parameter for a first-order transition — the correlation length stays finite at the transition. Setting ν_Potts = 0.5 as a numerical literature anchor is misleading. The Lean theorem `ising_nu_gt_potts_nu` then compares 0.6299 (true Ising exponent) with 0.5 (placeholder), giving a "structural" inequality that is not a comparison between two measured exponents.
- **Evidence:** `CenterSymmetryConfinement.lean:218-225`: `critical_exponent_nu UniversalityClass.three_state_Potts => 0.5  -- 3D 3-state Potts (mean-field-like, weak first order)`. The Wikipedia/RMP standard for 3D 3-state Potts: weakly first-order in some early studies, but established as first-order in modern lattice work. A genuine continuous-transition ν exponent does not exist.
- **Expected:** Either (a) state explicitly that ν_Potts = 0.5 is a *placeholder mean-field value* used for structural comparison, not a measured critical exponent, or (b) replace with a *latent-heat scale* or *correlation length at T_c* that is genuinely measurable for a first-order transition.
- **Fix:** Add a paper paragraph at §IV (around line 156-160) noting "the 3D 3-state Potts transition is first-order, so ν is not a measured exponent; the value 0.5 is a mean-field placeholder used to mark the Z_3 vs. Z_2 separation structurally." Update the Lean docstring at `CenterSymmetryConfinement.lean:223` from "mean-field-like, weak first order" to "placeholder mean-field value (transition is first-order, ν is not measured)." Optionally add a project parameter-provenance entry tagging this as `PROJECTED` / placeholder rather than primary-source-anchored.

### 3.1 — 🔵 RECOMMENDED — `ising_nu_above_0_6 : 0.6 < critical_exponent_nu UniversalityClass.Ising` proof reduces to `norm_num` on `0.6 < 0.6299`

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/CenterSymmetryConfinement.lean:232-235`
- **Observed:** Proof body unfolds the `match` and runs `norm_num` on `0.6 < 0.6299`. The structural content is just an inequality between two numeric literals; the load-bearing physics content lives in the choice of `0.6299` as the Ising exponent (which the Lean module documents in its docstring but does not back by a primary-source citation in the formalization itself).
- **Evidence:** `CenterSymmetryConfinement.lean:232-235`. The threshold "0.6" is somewhat arbitrary; the more substantive theorem `ising_nu_gt_potts_nu` (line 253-257) compares the two literature values directly without a fixed threshold.
- **Expected:** `ising_nu_above_0_6` and `potts_nu_below_0_6` are individually weak; consolidate into a single substantive theorem (the existing `ising_nu_gt_potts_nu` already does this — those threshold theorems become redundant).
- **Fix:** Consider deleting `ising_nu_above_0_6` and `potts_nu_below_0_6`, or downgrading them to a single combined "Ising vs. Potts ν exponents bracketed around 0.6" lemma. The substantive comparison `ising_nu_gt_potts_nu` is sufficient.

### 6.1 — 🔵 RECOMMENDED — `walker_wang_witness_at_kss_lower` is a witness with `eta = KSS_BOUND` boundary case; document load-bearing assumptions

- **Gate:** AssumptionDisclosure (Gate 6)
- **Location:** `paper36_center_symmetry/paper_draft.tex:201-211`; `lean/SKEFTHawking/CenterSymmetryConfinement.lean:322-327`
- **Observed:** The Walker-Wang correctness-push tracked Prop is `H_WalkerWangTransportNearKSS (eta_over_s : ℝ) := KSS_BOUND ≤ eta_over_s ∧ eta_over_s ≤ 2 * KSS_BOUND`. The witness `walker_wang_witness_at_kss_lower` saturates the lower bound at `eta = KSS_BOUND`. Paper §V lists two falsifiers (η = 0 and η = 1) but does not list the witness. A reader who scans only the paper might think the predicate is only used in falsifier mode.
- **Evidence:** Paper §V lists the falsifiers (lines 213-220) but not the witness.
- **Expected:** Mention the witness explicitly so the reader sees the bracket has both an existence proof and falsifiers.
- **Fix:** Add to paper §V: "A boundary witness theorem `walker_wang_witness_at_kss_lower` confirms the predicate is non-vacuous: η/s = KSS\_BOUND saturates the lower bound."

### 5.2 — 🔵 RECOMMENDED — abstract "20 substantive Lean theorems" matches; counts.tex retrofit

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `paper36_center_symmetry/paper_draft.tex:48, 266`
- **Observed:** Both abstract and §formalization say "20 substantive theorems." `grep -cE "^theorem " CenterSymmetryConfinement.lean = 20`. Match.
- **Expected:** Same retrofit advisory as paper 35.

## Class 1 cache-skip summary

All seven bibitems are major published works:
- `SvetitskyYaffe1982` — Nucl. Phys. B 210, 423 (1982) — `cache-skip`.
- `KovtunSonStarinets2005` — arXiv:hep-th/0405231, PRL 94, 111601 (2005) — `cache-skip`.
- `HofmanIqbal2018` — arXiv:1707.08577, SciPost Phys. 4, 005 (2018) — `cache-skip`.
- `PelissettoVicari2002` — arXiv:cond-mat/0012164, Phys. Rep. 368, 549 (2002) — `cache-skip`.
- `KosPolandSimmonsDuffin2016` — arXiv:1603.04436, JHEP 03, 086 (2016) — `cache-skip`.
- `Polyakov1978` — Phys. Lett. B 72, 477 (1978) — `cache-skip` (also cited in paper 38).
- `KitaevAnyons2003` — arXiv:quant-ph/9707021 — `cache-skip` (also cited in paper 35).

## Class 4 cross-paper consistency

`Polyakov1978` shared with paper 38 (CFL); both bibitems are identical (Phys. Lett. B 72, 477 (1978)). Consistent.
`KitaevAnyons2003` shared with paper 35 (QEC); both bibitems are identical. Consistent.

## Class 3 substantive-body confirmation

All 20 cited theorems inspected; bodies use real Mathlib lemmas (`Complex.exp_eq_one_iff`, `Complex.norm_exp`, `Real.pi_gt_d4`, `nlinarith`, `Finset.single_le_sum`-style sum bounds elsewhere). No `rfl`-on-non-trivial bodies. The KSS bracket [0.07, 0.08] is genuinely substantive (`norm_num` on the Mathlib π bound).
