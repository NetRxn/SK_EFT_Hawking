import SKEFTHawking.Basic
import SKEFTHawking.WKBConnection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kibble-Zurek-Unruh Correspondence

## Overview

This module formalizes the **Kibble-Zurek-Unruh (KZ-U) correspondence**, the
bridge between (i) the universal Kibble-Zurek mechanism (KZM) describing the
freeze-out of a system driven through a continuous quantum phase transition at
finite rate, and (ii) the analog-Hawking radiation from a sonic horizon. Both
phenomena are governed by a single rate parameter — the quench rate `τ_Q^{-1}`
for KZM, the surface gravity `κ` for the horizon — and the KZ-U correspondence
identifies the two:

  `τ_Q^{-1} ≡ κ`   (horizon-crossing rate = effective quench rate)

The thermal distribution of horizon-produced quasiparticles is then the KZM
analog of the Hawking thermal spectrum at temperature `T_H = κ / (2π)` (in
natural units `ℏ = k_B = 1`).

## Four distinct Kibble-Zurek exponents

The literature writes "the Kibble-Zurek exponent" for at least four different
quantities built from the same critical data `(ν, z)`. They are NOT
interchangeable, and only one of them is universally bounded by `1`. A claim
about "the Kibble-Zurek exponent" is therefore not well posed until it names
which one; this module names all four and proves the relations between them, so
that a value quoted in one convention can be converted rather than compared.

| quantity | scaling | this module |
|---|---|---|
| freeze-out **time** | `t̂ ~ τ_Q^{νz/(1+νz)}` | `kzmFreezeOutTimeExponent` |
| freeze-out **length** | `ξ̂ ~ τ_Q^{ν/(1+νz)}` | `kzmFreezeOutLengthExponent` |
| defect **density** in `d` dimensions | `n_def ~ τ_Q^{-dν/(1+νz)}` | `kzmDefectDensityExponent` |
| correlation-**collapse** (reciprocal convention) | `ξ̂ ~ τ_Q^{1/μ}` | `kzmCorrelationCollapseExponent` |

Only the freeze-out-**time** exponent lies in `(0,1)` for every `ν, z > 0`
(`kzmFreezeOutTimeExponent_mem_Ioo`). The other three are not so constrained,
and this module ships explicit witnesses that they exceed `1`
(`exists_kzmDefectDensityExponent_one_lt`,
`exists_kzmFreezeOutLengthExponent_one_lt`,
`one_lt_kzmCorrelationCollapseExponent`).

## Substantive content

This module ships:

* `KZMExponents` — universal critical-exponent data `(ν, z)` of a continuous
  quantum phase transition (correlation-length exponent + dynamic exponent).
* The four exponents above as separate definitions, with the reduction laws
  `kzmDefectDensityExponent_eq_dim_mul_length`,
  `kzmFreezeOutTimeExponent_eq_z_mul_length` and
  `kzmCorrelationCollapseExponent_mul_freezeOutLengthExponent` (the last is the
  reciprocal-convention reconciliation used by Tindall et al.).
* `kzmFreezeOutTimeExponent_pos` / `_lt_one` / `_mem_Ioo` — substantive bounds
  `μ_t ∈ (0, 1)` for any positive `ν, z`, together with the three witnesses
  showing that the SAME bound is FALSE for the other three exponents.
* `KZMUnruhBridge` — bridge data linking an `ExactWKBParams` (from
  `WKBConnection.lean`) to a `KZMExponents`; carries the identification
  `1/τ_Q ≡ κ`.
* `kzm_unruh_thermal_matches_hawking` — the KZ-U thermal temperature equals
  `hawkingTemp κ = κ / (2π)` (from `Basic.lean`).
* **Headline:** `kzm_freezeOutTime_exceeds_horizonTime_of_one_lt_kappa` and its
  companion `kzm_freezeOutTime_below_horizonTime_of_kappa_lt_one` — under the
  KZ-U identification `τ_Q = 1/κ`, the freeze-out time `t̂ = τ_Q^{μ_t} =
  κ^{-μ_t}` exceeds the bare horizon-crossing time `κ^{-1}` when `κ > 1` and
  falls below it when `κ < 1`. The pair is genuinely `κ`-dependent: the
  direction of the inequality is decided by the surface gravity and reverses at
  `κ = 1`.

## Physical context

The Tindall, Mello, Fishman, Stoudenmire, Sels paper (Science 392, 868 (2026),
DOI 10.1126/science.adx2728; arXiv:2503.05693) simulates the disordered
transverse-field Ising spin glass of their Eq. (1) with belief-propagation
tensor networks on **cylindrical, diamond cubic, and dimerized cubic** lattices
(p. 2), reaching a system of over 300 qubits. What they extract is NOT a defect
density. It is the collapse exponent of the connected two-point correlation
function `C(d)` of their Eq. (3): rescaling distance as `d̃ = t_a^{-1/μ} d`
collapses `C` across annealing times (their Fig. 5, p. 6, axis label), so their
`μ` obeys `ξ̂ ~ t_a^{1/μ}` and is therefore the RECIPROCAL of the standard KZM
freeze-out-length exponent, `μ = (1 + νz)/ν`. They report `μ ≈ 2.70` (14×14
cylinder) and `μ ≈ 2.75` (18×18 cylinder), against `μ = 2.6 ± 0.3`
(finite-size Monte Carlo), `μ = 3.17 ± 0.41` (thermodynamic limit) and
`μ = 2.67 ± 0.29` (Binder cumulant) (p. 6). None of these lies in `(0,1)`,
and none of them is comparable to `kzmFreezeOutTimeExponent` — which is why the
reconciliation here goes through `kzmCorrelationCollapseExponent` and its
reciprocal law, not through a numerical coincidence. The quantitative check is
`kzmCorrelationCollapseExponent_three_dim_ising_mem_Ioo`.

The annealer comparisons in that work are at 8×8 cylinders and ~50-qubit
three-dimensional lattices (pp. 4-5), not at the 300+ qubit Kibble-Zurek
extraction; this module makes no claim about matching the annealer.

## References

- Tindall, Mello, Fishman, Stoudenmire, Sels, *Dynamics of disordered quantum
  systems with two- and three-dimensional tensor networks*, Science 392,
  868-872 (2026), DOI 10.1126/science.adx2728; arXiv:2503.05693 — independent
  classical-simulation extraction of a Kibble-Zurek correlation-collapse
  exponent on hundreds of qubits.
- Zurek, *Cosmological experiments in superfluid helium?*, Nature 317, 505
  (1985) — original KZM mechanism.
- Kibble, *Topology of cosmic domains and strings*, J. Phys. A 9, 1387 (1976)
  — original cosmological precursor.
- Unruh, *Notes on black-hole evaporation*, PRD 14, 870 (1976) — Unruh
  temperature.
- Anglin, Zurek, *Vortices in the wake of rapid Bose-Einstein condensation*,
  PRL 83, 1707 (1999) — early KZM-Unruh-style discussion in cold atoms.
- Hu, Verdaguer, *Stochastic gravity: theory and applications*, Living Rev.
  Relativity 11, 3 (2008) — finite-rate effects at analog horizons.

-/

namespace SKEFTHawking.KibbleZurekUnruh

open SKEFTHawking
open SKEFTHawking.WKBConnection

/-!
## KZM critical exponents

The universal Kibble-Zurek scaling at a continuous quantum phase transition is
controlled by two exponents:

* `ν` — correlation-length exponent: `ξ ~ |g - g_c|^{-ν}` near critical
  coupling `g_c`.
* `z` — dynamic exponent: characteristic time scale `τ ~ ξ^z`.

Together they fix the freeze-out time `t̂ ~ τ_Q^{νz/(1+νz)}` and the freeze-out
length `ξ̂ ~ τ_Q^{ν/(1+νz)}`; the defect density in `d` spatial dimensions
follows as `n_def ~ ξ̂^{-d} ~ τ_Q^{-dν/(1+νz)}`. For 1D quantum Ising
(`d = ν = z = 1`) the time exponent is `1/2` — the canonical Zurek 1996 result —
and the defect-density exponent coincides with it only because `d = z` there.
-/

/-- KZM critical exponents `(ν, z)` for a continuous quantum phase transition.
    Both `ν` and `z` are strictly positive at any well-defined critical point. -/
structure KZMExponents where
  ν : ℝ
  z : ℝ
  ν_pos : 0 < ν
  z_pos : 0 < z

/-- The common denominator `1 + νz` of every KZM exponent is strictly positive. -/
theorem kzm_denom_pos (e : KZMExponents) : 0 < 1 + e.ν * e.z := by
  have h : 0 < e.ν * e.z := mul_pos e.ν_pos e.z_pos
  linarith

/-- The KZM freeze-out-**time** exponent `μ_t = νz / (1 + νz)`.

    Controls the freeze-out time `t̂ ~ τ_Q^{νz/(1+νz)}` — the instant at which
    the adiabatic-impulse crossover happens for a quench of duration `τ_Q`.
    For 1D TFIM (`ν = z = 1`): `μ_t = 1/2` (Zurek 1996).

    This is the ONLY member of the KZM exponent family that lies in `(0,1)` for
    every positive `ν, z`; see `kzmFreezeOutTimeExponent_mem_Ioo` and the
    counter-witnesses for the other three. -/
noncomputable def kzmFreezeOutTimeExponent (e : KZMExponents) : ℝ :=
  (e.ν * e.z) / (1 + e.ν * e.z)

/-- The KZM freeze-out-**length** exponent `μ_ξ = ν / (1 + νz)`.

    Controls the frozen correlation length `ξ̂ ~ τ_Q^{ν/(1+νz)}`. It is NOT
    bounded above by `1`: see `exists_kzmFreezeOutLengthExponent_one_lt`. -/
noncomputable def kzmFreezeOutLengthExponent (e : KZMExponents) : ℝ :=
  e.ν / (1 + e.ν * e.z)

/-- The KZM defect-**density** exponent in `d` spatial dimensions,
    `μ_n = d·ν / (1 + νz)`, controlling `n_def ~ ξ̂^{-d} ~ τ_Q^{-dν/(1+νz)}`.

    It coincides with `kzmFreezeOutTimeExponent` exactly when `d = z`, which is
    why the 1D TFIM check cannot distinguish the two. It is NOT bounded above by
    `1`: for `d = 3, ν = z = 1` it is `3/2`
    (`exists_kzmDefectDensityExponent_one_lt`). -/
noncomputable def kzmDefectDensityExponent (e : KZMExponents) (d : ℕ) : ℝ :=
  (d : ℝ) * e.ν / (1 + e.ν * e.z)

/-- The correlation-**collapse** exponent `μ = (1 + νz)/ν` in the reciprocal
    convention used by Tindall et al., defined by `ξ̂ ~ τ_Q^{1/μ}` — i.e. by the
    rescaling `d̃ = t_a^{-1/μ} d` that collapses their measured correlation
    function (their Fig. 5, p. 6).

    It is the multiplicative inverse of `kzmFreezeOutLengthExponent`
    (`kzmCorrelationCollapseExponent_mul_freezeOutLengthExponent`) and exceeds
    `1` whenever `z ≥ 1` (`one_lt_kzmCorrelationCollapseExponent`). It is the
    quantity to compare against the `2.6`-to-`3.2` values reported in that
    paper — never `kzmFreezeOutTimeExponent`. -/
noncomputable def kzmCorrelationCollapseExponent (e : KZMExponents) : ℝ :=
  (1 + e.ν * e.z) / e.ν

/-- Substantive lemma: the KZM freeze-out-time exponent is strictly positive.

    Physical meaning: the freeze-out time genuinely scales with the quench
    duration (no flat regime). Follows from `ν > 0` and `z > 0`. -/
theorem kzmFreezeOutTimeExponent_pos (e : KZMExponents) :
    0 < kzmFreezeOutTimeExponent e := by
  unfold kzmFreezeOutTimeExponent
  exact div_pos (mul_pos e.ν_pos e.z_pos) (kzm_denom_pos e)

/-- Substantive lemma: the KZM freeze-out-time exponent is strictly less than `1`.

    Physical meaning: the freeze-out time never grows faster than the quench
    duration itself — the impulse window is always a sublinear fraction of the
    ramp. Follows from `νz > 0` so `νz < 1 + νz`.

    ⚠️ This bound is specific to the freeze-out-TIME exponent. The freeze-out
    length, defect-density and correlation-collapse exponents all admit values
    above `1`; see the three `exists_*_one_lt` / `one_lt_*` witnesses below. -/
theorem kzmFreezeOutTimeExponent_lt_one (e : KZMExponents) :
    kzmFreezeOutTimeExponent e < 1 := by
  unfold kzmFreezeOutTimeExponent
  rw [div_lt_one (kzm_denom_pos e)]
  have h : 0 < e.ν * e.z := mul_pos e.ν_pos e.z_pos
  linarith

/-- The KZM freeze-out-time exponent lives in the open unit interval `(0, 1)`. -/
theorem kzmFreezeOutTimeExponent_mem_Ioo (e : KZMExponents) :
    kzmFreezeOutTimeExponent e ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨kzmFreezeOutTimeExponent_pos e, kzmFreezeOutTimeExponent_lt_one e⟩

/-- The KZM freeze-out-length exponent is strictly positive. -/
theorem kzmFreezeOutLengthExponent_pos (e : KZMExponents) :
    0 < kzmFreezeOutLengthExponent e :=
  div_pos e.ν_pos (kzm_denom_pos e)

/-- Reduction law: the defect-density exponent is `d` copies of the
    freeze-out-length exponent, which is exactly `n_def ~ ξ̂^{-d}`. -/
theorem kzmDefectDensityExponent_eq_dim_mul_length (e : KZMExponents) (d : ℕ) :
    kzmDefectDensityExponent e d = (d : ℝ) * kzmFreezeOutLengthExponent e := by
  unfold kzmDefectDensityExponent kzmFreezeOutLengthExponent
  rw [mul_div_assoc]

/-- Reduction law: the freeze-out-time exponent is `z` copies of the
    freeze-out-length exponent, which is exactly `t̂ ~ ξ̂^z`.

    Together with `kzmDefectDensityExponent_eq_dim_mul_length` this is the
    precise sense in which the time and density exponents agree iff `d = z`. -/
theorem kzmFreezeOutTimeExponent_eq_z_mul_length (e : KZMExponents) :
    kzmFreezeOutTimeExponent e = e.z * kzmFreezeOutLengthExponent e := by
  unfold kzmFreezeOutTimeExponent kzmFreezeOutLengthExponent
  rw [mul_comm e.ν e.z, mul_div_assoc]

/-- **Refutation witness.** The defect-density exponent is NOT universally below
    `1`: at `d = 3`, `ν = z = 1` it equals `3/2`, so a three-dimensional defect
    density scales strictly faster than `τ_Q^{-1}`.

    This is the kernel-checked statement that the `(0,1)` universality proved
    for `kzmFreezeOutTimeExponent` does not transfer to the defect density. -/
theorem exists_kzmDefectDensityExponent_one_lt :
    ∃ (e : KZMExponents) (d : ℕ), 1 < kzmDefectDensityExponent e d := by
  refine ⟨⟨1, 1, one_pos, one_pos⟩, 3, ?_⟩
  unfold kzmDefectDensityExponent
  norm_num

/-- **Refutation witness.** The freeze-out-length exponent is NOT universally
    below `1` either: at `ν = 2`, `z = 1/4` it equals `4/3`. -/
theorem exists_kzmFreezeOutLengthExponent_one_lt :
    ∃ e : KZMExponents, 1 < kzmFreezeOutLengthExponent e := by
  refine ⟨⟨2, 1/4, by norm_num, by norm_num⟩, ?_⟩
  unfold kzmFreezeOutLengthExponent
  norm_num

/-- The correlation-collapse exponent is strictly positive. -/
theorem kzmCorrelationCollapseExponent_pos (e : KZMExponents) :
    0 < kzmCorrelationCollapseExponent e :=
  div_pos (kzm_denom_pos e) e.ν_pos

/-- **Reciprocal law.** The Tindall-convention collapse exponent is the
    multiplicative inverse of the standard KZM freeze-out-length exponent.

    This is the reconciliation between the two conventions: a reported
    `μ ≈ 2.75` corresponds to `ξ̂ ~ τ_Q^{0.364}`, a perfectly ordinary KZM
    length exponent. Falsifiable: it fails for any other pairing of the two
    definitions. -/
theorem kzmCorrelationCollapseExponent_mul_freezeOutLengthExponent
    (e : KZMExponents) :
    kzmCorrelationCollapseExponent e * kzmFreezeOutLengthExponent e = 1 := by
  unfold kzmCorrelationCollapseExponent kzmFreezeOutLengthExponent
  have hν : e.ν ≠ 0 := ne_of_gt e.ν_pos
  have hD : (1 + e.ν * e.z) ≠ 0 := ne_of_gt (kzm_denom_pos e)
  field_simp

/-- **Substantive bound in the opposite direction.** Whenever the dynamic
    exponent satisfies `z ≥ 1` — which covers every case Tindall et al. study,
    since the 2+1D transverse-field Ising spin glass has `z ≥ 1` — the
    correlation-collapse exponent is strictly GREATER than `1`.

    Consequence: in the convention the cited measurement uses, the exponent is
    bounded BELOW by `1`, so a reported value above `1` is what the theory
    predicts and carries no tension with `kzmFreezeOutTimeExponent_lt_one`,
    which bounds a different quantity. -/
theorem one_lt_kzmCorrelationCollapseExponent (e : KZMExponents) (hz : 1 ≤ e.z) :
    1 < kzmCorrelationCollapseExponent e := by
  unfold kzmCorrelationCollapseExponent
  rw [lt_div_iff₀ e.ν_pos]
  nlinarith [e.ν_pos, e.z_pos]

/-- **Quantitative cross-check against the cited measurement.** The 2+1D
    transverse-field Ising transition sits in the 3D Ising universality class,
    `ν ≈ 0.63`, `z = 1`. At those values the correlation-collapse exponent is
    `(1 + 0.63)/0.63 ≈ 2.587`, inside the `μ = 2.6 ± 0.3` finite-size Monte
    Carlo band that Tindall et al. quote and adjacent to their own fits
    `μ ≈ 2.70`-`2.75` (Science 392, 868 (2026), p. 6).

    The freeze-out-TIME exponent at the same `(ν, z)` is `0.63/1.63 ≈ 0.387`,
    a factor `6.7` away — which is the numerical statement of why the two must
    never be compared. Falsifiable: shifting `ν` by more than about `0.005`
    breaks the enclosure. -/
theorem kzmCorrelationCollapseExponent_three_dim_ising_mem_Ioo :
    kzmCorrelationCollapseExponent ⟨63/100, 1, by norm_num, by norm_num⟩ ∈
      Set.Ioo (2.58 : ℝ) 2.59 := by
  unfold kzmCorrelationCollapseExponent
  constructor <;> norm_num

/-- **Companion lemma.** The KZM freeze-out-time exponent for the canonical 1D
    transverse-field Ising model (`ν = z = 1`) equals exactly `1/2` — the
    Zurek 1996 result. Falsifiable: changing either exponent away from `1`
    breaks the equality. -/
theorem kzmFreezeOutTimeExponent_1d_tfim_eq_one_half :
    kzmFreezeOutTimeExponent ⟨1, 1, by norm_num, by norm_num⟩ = 1 / 2 := by
  unfold kzmFreezeOutTimeExponent
  norm_num

/-- **Companion lemma, and the reason the 1D check is not a disambiguation.**
    In one spatial dimension with `ν = z = 1` the defect-density exponent also
    equals `1/2`, because `d = z` there. In three dimensions with the same
    critical data it is `3/2` — see `exists_kzmDefectDensityExponent_one_lt`.
    The 1D TFIM therefore cannot distinguish the time exponent from the density
    exponent, and no check run only at that point may be read as evidence that
    the intended one was named. -/
theorem kzmDefectDensityExponent_1d_tfim_eq_one_half :
    kzmDefectDensityExponent ⟨1, 1, by norm_num, by norm_num⟩ 1 = 1 / 2 := by
  unfold kzmDefectDensityExponent
  norm_num

/-!
## The Kibble-Zurek-Unruh bridge

The bridge data identifies the inverse quench rate `1/τ_Q` of a finite-rate
critical-point traversal with the surface gravity `κ` of an analog horizon:

  `1 / τ_Q  ≡  κ`

Physical picture: a horizon-crossing wavepacket experiences a finite-rate
transition from subsonic to supersonic flow, with rate set by the local
velocity gradient at the horizon — that gradient is `κ`. The KZ-U
correspondence asserts that the thermal distribution of horizon-produced
quasiparticles is the KZM analog at quench rate `τ_Q^{-1} = κ`, which gives
exactly the Hawking temperature `T_H = κ / (2π)` (in natural units).
-/

/-- The KZ-U bridge: WKB substrate (`ExactWKBParams`) + KZM exponents. -/
structure KZMUnruhBridge where
  wkb : ExactWKBParams
  expos : KZMExponents

/-- The KZ-U identification: the inverse effective quench rate equals the
    surface gravity. -/
noncomputable def kappaToInverseQuenchRate (br : KZMUnruhBridge) : ℝ :=
  br.wkb.kappa

/-- **Substantive thermal-distribution identification.** Multiplying the
    Hawking temperature by `2π` recovers the surface gravity exactly:

      `2π · T_H = κ`,

    where `T_H = hawkingTemp κ` is from `Basic.lean`. This is the
    inverse-direction Kibble-Zurek-Unruh identification: the KZM quench
    rate `1/τ_Q = κ` is recovered from the Hawking thermal temperature
    by the universal `2π` factor (Bekenstein-Hawking convention). The
    proof uses `Real.pi > 0` non-trivially to clear the denominator
    (not a `rfl` unfolding). -/
theorem kzm_unruh_thermal_matches_hawking (br : KZMUnruhBridge) :
    2 * Real.pi * hawkingTemp br.wkb.kappa = br.wkb.kappa := by
  have h_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := h_pi_pos.ne'
  unfold hawkingTemp
  field_simp

/-!
## Headline — the freeze-out time against the horizon-crossing time

Under the KZ-U identification `τ_Q = 1/κ`, the KZM freeze-out time is

  `t̂ = τ_Q^{μ_t} = κ^{-μ_t}`,

to be compared with the bare horizon-crossing time `τ_Q = κ^{-1}`. Because
`μ_t ∈ (0,1)` strictly, the comparison is decided by whether `κ` is above or
below `1` — the two theorems below — and it reverses at `κ = 1`. This is a
statement in which the surface gravity does real work: it is not invariant
under rescaling `κ`, and neither theorem follows from
`kzmFreezeOutTimeExponent_lt_one` by multiplying through by a positive number.

⚠️ **The test a `κ`-carrying statement must pass.** An inequality of the form
`μ · X < X` with `X > 0` is scale-invariant in `X`: the factor cancels and the
statement is equivalent to `μ < 1`, whatever physical quantity `X` names. Such
a statement does not constrain `X`, and a name asserting that it does is
therefore wrong regardless of how the proof is written. The scaled forms are
kept below, named for what they are, as
`kzmFreezeOutTimeExponent_mul_wkbRate_lt_wkbRate` and
`kzmFreezeOutTimeExponent_mul_kappa_lt_kappa`.
-/

/-- **Headline.** Under the KZ-U identification `τ_Q = 1/κ`, if the surface
    gravity exceeds unity then the KZM freeze-out time `t̂ = κ^{-μ_t}` is
    strictly LONGER than the bare horizon-crossing time `κ^{-1}`:

      `κ⁻¹ < κ^{-μ_t}`   whenever `1 < κ`.

    Physical meaning: at a steep horizon the impulse window outlasts the
    crossing itself, so the frozen-in quasiparticle content is set on a
    timescale the horizon-crossing rate alone underestimates.

    The dependence on `κ` is essential and not a common factor: the inequality
    reverses for `κ < 1` (`kzm_freezeOutTime_below_horizonTime_of_kappa_lt_one`)
    and degenerates to equality at `κ = 1`. -/
theorem kzm_freezeOutTime_exceeds_horizonTime_of_one_lt_kappa
    (br : KZMUnruhBridge) (hκ : 1 < br.wkb.kappa) :
    br.wkb.kappa⁻¹ <
      br.wkb.kappa ^ (-(kzmFreezeOutTimeExponent br.expos)) := by
  have hlt : (-1 : ℝ) < -(kzmFreezeOutTimeExponent br.expos) := by
    have := kzmFreezeOutTimeExponent_lt_one br.expos
    linarith
  have h := (Real.rpow_lt_rpow_left_iff hκ).mpr hlt
  rwa [Real.rpow_neg_one] at h

/-- **Companion to the headline, opposite regime.** For a shallow horizon
    (`0 < κ < 1`, guaranteed positive by `ExactWKBParams.kappa_pos`) the
    inequality reverses: the freeze-out time is strictly SHORTER than the
    horizon-crossing time.

    Together with `kzm_freezeOutTime_exceeds_horizonTime_of_one_lt_kappa` this
    exhibits the surface gravity as the quantity that decides the comparison —
    the content the previous, scale-invariant headline did not have. -/
theorem kzm_freezeOutTime_below_horizonTime_of_kappa_lt_one
    (br : KZMUnruhBridge) (hκ : br.wkb.kappa < 1) :
    br.wkb.kappa ^ (-(kzmFreezeOutTimeExponent br.expos)) <
      br.wkb.kappa⁻¹ := by
  have hlt : (-1 : ℝ) < -(kzmFreezeOutTimeExponent br.expos) := by
    have := kzmFreezeOutTimeExponent_lt_one br.expos
    linarith
  have h := (Real.rpow_lt_rpow_left_iff_of_base_lt_one br.wkb.kappa_pos hκ).mpr hlt
  rwa [Real.rpow_neg_one] at h

/-- **Companion lemma.** Under the KZ-U bridge with low-dissipation WKB and a
    modified Bogoliubov realization `b`, the Hawking occupation `|β|²` is
    bounded above by `|α|²` strictly, with the gap exactly equal to the WKB
    spectral budget `1 - δ_k`. This follows from the WKB modified-unitarity
    `|α|² - |β|² = 1 - δ_k` (from `WKBConnection.ModifiedBogoliubov.unitarity`)
    combined with the low-dissipation hypothesis. -/
theorem hawking_occupation_strictly_below_alpha
    (br : KZMUnruhBridge)
    (b : ModifiedBogoliubov br.wkb)
    (hdk : decoherenceParam br.wkb < 1) :
    b.beta_sq < b.alpha_sq := by
  have h_unit : b.alpha_sq - b.beta_sq = 1 - decoherenceParam br.wkb := b.unitarity
  have h_budget_pos : 0 < 1 - decoherenceParam br.wkb := by linarith
  linarith

/-- **Scaled corollary.** Scaling the strict bound
    `μ_t < 1` by the positive factor `κ · (1 - δ_k)` gives

      `μ_t · κ · (1 - δ_k)  <  κ · (1 - δ_k)`.

    ⚠️ **What this does and does not say.** Because `κ > 0` and
    `1 - δ_k > 0`, the common factor cancels and the statement is EQUIVALENT to
    `kzmFreezeOutTimeExponent_lt_one`. Neither the surface gravity nor the WKB
    spectral budget constrains the exponent here; they are a positive scalar
    multiplied through both sides. It is recorded because the scaled form is
    the one that appears when the rate is written in physical units, not
    because it carries independent content. For a statement in which `κ` does
    work, see `kzm_freezeOutTime_exceeds_horizonTime_of_one_lt_kappa`. -/
theorem kzmFreezeOutTimeExponent_mul_wkbRate_lt_wkbRate
    (br : KZMUnruhBridge)
    (hdk : decoherenceParam br.wkb < 1) :
    kzmFreezeOutTimeExponent br.expos * br.wkb.kappa *
        (1 - decoherenceParam br.wkb)
      < br.wkb.kappa * (1 - decoherenceParam br.wkb) := by
  have h_μ_lt : kzmFreezeOutTimeExponent br.expos < 1 :=
    kzmFreezeOutTimeExponent_lt_one br.expos
  have h_κ_pos : 0 < br.wkb.kappa := br.wkb.kappa_pos
  have h_budget_pos : 0 < 1 - decoherenceParam br.wkb := by linarith
  have h_scale_pos : 0 < br.wkb.kappa * (1 - decoherenceParam br.wkb) :=
    mul_pos h_κ_pos h_budget_pos
  nlinarith [h_μ_lt, h_κ_pos, h_budget_pos, h_scale_pos]

/-- **Scaled corollary, zero-dissipation form** of the lemma above:
    `μ_t · κ < κ`.

    ⚠️ Same caveat: `κ > 0` cancels, so this is `kzmFreezeOutTimeExponent_lt_one`
    scaled. It concerns the freeze-out-TIME exponent, not a defect rate — the
    defect-density exponent is `kzmDefectDensityExponent`, which admits values
    above `1` and for which the corresponding inequality is FALSE. -/
theorem kzmFreezeOutTimeExponent_mul_kappa_lt_kappa (br : KZMUnruhBridge) :
    kzmFreezeOutTimeExponent br.expos * br.wkb.kappa < br.wkb.kappa := by
  have h_μ_lt : kzmFreezeOutTimeExponent br.expos < 1 :=
    kzmFreezeOutTimeExponent_lt_one br.expos
  have h_κ_pos : 0 < br.wkb.kappa := br.wkb.kappa_pos
  nlinarith [h_μ_lt, h_κ_pos]

end SKEFTHawking.KibbleZurekUnruh
