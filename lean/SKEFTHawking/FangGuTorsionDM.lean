/-
Phase 5x Wave 4: Fang-Gu Torsion DM — Kinematic Obstruction

Narrow formalization of the tree-level algebraic consequence of the
Fang-Gu e-loop stress tensor being traceless on an FRW background.

## Physics

Fang-Gu (arXiv:2106.10242) construct topological gravity with three
TQFT terms; ω-loop condensation generates vacuum Einstein-Cartan,
and unlinked e-loops survive as extended 1D dark-matter candidates.
The central kinematic feature is that the e-loop stress-energy
tensor is traceless: `η^{μν} T_{μν}^{loop} = 0`, which is the
mechanism by which `R = 0` in the emergent Einstein equation (trace
of `G_{μν} = 8πG T_{μν}`).

For a perfect fluid with energy density ρ and isotropic pressure p
in Minkowski signature (−, +, +, +), the mixed-index trace is

  T^μ_μ = −ρ + 3p.

Tracelessness forces `p = ρ/3`, i.e. `w ≡ p/ρ = 1/3` — a radiation-
like equation of state. This is incompatible with the `w = 0` dust
EOS that defines cold dark matter (CDM): CDM scales as `ρ ∝ a^{−3}`
and clusters via `∇²Φ = 4πG ρ`, whereas a traceless fluid scales as
`ρ ∝ a^{−4}` and sources `∇²Φ = 4πG (ρ + 3p) = 8πG ρ` — double the
Newtonian coupling.

## Scope

This module encodes the *kinematic* obstruction only, as a set of
tree-level perfect-fluid algebraic identities. It does **not**
rule out Fang-Gu torsion DM as a dark-sector candidate: several
literature-level escape hatches (cosmic-string-gas coarse graining,
effective loop velocity dispersion, trace-anomalous quantum
corrections) could in principle rescue a CDM-like effective
description at macroscopic scales. None of those rescues is
supplied by the 2021 or 2023 FG papers; a quantitative realization
is outside the scope of Phase 5x and is flagged in the memo
(`docs/dark_sector/W4_FangGu_Torsion_DM_Assessment.md`, §6) as the
"revisit trigger" for a full Phase 6 wave.

## Main results

- **FG1 `traceless_iff_w_one_third`**: for `ρ > 0`, traceless
  stress-energy is equivalent to `w = 1/3`.
- **FG2 `traceless_not_dust`**: traceless ⇒ ¬ dust (for `ρ > 0`).
- **FG3 `traceless_poisson_source_doubled`**: the Newtonian Poisson
  source equals `2ρ` in the traceless regime.
- **FG4 `dust_poisson_source_equals_rho`**: baseline — dust gives
  Poisson source `= ρ`.
- **FG5 `fg_cdm_obstruction`**: combined obstruction — traceless
  ⇒ ¬ dust ∧ Poisson source `= 2ρ`.

## References

- Fang, Gu, arXiv:2106.10242 (2021) — topological gravity, e-loop DM,
  traceless T; eq. (13)-(17) for the trace condition.
- Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology
  from Topological Gravity.md lines 80-82 (trace mechanism),
  243-245 (Poisson modification), 263-265 (EOS obstruction flag).
- docs/dark_sector/W4_FangGu_Torsion_DM_Assessment.md §3 (EOS row),
  §4.6 (kinematic obstruction summary), §6 (rationale for this
  narrow Lean module).
-/

import Mathlib

namespace SKEFTHawking.FangGuTorsionDM

/-- Perfect-fluid stress-energy parameters: energy density ρ and
isotropic pressure p. Signature (−, +, +, +). -/
structure PerfectFluidData where
  rho : ℝ
  p : ℝ
deriving Inhabited

/-- Mixed-index trace `T^μ_μ = −ρ + 3p` in signature (−, +, +, +). -/
def mink_trace (s : PerfectFluidData) : ℝ := -s.rho + 3 * s.p

/-- Equation-of-state parameter `w = p/ρ`. Total division: undefined
at `ρ = 0` (`w = 0` by Lean convention, not physically meaningful).

Noncomputable because real division goes through `Real.instDivInvMonoid`. -/
noncomputable def eos_w (s : PerfectFluidData) : ℝ := s.p / s.rho

/-- CDM / dust equation of state: `p = 0`, equivalently `w = 0`. -/
def is_dust (s : PerfectFluidData) : Prop := s.p = 0

/-- Newtonian Poisson source with relativistic correction,
`∇²Φ = 4πG · (ρ + 3p)`. For dust (p = 0) the source is `ρ`; for a
traceless fluid (p = ρ/3) it is `2ρ`. -/
def poisson_source (s : PerfectFluidData) : ℝ := s.rho + 3 * s.p

/--
**FG1 (traceless_iff_w_one_third)**: for `ρ > 0`, the perfect-fluid
stress tensor is traceless iff `w = 1/3`. Tree-level algebraic
consequence of the Fang-Gu e-loop trace condition.
-/
theorem traceless_iff_w_one_third {s : PerfectFluidData} (hρ : 0 < s.rho) :
    mink_trace s = 0 ↔ eos_w s = 1/3 := by
  unfold mink_trace eos_w
  have hρne : s.rho ≠ 0 := ne_of_gt hρ
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/--
**FG2 (traceless_not_dust)**: traceless stress-energy with `ρ > 0` is
not the dust EOS. This is the formal kinematic obstruction: FG e-loops
with exact traceless `T_{μν}` cannot simultaneously have the CDM
equation of state `p = 0`.
-/
theorem traceless_not_dust {s : PerfectFluidData} (hρ : 0 < s.rho)
    (htrace : mink_trace s = 0) : ¬ is_dust s := by
  -- `hρ` is load-bearing: without `ρ > 0`, `{ρ = 0, p = 0}` is both
  -- traceless and dust (a vacuous solution). Include it explicitly.
  unfold mink_trace is_dust at *
  intro hp
  rw [hp] at htrace
  -- htrace : -s.rho + 3 * 0 = 0, i.e. s.rho = 0; contradicts hρ.
  linarith

/--
**FG3 (traceless_poisson_source_doubled)**: for a traceless perfect
fluid, the Newtonian Poisson source `ρ + 3p` equals `2ρ`. This is
the observable consequence of the trace condition: the effective
gravitational coupling is *doubled* relative to dust.

(The identity holds for every `ρ`, including `ρ = 0`; the `ρ > 0`
hypothesis is not needed for this specific statement but is
required downstream in `fg_cdm_obstruction` to distinguish the
vacuous `ρ = 0 = p` case from the physical one.)
-/
theorem traceless_poisson_source_doubled {s : PerfectFluidData}
    (htrace : mink_trace s = 0) :
    poisson_source s = 2 * s.rho := by
  unfold mink_trace poisson_source at *
  linarith

/--
**FG4 (dust_poisson_source_equals_rho)**: baseline — dust has Poisson
source `ρ` (the standard CDM clustering input).
-/
theorem dust_poisson_source_equals_rho {s : PerfectFluidData}
    (hd : is_dust s) : poisson_source s = s.rho := by
  unfold poisson_source is_dust at *
  rw [hd]
  ring

/--
**FG5 (fg_cdm_obstruction)**: combined kinematic obstruction. A
perfect fluid with `ρ > 0` and traceless `T_{μν}` is simultaneously
(a) *not* dust and (b) sources a Poisson equation with *twice* the
dust coupling.

Physical interpretation: Fang-Gu e-loops, taken as a perfect fluid
with the microscopic `T^μ_μ = 0` of the 2021 construction, cannot
be drop-in CDM. A CDM-like macroscopic description requires a
trace-anomalous or coarse-grained completion (cosmic-string-gas
averaging, velocity dispersion, quantum corrections) not supplied
by the 2021 or 2023 FG papers.
-/
theorem fg_cdm_obstruction {s : PerfectFluidData} (hρ : 0 < s.rho)
    (htrace : mink_trace s = 0) :
    (¬ is_dust s) ∧ (poisson_source s = 2 * s.rho) :=
  ⟨traceless_not_dust hρ htrace,
   traceless_poisson_source_doubled htrace⟩

/--
**FG6 (dust_not_traceless)**: the converse flag — dust with `ρ > 0`
has `mink_trace = −ρ ≠ 0`. Confirms traceless and dust are mutually
exclusive in the perfect-fluid model.
-/
theorem dust_not_traceless {s : PerfectFluidData} (hρ : 0 < s.rho)
    (hd : is_dust s) : mink_trace s ≠ 0 := by
  -- Goal: `mink_trace s ≠ 0`. With `hd : p = 0`, `mink_trace = -ρ`.
  -- Since `hρ : 0 < ρ`, `-ρ < 0`, so `-ρ ≠ 0`.
  unfold mink_trace is_dust at *
  rw [hd, mul_zero, add_zero]
  exact neg_ne_zero.mpr (ne_of_gt hρ)

/-! ## Concrete witnesses -/

/-- Dust with ρ = 1, p = 0 has mink_trace = −1. -/
theorem witness_dust_trace_nonzero :
    mink_trace ⟨1, 0⟩ = -1 := by
  unfold mink_trace; norm_num

/-- Radiation with ρ = 3, p = 1 (so `w = 1/3`) has mink_trace = 0. -/
theorem witness_radiation_traceless :
    mink_trace ⟨3, 1⟩ = 0 := by
  unfold mink_trace; norm_num

/-- Radiation with ρ = 3, p = 1 has Poisson source `= 6 = 2ρ`. -/
theorem witness_radiation_poisson_doubled :
    poisson_source ⟨3, 1⟩ = 2 * 3 := by
  unfold poisson_source; norm_num

/-! ## Module summary -/

/-! ## Module summary

Module summary. Ships the kinematic obstruction (5 main theorems + 1
converse + 3 witnesses) for the Fang-Gu perfect-fluid trace condition.
Not a full Wave 4 formalization — Wave 4 remains an assessment wave
per the Phase 5x roadmap. This module exists to make the "no drop-in
CDM" claim load-bearing (formal, not narrative). Quantitative
treatments of the literature escape hatches (loop-gas averaging,
velocity dispersion) are outside Phase 5x scope.
-/
end SKEFTHawking.FangGuTorsionDM
