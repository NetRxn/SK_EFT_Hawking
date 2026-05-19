# Permanent Tracked Hypotheses

**Purpose.** Catalogue the project's load-bearing **tracked-hypothesis Props** — Lean predicates that are consumed by substantive theorems but are NOT independently derived in the project. Each entry documents what the Prop says, where it is consumed, the physics status of the underlying claim, and the project's posture toward it (permanent honest-framing vs deferred-to-future-phase discharge).

**Why this doc.** The project's posture per CLAUDE.md is that **axioms are temporary scaffolding, not permanent commitments** (Pipeline Invariant #15). Tracked-hypothesis Props are the *constructive* alternative to axioms: instead of asserting a load-bearing physical claim as a global `axiom`, we package it as a `def`-Prop and have consumers take an explicit hypothesis. This makes the project's claim surface visible at the type-signature level and locates *all* load-bearing physical assumptions in one document (here).

**Scope.** This catalogue covers tracked-hypothesis Props at the project-scope boundary — claims that the SK_EFT_Hawking program does NOT derive from first principles within Phases 1–6 but consumes as external physical input. Items recorded here fall into two categories:

- **KEEP_AS_TRACKED** — the underlying claim is a research-grade conjecture, an empirically-supported but not-derivable assumption, or a project-scope boundary. The tracked-Prop form *is* the principled framing; "discharging" would mean shipping a different microscopic substrate that the project does not commit to.
- **DISCHARGE_FUTURE_PHASE** — the underlying claim is in-principle derivable within the project's substrate and is scheduled for substantive discharge in a specific future phase. The tracked-Prop form is honest interim framing.

**Sensitivity.** internal-and-publishable — this doc IS appropriate for external publication alongside any paper that consumes one of these tracked Props.

---

## 1. `H_VestigialModeIsGraviton` — KEEP_AS_TRACKED

**File:** `lean/SKEFTHawking/GravitationalWaves.lean:326-329`

**Statement.**

```lean
def H_VestigialModeIsGraviton (χ_vest : ℝ) : Prop :=
  0 < χ_vest ∧ LigoSatisfied (c_GW_deviation χ_vest) ∧ |c_GW_deviation χ_vest| < 1/2
```

**What the Prop says.** A vestigial-mode coupling `χ_vest` represents a graviton-like degree of freedom if (a) the coupling is positive, (b) the implied gravitational-wave-speed deviation passes the LIGO constraint, and (c) the deviation magnitude is bounded by 1/2.

**Anchor + falsifiers.** The Prop is non-vacuous: there is an explicit anchor at `χ_vest = 1` discharging the Prop, and 4 falsifier theorems rule out trivial inhabitants — P2-violation patterns at `χ_vest ∈ {0.1, 10}`, P1 at `χ_vest = 0`, and a P3 falsifier at `χ_vest = 1/4`. These witness that the Prop genuinely picks out a non-trivial subclass of `ℝ`.

**Underlying physics status.** **Conjectural.** Volovik 2024 (the "second-sound graviton" proposal) derives the phase velocity `s_2 = c` at equilibrium from Landau hydrodynamics, but does not supply an off-shell propagator, a dispersion relation `ω(k)`, or a coupling to matter. Volovik himself writes that *"the type of graviton this mode represents requires further consideration"*. The bridge from this hydrodynamic mode to a graviton with the required Riemann-tensor coupling structure is, to our knowledge, not derived in any published source.

**Why KEEP_AS_TRACKED.** Discharging this Prop would require shipping a different microscopic theory than the one this project commits to — specifically, a microscopic substrate from which the vestigial-mode-to-graviton bridge follows derivatively. Such a substrate is out of scope for the current SK_EFT_Hawking program (analog-Hawking physics on a BEC condensate, not full quantum gravity). The tracked-Prop form is the **principled treatment**: it makes the physical assumption visible to consumers, lets them propagate the dependency explicitly through their own derivations, and avoids the overreach of treating a research-grade conjecture as an established result.

**Consumers.** Any theorem citing `H_VestigialModeIsGraviton` in its hypotheses propagates the conjecture-status to its conclusion. Downstream gravitational-wave-related theorems should explicitly carry this Prop as a hypothesis parameter rather than discharging it silently.

**Reassessment trigger.** If a future microscopic-substrate ship in the project derives the vestigial-mode-to-graviton bridge (Phase 7+ speculative), this entry would be revisited and the Prop could be upgraded from "tracked" to "shipped". No such ship is currently scheduled.

---

## 2. `H_DESICompatibility` — DISCHARGE_FUTURE_PHASE (Phase 6b.2)

**File:** `lean/SKEFTHawking/FLRWDynamics.lean:272-276`

**Statement.**

```lean
def H_DESICompatibility (pred : DEPredictor) (Λ_UV N_f α_ADW : ℝ) : Prop :=
  0 < Λ_UV ∧ 0 < N_f ∧ 0 < α_ADW
  ∧ |(pred Λ_UV N_f α_ADW).1 - w_0_DESI| < 0.1
  ∧ |(pred Λ_UV N_f α_ADW).2 - w_a_DESI| < 0.2
```

where `(w_0_DESI, w_a_DESI) = (-0.838, -0.62)` are the DESI DR2 best-fit values for the Chevallier-Polarski-Linder parametrization of the dark-energy equation of state.

**What the Prop says.** A dark-energy predictor `pred` produces `(w_0, w_a)` values within 0.1 / 0.2 absolute tolerance of the DESI DR2 measurements, for some positive `(Λ_UV, N_f, α_ADW)` parameter triple.

**Non-vacuity.** No anchor discharge is currently shipped (the Prop is parameterized over an unknown predictor); 3 falsifiers establish non-vacuity by ruling out (a) the `α_ADW ≤ 0` regime, (b) the constant-zero predictor, and (c) the ΛCDM predictor (which has CPL gap `|w_0 - (-1)| = 0.162 > 0.1`).

**Underlying physics status.** **Derivable in principle within the project's substrate**, not yet executed. The Anti-De-Witt (ADW) FLRW dynamics formalized in `FLRWDynamics.lean` provide the foundation; what remains is the cosmological-perturbation-theory chain (linear perturbations of the ADW background → growth-of-structure observable → CPL extraction → likelihood comparison against DESI DR2). Phase 5y Round 3 established that single-scalar mechanisms in the project's substrate lock `w = -1` via Gibbs-Duhem no-go; ADW offers a different mechanism (multi-scalar) but has not yet been forked through to `(w_0, w_a)` territory.

**LoE for substantive discharge.** Estimated ~50 person-hours: coupled FLRW perturbations, numerical ODE solver for the perturbed-ADW background, Boltzmann code integration, CPL likelihood scan, Lean formalization of the bridge. Outside the budget for Phase 6, slotted for Phase 6b.2 ("cosmological perturbation theory") which is not currently active.

**Why DISCHARGE_FUTURE_PHASE (not KEEP).** Unlike the vestigial-mode-to-graviton bridge in §1, the DESI compatibility claim *is* expected to follow derivatively from the project's existing substrate (ADW dynamics) once the perturbation-theory machinery is shipped. The tracked-Prop form is **honest interim framing**, not permanent project-scope boundary.

**Consumers.** Any cosmology-adjacent theorem citing `H_DESICompatibility` carries the deferred-status to its conclusion. External writeups that consume this Prop should hedge: *"predicated on the H_DESICompatibility tracked hypothesis, which remains open pending Phase 6b.2"*.

**Reassessment trigger.** When Phase 6b.2 is opened.

---

## 3. `H_RT_Formula_Valid` — KEEP_AS_TRACKED

**File:** `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:87-88`

**Statement.**

```lean
structure H_RT_Formula_Valid (S_BH : ℝ → ℝ → ℝ) : Prop where
  rt_proportional : ∀ A G_N, 0 < A → 0 < G_N → S_BH A G_N = A / (4 * G_N)
```

**What the Prop says.** A given black-hole-entropy function `S_BH` satisfies the Ryu-Takayanagi proportionality `S = A/(4G_N)` for all positive `(A, G_N)`.

**Non-vacuity.** The Prop is consumed in 4 substantive cross-bridge theorems shipped in `RTCasiniHuertaBounds.lean`:
- `rt_entropy_pos` — RT-form entropy is positive.
- `rt_falsified_by_kaul_majumdar` — the Kaul-Majumdar correction (with non-trivial reduced-area term) violates `H_RT_Formula_Valid`.
- `isolatedHorizon_violates_H_RT` — loop-quantum-gravity isolated-horizon hypotheses imply `¬H_RT_Formula_Valid`.
- `kaulMajumdarS_violates_H_RT_via_IH` — compositional sanity-check tying the previous two together.

These consumers establish that `H_RT_Formula_Valid` is a **load-bearing boundary condition**, not a placeholder. The Prop's falsification has substantive consequences (RT-vs-alternatives can be distinguished within the project's substrate).

**Underlying physics status.** **Empirically supported in AdS/CFT; research-grade conjecture in quantum gravity.** The Ryu-Takayanagi formula is derived from the holographic principle via the Lewkowycz-Maldacena replica trick in AdS/CFT and has been corroborated in multiple holographic test-cases. However, in the broader context of quantum gravity (without holographic dual), the RT formula remains a conjecture. The SK_EFT_Hawking program does NOT independently derive the RT formula — the bulk holographic dual is out of Phase 6 scope.

**Why KEEP_AS_TRACKED.** Same as §1: the underlying claim is a **project-scope boundary**, not deferred substrate work. The 4 substantive consumers establish that the Prop is consumed as a *boundary condition* — external comms that cite the Prop should treat it as a standard holographic working assumption with explicit hedging when used outside AdS/CFT contexts.

**Consumers.** The 4 theorems listed above. External writeups should hedge appropriately when relying on RT outside AdS/CFT.

**Reassessment trigger.** If the project ships an independent derivation of the RT formula (Phase 7+ speculative; not currently scheduled), this entry would be revisited.

---

## 4. `TPFConjecture` — KEEP_AS_TRACKED (converted from `axiom gapped_interface_axiom` on 2026-05-19)

**File:** `lean/SKEFTHawking/SPTClassification.lean:254`

**Statement.**

```lean
def TPFConjecture : Prop :=
  ∀ (spt : SPTPhaseData), spt.anomaly_free →
    ∃ (interface : InterfaceData spt) (props : GappedInterfaceProperties),
      interface.is_local ∧ interface.preserves_symmetry ∧
      props.unique_ground_state ∧ props.short_range_entangled
```

**What the Prop says.** The Thorngren-Preskill-Fidkowski (TPF) 2026 conjecture: for every anomaly-free SPT phase, there exists a local, symmetric interface Hamiltonian that is gapped with a unique ground state and short-range entanglement (between the free-fermion and commuting-projector realizations).

**Anchor + falsifier.** `TPFConjecture_iff_explicit` (well-typed-ness — confirms `TPFConjecture` reduces to the expected `∀ spt h_free, ∃ interface props, …` statement) and `TPFConjecture_falsifier_has_nonempty_hypothesis` (non-vacuity — exhibits `spt_4plus1d 16` with `spt_one_generation_anomaly_free` to guarantee the hypothesis pool is non-empty).

**Underlying physics status.** **Research-grade conjecture; "plausible but unproven" per TPF's own assessment.** The conjecture is precisely statable but numerically intractable in 3+1D / 4+1D (Hilbert space too large). Machine-checked dimensional ladder of evidence (`gapped_interface_dimensional_ladder` in `SPTClassification.lean`):

- **1+1D analog (proven):** `VillainHamiltonian.k3450_gappable` — K-matrix gappability for the 3450 chiral gauge theory (det K = 1, two mutually-local null vectors).
- **2+1D analog (proven, Wave 3 2026-04-15):** `FK.fk_summary` — explicit 16×16 FK Hamiltonian with spectral gap Δ = 14, ground-state energy E₀ = −14, fermion-parity preserved. Distinct framework (Cayley-calibration / Majorana) — the two-framework agreement is a non-trivial strengthening.
- **3+1D / 4+1D (this Prop):** no counterexample known; "plausible but unproven."

**Why KEEP_AS_TRACKED.** Discharging this Prop would require either (a) a constructive proof of TPF in 3+1D / 4+1D (open at the literature frontier; no known approach), or (b) a counterexample (which would also revolutionize the field). Both are out of project scope. The Tracked-Prop form is the **principled treatment**: the substantive 3+1D / 4+1D claim is preserved (still asserted as a Prop), but the dependency surface is now visible at the type-signature level of every downstream consumer, rather than silently propagating via a global axiom.

**Conversion provenance.** This Prop replaced `axiom gapped_interface_axiom` (the Phase-5h Wave-1 original ship) on 2026-05-19 (Phase 5h Wave 2). Per CLAUDE.md Pipeline Invariant #15 ("axioms are temporary scaffolding, not permanent commitments"), the constructive alternative of a tracked Prop is preferred when the substantive content is genuinely conjectural. The pre-conversion project-local axiom count drops by 1 with this ship. See `AXIOM_METADATA['gapped_interface_axiom']` in `src/core/constants.py` — `eliminability: 'closed'` with full conversion details under `evidence_on_close`.

**Consumers.** The 4 conditional theorems in `SPTClassification.lean`:

- `anomaly_free_implies_chiral_gauge` (takes `(H : TPFConjecture)`)
- `sm_generation_gapped_interface` (takes `(H : TPFConjecture)`)
- `sm_three_gen_gapped_interface` (takes `(H : TPFConjecture)`)
- `no_gap_implies_anomalous` (takes `(H : TPFConjecture)`)

External writeups that consume these theorems propagate the dependency on `TPFConjecture` and should hedge appropriately: *"predicated on the TPFConjecture tracked hypothesis, the 3+1D / 4+1D analog of TPF (proven in 1+1D and 2+1D in independent frameworks; conjectural in 3+1D / 4+1D)"*.

**Reassessment trigger.** If a future paper proves (or disproves) the 3+1D / 4+1D TPF conjecture, this entry would be revisited.

---

## 5. Posture summary

| Prop | Status | Discharge LoE | Scheduled phase |
|---|---|---|---|
| `H_VestigialModeIsGraviton` | KEEP_AS_TRACKED (permanent) | N/A — requires different substrate | None |
| `H_DESICompatibility` | DISCHARGE_FUTURE_PHASE | ~50 person-hours | Phase 6b.2 (not active) |
| `H_RT_Formula_Valid` | KEEP_AS_TRACKED (permanent) | N/A — project-scope boundary | None |
| `TPFConjecture` | KEEP_AS_TRACKED (permanent; converted from axiom on 2026-05-19) | N/A — open at literature frontier | None |

**Net axiom-and-tracked-Prop count rationale.** The project minimizes both `axiom` declarations (per Pipeline Invariant #15) AND tracked-Prop count by:

1. Categorizing each tracked Prop as either KEEP or DISCHARGE (not leaving it ambiguous).
2. For KEEP entries: documenting the project-scope-boundary rationale and the substrate that would be required to discharge.
3. For DISCHARGE entries: scheduling a specific future phase + estimating LoE.

This catalogue is the source of truth for the project's load-bearing tracked-Prop surface area. New tracked Props (added in any future wave) should be recorded here with a status assignment + rationale BEFORE being consumed by load-bearing theorems.

---

## 6. Cross-reference

- Pipeline Invariant #15: see `CLAUDE.md` workspace-level (no new project-local axiom without explicit user sign-off + discharge plan).
- Strengthening-pass discipline: see `CLAUDE.md` workspace-level §"Preemptive-strengthening discipline".
- For `axiom`-declarations (as opposed to tracked Props), see the `AXIOM_METADATA` registry in `src/constants.py` and the per-axiom eliminability metadata.
- For per-Prop consumer enumeration: `lean/SKEFTHawking/{GravitationalWaves,FLRWDynamics,RTCasiniHuertaBounds,SPTClassification}.lean` and any `grep -rn "H_VestigialModeIsGraviton\|H_DESICompatibility\|H_RT_Formula_Valid\|TPFConjecture" lean/`.

---

**Maintenance.** This doc is updated whenever (a) a new tracked Prop is added to the project's substrate, (b) an existing tracked Prop is substantively discharged, or (c) the status assignment changes (e.g., DISCHARGE_FUTURE_PHASE → KEEP, or KEEP → discharged).
