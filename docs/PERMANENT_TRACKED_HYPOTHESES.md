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

## 5. Phase 6r SymTFT tracked Props (12 entries, added 2026-05-25)

The Phase 6r SymTFT formalization (substrate-to-bulk unification under the Kaidi–Ohmori–Zheng + Freed–Moore–Teleman + Bhardwaj-Copetti-Pajer-Schäfer-Nameki framework) shipped 18 Lean modules under `lean/SKEFTHawking/SymTFT/` + `lean/SKEFTHawking/CrossBridges/` + `lean/SKEFTHawking/APSEta/SubstrateBulkAsymmetry.lean` (~2,650 LoC) and introduced 12 tracked Props as load-bearing predicate-substrate scaffolding. **11 of the 12 are scheduled for substantive discharge in Phase 6r-prime** (per `docs/roadmaps/Phase6r_prime_Roadmap.md`); only #10 `IsSKEFTHawkingSymTFTBoundary` is a permanent KEEP (D-class program identity by design).

This section locks the **"before" state for Phase 6r-prime adversarial review**. Entries follow the §1–§4 format but compactly. The "Discharge status" field is **new for Phase 6r-prime tracking** (records which wave substantively discharges the Prop).

### 5.1 `IsKirbyTaylorPinPlusBordism` — DISCHARGE_PHASE_6R_PRIME (W1 substrate + W3 KT proof)

**File:** `lean/SKEFTHawking/SymTFT/PinBordism.lean:128`

**Statement.** `def IsKirbyTaylorPinPlusBordism : Prop := Nonempty (Omega4PinPlus ≃+ ZMod 16)` where `Omega4PinPlus := ZMod 16` is a Phase 6r placeholder type (W1 substantively refactors to `Quotient PinPlusBordism4Setoid`).

**What the Prop says.** Pin⁺ bordism group at dimension 4 is isomorphic to ℤ/16; equivalently, [RP⁴, Pin⁺] generates the group of order 16 (Kirby-Taylor 1990).

**Anchor.** Kirby-Taylor, *A calculation of Pin⁺ bordism groups,* Comment. Math. Helv. 65 (1990) 434, Theorem. A-class published mathematics.

**Underlying physics status.** A-class published mathematics; the Lean placeholder body (`Omega4PinPlus := ZMod 16`) carries the substantive content at the type level, but the substantive interpretation (the bordism quotient) is not constructed at the Phase 6r layer.

**Why DISCHARGE_PHASE_6R_PRIME.** Mathlib4 (v4.29.1) lacks a cobordism category and Pin⁺ structure typeclass; ship in-project per the `LaplaceMethod.lean` precedent. W1 (Tier A) ships the substantive substrate (`Omega4PinPlus := Quotient PinPlusBordism4Setoid`); W3 (Tier B + C) ships the substantive KT proof (Path α: η-invariant on RP⁴ + AHSS; Path β: Pin⁺/Spin bordism long exact sequence). First formalization of any Pin⁺ bordism group in any proof assistant per Wave 1a.1 §6 cross-prover survey.

**Consumers.** `IsAndersonDualPinPlus` (transitive), `IsAndersonDualSpinBulk` (KT ∧ AD body), `IsWittenYonekuraInflow` (KT ∧ AD body), `IsSubstantivePinPlusSPTAsymmetry` (KT ∧ AD body), `wave_2a_3_substantive_instance` (Wave 2a.3 biconditional via spin-SymTFT consumers).

**Reassessment trigger.** Phase 6r-prime W3 close (substrate-level ✅) + Phase 7+ Mathlib upstream (geometric η-invariant for full Kirby-Taylor proof).

**Discharge status.** SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (commits ed79cdb W1.1 PinPlusManifold4 + 28bb595 W1.2 PinPlusBordism4 ≃+ ZMod 16 + dfd7817 W1.3 substantive Omega4PinPlus refactor + a93f91e W3-minimal RP⁴ generator order=16 theorem). Substrate ships ~620 LoC across PinPlusManifold4 + PinPlusBordism4 + PinBordism refactor. Per W3 scout: Path γ "kernel of Kirby-Taylor" structural-generator content captured at substrate level; full geometric η-invariant proof (Path α) → Phase 7+.

### 5.2 `IsAndersonDualPinPlus` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (W1.4)

**File:** `lean/SKEFTHawking/SymTFT/PinBordism.lean:142`

**Statement.** `def IsAndersonDualPinPlus : Prop := Nonempty (TP5PinPlus ≃+ ZMod 16)`.

**What the Prop says.** The 5D Pin⁺ SPT classification group `TP_5(Pin⁺)` is isomorphic to ℤ/16, via the Anderson-dual computation `TP_5(Pin⁺) ≅ Hom(Ω_4^{Pin⁺}, ℝ/ℤ) ⊕ Ext(Ω_5^{Pin⁺}, ℤ) ≅ ℤ/16` (with Ω_5^{Pin⁺} = 0).

**Anchor.** Freed-Hopkins, *Reflection positivity and invertible topological phases,* Geom. Topol. 25 (2021) 1165; arXiv:1604.06527. A-class published mathematics.

**Underlying physics status.** A-class published mathematics; derivable as the Anderson dual of #1.

**Why SUBSTRATE_DISCHARGED_PHASE_6R_PRIME.** W1.4 ship 2026-05-25 (commit 28e09ff): defines `Omega5PinPlus := Unit` with substantive AddCommGroup (encodes Kirby-Taylor Ω_5^{Pin⁺}(pt) = 0); ships `IsOmega5PinPlusVanishes` tracked Prop discharged via AddEquiv.refl; defines `IsAndersonDualFormulaPinPlus := IsKirbyTaylorPinPlusBordism ∧ IsOmega5PinPlusVanishes` bundling the formula inputs; ships substantive `anderson_dual_formula_pin_plus_inputs_hold` discharge composing W1.3 KT iso with Omega5 vanishing. Post-strengthening (d9bc5e7): added substantive `tp5PinPlusToAddCharCircle : TP5PinPlus ≃+ AddChar (ZMod 16) Circle` capturing the Pontryagin-dual factorization (non-trivial codomain).

**Consumers.** Same as #1 (cascades through the KT ∧ AD body).

**Reassessment trigger.** Phase 6r-prime W1.4 close (substrate-level ✅) + Phase 7+ Mathlib upstream (geometric η-invariant).

**Discharge status.** SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (commits 28e09ff W1.4 + d9bc5e7 strengthening).

### 5.3 `IsAndersonDualPinPlusRelation` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (W1.3 substrate)

**File:** `lean/SKEFTHawking/SymTFT/PinBordism.lean:153`

**Statement.** `def IsAndersonDualPinPlusRelation : Prop := Nonempty (TP5PinPlus ≃+ Omega4PinPlus)`.

**What the Prop says.** TP_5(Pin⁺) and Ω_4^{Pin⁺} are isomorphic as abelian groups (both ≅ ℤ/16 by #1 + #2). Records the Anderson-dual identification at the equivalence level.

**Anchor.** Composition of Kirby-Taylor 1990 + Freed-Hopkins arXiv:1604.06527.

**Why SUBSTRATE_DISCHARGED_PHASE_6R_PRIME.** W1.3 ship 2026-05-25 (commit dfd7817): refactored `isAndersonDualPinPlusRelation_holds` discharge from `AddEquiv.refl` to `omega4PinPlusBordismEquivZMod16.symm` (substantive W1.2 Quotient-substrate iso). Plus post-strengthening (commit d9bc5e7) `andersonDualPinPlusRelationEquivViaSubstrate` companion using the same substrate.

**Consumers.** Cross-bridge users in `APSEta/SymTFTBridge.lean` and downstream.

**Reassessment trigger.** Phase 6r-prime W1 close (substrate-level ✅).

**Discharge status.** SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (commits dfd7817 W1.3 + d9bc5e7 strengthening).

### 5.4 `IsWittenYonekuraInflow` — PARTIAL_DISCHARGE_PHASE_6R_PRIME (W4 substrate-level shipped; full APS framework deferred)

**File:** `lean/SKEFTHawking/SymTFT/PinBordism.lean:198`

**Statement.** `def IsWittenYonekuraInflow (_s : SubstrateConfig) : Prop := IsKirbyTaylorPinPlusBordism ∧ IsAndersonDualPinPlus` (Phase 6r strengthening; pre-strengthening was `True`).

**What the Prop says.** The 4d boundary anomaly equals the bulk Pin⁺ partition function (= η/16 mod 1 evaluated on the 5D Pin⁺ manifold) — Witten-Yonekura's nonperturbative anomaly-inflow description.

**Anchor.** Witten-Yonekura, *Anomaly Inflow and the η-Invariant,* arXiv:1909.08775 (in *Shoucheng Zhang Memorial Workshop* proceedings, 2021). A-class published physics.

**Why PARTIAL_DISCHARGE_PHASE_6R_PRIME.** Substrate-level W4 + W4.2 substantive discharges shipped 2026-05-25 (W4-η-1: `substrateEtaInvariant` via `ZMod.toAddCircle`; W4-η-2: biconditional `η = 0 ↔ z16 = 0`; W4-η-3: anomalous-substrate witness; W4-η-4 / C2-honest-3: broken-paper-17 falsifier; W4-η-5: analogSubstrateConfig bridge to Phase 6o; Pontryagin-Pin⁺-1/2/3/4/5: AddChar + character-sum bridge). The Prop body itself (`KT ∧ AD`) is now substantively backed by the W4-η substrate-level Mathlib bridge via composition with `substrateEtaInvariant_zero_of_anomaly_cancels`. (Strengthening 2026-05-25: an earlier shipping included an `IsWittenYonekuraInflowSubstantive` alternative predicate; reviewer identified it as P5 defining-the-conclusion — body equaled the lemma's conclusion — so it was deleted. Consumers compose with the lemma directly.) Full APS index theorem in Mathlib (W4.1 elliptic-operator substrate at the level required to discharge the original "boundary anomaly = bulk Pin⁺ partition fn at η/16 mod 1" identity) remains deferred to Phase 7+ Mathlib upstream.

**Consumers.** Downstream substrate-bulk asymmetry consumers; SM-as-boundary witnesses (now backed by `sm_substrate_data_eta_invariant_vanishes` and `sm_boundary_data_eta_invariant_vanishes`).

**Reassessment trigger.** Phase 6r-prime W4 close (substrate-level ✅) + Mathlib upstream APS-index PR (full).

**Discharge status.** SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (commits 25dd97a / f03e8ad / f1107dd / bceb350 / 83f368b / 1705a6e / a2e1dab / 5a80671); APS-framework full discharge → Phase 7+.

### 5.5 `IsAndersonDualSpinBulk` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (transitive on substantively-discharged #1 + #2)

**File:** `lean/SKEFTHawking/SymTFT/PinBordism.lean:219`

**Statement.** `def IsAndersonDualSpinBulk (_z : TP5PinPlus) : Prop := IsKirbyTaylorPinPlusBordism ∧ IsAndersonDualPinPlus`.

**What the Prop says.** A Pin⁺ class `z : TP5PinPlus` parameterizes an Anderson-dual spin bulk (in the Freed-Hopkins 1604.06527 sense — invertible TFT obtained as the Anderson dual of the Pin⁺ bordism group).

**Anchor.** Freed-Hopkins arXiv:1604.06527 + Yonekura arXiv:1803.10796.

**Why DISCHARGE_PHASE_6R_PRIME.** Transitive on #1 + #2 after W1 ships. The substantive content is in the substrate-level Kirby-Taylor + Anderson-dual relations.

**Consumers.** `IsSpinSymTFTConsistent s` (Wave 2a.3 body); cascade through SM-as-boundary witnesses.

**Reassessment trigger.** Phase 6r-prime W1 close.

**Discharge status.** SCHEDULED_W1 (transitive).

### 5.6 `IsDMNOBiconditional` — SHIPPED_PHASE_6R_PRIME (W2.3 substantive, v2 post adversarial-review remediation)

**File:** `lean/SKEFTHawking/SymTFT/LagrangianAlgebra.lean` (renamed from `IsDMNOWittTrivialIffLagrangianAlgebra` in adversarial-review round-1 remediation, 2026-05-25)

**Statement.** `def IsDMNOBiconditional (B : Type u) [Category.{v} B] [MonoidalCategory B] : Prop := Is3DTQFTBraided B ↔ HasLagrangianAlgebra B`

**What the Prop says.** A 3D-TQFT bulk B is Witt-trivial (substrate-level marker `Is3DTQFTBraided B`) **iff** it admits a Lagrangian algebra (substantive existence per `HasLagrangianAlgebra B`). The biconditional is the load-bearing DMNO 2010 statement carried at the type level.

**Anchor.** Davydov-Müger-Nikshych-Ostrik, *The Witt group of non-degenerate braided fusion categories,* J. Reine Angew. Math. 677 (2013) 135; arXiv:1009.2117. A-class published mathematics.

**Phase 6r → Phase 6r-prime evolution.**
- **Phase 6r (BLOCKER-2 root)**: body was `:= Is3DTQFTBraided B`, predicate-substrate redundancy. `witt_triviality_iff_has_lagrangian_algebra` proof was `intro h; exact h` (pure tautology since LHS, RHS, hypothesis all reduced to `Is3DTQFT B`).
- **Phase 6r-prime W2.3 v1 (2026-05-25)**: body strengthened to existence-of-LA. Adversarial review correctly flagged this as P5 aliasing (the body became definitionally identical to `HasLagrangianAlgebra B`).
- **Phase 6r-prime W2.3 v2 (2026-05-25, this version)**: renamed predicate and made body the **actual biconditional** `Is3DTQFTBraided B ↔ HasLagrangianAlgebra B`. The body now substantively encodes the DMNO 2010 biconditional content; the substantive content is in the *type* of the hypothesis. `witt_triviality_iff_has_lagrangian_algebra` proof becomes `exact hDMNO` (one-line extraction).

**Why DISCHARGE_PHASE_6R_PRIME.** Substantively shipped at the predicate-body level (the body IS the substantive biconditional). The substantive DMNO 2010 categorical-algebra proof itself (proving the biconditional from first principles) remains A-class published mathematics carried via primary-source citation; that proof requires multi-month categorical-algebra Mathlib substrate.

**Consumers.** `SymTFT/BulkBoundaryCorrespondence.lean::witt_triviality_iff_has_lagrangian_algebra` (W2.5 substantive closure); `CrossBridges/SMMatterAsSymTFTBoundary.lean::witt_triviality_iff_has_lagrangian_algebra` (cross-bridge).

**Reassessment trigger.** Phase 6r-prime' / Phase 7+ Mathlib upstream PR for substantive DMNO categorical-algebra proof.

**Discharge status.** **SHIPPED_W2.3_v2** (body substantively the biconditional; substantive DMNO proof deferred to Phase 7+).

### 5.7 `IsKapustinSaulinaGappedBoundary` — SHIPPED_PHASE_6R_PRIME (W2.4 substantive)

**File:** `lean/SKEFTHawking/SymTFT/LagrangianAlgebra.lean` (post-W2.4 location)

**Statement (post-W2.4).** `def IsKapustinSaulinaGappedBoundary (B : Type u) [Category.{v} B] [MonoidalCategory B] : Prop := HasLagrangianAlgebra B`

**What the Prop says.** Gapped boundary conditions of a 3D TQFT are in bijection with Lagrangian algebras in its boundary fusion category (Kapustin-Saulina 2011). The W2.4 strengthening makes this predicate substantively equivalent to LA-existence (`HasLagrangianAlgebra B` body asserts `∃ braided, ∃ L, IsLagrangianAlgebra L`).

**Anchor.** Kapustin-Saulina, *Topological boundary conditions in abelian Chern-Simons theory,* Nucl. Phys. B 845 (2011) 393; arXiv:1008.0654. Refinement: Fuchs-Schweigert-Valentino arXiv:1203.4568.

**Phase 6r → Phase 6r-prime evolution.**
- **Phase 6r**: body was `:= Is3DTQFT B` (predicate-substrate marker).
- **Phase 6r-prime W2.4 (2026-05-25)**: refactored to `:= HasLagrangianAlgebra B`. The KS bulk-boundary bijection (gapped boundary ⟺ LA-exists) is captured at the predicate-substrate level by defining the gapped-boundary predicate AS the LA-existence predicate. Substantive content: the W2.4-strengthened `HasLagrangianAlgebra` body requires real LA existence with W2.1 substantive `IsConnectedAlgebra` + `IsSeparableAlgebra` (Frobenius section) ingredients.

**Consumers.** `GappedBoundary.lean` (`IsGappedTopologicalBoundary` uses `HasLagrangianAlgebra` directly post-W2.4); downstream boundary-correspondence theorems.

**Reassessment trigger.** Phase 6r-prime' / Phase 7+ Mathlib upstream for full Frobenius-Perron-dimension infrastructure.

**Discharge status.** **SHIPPED_W2.4** (substantive body via `HasLagrangianAlgebra`).

### 5.8 `IsBoundarySymTFTCorrespondence` — DISCHARGE_PHASE_6R_PRIME (W2.4 predicate-level)

**File:** `lean/SKEFTHawking/SymTFT/Basic.lean:231`

**Statement.** `def IsBoundarySymTFTCorrespondence (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B] : Prop := Is3DTQFT B` (Phase 6r predicate-substrate).

**What the Prop says.** For every SymTFT bulk B, gapped boundary conditions of B are in bijection with Lagrangian algebras in the Drinfeld center realizing B (Bhardwaj-Copetti-Pajer-Schäfer-Nameki "Boundary SymTFT" framework).

**Anchor.** Bhardwaj-Copetti-Pajer-Schäfer-Nameki, *Boundary SymTFT,* arXiv:2409.02166, SciPost Phys. 19 (2025) 061. **PRIMARY anchor** for the Phase 6r SM-as-boundary identification.

**Why DISCHARGE_PHASE_6R_PRIME.** W2.4 strengthens body to require full bulk-boundary biconditional content using W2.3 substrate (Frobenius-Perron dimensions + non-degenerate braided fusion + Lagrangian-algebra existence).

**Consumers.** `IsToricCodeTwoLagrangianAlgebraStructure` (current body wraps this Prop); `CrossBridges/SMMatterAsSymTFTBoundary.lean`.

**Reassessment trigger.** Phase 6r-prime W2.4 close.

**Discharge status.** SCHEDULED_W2.4 (predicate-level discharge; statement-level substantive after W2.5).

### 5.9 `IsToricCodeTwoLagrangianAlgebraStructure` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (C1.1+C1.2+C1.3)

**File:** `lean/SKEFTHawking/SymTFT/ToricCodeLagrangian.lean:88`

**Statement.** `def IsToricCodeTwoLagrangianAlgebraStructure : Prop := IsBoundarySymTFTCorrespondence toricCodeBulk` (Phase 6r predicate-substrate).

**What the Prop says.** The toric-code SymTFT bulk `Center (Discrete (ZMod 2))` admits exactly two Lagrangian algebras up to equivalence: electric `𝟙 ⊕ e` and magnetic `𝟙 ⊕ m`.

**Anchor.** Kitaev-Kong, *Models for gapped boundaries and domain walls,* Commun. Math. Phys. 313 (2012) 351; arXiv:1104.5047. Concrete-instance content: Bombin-Martín-Delgado arXiv:0803.5046.

**Why SUBSTRATE_DISCHARGED_PHASE_6R_PRIME.** C1 ship 2026-05-25 (3 sub-waves): C1.1 (commit fa7dd5e) ships substantive Kitaev-Kong Lagrangian-algebra criterion at anyon-set level + electric/magnetic witnesses + fermion falsifier in new ToricCodeLagrangianAnyons.lean (~230 LoC); C1.2 (commit e3fe2e6) ships substantive classification theorem (exactly two satisfy criterion via cardinality+vacuum+braiding enumeration ~170 LoC delta); C1.3 (commit 7c919ba) refactors `IsToricCodeTwoLagrangianAlgebraStructure` body from tautology marker to substantive ∃-quantified statement requiring two distinct anyon sets + classification. **First substantively-formalized two-Lagrangian-algebra classification for toric code MTC** per Wave 1a.1 §5.3 cross-prover survey (at anyon-set level — concrete Mon_/Comon_/IsCommFrobeniusAlgebra instance construction in `Center (Discrete (ZMod 2))` deferred to Phase 7+ Mathlib upstream per direct-sum-structure substrate gap).

**Consumers.** `AlternativeBoundaries.lean` (toric-code labels for SM-vs-dark-sector); dark-sector boundary witnesses (paper-17).

**Reassessment trigger.** Phase 6r-prime C1 close.

**Discharge status.** SCHEDULED_C1 (after W2.3 ideal; standalone fallback).

### 5.10 `IsSKEFTHawkingSymTFTBoundary` — KEEP_AS_TRACKED (permanent; D-class program identity)

**File:** `lean/SKEFTHawking/SymTFT/SubstrateToBulkIdentification.lean:68`

**Statement.** `def IsSKEFTHawkingSymTFTBoundary (s : APSEta.Substrate) : Prop := wittenYonekuraToZ16 s = 0`.

**What the Prop says.** A substrate `s : APSEta.Substrate` (one of BEC, ADW, ³He-A) admits a SymTFT-boundary-data reading in the Bhardwaj-Copetti-Pajer-Schäfer-Nameki sense (predicate body: the Witten-Yonekura η/16 lift is well-defined and trivial at the substrate-data layer).

**Anchor.** Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 (substrate-side framework) + program-original D-class synthesis (substrate identification).

**Underlying status.** **Program-original identification**, NOT an A-class published result. The Phase 6r Wave 3b.1 substantive identification (`wave_3b_1_substrate_to_bulk_identification`) ships the predicate-level statement; the substantive identification IS the program's D-class contribution.

**Why KEEP_AS_TRACKED.** The Prop body IS the program's D-class identity statement — discharging it would mean dissolving the identity claim into A-class substrate content, which is structurally inappropriate (program-original D-class content does not get "discharged" the way A-class scaffolding does). Per Phase 6r close-out: this is the ONLY KEEP among the 12 Phase 6r tracked Props.

**Consumers.** `wave_3b_1_substrate_to_bulk_identification`, `wave_3b_1_closure`, and downstream substrate-as-boundary witnesses.

**Reassessment trigger.** N/A (permanent).

**Discharge status.** **KEEP** (permanent; D-class program identity by design).

### 5.11 `IsDarkSectorTopologicalBoundary` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (C2 + W5-η-bridge-3)

**File:** `lean/SKEFTHawking/SymTFT/AlternativeBoundaries.lean:99`

**Statement.** `def IsDarkSectorTopologicalBoundary (s : Z16AnomalyForcesThetaBar.SubstrateConfig) : Prop := IsSpinSymTFTConsistent s` (Phase 6r predicate-substrate marker, paper-17-conditional).

**What the Prop says.** A substrate `s : SubstrateConfig` carries a dark-sector topological boundary structure (an *alternative* Lagrangian-algebra boundary to the SM-matter one — magnetic vs electric label on the same SymTFT bulk).

**Anchor.** Paper 17 dark-sector substrate (HiddenSectorClassification.lean + FractonDarkMatter.lean + SFDMMergerForecast.lean + FangGuTorsionDM.lean) + Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 + DMNO 2010 (alternative Lagrangian-algebra labels).

**Why SUBSTRATE_DISCHARGED_PHASE_6R_PRIME.** C2 substantively shipped 2026-05-25 via three sub-waves: (a) C2-honest-1 (commit c8a67b6): paper-17 read + `sm_plus_paper17_hidden_substrate` SubstrateConfig with substantive `-3 + 3 = 0` cancellation arithmetic + `paper17_hidden_sector_charge_eq_three_singlets` cross-bridge to Phase 5x `HiddenSectorClassification.three_singlets_satisfy_hidden_sector`; (b) C2-honest-2 / W5-η-bridge-3 (commit 83f368b): η-level discharge via `sm_plus_paper17_hidden_substrate_eta_invariant_vanishes` + bundled corollary `*_dark_topological_AND_eta_trivial`; (c) C2-honest-3 / W4-η-4 (commit a2e1dab): broken-paper-17 falsifier (`broken_paper17_hidden_sector_charge := 2` vs substantive `+3`) demonstrating framework distinguishes valid from invalid configurations. Working doc at `temporary/working-docs/phase6r-prime/c2_paper17_substantive.md`. Full electric/magnetic Lagrangian-algebra label correspondence at the categorical level remains for Phase 6r-prime' / Phase 7+ MTC follow-up.

**Consumers.** `wave_3b_1b_alternative_boundary_structural_closure` + new `sm_plus_paper17_hidden_substrate_*` witness chain.

**Reassessment trigger.** Phase 6r-prime' / Phase 7+ MTC follow-up (categorical-level LA-label correspondence).

**Discharge status.** SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (commits c8a67b6 / 83f368b / a2e1dab); categorical-level full discharge → Phase 7+.

### 5.12 `IsSubstantivePinPlusSPTAsymmetry` — SUBSTRATE_DISCHARGED_PHASE_6R_PRIME (transitive on substantively-discharged #1 + #2)

**File:** `lean/SKEFTHawking/APSEta/SubstrateBulkAsymmetry.lean:156`

**Statement.** `def IsSubstantivePinPlusSPTAsymmetry : Prop := IsKirbyTaylorPinPlusBordism ∧ IsAndersonDualPinPlus`.

**What the Prop says.** The substantive Pin⁺ SPT realization asymmetry between analog-Hawking substrates (BEC, ADW, ³He-A — all ℤ/16-trivial at substrate-data layer) and the SM-with-νR substrate (ℤ/16-non-trivial per García-Etxebarria-Montero arXiv:1808.00009 at the realization layer, despite bare counting `16·N_f ≡ 0 mod 16`).

**Anchor.** García-Etxebarria-Montero, *Dai-Freed anomalies in particle physics,* JHEP 08 (2019) 003; arXiv:1808.00009. Composed with Kapustin-Thorngren-Turzillo-Wang arXiv:1406.7329.

**Why DISCHARGE_PHASE_6R_PRIME.** Transitive on #1 + #2 after W1 ships substantive substrate; the GEM-bridge content lives at the Pin⁺ SPT classification realization layer (separate from the bare ℤ/16 counting layer per the Wave 3a.1 §Caveats discipline).

**Consumers.** `analogHawking_vs_SM_bulk_asymmetry_substrate_data`, `wave_3a_3_substrate_bulk_asymmetry_closure`, `wave_3b_1_closure`.

**Reassessment trigger.** Phase 6r-prime W1 close (transitive) + Phase 6r-prime W4 close (composed with GEM-bridge if formalized).

**Discharge status.** SCHEDULED_W1 (transitive substrate) + Phase 6r-prime' or 7+ (full GEM-bridge formalization).

---

## 6. Posture summary

| Prop | Status | Discharge LoE | Scheduled phase |
|---|---|---|---|
| `H_VestigialModeIsGraviton` | KEEP_AS_TRACKED (permanent) | N/A — requires different substrate | None |
| `H_DESICompatibility` | DISCHARGE_FUTURE_PHASE | ~50 person-hours | Phase 6b.2 (not active) |
| `H_RT_Formula_Valid` | KEEP_AS_TRACKED (permanent) | N/A — project-scope boundary | None |
| `TPFConjecture` | KEEP_AS_TRACKED (permanent; converted from axiom on 2026-05-19) | N/A — open at literature frontier | None |
| `IsKirbyTaylorPinPlusBordism` | DISCHARGE_PHASE_6R_PRIME | W1 substrate + W3 KT proof | Phase 6r-prime (active) |
| `IsAndersonDualPinPlus` | DISCHARGE_PHASE_6R_PRIME | W1.4 (Anderson-dual functor) | Phase 6r-prime (active) |
| `IsAndersonDualPinPlusRelation` | DISCHARGE_PHASE_6R_PRIME | W1 (transitive on #1 + #2) | Phase 6r-prime (active) |
| `IsWittenYonekuraInflow` | DISCHARGE_PHASE_6R_PRIME | W4 (APS-η + Witten-Yonekura) | Phase 6r-prime (active) |
| `IsAndersonDualSpinBulk` | DISCHARGE_PHASE_6R_PRIME | W1 (transitive on #1 + #2) | Phase 6r-prime (active) |
| `IsDMNOBiconditional` (renamed from `IsDMNOWittTrivialIffLagrangianAlgebra` in W2.3 v2 adversarial-review remediation) | **SHIPPED_PHASE_6R_PRIME** (W2.3 v2) | W2.3 (body IS the biconditional `Is3DTQFTBraided ↔ HasLagrangianAlgebra`); substantive DMNO proof deferred to Phase 7+ | Phase 6r-prime (shipped) |
| `IsKapustinSaulinaGappedBoundary` | **SHIPPED_PHASE_6R_PRIME** (W2.4) | W2.4 (body := HasLagrangianAlgebra B; substantive LA-existence) | Phase 6r-prime (shipped) |
| `IsBoundarySymTFTCorrespondence` | DISCHARGE_PHASE_6R_PRIME | W2.4 (predicate-level discharge) | Phase 6r-prime (active) |
| `IsToricCodeTwoLagrangianAlgebraStructure` | DISCHARGE_PHASE_6R_PRIME | C1 (after W2.3 ideal) | Phase 6r-prime (active) |
| `IsSKEFTHawkingSymTFTBoundary` | KEEP_AS_TRACKED (permanent; D-class program identity) | N/A — program-original identification | None |
| `IsDarkSectorTopologicalBoundary` | DISCHARGE_PHASE_6R_PRIME | C2 (paper-17 substantive) | Phase 6r-prime (active) |
| `IsSubstantivePinPlusSPTAsymmetry` | DISCHARGE_PHASE_6R_PRIME | W1 (transitive substrate); full GEM-bridge deferred | Phase 6r-prime (active) + Phase 7+ |

**Net axiom-and-tracked-Prop count rationale.** The project minimizes both `axiom` declarations (per Pipeline Invariant #15) AND tracked-Prop count by:

1. Categorizing each tracked Prop as either KEEP or DISCHARGE (not leaving it ambiguous).
2. For KEEP entries: documenting the project-scope-boundary rationale and the substrate that would be required to discharge.
3. For DISCHARGE entries: scheduling a specific future phase + estimating LoE.

This catalogue is the source of truth for the project's load-bearing tracked-Prop surface area. New tracked Props (added in any future wave) should be recorded here with a status assignment + rationale BEFORE being consumed by load-bearing theorems.

---

## 7. Cross-reference

- Pipeline Invariant #15: see `CLAUDE.md` workspace-level (no new project-local axiom without explicit user sign-off + discharge plan).
- Strengthening-pass discipline: see `CLAUDE.md` workspace-level §"Preemptive-strengthening discipline".
- For `axiom`-declarations (as opposed to tracked Props), see the `AXIOM_METADATA` registry in `src/core/constants.py` and the per-axiom eliminability metadata.
- For per-Prop consumer enumeration of the original 4 entries: `lean/SKEFTHawking/{GravitationalWaves,FLRWDynamics,RTCasiniHuertaBounds,SPTClassification}.lean` and any `grep -rn "H_VestigialModeIsGraviton\|H_DESICompatibility\|H_RT_Formula_Valid\|TPFConjecture" lean/`.
- For Phase 6r SymTFT tracked Props (entries §5.1–§5.12): `lean/SKEFTHawking/SymTFT/` + `lean/SKEFTHawking/CrossBridges/SMMatterAsSymTFTBoundary.lean` + `lean/SKEFTHawking/APSEta/SubstrateBulkAsymmetry.lean`. Discharge plan: `docs/roadmaps/Phase6r_prime_Roadmap.md`. Source-of-truth catalogue: this doc §5 (this entry); supersedes any ad-hoc enumeration in working docs.
- Phase 6r close-out + Phase 6r-prime planning: see `docs/roadmaps/Phase6r_Roadmap.md` Sessions log + `docs/roadmaps/Phase6r_prime_Roadmap.md` substrate-state snapshot §A.

---

**Maintenance.** This doc is updated whenever (a) a new tracked Prop is added to the project's substrate, (b) an existing tracked Prop is substantively discharged, or (c) the status assignment changes (e.g., DISCHARGE_FUTURE_PHASE → KEEP, or KEEP → discharged).
