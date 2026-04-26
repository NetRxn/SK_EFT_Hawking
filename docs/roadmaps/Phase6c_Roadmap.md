# Phase 6c: Bridge Theorems — Cross-Pillar Formal Bridges

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §6. Short cross-pillar theorems; each integrates two existing program pillars and surfaces a concrete tension.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Primary pillars for bridging: `Z16AnomalyComputation.lean` (23), `ModularInvarianceConstraint.lean` (12), `ChiralityWallMaster.lean` (17), `GaugingStep.lean` (34, SM anomaly 16 ≡ 0 mod 16), `SMFermionData.lean` (19), `VestigialGravity.lean` (24 after 5y W6), Phase 5x Waves 4/5/6/7 (Fang-Gu torsion, SFDM/MOND, fracton subdiffusion, vestigial relics), `IsingBraiding.lean` (25), `FibonacciMTC.lean` (11), `SU3kFusion.lean` (99), `SU3k2FSymbols.lean` (9), `DrinfeldDouble.lean` (15), full MTC stack, Phase 5y closure context (`GibbsDuhemTheorem`, `QTheoryNoGoTheorem`), Phase 6a.3 `BHEntropyMicroscopic` (target for 6c.4, 6c.5).

**Thesis.** Five short bridge theorems. Each one connects two existing pillars of the program and surfaces a concrete tension — the kind of thing that cannot exist inside one pillar alone. None requires major new physics; all require careful formal integration.

**Correctness-push framing.** Three of five waves are correctness-push highlights. 6c.2 (EW baryogenesis) is especially load-bearing — it determines the baryogenesis escape path for the program's chirality-wall framework.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §6 (6c) and §12 (correctness-push highlights)
> 4. Wave-specific pre-reads:
>    - 6c.1 — `Z16AnomalyComputation.lean`, `ModularInvarianceConstraint.lean`, Phase 5x W3 (Van Waerbeke-Zhitnitsky `Lit-Search/Phase-5x/ADW Emergent Gravity and the Cosmological Constant...`), Phase 5y q-theory closure modules
>    - 6c.2 — `ChiralityWallMaster.lean`, `GaugingStep.lean`, `Z16AnomalyComputation.lean`, `SMFermionData.lean`, Phase 5z.3 `EWPhaseTransition.lean` output
>    - 6c.3 — `VestigialGravity.lean` (EP-violation theorem), Phase 5x W4–7 memos in `docs/dark_sector/`
>    - 6c.4 — `IsingBraiding.lean`, `FibonacciMTC.lean`, `SU3k2FSymbols.lean`, `DrinfeldDouble.lean`, full MTC stack; published Hayden-Preskill 2007 + subsequent holographic-QEC literature
>    - 6c.5 — Phase 6a.3 `BHEntropyMicroscopic.lean` (prerequisite), MTC stack, `StimulatedHawking.lean`; Ryu-Takayanagi 2006 + Casini-Huerta entropy-bound literature
> 5. 6c is a "bridge phase": every wave is short (0.5–6 PM), but every wave REQUIRES that both pillars it bridges are already deep and zero-sorry. Do not start a 6c wave if either pillar has open sorrys on the relevant theorems.
> 6. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline. **6c.3 strengthening pass cost (2026-04-27): 12 retroactive theorems** — that's the baseline to beat.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6c:**
- 6c.1: Strong-CP ↔ topological dark energy (θ-vacuum → Zhitnitsky DE)
- 6c.2: EW baryogenesis ↔ chirality wall (Dai-Freed + sphaleron)
- 6c.3: `EquivalencePrinciple.lean` (abstracted over mechanism)
- 6c.4: QEC ↔ holography (Hayden-Preskill on MTC stack)
- 6c.5: RT / Casini-Huerta entropy bounds (external-hypothesis-tracked)

**OUT OF SCOPE for 6c:**
- Full derivations (each bridge is a short formal statement + tension identification, not a standalone pillar)
- Lattice QCD / Wilson-loop confinement — 6d.1 covers via center-symmetry
- Holographic QEC beyond code-distance scaling — deferred to backlog
- Generic RT formula derivation — 6c.5 treats RT as external hypothesis

**Phase 5x relationship:** 6c.3 unifies Phase 5x Waves 4/5/6/7 EP-violation mechanisms under a single abstract statement. 5x roadmap updates after 6c.3 ships.

---

## Track A: Symmetry Bridges (6c.1, 6c.2)

### Wave 1 — `StrongCPTopologicalDE.lean` (6c.1) [Pipeline: Stages 1–8]

**Goal:** Formal bridge: if QCD θ-vacuum sources DE via Zhitnitsky mechanism, then θ must be dynamically small. Connects strong-CP to cosmological Λ via anomaly-matching chain.

**Prerequisites:** Phase 5x Wave 3 (Van Waerbeke-Zhitnitsky QCD topological DE) fully read. Phase 5y closure modules for DE-framework context. Optional: 6b.2 if perturbation-level DE comparison desired.

**Module structure:**
- `lean/SKEFTHawking/StrongCPTopologicalDE.lean`
  - θ-vacuum state definition; energy density as function of θ
  - Zhitnitsky DE identification: `ρ_Λ_Zhitnitsky(θ) = f(N_c, Λ_QCD, θ)` — structural closed form
  - Bridge theorem: `zhitnitsky_DE_sources_Λ_iff_θ_dynamically_small`
  - Anomaly-matching chain: Z16 ↔ strong-CP ↔ cosmological-Λ — an `IsCompatible` Prop connecting all three
  - **Correctness-push theorem:** `zhitnitsky_and_qtheory_DE_both_active_gives_inconsistency` — if both Zhitnitsky (6c.1) and any residual Volovik-family DE (Phase 5y) were active, their combined contribution would conflict with ρ_Λ ~ (2.3 meV)⁴; identifies the yielding
- Target ~7–10 theorems.

**Python side:**
- `src/strong_cp_de/zhitnitsky_eval.py` — Zhitnitsky DE numerical evaluation over `(N_c, Λ_QCD, θ)`
- `src/strong_cp_de/combined_de_consistency.py` — Zhitnitsky + q-theory residual combined check

**Bridges:**
- Integrates `Z16AnomalyComputation.lean`, `ModularInvarianceConstraint.lean`, Phase 5x Van Waerbeke-Zhitnitsky deep research, Phase 5y closure modules
- Feeds back into Phase 5x/5y DE discussion — another node in the DE-mechanism landscape

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_strong_cp_de.py`
- PRL paper `papers/paper32_strong_cp_de/paper_draft.tex`
- Figure: `fig_zhitnitsky_de_theta_scan` — `ρ_Λ_Zhitnitsky` over θ, observed value contour
- Inventory update: +7–10 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 2–4 person-months
**Risk:** Low–medium. Main risk is the anomaly-matching chain formalization — Z16-to-strong-CP-to-Λ requires careful bookkeeping.

### Wave 2 — `EWBaryogenesisChiralityWall.lean` (6c.2) [Pipeline: Stages 1–12]

**Goal:** Dai-Freed anomaly + sphaleron combinatorics as formal bridge: "Chirality-wall obstruction forbids / permits electroweak baryogenesis in the SM." Uses Phase 5z.3 EW-phase-transition-order output.

**Prerequisites:** `ChiralityWallMaster.lean`, `GaugingStep.lean`, `Z16AnomalyComputation.lean`, `SMFermionData.lean` all at zero-sorry (currently the case). Phase 5z.3 `EWPhaseTransition.lean` substantially complete (first-order vs crossover output).

**Module structure:**
- `lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean`
  - Sphaleron combinatorics: `sphaleron_rate(T, v)` structural form
  - Dai-Freed anomaly pull-back to SM anomaly cancellation
  - Chirality-wall obstruction predicate: `ChiralityWallBlocksEWBG : Prop`
  - Bridge theorem: `EWBG_forbidden_if_chirality_wall_blocks_and_transition_crossover`
  - **Correctness-push theorem:** `SM_EWBG_allowed_iff_wall_cracks_and_transition_first_order` — definitive statement incorporating 5z.3 transition-order prediction
- Target ~10–14 theorems.

**Python side:**
- `src/ew_baryogenesis/sphaleron_computation.py` — sphaleron rate
- `src/ew_baryogenesis/bridge_check.py` — bridge predicate evaluation on Phase 5z.3 parameters

**Bridges:**
- Integrates `ChiralityWallMaster`, `GaugingStep`, `Z16AnomalyComputation`, `SMFermionData`, Phase 5z.3 `EWPhaseTransition`
- Feeds backlog item "Leptogenesis dynamics" (if EWBG forbidden, push to leptogenesis)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_ew_baryogenesis.py`
- PRL paper `papers/paper33_ewbg_chirality_wall/paper_draft.tex`
- Figure: `fig_ewbg_allowed_region` — first-order vs crossover × wall-intact vs cracked, baryogenesis-allowed region
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Correct modeling of the chirality-wall obstruction at SM-embedding level requires careful bookkeeping.

**Correctness-push highlight.** If EWBG *forbidden* by chirality-wall obstruction in SM-as-is → baryogenesis must go to leptogenesis / BSM. Directly feeds downstream model-building.

---

## Track B: Equivalence Principle Abstraction (6c.3) — **SHIPPED 2026-04-27**

**Status:** Wave 3 closed end-to-end. Pipeline through Stage 5.
- `EquivalencePrinciple.lean`: 12 substantive theorems + 1 module-summary marker, 0 sorry, 0 new axioms (verified `propext, Classical.choice, Quot.sound` only on key theorems via `lean_verify`).
- `src/equivalence_principle/`: 2 Python modules (`__init__.py`, `mechanism_classifier.py`) + 32 pytest cases (32/32 PASS in 0.03s).
- `papers/paper34_equivalence_principle/`: short formalization paper, 4 pages, 433 KB, compiles clean, 11 bibitems.
- `fig_ep_violation_matrix`: 6×3 mechanism × EP-level heatmap + η-scale comparison bar chart, registered in `review_figures.py`.
- **Six mechanisms classified**: vestigialDifferentialCoupling (η=1 max, violates WEP), vestigialReliscSTEPClass (η~10⁻¹⁸ STEP-class, violates WEP), fangGuTorsionTrace + fractonSubdiffusion + sfdmThomasFermi + hiddenSectorZ16Singlet (all satisfy WEP/EEP/SEP).
- **Structural punchline**: `ep_violation_is_vestigial_only` — among the six mechanisms, exactly the two vestigial-phase phenomena violate WEP. EP-violation surface is *vestigial-only*.
- Cross-bridges: `vestigial_microscope_violation_consistent` (links to `ClassificationTableDark.MicroscopeStatus.violated`); `VestigialGravity.ep_violation_in_vestigial` consumed.
- Numerical constants: MICROSCOPE_BOUND = 1e-15 (Touboul 2017), STEP_TARGET = 1e-18, VESTIGIAL_PHASE_ETA_MAX = 1.0, VESTIGIAL_RELICS_ETA = 1e-18.
- Stages 9 (LLM figure review) and 13 (adversarial review) deferred per pipeline policy (user-triggered).

### Wave 3 — `EquivalencePrinciple.lean` (6c.3) [Pipeline: Stages 1–5]

**Goal:** Abstract EP statement parametrized over violation mechanism; enumerates which mechanisms violate WEP vs SEP vs EEP. Unifies Phase 5x Waves 4/5/6/7 under a single formal statement.

**Prerequisites:** Phase 5x Waves 4/5/6/7 memos in `docs/dark_sector/` (read directly). `VestigialGravity.lean` EP-violation theorem.

**Module structure:**
- `lean/SKEFTHawking/EquivalencePrinciple.lean`
  - EP levels as typed Props: `WEP`, `SEP`, `EEP`
  - Violation-mechanism typeclass: `ViolatesEP (M : MechanismType) : Prop` with projections to level
  - Instances for mechanisms: Fang-Gu torsion, MOND/SFDM, fracton subdiffusion, vestigial
  - **Correctness-push theorem:** `mechanism_ep_violation_level_is_unique` — forces explicit commitment on which level each mechanism violates
  - Cross-mechanism tension surfacing: `(Fang-Gu) ∩ (SFDM) → no common EP violation level`
- Target ~6–8 theorems.

**Python side:**
- `src/equivalence_principle/mechanism_classifier.py` — classifies violation level per mechanism

**Bridges:**
- Integrates `VestigialGravity.lean` EP-violation theorem, Phase 5x W4/W5/W6/W7 memos
- Feeds back into Phase 5x — any mechanism whose EP-violation level was previously ambiguous gets fixed by this module

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_equivalence_principle.py`
- CPP paper `papers/paper34_equivalence_principle/paper_draft.tex` — short, formalization-focused
- Figure: `fig_ep_violation_matrix` — matrix of mechanisms × EP levels
- Inventory update: +6–8 theorems, +1 Lean module, +1 Python subpackage, +1 short paper

**Estimated LOE:** 0.5 person-months (smallest wave; self-contained win)
**Risk:** Minimal. Pure abstraction over existing mechanisms. The output is a cleanup/clarification task that produces a publishable note.

---

## Track C: Holographic / MTC Bridges (6c.4, 6c.5)

### Wave 4 — `QECHolographyBridge.lean` (6c.4) [Pipeline: Stages 1–12]

**Goal:** Hayden-Preskill / holographic QEC statements on existing MTC / anyonic-computation substrate. Connects anyonic fusion/braiding to AdS/CFT-adjacent error correction.

**Prerequisites:** MTC stack modules all zero-sorry; `IsingBraiding.lean` trefoil invariant; `FibonacciMTC.lean`; `SU3k2FSymbols.lean`; `DrinfeldDouble.lean`.

**Module structure:**
- `lean/SKEFTHawking/QECHolographyBridge.lean`
  - Hayden-Preskill protocol on MTC substrate: encoding, scrambling time, information recovery
  - Code-distance scaling from MTC fusion rules
  - Holographic QEC correspondence: which MTC spectrum = which CFT boundary theory (structural, not full AdS/CFT)
  - **Correctness-push theorem:** `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class`
- Target ~10–14 theorems.

**Python side:**
- `src/qec_holography/code_distance.py` — code-distance numerical over MTC spectra
- `src/qec_holography/scrambling_time.py` — Hayden-Preskill scrambling-time evaluator

**Bridges:**
- Integrates full MTC stack
- Cross-references 6a.3 (`BHEntropyMicroscopic.lean`) — same MTC substrate

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_qec_holography.py`
- Quantum / JHEP paper `papers/paper35_qec_holography/paper_draft.tex`
- Figure: `fig_code_distance_vs_fusion_spectrum` — code-distance scaling across MTC spectra
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python subpackage, +1 paper

**Estimated LOE:** 4–6 person-months
**Risk:** Medium. Hayden-Preskill formalization depth is the main variable; scoped to structural statement, not full derivation.

### Wave 5 — `RTCasiniHuertaBounds.lean` (6c.5) [Pipeline: Stages 1–8]

**Goal:** Ryu-Takayanagi / Casini-Huerta entropy bounds as external-hypothesis-tracked Props connecting analog (BEC Hawking) to real holographic entropy.

**Prerequisites:** Phase 6a.3 (`BHEntropyMicroscopic.lean`) substantially complete. MTC stack. `StimulatedHawking.lean`, `HawkingUniversality.lean`.

**Module structure:**
- `lean/SKEFTHawking/RTCasiniHuertaBounds.lean`
  - Ryu-Takayanagi statement as tracked Prop `H_RT_Formula_Valid` (external hypothesis, not derived)
  - Casini-Huerta entropy bound similarly as tracked Prop
  - Bridge theorem under RT assumption: `bh_entropy_microscopic_matches_rt_iff_boundary_matches_mtc`
  - **Correctness-push theorem:** `rt_consistent_with_6a3_coefficient_match` — if 6a.3 Gate A.2 passed (coefficient = 1/4), RT assumption is consistent; if 6a.3 showed log corrections, RT assumption must be modified
- Target ~7–10 theorems.

**Python side:**
- `src/rt_ch_bounds/rt_comparison.py` — numerical RT-formula evaluation on simple BH backgrounds
- `src/rt_ch_bounds/ch_bound_check.py` — Casini-Huerta bound check

**Bridges:**
- Depends on 6a.3 (`BHEntropyMicroscopic`)
- Integrates MTC stack, `StimulatedHawking`, `HawkingUniversality`
- Cross-references 6c.4 shared MTC substrate

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_rt_ch_bounds.py`
- Short arXiv note `papers/note_rt_ch_bounds/` — structural connection analog ↔ real holographic entropy
- Figure: `fig_rt_ch_bounds_mtc` — RT coefficient vs MTC spectrum
- Inventory update: +7–10 theorems, +1 Lean module, +1 Python subpackage, +1 short note

**Estimated LOE:** 2–3 person-months
**Risk:** Low. External-hypothesis-tracked approach keeps scope tight.

---

## Decision Gates

**Gate C.1 — before Wave 1 (`StrongCPTopologicalDE`) begins:** Is Phase 5x W3 Van Waerbeke-Zhitnitsky deep research available? If NO, drop deep-research prompt first and de-prioritize 6c.1 behind 6c.2 and 6c.3 until research lands.

**Gate C.2 — after Wave 2 (`EWBaryogenesisChiralityWall`) ships:** Is EWBG forbidden or allowed in SM under 5z.3 transition-order result? If FORBIDDEN, push leptogenesis into backlog activation; update Phase 5z roadmap correspondence notes. If ALLOWED, document which microscopic parameter region enables it and feed to 6e nonlinear stress-energy work.

**Gate C.3 — before Wave 5 (`RTCasiniHuertaBounds`) begins:** Is Phase 6a.3 Gate A.2 resolved (BH entropy coefficient match)? If NO, 6c.5 is de-prioritized until 6a.3 ships.

---

## Dependencies

```
6c.1 (StrongCPTopologicalDE) — depends on Phase 5x W3 + 5y closure;
    independent of other 6c waves

6c.2 (EWBaryogenesisChiralityWall) — depends on 5z.3 (EWPhaseTransition);
    independent of other 6c waves

6c.3 (EquivalencePrinciple) — depends on Phase 5x W4–W7; smallest wave

6c.4 (QECHolographyBridge) — depends on MTC stack only; independent of 6a

6c.5 (RTCasiniHuertaBounds) — depends on 6a.3 (BHEntropyMicroscopic);
    Gate C.3 before start

Parallelism:
  6c.1, 6c.2, 6c.3, 6c.4 all independent and parallelizable
  6c.5 blocked on 6a.3
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6c.1 | `StrongCPTopologicalDE.lean` + PRL paper | 2–4 | 5x W3 + 5y closure | **TIER 1** |
| 6c.2 | `EWBaryogenesisChiralityWall.lean` + PRL paper | 3–5 | 5z.3 | **TIER 1** |
| 6c.3 | `EquivalencePrinciple.lean` + CPP paper | 0.5 | 5x W4–W7 | **SHIPPED 2026-04-27** |
| 6c.4 | `QECHolographyBridge.lean` + Quantum/JHEP paper | 4–6 | MTC stack | **TIER 1** |
| 6c.5 | `RTCasiniHuertaBounds.lean` + arXiv note | 2–3 | 6a.3 | **TIER 2** |

**Total Phase 6c LOE:** 11.5–18.5 person-months. Full parallelism across 6c.1–6c.4 + 6c.5 after 6a.3: wall-clock 6–10 months minimum.

**Deliverables cumulative:**
- 5 new Lean modules
- 5 new Python subpackages
- 4 papers (Papers 32–35 reserved) + 1 short note
- ~40–56 new theorems; zero sorry target

---

## Open Questions

**O.1** — 6c.1 paper venue: PRL vs short PRD; coordinated with Phase 5x W3 findings.

**O.2** — 6c.3 is marked 0.5 PM but delivers a CPP paper — confirm with user that short formalization papers are in-scope for publication output (vs internal doc).

**O.3** — 6c.4 QEC scope: "structural" vs "derivational" (how much Hayden-Preskill to formalize from scratch)? Default to structural, with derivation deferred to backlog.

**O.4** — 6c.5 external-hypothesis-tracked approach: is the user comfortable with tracked-Prop RT rather than derived RT? Confirm at Stage 3b.

---

## What Success Looks Like

**Per wave:**
- 6c.1: Formal bridge strong-CP ↔ topological DE; Zhitnitsky-vs-q-theory consistency identified
- 6c.2: Definitive statement on EWBG viability in SM under 5z.3 transition-order result
- 6c.3: EP-violation level assigned to every Phase 5x mechanism; matrix surfaces tensions
- 6c.4: Code-distance-scaling bridge from MTC fusion to holographic QEC
- 6c.5: RT / Casini-Huerta bound formal connection analog ↔ real

**Cumulative:**
- 5 new Lean modules, 5 Python subpackages, 4 papers + 1 short note
- Correctness-push anchors: EWBG viability (6c.2), CFL-vs-center Z₃ consistency (routed through 6d.3)

---

## Cross-References

**Prior phases this bridges:**
- Phase 5c (Wang-Rokhlin, Z16) — `Z16AnomalyComputation`, `SMFermionData`
- Phase 5e/5i (MTC stack) — `IsingBraiding`, `FibonacciMTC`, `SU3kFusion`, `SU3k2FSymbols`, `DrinfeldDouble`
- Phase 5h (chirality wall) — `ChiralityWallMaster`, `GaugingStep`
- Phase 5x W3/W4/W5/W6/W7 — DE, torsion, MOND, fracton, vestigial DM candidates
- Phase 5y closure — DE-mechanism landscape context
- Phase 5z.3 — EW-phase-transition input for 6c.2
- Phase 6a.3 — BH entropy microscopic for 6c.5

**Feeds downstream phases:**
- Backlog "Leptogenesis dynamics" — triggered if 6c.2 forbids EWBG
- Phase 6d.3 (CFL ↔ center Z₃) — consistency check documented via 6c bridge pattern
- Phase 6e (nonlinear EFE) — stress-energy structure informed by 6c.2 baryogenesis verdict

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §6

**Correctness-push highlights from strategy doc §12:**
- 6c.2: EW baryogenesis permitted / forbidden in SM

---

*Phase 6c roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Five bridge theorems (6c.1–6c.5); all short, all cross-pillar, one correctness-push anchor (6c.2). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 11.5–18.5.*
