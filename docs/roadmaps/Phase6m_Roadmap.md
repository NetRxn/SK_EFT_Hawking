# Phase 6m: Untested Dark-Energy Mechanism Probes (Phase 5y Reframe)

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **New phase, structurally parallel to Phase 5y.** Sources: `docs/ARCHITECTURE_SCOPE.md` (Phase 5y closure verdict 2026-04-23: "obstruction covers Volovik-family mechanisms specifically; entropic gravity, causal-set approaches, Jacobson-type thermodynamic GR are outside the tested scope"); user gap-analysis (2026-04-28 Research Overview): "the Volovik family is closed, but the closure was deliberately scoped — the architecture-scope memo flags entropic gravity, causal sets, and Jacobson-type thermodynamic GR as untested. Each is a candidate for a Phase 5y-style 6-round probe."*

**Trigger condition (no gate — autonomous):** Phase 6m can dispatch any time. It is independent of all other Phase 6 roadmaps.

**Status (2026-04-28):** **OPEN** for user authorization Gate M.1 (Wave 1 dispatch).

**Methodology — Phase 5y reframe.** Phase 5y closed the Volovik-family q-theory dark-energy direction with a six-round deep-research program returning a uniform NO-GO. Phase 6m applies the same six-round methodology to *three explicitly out-of-scope* mechanism families flagged by `ARCHITECTURE_SCOPE.md`:
- **Causal-set theory dark energy** (Sorkin 1989; Sorkin-Surya 2004; Ahmed-Dowker-Surya 2017): emergent Λ from underlying discrete causal-set structure.
- **Entropic gravity dark energy** (Verlinde 2011, 2017): emergent gravity + DE from entanglement / holographic entropy considerations.
- **Jacobson-thermodynamic-GR dark energy** (Jacobson 1995; Padmanabhan 2010): GR equations from thermodynamic identities at local Rindler horizons; Λ as a thermodynamic "boundary term."

Each mechanism gets a six-round probe (analog of Phase 5y rounds 1–6) returning either a NO-GO (with structural obstruction theorem in Lean) or a PARTIAL-VIABLE verdict (with explicit substrate-realization conditions). The endpoint is `ClassificationTableDark.lean` extension covering all three new families.

**Entry state (2026-04-28 Inventory_Index snapshot):** ~187 active modules, ~4,385 theorems, 0 sorry, 1 axiom. Phase 5y CLOSED; `ARCHITECTURE_SCOPE.md` 2026-04-23 explicitly flags these three as "outside tested scope."

**Anchors carried forward into Phase 6m:**
- `GibbsDuhemTheorem.lean` (Phase 5y) — Gibbs-Duhem emergent-vacuum obstruction; the structural template Phase 6m tests against the new mechanism families.
- `QTheoryNoGoTheorem.lean` (Phase 5y) — realization-independent obstruction template.
- `DarkEnergyObstructionPrinciple.lean` (Phase 5y) — four-factor orthogonality decomposition (Gibbs-Duhem ∩ c_s² ≥ 0 ∩ natural T_c ∩ MICROSCOPE).
- `DESIComparison.lean` (Phase 5y) — DESI DR2 (w₀, w_a) comparison infrastructure.
- `ClassificationTableDark.lean` (Phase 5y) — dark-sector classification consolidation (Phase 6m extends).
- `ARCHITECTURE_SCOPE.md` — predictive-scope boundary documentation (Phase 6m updates).

**Thesis.** Phase 5y's closure was decisive *and scoped*. The architecture-scope memo explicitly preserves three untested mechanism families as candidates for future probes. Phase 6m exercises the same six-round methodology against each; each probe ships either a NO-GO with formal obstruction (extending the Layer 3 dark-sector OUT-OF-SCOPE boundary) or a PARTIAL-VIABLE result (opening a new substrate-realization chain). In either case, the architectural-scope statement gets sharper.

**Three-track structure:**
- **Track A (Causal-set DE):** Waves 1a–1f, six rounds.
- **Track B (Entropic-gravity DE):** Waves 2a–2f, six rounds.
- **Track C (Jacobson-thermodynamic-GR DE):** Waves 3a–3f, six rounds.
- **Wave 4:** classification consolidation + `ARCHITECTURE_SCOPE.md` update.

**Correctness-push framing.** Quantitative anchors (against DESI DR2 + observational constraints):
1. (Track A) Causal-set predicted Λ from `Λ ~ √(N_causet)/V_causet` (Sorkin everpresent-Λ): does Λ_predicted match observed `Λ_obs ≈ 1.1 × 10⁻⁵² m⁻²` within order of magnitude?
2. (Track B) Entropic-gravity predicted DE EOS `w(z)` from holographic-entanglement entropy: matches DESI DR2 (w₀, w_a) ≈ (−0.8 ± 0.07, −0.7 ± 0.3)?
3. (Track C) Jacobson-thermodynamic-GR boundary-term Λ: does the local-Rindler-horizon thermodynamics force Λ to a fixed value, or leave it as a free integration constant?

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap.**
> 2. Read this roadmap end-to-end before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/GibbsDuhemTheorem.lean` (Phase 5y).
>    - `lean/SKEFTHawking/QTheoryNoGoTheorem.lean` (Phase 5y).
>    - `lean/SKEFTHawking/DarkEnergyObstructionPrinciple.lean` (Phase 5y).
>    - `lean/SKEFTHawking/ClassificationTableDark.lean` (Phase 5y).
>    - `docs/ARCHITECTURE_SCOPE.md` — read fully; this is what Phase 6m updates.
> 4. **Critical deep-research dossiers required** — six per track, dispatched in sequence at Stage 1 of each wave. Track A round 1 example: `Phase6m_TA_R1_causal_set_de_landscape.md`. (Naming convention: `Phase6m_T<A|B|C>_R<1..6>_<topic>.md`.)
> 5. **Phase 5y methodology mirror.** Each round filters the candidate-mechanism realizations against the four-factor orthogonality decomposition (Gibbs-Duhem ∩ c_s² ≥ 0 ∩ natural T_c ∩ MICROSCOPE). Surviving realizations get a Lean obstruction or viability theorem.
> 6. **Apply preemptive-strengthening checklist.**
> 7. **Do not delegate Lean theorem proving to subagents.**
> 8. **User authorization gates:** Gate M.1 (Track A start), Gate M.2 (Track B start), Gate M.3 (Track C start), Gate M.4 (consolidation/scope-update wave). Each track can run autonomously after its gate.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6m:**
- Six-round deep-research probe of causal-set theory dark energy (Track A).
- Six-round deep-research probe of entropic-gravity dark energy (Track B).
- Six-round deep-research probe of Jacobson-thermodynamic-GR dark energy (Track C).
- Per-track NO-GO / PARTIAL-VIABLE / VIABLE verdict in Lean.
- Extension of `ClassificationTableDark.lean` covering all three families.
- Update to `docs/ARCHITECTURE_SCOPE.md` recording the new probes' verdicts.
- One paper (target: Phys. Rep. or PRD): "Untested Dark-Energy Mechanisms on the SK-EFT Substrate: Causal-Set, Entropic, Jacobson-Thermodynamic Probes."

**OUT OF SCOPE for Phase 6m:**
- Re-opening Volovik-family q-theory (Phase 5y closure stands).
- Full causal-set lattice simulation — beyond formalization scope; deep-research synthesis only.
- Tensor-network holographic codes — adjacent but separate (Phase 6j Wave 1 territory if at all).
- Scale-invariance / unimodular gravity DE proposals — already partly absorbed by Phase 5y's q-theory unimodular realization.
- Dark-energy "modified gravity" routes (f(R), DGP, massive gravity) — outside SK-EFT substrate scope.

**Phase 5y relationship.** Phase 6m *extends* Phase 5y's methodology to three explicitly-deferred mechanism families. Phase 5y modules are not modified; Phase 6m adds new modules and extends `ClassificationTableDark.lean`. The closure verdict of Phase 5y on Volovik-family q-theory is preserved.

**Phase 6c.1 relationship.** Phase 6c.1's Zhitnitsky topological-DE absorption is currently the project's only viable DE mechanism (within ≤3 orders of observed Λ, no free parameters). Phase 6m's three new mechanism families either (a) fail (NO-GO), preserving the single-DE-mechanism commitment from 6c.1, or (b) survive (PARTIAL-VIABLE), creating a multi-mechanism landscape that requires re-examination of 6c.1's combined-mechanism falsifier.

---

## Track A: Causal-Set Theory Dark Energy

### Wave 1a — Round 1: Causal-Set DE Landscape Survey [Pipeline: Stages 1–7]

**Goal.** Deep-research synthesis of all known causal-set-derived DE mechanisms; enumerate candidate realizations; first-pass filter against the four-factor orthogonality decomposition.

**Prerequisites:** Phase 5y modules read; `ARCHITECTURE_SCOPE.md` read.

**Module structure:**
- Deep-research dossier `Lit-Search/Tasks/Phase6m_TA_R1_causal_set_de_landscape.md`.
- No Lean module yet (research-only round).
- Working doc: `temporary/working-docs/phase6m_TA_R1_synthesis.md`.

**Headline content:** Sorkin everpresent-Λ (Phys. Rev. D 36, 1731, 1987; Sorkin-Surya 2004; Ahmed-Dowker-Surya 2017); causal-set "atomicity" → discrete fluctuations of Λ; Bombelli-Lee-Meyer-Sorkin causal-set kinematics (PRL 59, 521, 1987).

**Output:** Round 1 verdict: how many causal-set realizations survive first-pass filter? Trigger Round 2 (R2 = closer mechanism dive on top-3 survivors).

---

### Wave 1b — Round 2: Top-Survivor Detailed Analysis [Pipeline: Stages 1–7]

**Goal.** Deep-dive on top survivors from Round 1.

**Module structure:**
- Deep-research dossier `Phase6m_TA_R2_*` (filed at Round 1 close).
- Working doc continuation.

**Output:** Round 2 verdict.

---

### Wave 1c — Round 3: Gibbs-Duhem Filter [Pipeline: Stages 1–7]

**Goal.** Apply the Gibbs-Duhem obstruction (Phase 5y `GibbsDuhemTheorem`) to surviving realizations. Causal-set DE typically does NOT have a single-scalar field structure (it's discrete-causet kinematic), so Gibbs-Duhem may not apply; this round determines that.

**Output:** which realizations are still alive?

---

### Wave 1d — Round 4: c_s² Stability Filter [Pipeline: Stages 1–7]

**Goal.** Sound-speed-squared positivity (avoid catastrophic gradient instability, the same filter that killed vestigial-EOS natural-branch in Phase 5y).

**Output:** survivors after stability filter.

---

### Wave 1e — Round 5: DESI DR2 (w₀, w_a) Comparison [Pipeline: Stages 1–7]

**Goal.** For each surviving causal-set DE realization, compute predicted (w₀, w_a) and compare to DESI DR2 1σ band `[−0.8, −0.66] × [−1.35, −0.75]`.

**Output:** DESI-compatible survivors (if any).

---

### Wave 1f — Round 6 + Lean Closure: `CausalSetDarkEnergy.lean` [Pipeline: Stages 1–13]

**Goal.** Final round + Lean formalization of the verdict (NO-GO with obstruction theorem, or PARTIAL-VIABLE with substrate-realization conditions, or VIABLE with prediction band).

**Module structure:**
- `lean/SKEFTHawking/CausalSetDarkEnergy.lean` — new module, ~14 substantive theorems target.
- `src/dark_energy/causal_set_de.py` — numerical Λ from causal-set everpresent fluctuations.
- `tests/test_causal_set_de.py` — DESI-comparison + everpresent-Λ tests; 10+ tests.
- `figures/fig_causal_set_de_verdict.{png,html}`.

**Headline theorems (one branch fires):**

**Branch NO-GO:**
1. `causal_set_de_no_go_under_<filter>` — formalizes which Phase 5y filter kills causal-set DE.
2. `everpresent_lambda_fails_desi_compatibility` — Sorkin everpresent-Λ predicts time-evolving Λ but with magnitude / amplitude mismatching observation.
3. `classification_table_dark_appends_causal_set_no_go` — extends `ClassificationTableDark.lean`.

**Branch PARTIAL-VIABLE:**
1. `causal_set_de_viable_under_substrate_condition_<X>` — explicit substrate-condition theorem.
2. `causal_set_de_open_for_phase_<future>` — opens a new chain.

**Strengthening checklist:**
- (P5 trivial-discharge): if branch NO-GO fires, the obstruction theorem must be falsifiable (a counterexample causal-set realization would falsify the theorem).
- (Quantitative): (w₀, w_a) closed-form values vs DESI 1σ band.

**Stage 13 anchors:**
- Sorkin, PRD 36, 1731 (1987); Mod. Phys. Lett. A 9, 3119 (1994).
- Bombelli, Lee, Meyer, Sorkin, PRL 59, 521 (1987).
- Ahmed, Dowker, Surya, CQG 34, 124002 (2017).
- DESI Collaboration, arXiv:2503.14738 (2025).

**Deliverables.** `CausalSetDarkEnergy.lean`; numerical module; figure suite; section in flagship paper.

---

## Track B: Entropic-Gravity Dark Energy

### Waves 2a–2f — Six rounds, parallel structure to Track A

**Round 1 (2a):** Entropic-gravity DE landscape — Verlinde 2011 (JHEP 04 029); Verlinde 2017 (SciPost Phys. 2 016) emergent-DE in de Sitter spacetime; Padmanabhan thermodynamic-GR overlaps.

**Round 2 (2b):** Top-survivor detailed analysis — Verlinde 2017 emergent-DE the most concrete; cross-check with Cadoni-Tuveri thermal entropy.

**Round 3 (2c):** Gibbs-Duhem filter — entropic-gravity DE does have single-scalar (apparent-horizon temperature) structure; Gibbs-Duhem applies and may force `w_DE = −1` analogously.

**Round 4 (2d):** c_s² filter.

**Round 5 (2e):** DESI DR2 comparison.

**Round 6 + Lean Closure (2f):** `EntropicGravityDarkEnergy.lean` — verdict module.

**Lean module (Wave 2f):**
- `lean/SKEFTHawking/EntropicGravityDarkEnergy.lean` — ~12 theorems target.
- Verlinde-2017 emergent-Λ closed-form; Gibbs-Duhem application; DESI comparison; classification-table extension.

**Stage 13 anchors:**
- Verlinde, JHEP 04 029 (2011), arXiv:1001.0785.
- Verlinde, SciPost Phys. 2, 016 (2017), arXiv:1611.02269.
- Padmanabhan, Rep. Prog. Phys. 73, 046901 (2010).

---

## Track C: Jacobson-Thermodynamic-GR Dark Energy

### Waves 3a–3f — Six rounds, parallel structure

**Round 1 (3a):** Jacobson-thermodynamic-GR DE landscape — Jacobson 1995 (PRL 75, 1260); Padmanabhan thermodynamic-GR; Eling-Guedens-Jacobson 2006 nonequilibrium thermodynamics; recent work by Cai-Cao on F(R) thermodynamic gravity.

**Round 2 (3b):** Top-survivor detailed analysis.

**Round 3 (3c):** Gibbs-Duhem filter — Jacobson's thermodynamic identities at local Rindler horizons may force Λ as a free integration constant (no GD obstruction) OR may obstruct it (analog to Phase 5y q-theory). Round 3 determines which.

**Round 4 (3d):** c_s² filter.

**Round 5 (3e):** DESI DR2 comparison.

**Round 6 + Lean Closure (3f):** `JacobsonThermoGRDarkEnergy.lean` — verdict module.

**Lean module (Wave 3f):**
- `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` — ~12 theorems target.

**Stage 13 anchors:**
- Jacobson, PRL 75, 1260 (1995), arXiv:gr-qc/9504004.
- Padmanabhan, Class. Quant. Grav. 21, 4485 (2004).
- Eling, Guedens, Jacobson, PRL 96, 121301 (2006), arXiv:gr-qc/0602001.

---

## Wave 4 — `DarkSectorClassificationExtension.lean` + ARCHITECTURE_SCOPE.md update [6m.4] [Pipeline: Stages 1–13]

**Goal.** Consolidate Tracks A/B/C verdicts into an extended dark-sector classification table; update `ARCHITECTURE_SCOPE.md` with the new verdicts. The Layer 3 dark-energy scope statement is sharpened: previously "Volovik-family mechanisms outside scope," now "Volovik-family + (NO-GO results from Tracks A/B/C) outside scope; (any PARTIAL-VIABLE/VIABLE results) opened as new chains."

**Prerequisites:**
- Tracks A/B/C all SHIPPED.

**Module structure:**
- `lean/SKEFTHawking/DarkSectorClassificationExtension.lean` — new module, ~10 theorems target (consolidates Tracks A/B/C verdicts as bridge theorems into existing `ClassificationTableDark.lean`).
- Extension to `ClassificationTableDark.lean` (additive, not editing).
- `docs/ARCHITECTURE_SCOPE.md` — append-only update with the new probe verdicts.

**Headline theorems:**
1. `causal_set_de_classified` — Tracks A's verdict as a structured Lean proposition.
2. `entropic_gravity_de_classified` — Track B's verdict.
3. `jacobson_thermo_de_classified` — Track C's verdict.
4. `architecture_scope_extended_2026Q3` — meta-theorem: `Layer3DarkEnergyScope = VolovikFamily ∪ {Track-A-NoGoPart, Track-B-NoGoPart, Track-C-NoGoPart}`.
5. `single_de_mechanism_commitment_holds_iff_no_partial_viable` — biconditional: Phase 6c.1's combined-mechanism falsifier remains in force IFF no Track A/B/C realization is partial-viable.

**Stage 13 anchors:** all primary sources from Waves 1f, 2f, 3f.

**Deliverables.** `DarkSectorClassificationExtension.lean`; `ARCHITECTURE_SCOPE.md` updated; flagship paper closure.

---

## Paper deliverable

**Paper 45** (target: Phys. Rep. or PRD): "Untested Dark-Energy Mechanisms on the SK-EFT Substrate: Causal-Set, Entropic, Jacobson-Thermodynamic Probes." 12–20 pages (review-paper-flavored). Structure:
- §2 Causal-set DE (Track A) — six-round summary + verdict.
- §3 Entropic-gravity DE (Track B) — six-round summary + verdict.
- §4 Jacobson-thermodynamic-GR DE (Track C) — six-round summary + verdict.
- §5 Classification table extension (Wave 4).
- §6 Updated architecture-scope statement.
- §7 What remains untested (next-generation candidates: tensor-network holographic codes, modified-gravity DE, ...).

**Submission readiness:** target Stage 13 closure ~16–24 weeks post-Wave 4 (heavy review-paper drafting).

---

## Cross-phase impact

- **Phase 5y**: Phase 6m extends but does not modify; Volovik-family closure preserved.
- **Phase 6c.1**: Phase 6m's verdicts on Tracks A/B/C either preserve 6c.1's single-DE-mechanism commitment (NO-GO branch) or break it (PARTIAL-VIABLE branch, requiring 6c.1 falsifier re-examination).
- **`ARCHITECTURE_SCOPE.md`**: Wave 4 updates this document.
- **`ClassificationTableDark.lean`**: Wave 4 extends this module additively.

---

## Total LOE estimate

- Track A (6 rounds + Lean closure): 4–6 PM (research-heavy)
- Track B (6 rounds + Lean closure): 4–6 PM
- Track C (6 rounds + Lean closure): 4–6 PM
- Wave 4 (consolidation): 2 PM
- Paper 45 drafting (review-flavored): 4–6 PM
- **Total: 18–26 PM** (~4.5–6.5 months at full intensity)

Tracks A/B/C can run in parallel after Gates M.1, M.2, M.3 are opened; serial execution is also acceptable.

---

*Last updated: 2026-04-28. Status: OPEN, awaiting Wave 1a deep-research dispatch + user authorization Gate M.1.*
