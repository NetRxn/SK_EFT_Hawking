# Phase 5y: Terminal Closure — Obstruction Harvest, Formalization, and Scoping Recalibration

## Technical Roadmap — April 2026 (Terminal Revision)

> **STATUS: CLOSED — 2026-04-23.** All 9 waves executed end-to-end.
> 8 new Lean modules + 3 extensions, **110 new theorems, 0 new sorry**,
> full no-cache `lake build SKEFTHawking.ExtractDeps` clean (8430 jobs).
> Architectural scope (`docs/ARCHITECTURE_SCOPE.md`) + 5 stakeholder
> impact memos + classification table (Lean + markdown) shipped. No
> papers per user preference. Closure summary:
> [`docs/stakeholder/Phase5y_Closure_Summary.md`](../stakeholder/Phase5y_Closure_Summary.md).
>
> **Per-wave closure log:**
> - ✅ Wave 1 — `GibbsDuhemTheorem.lean` (16 thms)
> - ✅ Wave 2 — `QTheoryNoGoTheorem.lean` (12 thms + `massOfRealization` enum)
> - ✅ Wave 3 — `DarkEnergyObstructionPrinciple.lean` (8) + `DESIComparison.lean` (8)
> - ✅ Wave 4 — `CondensedMatterAnalog.lean` (10) + `VestigialMapping.lean` (8)
> - ✅ Wave 5 — `VestigialEOS.lean` (20 + `fine_tuning_log_lower_bound` VE18a)
> - ✅ Wave 6 — Extensions: `VestigialGravity` +7, `VestigialSusceptibility` +8, `TetradGapEquation` +4
> - ✅ Wave 7 — `ClassificationTableDark.lean` (8) + companion markdown
> - ✅ Wave 8 — `ARCHITECTURE_SCOPE.md` (new) + `README.MD` Phase 5y milestone
> - ✅ Wave 9 — 5 stakeholder memos (Closure_Summary + Impact_on_5x/5u/5d/5w)

*Supersedes `Phase5y_Roadmap.md` v1 (2026-04-22). Closes the phase after six rounds of deep research returned dual NO-GO on the original headline bet and the reframed alternatives. Follows the Phase 5s convention: decompose a program-level outcome ("5y is closed, harvest what was learned") into tractable finite deliverables with clear Tier-0 / Tier-1 / Tier-2 priorities.*

**Entry state:** 3021 Lean theorems, 0 sorry, 1 axiom across 133 modules. `ADWMechanism` (21), `VestigialGravity` (18), `VestigialSusceptibility` (16), `TetradGapEquation` (20), `WetterichNJL` (18), `FractonFormulas` (45), `FractonHydro` (17), `FractonGravity` (20) provide the Layer-1→Layer-2 machinery. `AcousticMetric` (8), `SKDoubling` (9), `CGLTransform` (7), `SecondOrderSK` (19) provide the Layer-2→Layer-3 SK-EFT machinery. `KerrSchild` (7) provides gravitational solutions scaffolding. **The substantive output of 5y's six deep-research rounds is formally ready for Lean harvest.** Paper 6 Monte Carlo remains the standing bottleneck; 5y's terminal formalization wave is explicitly designed to run in parallel without touching it.

**Strategic framing:** Rounds 3, 4a, 4b, 5 executed the original q-theory → DESI spine and returned NO-GO via a Gibbs-Duhem structural theorem covering all four KV realizations (4-form, 2-brane, fermionic-crystal, unimodular). Rounds H1 and H4 executed the reframe alternatives (Volovik second-sound graviton; vestigial-gravity effective EOS via charge-4e analog) and returned NO-GO again — H1 because the mode is not a derived propagating DOF and its decay channel reduces to q-theory; H4 because the original-derivation EOS produces phantom-today (wrong sign from DESI) on its natural branch, `c_s² = −1/3` gradient instability at late times, and recovers the 10⁻¹²¹ fine-tuning under Λ₀-augmentation. **Five NO-GOs constitute structural evidence.** The phase closes. What remains is a substantive harvest of five formal-verifiable results that advance the program's Lean backbone and sharpen its claim-space.

**Formalization architecture:** 5y closure produces **no Paper A, no Paper B** (user-stated preference: program advancement, not publications). Instead the harvest decomposes into three Lean formalization tracks covering ~85-100 new theorems across 7 new modules + extensions to 3 existing ones, plus one architectural/classification-table track. The Lean output is the 5y ledger entry, not papers. The architectural-scoping output feeds every future Phase-5/Phase-6 conversation about what Layer 3 is trying to predict.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the six deep-research deliverables in `Lit-Search/Phase-5y/`:
>    - `Phase5y_qtheory_desi_derivation.md` (Round 3)
>    - `Phase5y_qtheory_deltaq_extension.md` + `Phase5y_Round4a_Validation.md` (Round 4a)
>    - `Phase5y_aether_3form_literature.md` (Round 4b)
>    - `Phase5y_fermionic_crystal_elasticity_tetrad.md` (Round 5)
>    - `Phase5y_H1_second_sound_graviton.md` (H1)
>    - `Phase5y_H4_vestigial_gravity_EOS.md` (H4)
> 4. Read the consolidated critical review (v3) for architectural context
> 5. Related prior phases: Phase 3 Wave 3 (ADW), Phase 4 Wave 2 (vestigial MC), Phase 5f (EmergentGravityBounds). 5y **closes and harvests**; it does not reopen or re-scope.

---

## Terminal Status Declaration

**5y closes as of the date of this roadmap.** No further deep-research rounds are scheduled. No further hypothesis-testing waves are scheduled. H3 (inflation-regime q-dynamics) is explicitly rejected as a trailing round — if it becomes interesting later, it is scoped as a fresh phase (6y or similar), not as a 5y continuation. The waves below are harvest-and-close activities, not exploratory research.

**Decision already made:** dual NO-GO on H1/H4 + three prior NO-GOs = structural obstruction. The formalization waves that follow are about preserving what 5y produced, not about revisiting the decision.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for 5y terminal:**
- Lean formalization of the Gibbs-Duhem obstruction theorem (Round 5 consolidated)
- Lean formalization of the q-theory NO-GO in all four KV realizations (Rounds 3, 4a, 5)
- Lean formalization of the H4 original vestigial-gravity effective fluid EOS derivation
- Lean formalization of the charge-4e ↔ vestigial-tetrad dictionary (H4 §3)
- Lean formalization of the orthogonality principle for dark-energy obstructions (H4 §9)
- Lean formalization of the generic gradient-instability result for GL bilinear FRW condensates
- Extensions to existing `VestigialGravity`, `VestigialSusceptibility`, `TetradGapEquation` modules
- Master classification table update: dark-sector viability columns with Gibbs-Duhem / orthogonality flags
- Architectural framing document update: Layer-3 emergent-physics predictive-scope recalibration
- Cross-phase integration memos: 5x, 5u, 5d, 5w impact statements

**OUT OF SCOPE for 5y terminal:**
- Paper A (q-theory DESI fit publication) — dual NO-GO verdict, no headline to write
- Paper B (vestigial EOS + fracton DM publication) — user-stated no-papers preference; content harvested into Lean instead
- H3 (inflation-regime probe) — rejected per terminal-roadmap reasoning, not rescheduled
- Any further deep-research rounds on 5y topics
- Fracton dark matter phenomenology — that work belongs to Phase 5x, which does not inherit 5y's NO-GO
- External cosmology-community engagement for 5y-specific results — no papers means no engagement track for 5y (redirect engagement budget to 5u polariton collaboration instead)
- Resolving T=H/π vs T=H/2π controversy — the six rounds computed at both where relevant; no further resolution attempted
- Full Boltzmann-code cosmological fits — the NO-GOs are structural, not fit-quality dependent

**Phase 5x relationship:** Phase 5x (dark matter at EFT-agnostic level) **does not inherit** 5y's NO-GO verdict. Fracton dark matter, residual fermionic-quartet condensates, and other DM mechanisms have different obstruction landscapes. 5x scoping proceeds independently when program bandwidth permits. The 5y roadmap explicitly documents this non-inheritance to prevent scope confusion.

**Phases 5u, 5d, 5w relationship:** Unaffected. 5u (polariton Hawking SK-EFT, Tier A priority) operates at Layer 2 in a controlled experimental regime; 5y's cosmological-scale obstructions do not propagate. 5d (RHMC ADW fermion-bootstrap) and 5w (graphene Dirac fluid) are orthogonal physics questions. These phases remain the program's active forward-motion work during and after 5y's terminal formalization.

---

## Track A: Obstruction Theorem Formalization (PRIMARY HARVEST)

### Motivation

Rounds 3, 4a, 5, and H4 §9 collectively establish a structural theorem: **emergent dark-energy frameworks based on a single self-tuning composite scalar vacuum variable `q`, with action `L = R/(16πG) + ε(q) + L_SM` and standard Gibbs-Duhem equilibrium, lock `w_vac = −1` instantaneously by Lorentz invariance and cannot produce DESI-compatible time-evolving `w(z)`.** The theorem covers the 4-form realization (KV 2008), the 2-brane realization (KV 2011), the fermionic-crystal elasticity-tetrad realization (KV 2019), and unimodular q-theory — the full tested KV family. No prior formalization of emergent-vacuum obstruction theorems exists in any proof assistant.

Formalizing this is the single highest-leverage Lean harvest from 5y. It produces a first-of-its-kind result in the formal-verification literature (valuable for CPP 2027 flag-planting), it documents the Round 3-5 work in a permanent machine-checked form, and it provides a reusable formal tool for evaluating future emergent-vacuum proposals in the program.

### Wave 1 — `GibbsDuhemTheorem.lean` [Pipeline: Stages 1–5]

**Goal:** Formalize the core Gibbs-Duhem obstruction theorem as a standalone Lean module.

**Prerequisites:** None beyond existing infrastructure. Round 5 provides the mathematical content in full.

**Module structure:**
- `lean/SKEFTHawking/GibbsDuhemTheorem.lean` — core theorem: for any (ε, q) pair satisfying the hypothesis triple (single scalar self-tuning variable, standard emergent-vacuum action, Gibbs-Duhem equilibrium `ρ_V(q₀) = 0, dρ_V/dq|_{q₀} = 0`), `w_vac(q₀) = −1` identically. Lorentz-invariance lemma. Stress-tensor decomposition lemma. Locality-of-EOS-in-time corollary.
- Target ~15 theorems.

**Bridges:**
- Feeds `QTheoryNoGoTheorem.lean` (Wave 2) as the foundational hypothesis
- Feeds `DarkEnergyObstructionPrinciple.lean` (Wave 3) as the first of four obstruction factors

**Deliverables:**
- `lean/SKEFTHawking/GibbsDuhemTheorem.lean` zero-sorry, building clean
- `tests/test_gibbs_duhem.lean` (or `.py` per project convention) verifying key derivations
- Inline documentation citing Rounds 3, 4a, 5 source equations `[EQ.01]` through `[EQ.77]`
- Inventory update: +15 theorems, +1 module

**Estimated LOE:** 1.5 weeks
**Risk:** Low. Mean-field thermodynamic argument plus algebraic manipulation of real-valued functions. No transcendental functions, no category-theory heavy-lifting, no anticipated Mathlib gaps.

---

### Wave 2 — `QTheoryNoGoTheorem.lean` [Pipeline: Stages 1–5]

**Goal:** Apply the Gibbs-Duhem theorem to all four tested KV q-theory realizations, producing a unified formal NO-GO result.

**Prerequisites:** Wave 1 complete.

**Module structure:**
- `lean/SKEFTHawking/QTheoryNoGoTheorem.lean` — instances of the Gibbs-Duhem theorem for:
  - 4-form realization (Round 3): `F_{μνλκ} = q·ε_{μνλκ}` abstractly encoded as scalar invariant
  - 2-brane realization (Rubakov-Sibiryakov 2005 / KV 2011)
  - Fermionic-crystal elasticity-tetrad realization (Round 5, KV 2019 arXiv:1812.07046): `q = (1/4) e_a^μ E^a_μ` algebraic composite
  - Unimodular q-theory realization
  - Quantitative `m_δq² ~ M_Pl²` bound (Round 4a KV 2016 Eq. 17b cross-check)
  - Corollary: `(H₀/M_Pl)² ~ 10⁻¹²¹` DESI-suppression factor is universal across realizations
- Target ~12 theorems.

**Bridges:**
- Depends on `GibbsDuhemTheorem.lean` (Wave 1)
- Feeds `DarkEnergyObstructionPrinciple.lean` (Wave 3) as the concrete-realization layer

**Deliverables:**
- `lean/SKEFTHawking/QTheoryNoGoTheorem.lean` zero-sorry, building clean
- `tests/test_qtheory_nogo.*` with numerical suppression-factor verification
- Explicit cross-references to source equations from Rounds 3, 4a, 5
- Inventory update: +12 theorems, +1 module

**Estimated LOE:** 1.5 weeks
**Risk:** Low. Instance-of-theorem work; structurally parallel to prior per-realization analyses already in deep-research deliverables.

---

### Wave 3 — `DarkEnergyObstructionPrinciple.lean` + `DESIComparison.lean` [Pipeline: Stages 1–5]

**Goal:** Formalize the H4-articulated orthogonality principle and the quantitative DESI comparison.

**Prerequisites:** Waves 1, 2 complete.

**Module structure:**
- `lean/SKEFTHawking/DarkEnergyObstructionPrinciple.lean` — four-factor decomposition per H4 EQ.137-138:
  ```
  {DESI reachable without fine-tuning}
    = {Gibbs-Duhem evaded}
    ∩ {c_s² ≥ 0 at late times}
    ∩ {natural T_c dynamical attractor}
    ∩ {MICROSCOPE / WEP compatible}
  ```
  Each factor encoded as a Lean predicate over emergent-dark-energy models. Theorem: no known Volovik-family framework satisfies all four. Orthogonality lemmas: evading one factor does not imply satisfying others. Target ~8 theorems.
- `lean/SKEFTHawking/DESIComparison.lean` — DESI DR2 preferred region encoded as `(w₀, w_a) ∈ [−0.8, −0.66] × [−1.35, −0.75]` (1σ), 3σ envelope, quintom-B region predicate, σ-offset computation for candidate `(w₀, w_a)` predictions. Target ~8 theorems.

**Bridges:**
- Depends on `GibbsDuhemTheorem.lean`, `QTheoryNoGoTheorem.lean` (Waves 1, 2)
- Feeds `VestigialEOS.lean` (Wave 5) as the comparison target
- Cross-references `MICROSCOPEBound.lean` if extant, else trivially encodes `η_Eöt < 2.7×10⁻¹⁵`

**Deliverables:**
- Both modules zero-sorry, building clean
- Test coverage: numerical DESI comparison for candidate `(w₀, w_a)` values, including the H4 vestigial-EOS predictions from its §8 table
- Inventory update: +16 theorems, +2 modules

**Estimated LOE:** 1 week
**Risk:** Low. Predicate encoding plus real-valued comparison; no deep theorem work.

---

## Track B: Vestigial EOS Formalization (ORIGINAL DERIVATION HARVEST)

### Motivation

H4 produced what appears to be the first closed-form derivation of the effective fluid EOS `(w_vest, c_s², ζ_vest)` for a Volovik vestigial gravitational phase, via systematic analogy with the Fernandes-Fu charge-4e GL free energy. Key results: `w_vest(τ) = (1 − τ²)/(5τ² − 1)` (H4 EQ.117), `c_s²(τ) = −(1 − τ²)/(3 − 5τ²)` (EQ.120), CPL parameters `(w₀, w_a)` in closed form (EQ.129). The derivation fails DESI quantitatively — that's the H4 NO-GO verdict — but the derivation itself is a substantive technical contribution that did not exist before.

Formalizing this preserves the derivation permanently, establishes a reusable condensed-matter ↔ emergent-gravity dictionary in Lean, and demonstrates a concrete Layer-2 → Layer-3 computation whose output is falsifiable (even though in this case it is falsified). The formalization makes the architecture's scoping claim ("Layer 3 produces falsifiable predictions under concrete mechanisms") explicit and machine-checked.

### Wave 4 — `CondensedMatterAnalog.lean` + `VestigialMapping.lean` [Pipeline: Stages 1–5]

**Goal:** Formalize the charge-4e GL template and the explicit dictionary to vestigial-tetrad gravity.

**Prerequisites:** None (runs in parallel with Track A).

**Module structure:**
- `lean/SKEFTHawking/CondensedMatterAnalog.lean` — Fernandes-Fu GL action (H4 EQ.100), charge-4e composite `ψ = Δ₁² + Δ₂²` (EQ.101), Hubbard-Stratonovich decoupling in nematic and 4e channels (EQ.102-103), Jian-Huang-Yao nematic-vortex proliferation mechanism (EQ.104), Fernandes-Orth-Chubukov vestigial-order classification. Target ~10 theorems.
- `lean/SKEFTHawking/VestigialMapping.lean` — H4 §3 dictionary table as formal mapping: condensed-matter variables → gravitational variables, with preservation lemmas for each row. Target ~8 theorems.

**Bridges:**
- Feeds `VestigialEOS.lean` (Wave 5) as the source side of the derivation
- Cross-references existing `VestigialGravity.lean` for target side

**Deliverables:**
- Both modules zero-sorry, building clean
- Documentation citing Fernandes-Fu PRL 127, 047001 (2021), Jian-Huang-Yao PRL 127, 227001 (2021), Fernandes-Orth-Chubukov Annu. Rev. Condens. Matter Phys. 10, 133 (2019)
- Inventory update: +18 theorems, +2 modules

**Estimated LOE:** 2 weeks
**Risk:** Low-medium. The condensed-matter GL action is standard; mapping lemmas require care to preserve the structural analogy but do not introduce novel Lean-level difficulty.

---

### Wave 5 — `VestigialEOS.lean` [Pipeline: Stages 1–5]

**Goal:** Formalize the H4 closed-form derivation of `(w_vest, c_s², ζ_vest)` and its CPL extraction.

**Prerequisites:** Wave 4 complete.

**Module structure:**
- `lean/SKEFTHawking/VestigialEOS.lean` — vestigial thermodynamic potential `Ω_vest(T, χ)` (H4 EQ.112), saddle-point condensate (EQ.109), energy density `ρ_vest(τ)` (EQ.115), pressure `p_vest(τ)` (EQ.116), EOS `w_vest(τ)` (EQ.117), sound speed `c_s²(τ)` (EQ.120), bulk viscosity `ζ_vest(τ)` (EQ.123), CPL parameters `(w₀, w_a)` (EQ.129), gradient-instability theorem (`c_s² < 0` for `τ² < 3/5`, growth equation pathology), DESI-incompatibility theorem (no `τ₀ ∈ (0, 1)` produces `w₀ = −0.73`), fine-tuning theorem (Λ₀-augmentation requires `10⁻⁶²` to `10⁻¹²¹` tuning). Target ~20 theorems.

**Bridges:**
- Depends on `CondensedMatterAnalog.lean`, `VestigialMapping.lean` (Wave 4)
- Depends on `DESIComparison.lean` (Wave 3) for quantitative incompatibility encoding
- Feeds `DarkEnergyObstructionPrinciple.lean` (Wave 3) as a worked example of all-four-factors failure

**Deliverables:**
- Module zero-sorry, building clean
- Test coverage: numerical verification of the H4 §8 table at multiple `τ₀` values
- Explicit `GAP-1` (relaxation rate `Γ_χ`) and `GAP-2` (anisotropy coefficient `K(κ_*)`) encoded as unresolved parameters (not axioms — they are free parameters with noted sensitivity)
- Inventory update: +20 theorems, +1 module

**Estimated LOE:** 2.5 weeks
**Risk:** Medium. The algebraic manipulations are exact and finite, but the derivation touches multiple modules (thermodynamics, FRW cosmology, CPL parameterization) and the closed forms must be kept precisely aligned with the H4 deliverable. Extra care on equation transcription.

---

### Wave 6 — Extensions to Existing Vestigial-Gravity Modules [Pipeline: Stages 1–5]

**Goal:** Extend `VestigialGravity.lean`, `VestigialSusceptibility.lean`, `TetradGapEquation.lean` with the new bridging content from Track B.

**Prerequisites:** Waves 4, 5 complete.

**Module extensions:**
- `lean/SKEFTHawking/VestigialGravity.lean` (current: 18 theorems) — add vestigial-phase definition formalization matching H4 EQ.96 (`⟨ē^a_μ⟩ = 0`, `g_μν = η_ab ⟨ē^a_μ ē^b_ν⟩ ≠ 0`); Z4 symmetry structure per Volovik arXiv:2406.00718; fermion-vs-boson WEP-violation structural lemma. Add ~6 theorems → 24 theorems.
- `lean/SKEFTHawking/VestigialSusceptibility.lean` (current: 16 theorems) — add Kubo formula connection to bulk viscosity (H4 EQ.121), RPA-summed susceptibility closed form at FRW, FDT connection to dissipation. Add ~8 theorems → 24 theorems.
- `lean/SKEFTHawking/TetradGapEquation.lean` (current: 20 theorems) — add vestigial-phase gap equation extension; BCS-like `T_{c,vest} = Λ_UV exp[−1/g̃_*]` (H4 EQ.108); natural-scale obstruction lemma ("no dynamical mechanism ties `T_{c,vest}` to `H(t)`"). Add ~4 theorems → 24 theorems.

**Bridges:**
- Draws from `VestigialEOS.lean` (Wave 5) for EOS-extraction connections
- Draws from `VestigialMapping.lean` (Wave 4) for the dictionary

**Deliverables:**
- Three extended modules zero-sorry, building clean
- Existing theorem numbers preserved; new theorems appended
- Inventory update: +18 theorems, 0 new modules (extensions)

**Estimated LOE:** 1.5 weeks
**Risk:** Low. Extension work on stable modules using the same predicate-style conventions.

---

## Track C: Architectural Consolidation (CHEAP, HIGH-LEVERAGE)

### Motivation

The 5y phase produces not only formal-verifiable content but architectural-scoping insight. The three-layer architecture's predictive-scope boundary has been clarified: Layer 3 produces SM+GR-sector emergent physics cleanly; it does not (via tested mechanisms) produce cosmological-constant-type physics. This is a sharpening of scope, not a retreat, and documenting it explicitly prevents future-Phase scope confusion. The classification table that has organized the program's mechanism survey gets its first dark-sector-compatibility columns — a cheap high-leverage consolidation that benefits every future architectural conversation.

### Wave 7 — Classification Table Update + `ClassificationTableDark.lean` [Pipeline: Stages 6–7]

**Goal:** Add dark-sector viability columns to the master classification table in `Emergent_Gauge_Fields_and_Gravity_from_Superfluid_Order_Parameters.md`; encode the flags formally.

**Prerequisites:** Waves 1-3 complete (need the obstruction principle for the flags to be meaningful).

**Deliverables:**
- Updated classification table in the existing markdown doc with new columns:
  - Gibbs-Duhem obstruction status (locked / evaded / N/A)
  - Orthogonality principle factor status (how many of the four factors satisfied)
  - DESI compatibility (under tested mechanisms) (yes / no / untested)
  - MICROSCOPE compatibility (satisfied / constrained / violated)
  - Compatibility with existing `GaugeErasure` theorem
  - Compatibility with ADW gravity Layer 3
- Companion `lean/SKEFTHawking/ClassificationTableDark.lean` — typeclass-encoded compatibility flags, one instance per mechanism row. Target ~8 theorems.

**Estimated LOE:** 3-5 days, can run during any slack period.
**Risk:** Minimal.

---

### Wave 8 — Architectural Framing Document Update

**Goal:** Update the project's architectural-scoping documentation to reflect the refined predictive-scope boundary.

**Prerequisites:** Waves 1-7 complete (the architectural claim must be grounded in the formalized obstruction theorems).

**Document updates:**
- `docs/ARCHITECTURE_SCOPE.md` (or equivalent top-level architecture doc) — add "Dark-Sector Scope" section documenting:
  - The tested mechanisms (KV q-theory in four realizations; Volovik vestigial gravity; Volovik two-fluid de Sitter / second-sound graviton)
  - The structural obstruction (Gibbs-Duhem + orthogonality principle)
  - The predictive-scope recalibration: Layer 3 produces SM+GR physics under tested mechanisms; dark-sector physics is outside the architecture's tested predictive scope
  - The explicit note that dark matter (Phase 5x target) does not inherit this result
- `docs/THREE_LAYER_ARCHITECTURE.md` (or equivalent) — amend Layer 3 claims to reflect scoping
- `README.md` or project top-level claim-statement — update to reflect sharpened scope

**Deliverables:**
- Updated architectural documentation with clear scoping claims
- Cross-references to the new Lean modules providing the formal backing

**Estimated LOE:** 3 days.
**Risk:** Minimal (documentation work).

---

### Wave 9 — Cross-Phase Integration Memos

**Goal:** Document the precise impact (or non-impact) of 5y's closure on each other active phase, preventing scope confusion.

**Prerequisites:** Waves 1-8 substantively complete or underway.

**Memo structure:**
- `docs/stakeholder/Phase5y_Impact_on_5x.md` — dark matter phase inherits no NO-GO from 5y; different mechanisms, different obstruction landscape; 5x scoping proceeds independently
- `docs/stakeholder/Phase5y_Impact_on_5u.md` — polariton Hawking Tier A work entirely unaffected; 5y cosmological-scale obstructions do not propagate to lab-scale analog gravity; Paris LKB collaboration preparation proceeds unchanged
- `docs/stakeholder/Phase5y_Impact_on_5d.md` — RHMC ADW fermion-bootstrap unaffected; ADW condensation as a mechanism for generating tetrad physics is orthogonal to the dark-energy application
- `docs/stakeholder/Phase5y_Impact_on_5w.md` — graphene Dirac fluid phase unaffected; pure Layer-2 physics with experimental handles independent of cosmology
- `docs/stakeholder/Phase5y_Closure_Summary.md` — one-page closure summary for any future reader (collaborator, reviewer, future-self): what 5y attempted, what it found, what remains valuable

**Deliverables:**
- Five integration memos filed
- No ongoing action items from 5y for any other phase

**Estimated LOE:** 2-3 days.
**Risk:** Minimal.

---

## Track D: Program-Level Redirect (NOT A WORK TRACK — CONTEXT ONLY)

The original Phase 5y roadmap included a Track D (external engagement) under the theory that 5y would produce papers needing community reception. Dual NO-GO + no-papers preference = Track D is explicitly dissolved for 5y. The engagement budget that would have gone into 5y community outreach redirects to:

- **Phase 5u Tier A polariton collaboration** — Paris LKB (Falque / Bramati / Giacobino) outreach, which was always the single highest-leverage external-engagement target in the program's ledger
- **Mathlib contributions** — PivotalCategory PR as first target, RibbonCategory / FusionCategory pipeline following
- **CPP 2027 formalization flag-planting** — the 5y harvest (particularly `GibbsDuhemTheorem.lean` as a first-of-its-kind obstruction theorem) feeds naturally into CPP 2027 submission material

No engagement work on 5y results themselves. If the Lean harvest attracts community interest post-filing, that's incidental and welcome, not scheduled.

---

## Decision Gates

**Wave 8 (original roadmap) — DISSOLVED.** The original roadmap's Wave 8 was a GO/NO-GO gate on the q-theory DESI fit; the gate has fired with a NO-GO outcome, and the current roadmap is the post-gate execution plan. No further decision gates scheduled for 5y.

**Optional abort gates on the formalization tracks:** If any wave in Track A or Track B hits an unanticipated Mathlib obstruction, the affected module scope is reduced to core theorems only (skip extensions), rather than extending the wall-clock timeline. The harvest is valuable at 60 theorems just as at 100; there is no quantitative threshold that makes 5y's closure more or less valid.

---

## Dependencies

```
Track A:
  Wave 1 (GibbsDuhemTheorem) → Wave 2 (QTheoryNoGoTheorem) → Wave 3 (DarkEnergyObstructionPrinciple + DESIComparison)

Track B:
  Wave 4 (CondensedMatterAnalog + VestigialMapping) → Wave 5 (VestigialEOS) → Wave 6 (extensions to VestigialGravity/Susceptibility/TetradGapEquation)

Track C:
  Wave 7 (Classification table update) — requires Waves 1-3
  Wave 8 (Architectural framing) — requires Waves 1-7
  Wave 9 (Cross-phase memos) — parallel with Wave 8

Parallelism:
  Track A and Track B run concurrently. Track C Wave 7 starts after Track A Wave 3.
  Track C Waves 8-9 close out the phase.
```

**Parallelism:** Tracks A and B are independent and can run concurrently. Estimated wall-clock if full sequence executes in parallel: 7-10 weeks. Track C adds ~2 weeks serial at the end.

---

## Timeline

| Wave | Track | Scope | LOE | Dependencies | Priority |
|---|---|---|---|---|---|
| Wave 1 | A | `GibbsDuhemTheorem.lean` | 1.5 weeks | None | **TIER 0 — foundational** |
| Wave 2 | A | `QTheoryNoGoTheorem.lean` | 1.5 weeks | Wave 1 | **TIER 1** |
| Wave 3 | A | `DarkEnergyObstructionPrinciple.lean` + `DESIComparison.lean` | 1 week | Waves 1, 2 | **TIER 1** |
| Wave 4 | B | `CondensedMatterAnalog.lean` + `VestigialMapping.lean` | 2 weeks | None | **TIER 1** |
| Wave 5 | B | `VestigialEOS.lean` | 2.5 weeks | Wave 4 | **TIER 1** |
| Wave 6 | B | Extensions to `VestigialGravity`, `VestigialSusceptibility`, `TetradGapEquation` | 1.5 weeks | Waves 4, 5 | **TIER 1** |
| Wave 7 | C | Classification table update + `ClassificationTableDark.lean` | 3-5 days | Waves 1-3 | **TIER 2** (slack-time) |
| Wave 8 | C | Architectural framing document update | 3 days | Waves 1-7 | **TIER 2** |
| Wave 9 | C | Cross-phase integration memos | 2-3 days | Waves 1-8 | **TIER 2** |

**Total estimated LOE:** 7-10 weeks wall-clock with Tracks A and B running in parallel. Minimum viable (core Track A only): 4 weeks. Background-priority execution alongside primary-program phases (5u, 5d, 5w) is expected.

**Not on this timeline:** papers, community engagement for 5y specifically, H3 inflation probe, any resumption of DESI-fitting work.

---

## Deep Research — All Rounds Complete

| # | Topic | File | Status |
|---|---|---|---|
| Round 3 | q-theory → DESI derivation (procedural recipe) | `Lit-Search/Phase-5y/Phase5y_qtheory_desi_derivation.md` | **COMPLETE — NO-GO verdict** |
| Round 4a | δq Klein-Gordon extension + KV 2016 validation | `Lit-Search/Phase-5y/Phase5y_qtheory_deltaq_extension.md` + `Phase5y_Round4a_Validation.md` | **COMPLETE — NO-GO verdict** |
| Round 4b | 3-form aether literature survey | `Lit-Search/Phase-5y/Phase5y_aether_3form_literature.md` | **COMPLETE — no new mechanism** |
| Round 5 | Fermionic-crystal elasticity-tetrad realization (KV 2019) | `Lit-Search/Phase-5y/Phase5y_fermionic_crystal_elasticity_tetrad.md` | **COMPLETE — NO-GO verdict; strengthened Gibbs-Duhem theorem** |
| H1 | Kronecker-anomaly second-sound graviton | `Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md` | **COMPLETE — NO-GO with PARTIAL footnote** |
| H4 | Vestigial-gravity effective fluid EOS via charge-4e analog | `Lit-Search/Phase-5y/Phase5y_H4_vestigial_gravity_EOS.md` | **COMPLETE — NO-GO for DESI, PARTIAL for framework; original derivation** |
| — | ~~H2 (Gibbs-Duhem as predictive constraint)~~ | absorbed into Round 5 theorem structure | **ABSORBED — not separately scheduled** |
| — | ~~H3 (inflation-regime q-dynamics)~~ | not scheduled | **REJECTED — scoped as potential future 6y, not 5y trailing round** |

**Six rounds delivered. Zero rounds pending. 5y deep-research work is closed.** Any future scheduling of H3 or related probes belongs to a fresh phase scoping, not to 5y.

---

## What Success Looks Like

**Track A (Obstruction Theorem Formalization):**
- Core Gibbs-Duhem obstruction theorem formalized as `GibbsDuhemTheorem.lean` with 15 theorems, zero sorry.
- All four KV q-theory realizations covered by `QTheoryNoGoTheorem.lean` with 12 theorems, zero sorry.
- Four-factor orthogonality principle encoded in `DarkEnergyObstructionPrinciple.lean` with 8 theorems, zero sorry.
- DESI DR2 comparison formally encoded in `DESIComparison.lean` with 8 theorems, zero sorry.
- **Program-level value:** first-of-its-kind emergent-vacuum obstruction theorem in any proof assistant; CPP 2027 flag-planting material.

**Track B (Vestigial EOS Formalization):**
- Charge-4e GL template + dictionary formalized (18 theorems across two modules).
- H4 closed-form `(w_vest, c_s², ζ_vest)` derivation fully formalized (20 theorems).
- Extensions to three existing vestigial-gravity modules (18 theorems total).
- **Program-level value:** first formalization of a condensed-matter ↔ emergent-gravity dictionary; concrete worked example of a Layer-2 → Layer-3 falsifiable prediction (even if the prediction is falsified).

**Track C (Architectural Consolidation):**
- Master classification table updated with dark-sector viability columns; `ClassificationTableDark.lean` with 8 theorems.
- Architectural-scoping documentation refined to reflect the Layer-3 predictive-scope boundary.
- Cross-phase integration memos prevent scope confusion on 5x/5u/5d/5w.

**Cumulative Lean deliverables:**
- 7 new modules: `GibbsDuhemTheorem`, `QTheoryNoGoTheorem`, `DarkEnergyObstructionPrinciple`, `DESIComparison`, `CondensedMatterAnalog`, `VestigialMapping`, `VestigialEOS`
- 1 classification module: `ClassificationTableDark`
- 3 extended modules: `VestigialGravity`, `VestigialSusceptibility`, `TetradGapEquation`
- ~85-100 new theorems
- Zero sorry target maintained
- Inventory: 3021 → ~3110-3125 theorems, 133 → 141 modules

**Paper deliverables:** NONE. 5y produces no papers. This is intentional and reflects user-stated program preference for formal-verification output over publication pursuit during the current period.

**Structural deliverables:**
- Predictive-scope boundary for the three-layer architecture explicitly documented.
- Dark-sector-compatibility columns in the master classification table.
- Cross-phase impact statements for 5x, 5u, 5d, 5w.
- GO/NO-GO decision framework *demonstrated in execution* (six rounds, clean closure) — reusable for future high-leverage bets where the path may also close negatively.

---

## Architectural Notes

**Why closure rather than H3 inflation probe:** The original roadmap's four-hypothesis list included H3 (inflation-regime q-dynamics where `H ~ M_Pl`) as a logical alternative escape route. The terminal-roadmap decision is to not execute H3 as a 5y trailing round, for three reasons: (1) the 3-form-inflaton literature is already populated (Koivisto-Nunes-Mulryne arXiv:1209.2156 et seq.), and the Gibbs-Duhem angle may not survive contact with inflation's non-equilibrium setting (the theorem assumes equilibrium thermodynamics); (2) the program's stated priority is forward progress, not scope completeness; (3) Phases 5u/5d/5w have positive-progress trajectories that outrank an inflation probe. If H3 becomes interesting later — e.g., from unexpected CMB results, a polariton-group collaboration with inflationary interests, or a new theoretical hook — it gets a fresh phase scoping (6y or similar), not a 5y revival.

**Why no papers:** User-stated preference during the H1/H4 reframe conversation: "I'm ok with writing up negative results, but I'm also not looking to push papers as an outcome either." 5y's substantive content (obstruction theorem, vestigial EOS derivation, orthogonality principle) is harvested into Lean instead, which produces program-ledger value without paper-pursuit overhead. If user preference changes later — e.g., CPP 2027 submission motivates a companion short paper on the obstruction theorem — the Lean modules are ready-made source material.

**Why the Lean harvest matters independent of publications:** The Gibbs-Duhem obstruction theorem is novel formalization territory — no prior emergent-vacuum obstruction theorem exists in any proof assistant. The vestigial-EOS derivation is novel physics content (H4 produced it; nobody else has derived it). Both become permanent, machine-checked program assets. The architecture's predictive-scope claim ("Layer 3 produces falsifiable predictions; here is a worked example, even if it fails DESI") becomes concrete and rigorous rather than aspirational.

**What 5y does NOT claim:**
- Does not claim q-theory is falsified as a vacuum-stability framework. The NO-GO applies specifically to late-time dark-energy phenomenology. Q-theory as a zero-temperature equilibrium framework and possibly inflationary framework (untested) remains intact.
- Does not claim vestigial gravity is ruled out as a concept. The H4 verdict is NO-GO for DESI under the natural mapping; PARTIAL for the framework. A future tetrad-condensation cosmology with dynamical gap scale might revive elements.
- Does not claim no emergent dark energy is possible. The obstruction covers the Volovik-family mechanisms specifically; entropic gravity, causal-set approaches, Jacobson-type thermodynamic GR are outside the tested scope.
- Does not claim the three-layer architecture is falsified. The architecture's Layer-3 SM+GR-sector claims are unaffected. Only the dark-sector predictive claim is scoped out.

**What 5y does claim, terminally:**
- The Gibbs-Duhem obstruction theorem covers all four tested KV q-theory realizations, formalized as a first-of-its-kind Lean result.
- The four-factor orthogonality principle decomposes why Volovik-family emergent-dark-energy frameworks fail DESI compatibility.
- The vestigial-gravity effective fluid EOS admits a closed-form derivation via charge-4e analogy, and this derivation quantitatively fails DESI under natural parameter values.
- GL-type bilinear condensates mapped onto FRW generically produce `c_s² < 0` at late times, constraining an entire class of emergent-cosmology proposals.
- The three-layer architecture's predictive-scope boundary is sharper: SM+GR sector in, dark sector out (under tested mechanisms).

---

## Cross-References

**Prior phases this extends / harvests from:**
- Phase 3 Wave 3 (ADW mean-field gap equation) — `src/adw/`, `ADWMechanism.lean`
- Phase 4 Wave 2 (Vestigial gravity simulation) — `src/vestigial/`, `VestigialGravity.lean`, `VestigialSusceptibility.lean`
- Phase 4 Wave 2-3 (Fracton hydrodynamics) — `src/fracton/`, `FractonHydro.lean`, `FractonFormulas.lean`, `FractonGravity.lean`
- Phase 5 Wave 9C-3 (Wetterich NJL fermion-bag MC) — `WetterichNJL.lean`, `src/vestigial/wetterich_model.py`
- Phase 5d (TetradGapEquation) — `TetradGapEquation.lean`, `src/adw/tetrad_gap_solver.py`
- Phase 5f (EmergentGravityBounds) — `EmergentGravityBounds.lean`

**Parallel phases (unaffected by 5y closure):**
- Phase 5u (Paper 10 polariton SK-EFT, Tier A) — continues on its own timeline
- Phase 5d (RHMC ADW fermion-bootstrap) — continues on its own timeline
- Phase 5w (Graphene Dirac fluid) — continues on its own timeline
- Phase 5x (Dark matter at EFT-agnostic level) — no NO-GO inheritance; scoping when bandwidth permits

**Superseded:**
- `Phase5y_Roadmap.md` v1 (2026-04-22) — the pre-deep-research exploratory scoping; this document replaces it

**Prior deep research corpus (all rounds COMPLETE, do not re-run):**
- Round 0.5: Nemotron consultation (Oct 2025) — original 5y scoping
- Round 1: wf-46ace029 (Apr 2026) — Volovik 2024-2026 landscape
- Round 1.5: wf-e02518ef (Apr 2026) — biographical context + q-theory centrality surfacing
- Round 3: q-theory DESI derivation — NO-GO
- Round 4a: δq Klein-Gordon extension — NO-GO
- Round 4b: 3-form aether literature survey — no new mechanism
- Round 5: fermionic-crystal elasticity-tetrad — NO-GO + strengthened theorem
- Round H1: Kronecker-anomaly second-sound graviton — NO-GO
- Round H4: vestigial-gravity EOS via charge-4e — NO-GO + original derivation

---

*Phase 5y terminal roadmap. Revised 2026-04-24, replacing `Phase5y_Roadmap.md` v1. All six deep-research rounds complete; five NO-GO verdicts plus one original derivation harvested. Roadmap structure follows [Phase 5s template](https://github.com/NetRxn/SK_EFT_Hawking/blob/main/docs/roadmaps/Phase5s_Roadmap.md). All waves follow [Wave Execution Pipeline](https://github.com/NetRxn/SK_EFT_Hawking/blob/main/docs/WAVE_EXECUTION_PIPELINE.md). Formalization-harvest waves proceed as background priority alongside primary-program phases 5u, 5d, 5w. No further deep-research rounds scheduled. No papers scheduled. 5y closes.*
