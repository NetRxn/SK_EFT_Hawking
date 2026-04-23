# Phase 5y: Emergent Cosmology from ADW — Dark Sector from Vestigial-Phase De Sitter Thermodynamics

## Technical Roadmap — April 2026

*Prepared 2026-04-22 | Follows the Phase 5s pattern: decompose a high-leverage question ("does the ADW architecture produce observable dark-sector physics?") into tractable finite deliverables with clear GO/NO-GO gates.*

**Entry state:** 3021 Lean theorems, 0 sorry, 1 axiom across 133 modules. `ADWMechanism` (21), `VestigialGravity` (18), `VestigialSusceptibility` (16), `TetradGapEquation` (20), `WetterichNJL` (18), `FractonFormulas` (45), `FractonHydro` (17), `FractonGravity` (20) provide the Layer-1→Layer-2 machinery. `AcousticMetric` (8), `SKDoubling` (9), `CGLTransform` (7), `SecondOrderSK` (19) provide the Layer-2→Layer-3 SK-EFT machinery. `KerrSchild` (7) provides gravitational solutions scaffolding. Paper 6 Monte Carlo is the standing bottleneck; 5y is explicitly designed to run in parallel without touching it.

**Strategic framing:** Two rounds of deep research (Oct 2025 Nemotron consultation; Round 1 wf-46ace029 Apr 2026; Round 1.5 wf-e02518ef Apr 2026) have locked the spine. DESI DR2 (Mar 2025) prefers w₀>−1 with w_a<0 at 2.8–4.2σ — quintom-like behavior wCDM cannot produce. MICROSCOPE final 2022 bounds the weak equivalence principle at η<2.7×10⁻¹⁵. Klinkhamer–Volovik q-theory (2008–2017) plus Volovik 2023–2026 de Sitter two-fluid decay papers provide a decades-old self-tuning-vacuum mechanism that predicts exactly the DESI trajectory. **Nobody has performed the q-theory→DESI fit.** That fit is 5y's headline deliverable.

**Paper architecture:** 5y splits into two papers. **Paper A (near-term, PRL/PRD-Rapid target):** q-theory + de Sitter decay → w_eff(z) → DESI DR2 fit. **Paper B (follow-up, PRD full paper target):** vestigial-phase EOS derivation + fracton dark matter phenomenology + classification table update. Paper A is the GO/NO-GO bet; Paper B consolidates regardless of Paper A outcome.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results in `Lit-Search/Phase-5y/` as they arrive
> 4. Read the consolidated critical review (v3) for architectural context
> 5. Related prior phases: Phase 3 Wave 3 (ADW), Phase 4 Wave 2 (vestigial MC), Phase 5f (EmergentGravityBounds). 5y **extends**, does not supersede, these.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for 5y:**
- Derivation of w_eff(z) from Klinkhamer–Volovik q-theory with de Sitter vacuum decay
- Fit to DESI DR2 + DES-SN5YR best-fit region (w₀,w_a) ≈ (−0.73, −1.0)
- MICROSCOPE residual-vestigial-phase bound
- Vestigial-phase effective fluid EOS (new derivation via charge-4e analogy)
- Fracton dark matter phenomenological assessment (Pretko + Doshi-Gromov)
- Dark-sector viability columns for the existing master classification table
- New Lean modules extending `VestigialGravity`, `VestigialSusceptibility`, `TetradGapEquation`, `FractonFormulas` to FRW cosmology

**OUT OF SCOPE for 5y (deferred or ruled out):**
- Verlinde entropic gravity as a positive framework (falsified by cluster lensing; documented as cautionary tale only)
- Any attempt to carry non-Abelian gauge information through Layer 2 (structurally ruled out by `GaugeErasure`)
- Full Mathlib differential geometry build-out (project uses predicate style)
- Full Boltzmann-code cosmological fits (use published DESI contours directly)
- Lattice Monte Carlo for dark-sector models (gated on Paper 6 MC unblock)
- Resolving the T=H/π vs T=H/2π controversy (Diakonov 2025 vs Volovik 2510.24502); 5y computes at both, reports both
- Wetterich pregeometry, Padmanabhan null-surface thermodynamics as alternative routes (noted in Paper A discussion, not derived)

**Phase 5x relationship:** Phase 5x treats dark matter/energy at EFT-agnostic level; 5y commits to ADW/vestigial as Layer-1→Layer-2 microphysics. No narrative consistency required between the phases; they are complementary bracketing.

---

## Track A: q-theory → DESI Fit (PAPER A, HEADLINE)

### Motivation

The Klinkhamer–Volovik q-theory program (2008 onward) provides a self-tuning mechanism for Λ: a 4-form field strength F_{μνλκ}=q·ε_{μνλκ} whose conjugate chemical potential drives the observable vacuum energy to zero in equilibrium. The 2017 extension (arXiv:1601.04676 "Relaxation of vacuum energy in q-theory"; arXiv:1612.02595 "Dark matter from dark energy in q-theory") explicitly couples q-dynamics to matter creation, producing a *decaying vacuum* whose residual Λ scales as K³_QCD/E²_Planck — the right order of magnitude observed. Volovik 2023–2026 added the de Sitter thermodynamic framework (T_dS=H/π, first law, two-fluid decomposition). **The pieces are published; the fit is not.**

If q-theory reproduces DESI DR2 (w₀,w_a) at physically reasonable parameter values, the program has its first quantitative observational contact. If it does not, the framework is falsified against current data, which is itself publishable as a clean negative result.

### Wave 1 — q-theory derivation [John + agent, primary deliverable]

**Task:** `Lit-Search/Phase-5y/5y-1-qtheory-desi-derivation.md` (**NEW PROMPT NEEDED — Round 3**)

**Goal:** Derive w_eff(a) = w₀ + w_a(1−a) + O((1−a)²) explicitly from coupled q-theory + matter-creation equations on flat FRW. Extract numerical (w₀, w_a) at both T_dS=H/π and T_dS=H/2π. Compare to DESI DR2 + DES-SN5YR preferred region.

**Primary inputs (required reads):**
- arXiv:0711.3170 — Klinkhamer-Volovik "Self-tuning vacuum variable" (2008, PRD 77, 085015)
- arXiv:0907.4887 — Klinkhamer-Volovik "Towards a solution of the CC problem" (2010, JETP Lett. 91, 259)
- arXiv:1601.04676 — Klinkhamer-Savelainen-Volovik "Relaxation of vacuum energy in q-theory" (2017, JETP 135, 727)
- arXiv:1612.02595 — Volovik "Dark matter from dark energy in q-theory" (2017, JETP Lett. 105, 273)
- arXiv:2312.02292 — Volovik "Thermodynamics and decay of de Sitter vacuum" (2024, Symmetry 16, 763)
- arXiv:2411.01892 — Volovik "Proton decay in de Sitter environment" (2025)
- arXiv:2504.05763 — Volovik "First law of de Sitter thermodynamics" (2025, JETP Lett. 121, 766)
- arXiv:2503.14738 — Adame et al. "DESI DR2 Results II: BAO and Cosmological Constraints" (2025)

**Deliverables:**
- Derivation memo in `Lit-Search/Phase-5y/` with numbered equations (ready for Appendix A of Paper A)
- Numerical (w₀, w_a) at both temperature conventions
- Parameter identification: required m-scale, implied Ω_Λ, any fine-tuning needed
- GO/NO-GO decision matrix (Paper A headline chart)

**Deep research gate:** This wave is a single focused derivation. Prior rounds returned survey/biographical content; Round 3 prompt enforces procedural recipe with stop-sign against drift. If Round 3 also underdelivers, pivot to manual derivation (user has capability; research was acceleration, not dependency).

**Estimated LOE:** 1–2 weeks (derivation + numerical overlay)
**Risk:** Medium. Derivation tractable in principle; risks are (a) free parameters not uniquely specified by Volovik/Klinkhamer, forcing choices, (b) fit requiring fine-tuning, (c) only one temperature convention works, requiring defensive framing.

---

### Wave 2 — Lean formalization core [Pipeline: Stages 1–5]

**Goal:** Machine-check the q-theory → w_eff(z) chain in Lean 4, integrating with existing vestigial/ADW infrastructure.

**Prerequisites:** Wave 1 derivation complete.

**New modules:**
- `lean/SKEFTHawking/QTheory.lean` — q-variable definition (as abstract 4-form scalar invariant), self-tuning equilibrium condition, ρ_vac(q) = ε(q) − q·dε/dq, residual Λ ~ K³_QCD/E²_Planck formula. Target ~15 theorems.
- `lean/SKEFTHawking/DeSitterThermodynamics.lean` — T_dS = H/π and T_dS = H/(2π) as explicit postulates (not theorems — the controversy is real); first law dE = T_dS dS − p dV as structure; matter-creation rate w_create ∝ exp(−E_act/T_dS) parameterized by E_act. Target ~12 theorems.
- `lean/SKEFTHawking/FRWCosmology.lean` — flat FRW scale factor, Friedmann equation, acceleration equation, CPL parameterization w(a)=w₀+w_a(1−a), condition `w < −1/3 → ä > 0` as theorem. Project uses predicate style; no Mathlib-DG dependency required. Target ~15 theorems.
- `lean/SKEFTHawking/TwoFluidDeSitter.lean` — Landau two-fluid decomposition on FRW: vacuum (ρ_s, p_s=−ρ_s) + normal (ρ_n, p_n=w_n·ρ_n), coupled conservation with exchange term Q(t) sourced by matter-creation rate. Target ~12 theorems.
- `lean/SKEFTHawking/QTheoryToCosmology.lean` — bridge theorems: q-theory equilibrium → w_vac=−1 instantaneous; decay-driven Q(t) → w_eff(a) departure from −1; extraction of (w₀, w_a) from model parameters. Target ~15 theorems.

**Bridges to existing infrastructure:**
- `VestigialSusceptibility.lean` → `TwoFluidDeSitter.lean` (susceptibility as input to Q(t) structure)
- `TetradGapEquation.lean` → `QTheory.lean` (parallel self-consistency structure)
- `AcousticMetric.lean` + `FRWCosmology.lean` (reuse metric predicate-style scaffolding)
- `KerrSchild.lean` → `FRWCosmology.lean` (Sherman-Morrison inverse pattern for FRW shift)

**Deliverables:**
- ~50–70 new theorems across 5 new modules, zero sorry target
- Build clean: full SKEFTHawking package compiles no-cache
- Test coverage: `tests/test_qtheory.py`, `tests/test_frw_cosmology.py`, cross-layer validation
- Inventory update: 3021 → ~3085 theorems, 133 → 138 modules

**Estimated LOE:** 3 weeks
**Risk:** Low. Each module is algebraic / predicate-style, pattern-matches to existing phases. No new Mathlib infrastructure required.

---

### Wave 3 — Paper A draft + constraint-survey inclusion [Pipeline: Stages 6–11]

**Goal:** Draft Paper A (`papers/paper13_qtheory_desi/paper_draft.tex`) targeting PRL (4pp+supplement) or PRD-Rapid. Include constraint-survey sidebar so the paper stands alone.

**Constraint survey content (I handle directly via targeted web-search, not deep research — see Round 2 lesson):**
- MICROSCOPE final 2022 bound η < 2.7×10⁻¹⁵ (Touboul et al. PRL 129, 121102) + 2024–2026 updates if any
- Atom interferometry EP tests: Stanford/Kasevich, Bremen ZARM, MAGIS-100/AION projections
- LLR 2023–2026 (Mueller-Biskupek-Williams) strong-EP bound
- LIGO/Virgo/KAGRA O4a graviton-speed bounds, |c_gw − c|/c < few × 10⁻¹⁵
- DESI DR2 full-shape clustering (arXiv:2411.12022) bounds on f(z)σ₈
- Ranked experimental handles for residual vestigial-phase EP violation

**Deliverables:**
- Paper A draft (4pp + supplement)
- Figure 1: predicted (w₀, w_a) vs DESI DR2 contours, both temperature conventions
- Figure 2: constraint chart (MICROSCOPE, LLR, GW) vs model parameter space
- Supplement: Lean theorem pointers (module + theorem name for each derivation step)
- Aristotle submission of any residual sorry (target: zero)

**Estimated LOE:** 2 weeks
**Risk:** Low (drafting). Outcome quality depends on Wave 1 fit result.

---

## Track B: Vestigial EOS + Fracton DM (PAPER B, CONSOLIDATION)

### Motivation

The vestigial-phase EOS derivation is **original work** — no one in the literature has extracted (w, c_s, ζ) for a Volovik-style vestigial gravity phase via the charge-4e analog. The Fernandes-Fu 2021 (PRL 127, 047001) and Jian-Huang-Yao 2021 (PRL 127, 227001) vestigial Ginzburg-Landau free energies for charge-4e order above T_c provide the condensed-matter template. Mapping to gravitational vestigial phase is the novelty.

Fracton dark matter via Pretko V(r)~V₀(1−e^(−r/ξ)) + Doshi-Gromov vortex-fracton identification is a second independent angle. Pretko's always-attractive fracton interaction has gravitational-like features; Doshi-Gromov (Commun. Phys. 4, 44, 2021) is not speculative — it's an exact duality.

Paper B can be written regardless of Paper A outcome. If Paper A is GO, Paper B extends. If Paper A is NO-GO on q-theory specifically, Paper B remains as the ADW-architecture dark-sector contribution.

### Wave 4 — Vestigial-phase effective fluid EOS [derivation + Lean]

**Task:** `Lit-Search/Phase-5y/5y-4-vestigial-eos-derivation.md` (**NEW PROMPT NEEDED — procedural recipe, no biography**)

**Goal:** Derive effective (w_vest, c_s_vest, ζ_vest) for a vestigial-tetrad gravitational phase by analogy with charge-4e vestigial phase above T_c.

**Primary inputs:**
- Fernandes-Fu PRL 127, 047001 (2021) — vestigial charge-4e GL theory
- Jian-Huang-Yao PRL 127, 227001 (2021) — vestigial charge-4e from nematic vortex proliferation
- Fernandes-Orth-Chubukov review (various 2019–2024) — vestigial order thermodynamics
- Volovik arXiv:2312.09435 — fermionic quartet and vestigial gravity (definitional)
- arXiv:2604.14289 (2026) — deconfined pseudocriticality charge-2e ↔ charge-4e
- Existing `VestigialSusceptibility.lean` RPA susceptibility result

**Derivation skeleton:**
1. Map condensed-matter vestigial GL free energy to gravitational vestigial phase: χ ↔ tetrad susceptibility, Δ ↔ four-fermion metric correlator
2. Extract thermodynamic functions from GL potential in vestigial regime
3. Compute (w, c_s, ζ) via standard thermodynamic relations
4. Connect c_s, ζ to already-formalized RPA susceptibility via fluctuation-dissipation

**Deliverables:**
- Derivation memo (paper-ready)
- `lean/SKEFTHawking/VestigialEOS.lean` — extracted (w, c_s, ζ) as functions of susceptibility parameters. Target ~12 theorems.
- Bridge to `VestigialSusceptibility.lean` (formal connection)

**Estimated LOE:** 2 weeks
**Risk:** Medium. Original work — may hit obstacles the condensed-matter analog doesn't warn about. Fallback: flag as "first derivation; expect follow-up refinements," publish with honest caveats.

---

### Wave 5 — Fracton dark matter phenomenology [assessment]

**Goal:** Assess whether a fracton DM sector coupled to ADW-gravity Layer 3 fits Lyman-α, subhalo counts, MW satellites.

**Primary inputs:**
- Pretko PRD 96, 024051 (2017) — fracton always-attractive interaction V(r)~V₀(1−e^(−r/ξ))
- Doshi-Gromov Commun. Phys. 4, 44 (2021) — superfluid vortex = fracton exact duality
- Gromov-Radzihovsky Rev. Mod. Phys. 96, 011001 (Jan 2024) — fracton colloquium
- Giergiel et al. PRR 4, 023151 (2022) — Bose-Hubbard fracton defects
- Matus PRB 113, 075138 (2026) — Wigner crystal fracton defects
- 2023–2026 Lyman-α updates from DESI spectra and eBOSS (targeted search)
- MW satellite counts post-DES (targeted search)

**Analytical questions:**
1. Express Pretko ξ in terms of underlying fracton Hamiltonian parameters
2. Map fracton dipole-conservation transport onto cosmological structure-formation scale
3. Identify window in ξ compatible with all small-scale structure constraints
4. Compatibility with non-Abelian-gauge-erasure theorem (pre-confirmed: fracton charges are not color charges)
5. Compatibility with existing `FractonGravity.lean` DOF-gap obstruction (pre-confirmed: fracton-DM uses fractons as matter, not as gravity)

**Deliverables:**
- Phenomenology memo with specific ξ range
- `lean/SKEFTHawking/FractonDarkMatter.lean` — if the window exists, formalize the allowed-parameter-region theorem. Target ~10 theorems. If the window is closed, document as negative result with ≤5 theorems.
- Bridge to `FractonFormulas.lean`, `FractonHydro.lean`, `FractonGravity.lean`

**Estimated LOE:** 1.5 weeks
**Risk:** Low-medium. Phenomenology is well-trodden ground; Lean encoding is modest.

---

### Wave 6 — Classification table update [cheap consolidation]

**Goal:** Add "dark-matter viability" and "dark-energy viability" columns to the master classification table in `Emergent_Gauge_Fields_and_Gravity_from_Superfluid_Order_Parameters.md`.

**Rows (existing):** scalar BEC, ³He-A, ³He-B, ADW tetrad, vestigial metric, spinor BEC variants, d-wave, string-net, helical Bose-Fermi.

**New columns:**
- DM viability (yes / no / conditional + citation)
- DE viability (yes / no / conditional + citation)
- Compatibility with `GaugeErasure` theorem
- Compatibility with ADW gravity Layer 3
- MICROSCOPE-compatible?
- DESI DR2 qualitative match?

**Deliverables:**
- Updated classification table in the existing markdown doc
- Companion `ClassificationTableDark.lean` — typeclass-encoded compatibility flags. Target ~8 theorems.

**Estimated LOE:** 3–5 days, can run during any MC-bottleneck slack.
**Risk:** Minimal.

---

### Wave 7 — Paper B draft [Pipeline: Stages 6–11]

**Goal:** Draft Paper B (`papers/paper14_adw_dark_sector/paper_draft.tex` — numbering TBD based on actual next free slot) targeting PRD full paper.

**Content integration:**
- Wave 4 vestigial-phase EOS derivation
- Wave 5 fracton DM phenomenology
- Wave 6 classification table
- MICROSCOPE residual-vestigial bound section (originally 5y-D3, absorbed here)

**Deliverables:**
- Paper B draft (~10–15pp)
- Lean supplement listing all new modules and key theorems

**Estimated LOE:** 2 weeks
**Risk:** Low.

---

## Track C: Decision Gates & Pivots (EXPLICIT FALLBACKS)

### Wave 8 — Wave 1 GO/NO-GO evaluation

**Gate point:** End of Wave 1.

**GO criteria (all required):**
- Derivation closes without fatal ambiguity in Volovik/Klinkhamer source equations
- Predicted (w₀, w_a) within 2σ of DESI DR2 preferred region at *at least one* temperature convention
- Required parameter values physically reasonable (no Planck-scale fine-tuning beyond what q-theory inherently provides)

**If GO:** Execute Track A Waves 2–3 and Track B Waves 4–7 in parallel. Paper A is headline, Paper B is companion.

**If PARTIAL (within 3σ but not 2σ, or requires moderate tuning):** Paper A becomes a constraint paper — "q-theory constrained by DESI, preferred parameter region is X." Still publishable in PRD, weaker headline than PRL. Track B proceeds unchanged.

**If NO-GO (outside 3σ at both temperature conventions):** Paper A becomes a negative result paper — "Klinkhamer-Volovik q-theory ruled out by DESI DR2 at >3σ." Still publishable (PRD accepts clean negatives). Track B becomes the headline 5y contribution, renumbered as Paper A'.

**If DERIVATION INCOMPLETE (Volovik/Klinkhamer inputs insufficient to close the calculation):** Paper A becomes a specification paper — "What q-theory needs to specify to make DESI-level predictions." Narrow audience but useful to the small community working on q-theory. Track B becomes headline.

**Deliverables:**
- Decision memo in `docs/stakeholder/Phase5y_GoNoGo_Decision.md`
- Updated roadmap if pivot triggered
- Communication to any engaged collaborators

**Estimated LOE:** 1 day (decision itself). Prerequisites: Wave 1 complete.

---

## Track D: External Collaboration (LONG HORIZON, TIER-A ADJACENT)

### Wave 9 — Cosmology community engagement [research-program-level]

**Goal:** Build the external-facing relationships that convert 5y from "arxiv paper by independent researcher" to "paper with engaged community readers." This is tier-building per the Nobel-territory analysis — not a prize bet in itself, but prerequisite infrastructure for work of that ambition.

**Activities (NOT part of the Wave 1–8 deliverable chain, but run in parallel):**
- Identify 2–3 cosmology theorists currently working on DESI-motivated evolving-DE models. Candidates: DESI collaboration members who published follow-up theory papers (check arXiv:2503.14738 author list + citations); Klinkhamer (Karlsruhe, natural home for q-theory); possibly a cosmologist at a US R1 who has published on quintom dark energy (Zhang group, Caldwell group)
- Post Paper A preprint to arXiv gr-qc with clear cross-listing to cond-mat (ADW framing)
- Engage one Volovik-adjacent group (Aalto or Landau Institute) for potential comment/collaboration on Paper B's vestigial EOS (original work — community input valuable)
- Attend or present at one emergent-gravity workshop if timing works (check 2026–2027 conference schedule)
- Establish Zulip / email contact with Mathlib category-theory reviewers (Riou, Morrison) for the Lean side of Paper B supplement

**Deliverables:**
- Contact list in `docs/stakeholder/Phase5y_Engagement.md`
- Preprint posting log with arXiv IDs and date
- Workshop submissions if any

**Estimated LOE:** Ongoing. ~2 hours/week during Waves 2–7.
**Risk:** N/A (infrastructure, not research).

**Note:** This is explicitly scoped because the Nobel-territory path analysis flagged external engagement as the highest-leverage structural change. 5y alone does not reach tier A, but 5y + sustained engagement *starts* the multi-year compounding that could.

---

## Dependencies

```
Wave 1 (q-theory derivation) → Wave 8 (GO/NO-GO gate) → branches:
  GO: Wave 2 (Lean core) → Wave 3 (Paper A draft)
  PARTIAL: Wave 2' (Lean constraint version) → Wave 3' (Paper A constraint)
  NO-GO: skip Wave 2/3, Track B becomes primary
  INCOMPLETE: Wave 2'' (Lean spec version) → Wave 3'' (Paper A spec)

Wave 4 (vestigial EOS) — independent of Wave 1 outcome
Wave 5 (fracton DM) — independent
Wave 6 (classification table) — independent, can run during any slack
Wave 7 (Paper B draft) — depends on Waves 4, 5, 6

Wave 9 (external engagement) — runs in parallel throughout
```

**Parallelism:** Track A Waves 2–3 and Track B Waves 4–7 can run concurrently post-gate. Estimated wall-clock if full sequence executes: 10–12 weeks.

---

## Timeline

| Wave | Scope | LOE | Dependencies | Priority |
|---|---|---|---|---|
| Wave 1 | q-theory → w_eff(z) derivation + DESI fit | 1–2 weeks | Round 3 deep research | **TIER 0 — gate** |
| Wave 2 | Lean formalization: QTheory, DeSitterThermodynamics, FRWCosmology, TwoFluidDeSitter, QTheoryToCosmology | 3 weeks | Wave 1 (conditional on GO/PARTIAL) | **TIER 1** |
| Wave 3 | Paper A draft + constraint survey | 2 weeks | Wave 2 | **TIER 1** |
| Wave 4 | Vestigial-phase EOS derivation + Lean | 2 weeks | Round 3 deep research (separate prompt) | **TIER 1** (Paper B headline) |
| Wave 5 | Fracton DM phenomenology + Lean | 1.5 weeks | None (pull refs directly) | **TIER 1** |
| Wave 6 | Classification table dark-sector columns | 3–5 days | None | **TIER 2** (slack-time) |
| Wave 7 | Paper B draft | 2 weeks | Waves 4, 5, 6 | **TIER 1** |
| Wave 8 | GO/NO-GO decision | 1 day | Wave 1 | **TIER 0** |
| Wave 9 | External engagement (cosmology, Volovik-adjacent, Mathlib) | Ongoing | None | **TIER 1** (parallel) |

**Total estimated LOE:** 10–12 weeks wall-clock if everything executes. Minimum viable (Track A only, NO-GO outcome): 4 weeks (Wave 1 + Wave 8 + fallback framing).

---

## Deep Research

| # | Topic | File | Status |
|---|---|---|---|
| 1 | q-theory → DESI derivation (Round 3, procedural recipe w/ stop-sign) | `Lit-Search/Tasks/Phase5y_qtheory_desi_derivation.md` | **PROMPT DRAFTED (this conversation), NEEDS FILING** |
| 2 | Vestigial-phase EOS via charge-4e analog | `Lit-Search/Tasks/Phase5y_vestigial_eos_derivation.md` | **PROMPT NEEDED** |
| 3 | Fracton DM phenomenology refs pull | `Lit-Search/Tasks/Phase5y_fracton_dm_phenomenology.md` | **DIRECT WEB-SEARCH — no deep research needed per Round 2 lesson** |
| 4 | Constraint survey (MICROSCOPE/LLR/GW 2024–2026 updates) | N/A | **DIRECT WEB-SEARCH during Wave 3** |
| — | ~~General survey of Volovik cosmology landscape~~ | ~~Round 1 wf-46ace029~~ | **COMPLETE Oct 2025 / Apr 2026 — SURVEY COMPLETE, DO NOT RE-RUN** |
| — | ~~Volovik biographical context~~ | ~~Round 2 wf-e02518ef~~ | **COMPLETE Apr 2026 — UNDERDELIVERED on derivation, surfaced q-theory centrality and T=H/π controversy; no further biography rounds** |

**Round-2 lesson explicitly captured:** Deep research agents tend to drift to biographical/landscape content when not given procedural stop-signs. Round 3 prompt enforces: numbered-equation output, procedural recipe with step gates, explicit out-of-scope list at top, and a final-check question the agent must answer before returning. If Round 3 drifts, pivot to manual derivation.

---

## What Success Looks Like

**Track A (q-theory → DESI):**
- **Best case:** Clean GO on Paper A, numbers within 1σ of DESI DR2 preferred region, PRL accepted. First quantitative fit of a decades-old emergent-vacuum mechanism to the leading observational anomaly in cosmology.
- **Expected case:** PARTIAL — constraint paper in PRD, bounds model parameters given DESI, sets up follow-up work when DESI DR3 / Euclid arrive.
- **Worst case:** NO-GO — clean negative result in PRD, q-theory ruled out, Track B becomes headline. Still publishable, still advances the program.

**Track B (vestigial EOS + fracton DM):**
- Original derivation of vestigial-phase fluid EOS — first in literature.
- Fracton DM phenomenological window identified (or cleanly closed).
- Classification table extended with dark-sector compatibility columns.
- Paper B in PRD regardless of Track A outcome.

**Lean deliverables (cumulative, across all waves):**
- 5 new core modules (QTheory, DeSitterThermodynamics, FRWCosmology, TwoFluidDeSitter, QTheoryToCosmology)
- 2 Track B modules (VestigialEOS, FractonDarkMatter)
- 1 classification module (ClassificationTableDark)
- ~70–100 new theorems
- Zero sorry target maintained
- Inventory: 3021 → ~3100–3120 theorems, 133 → 141 modules

**Paper deliverables:**
- Paper A (5y-P1): q-theory DESI fit — PRL or PRD-Rapid target, `papers/paper13_*`
- Paper B (5y-P2): ADW dark sector — PRD full paper target, `papers/paper14_*` (or next free slot)

**Structural deliverables:**
- External collaboration contacts established (Wave 9)
- Classification landscape consolidated (Wave 6)
- GO/NO-GO decision framework demonstrated (Wave 8) — reusable for future high-leverage bets

---

## Architectural Notes

**Why q-theory and not Verlinde:** Verlinde entropic gravity was considered and rejected for the 5y spine based on (a) circular derivation (pre-assumes Unruh temperature), (b) MOND predictions falsified by cluster kinematics and weak lensing, and (c) no dynamical mechanism for the observed Λ scale. Q-theory inherits none of these defects. Verlinde is referenced in Paper A discussion as cautionary contrast, not as a positive framework.

**Why split into Paper A and Paper B:** Paper A is a narrow, high-risk headline bet on a specific quantitative prediction. Paper B is architectural consolidation that survives any Paper A outcome. Splitting lets Paper A be PRL-scoped (short, sharp, one clean result) while Paper B absorbs the classification, the EOS derivation, and the fracton DM work at PRD scale. Either paper can be written without the other.

**Why T=H/π and T=H/2π both:** Volovik's factor-of-two claim vs Gibbons-Hawking is actively disputed (Diakonov 2025 vs Volovik 2510.24502, Oct 2025). 5y does not resolve this. Instead, the derivation runs at both conventions, reports both fits, and reports which (if either) matches DESI. This is honest defensive posture — if only H/π works, that's a soft argument for Volovik's interpretation; if both work, we're framework-agnostic and stronger for it.

**Why MICROSCOPE matters for 5y even though q-theory doesn't predict EP violation:** The *vestigial phase* predicts EP violation. If the current era is fully in the ECSK phase (tetrad condensed, EP restored), MICROSCOPE is automatically satisfied and we are cosmologically in the ECSK phase. If any residual vestigial-phase contribution persists today, MICROSCOPE η < 2.7×10⁻¹⁵ bounds it. This is a separate constraint Paper A addresses in Wave 3.

**What 5y does NOT claim:**
- Does not claim q-theory solves the cosmological constant problem (Klinkhamer-Volovik claim, not ours).
- Does not claim the T=H/π temperature is physical (controversy; we compute both).
- Does not claim vestigial gravity is realized in nature (Volovik claim, not ours; we derive consequences if it is).
- Does not claim fracton DM is dark matter (phenomenological assessment, not confirmation).
- Does not claim Nobel-territory relevance (that requires tier-A bet execution + decades of follow-through; 5y is Tier B/C infrastructure).

**What 5y does claim, if successful:**
- First quantitative fit of Klinkhamer-Volovik q-theory to cosmological data.
- First derivation of effective fluid EOS for Volovik-style vestigial gravitational phase.
- First machine-checked formalization of FRW cosmology + q-theory in a proof assistant.
- Integration of dark-sector phenomenology into the three-layer emergent-physics architecture.
- Cleanly parameterized experimental-falsifiability criteria for a specific emergent-vacuum framework.

---

## Cross-References

**Prior phases this extends:**
- Phase 3 Wave 3 (ADW mean-field gap equation) — `src/adw/`, `ADWMechanism.lean`
- Phase 4 Wave 2 (Vestigial gravity simulation) — `src/vestigial/`, `VestigialGravity.lean`, `VestigialSusceptibility.lean`
- Phase 4 Wave 2–3 (Fracton hydrodynamics) — `src/fracton/`, `FractonHydro.lean`, `FractonFormulas.lean`, `FractonGravity.lean`
- Phase 5 Wave 9C-3 (Wetterich NJL fermion-bag MC) — `WetterichNJL.lean`, `src/vestigial/wetterich_model.py`
- Phase 5d (TetradGapEquation) — `TetradGapEquation.lean`, `src/adw/tetrad_gap_solver.py`
- Phase 5f (EmergentGravityBounds) — `EmergentGravityBounds.lean`

**Parallel phase:**
- Phase 5x (dark-sector EFT-level exploration, architecture-neutral) — complementary bracket; no narrative consistency required.

**Prior deep research corpus:**
- Round 1: wf-46ace029 (Apr 2026) — Volovik 2024–2026 landscape, DESI DR2 context, fracton-vortex mapping, MICROSCOPE bound
- Round 1.5: wf-e02518ef (Apr 2026) — biographical context + q-theory centrality surfacing, T=H/π controversy flagged
- Round 0.5: Nemotron consultation (Oct 2025) — original 5y scoping, subsequently restructured

---

*Phase 5y roadmap. Created 2026-04-22. Roadmap structure follows [Phase 5s template](https://github.com/NetRxn/SK_EFT_Hawking/blob/main/docs/roadmaps/Phase5s_Roadmap.md). All waves follow [Wave Execution Pipeline](https://github.com/NetRxn/SK_EFT_Hawking/blob/main/docs/WAVE_EXECUTION_PIPELINE.md). Deep research prompts pending filing in `Lit-Search/Tasks/`. External engagement track active per Nobel-territory ambition analysis.*
