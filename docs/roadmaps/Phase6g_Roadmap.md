# Phase 6g: Global / Nonperturbative GR — Causal Structure, Singularity Theorems, Area Theorem, Cauchy Problem, No-Hair

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §10. Classical GR theorems not derivable from condensate side but required to discuss singularity resolution, cosmic censorship, BH uniqueness. Formalized as classical-GR theorems; condensate provides UV completion where these break down.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. All 6g waves depend on Phase 6f infrastructure; 6g.2 / 6g.4 additionally depend on Phase 6e.4 `T_μν^emerg` for NEC input.

**Thesis.** Six waves of classical-GR global / nonperturbative theorems: causal structure, Penrose singularity, Hawking-Penrose singularity, Hawking area theorem, Cauchy problem well-posedness (Fourès-Bruhat), no-hair theorem. **Heaviest Mathlib-dependent phase in the entire post-SK-EFT program.** Budget 39–65 PM Lean. The correctness-push output is the NEC-on-ADW-`T_μν^emerg` check through 6f.3 + 6g.2 — determines whether ADW produces classical singularities.

**Correctness-push framing.** 6g.2 (Penrose singularity) is the correctness-push anchor. Combined with 6f.3's NEC-check on `T_μν^emerg`, this either proves ADW produces classical singularities (requiring UV-completion claim) or proves it doesn't (NEC violated) — either outcome is a clean conclusion.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §10 (6g), §9 (6f — prerequisite), §8 (6e — 6e.4 `T_μν^emerg` input)
> 4. Wave-specific pre-reads:
>    - 6g.1 — Phase 6f.4 (exact solutions), 6f.5 (ADM); Wald GR Chapter 8 (causal structure), Hawking-Ellis 1973 (*Large Scale Structure of Spacetime* chapter 6)
>    - 6g.2 — 6f.3 (NEC), 6g.1, trapped-surface definitions; Penrose 1965 (original paper), Senovilla-Garfinkle 2015 review
>    - 6g.3 — 6g.2, SEC; Hawking-Penrose 1970
>    - 6g.4 — 6a.5 (BH thermodynamics 2nd law), 6f.3 (NEC), 6g.1; Hawking 1971 area-theorem paper
>    - 6g.5 — 6f.5 (ADM), LeanMillenniumPrizeProblems PDE framework; Fourès-Bruhat 1952 + Bruhat 1969 + Choquet-Bruhat textbook
>    - 6g.6 — 6g.1, 6g.4, 6f.4 (Kerr); Mazur / Bunting / Israel uniqueness literature
> 5. **Mathlib is the primary dependency risk.** 6g requires PDE + differential-geometry + global-analysis machinery at levels not yet present. Coordinate with Mathlib community early. Drop deep-research prompt `Lit-Search/Tasks/Phase6g_mathlib_global_gr_audit.md` before Wave 1.
> 6. User authorization required before every 6g wave — this is the heaviest Mathlib-dependent phase. Do not start 6g.5 without explicit LMPP coordination confirmation.
> 7. **MANDATORY: Apply the preemptive-strengthening checklist before writing each Lean theorem statement** (see CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist). Five questions: (1) drop-conjunct test for bundle redundancy P2; (2) numerical-content connection (`norm_num`-backed comparisons to published constants); (3) cross-module bridge integrity P6 (docstring references → `import + call`); (4) trivial-discharge P3/P4/P5 check (no `rfl`/`decide`/`not_lt.mpr h_disagree` tautologies); (5) defining-the-conclusion check (vacuous when `f := <obvious target>`). The end-of-wave strengthening pass should produce **0 retroactive theorems** — if it produces 5+, log the failure mode and tighten the next wave's discipline.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6g:**
- Global hyperbolicity, Cauchy surfaces, causal future/past, strong / stable causality
- Penrose singularity theorem (NEC + trapped surface + global hyperbolicity → geodesic incompleteness)
- Hawking-Penrose singularity theorem (SEC-based, covers cosmological + gravitational-collapse)
- Area theorem (Hawking 1971): classical `dA ≥ 0` under NEC + cosmic censorship
- Cauchy problem well-posedness (Fourès-Bruhat) via harmonic coordinates / Bel-Robinson energy
- No-hair theorem: vacuum stationary axisymmetric BH uniqueness

**OUT OF SCOPE for 6g (backlog per strategy doc §14):**
- Cosmic censorship conjecture itself — condensate UV-completes near singularities, not derivable from condensate side; may become 6g.7 long-term
- Dynamical / non-stationary BH theorems beyond 6g.6 — extension of 6g
- Gravitational collapse / numerical relativity — simulation, not formalization
- Non-vacuum no-hair (charged / rotating + matter) — 6g.6 covers vacuum only

**Strategic reminder:** 6g is classical-GR-side; ADW condensate UV-completes near singularities, it doesn't resolve them at the classical level. 6g.2 + 6f.3 NEC check is the bridge — determines the regime where classical GR applies.

---

## Track A: Causal Structure (6g.1)

### Wave 1 — `CausalStructure.lean` (6g.1) [Pipeline: Stages 1–8]

**Goal:** Global hyperbolicity, Cauchy surfaces, causal future/past, strong / stable causality.

**Prerequisites:** Phase 6f.4 (`ExactSolutions.lean`), 6f.5 (`ADMFormalism.lean`) substantially complete. User authorization.

**Module structure:**
- `lean/SKEFTHawking/CausalStructure.lean`
  - Causal future `J^+(p)`, causal past `J^-(p)`
  - Chronological future `I^+(p)`, chronological past
  - Causal curves, timelike curves, null curves
  - Global hyperbolicity predicate: `∀ p q, J^+(p) ∩ J^-(q) is compact`
  - Cauchy surface definition; uniqueness modulo equivalence
  - Strong causality: no closed causal curves + no almost-closed ones
  - Stable causality: Lorentzian metric admits time function
  - Specializations: Minkowski, Schwarzschild (modulo r=2M), Kerr (complications flagged), de Sitter
- Target ~14–18 theorems.

**Python side:**
- `src/global_gr/causal_structure.py` — causal-structure numerical check on representative solutions

**Bridges:**
- Depends on 6f.1, 6f.4, 6f.5
- Feeds 6g.2, 6g.3, 6g.4, 6g.5, 6g.6 (all downstream 6g waves)

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_causal_structure.py`
- **Mathlib PR:** Causal-structure infrastructure (possibly combined with 6g.2/6g.3)
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Causal-structure theory is mathematically heavy; Mathlib coverage likely thin.

---

## Track B: Singularity Theorems (6g.2, 6g.3)

### Wave 2 — `PenroseSingularity.lean` (6g.2) [Pipeline: Stages 1–12]

**Goal:** Penrose 1965: NEC + trapped surface + global hyperbolicity ⇒ geodesic incompleteness. **Correctness-push anchor.**

**Prerequisites:** 6f.3 (`EnergyConditions.lean`), 6g.1 (`CausalStructure.lean`) complete. User authorization (correctness-push wave).

**Module structure:**
- `lean/SKEFTHawking/PenroseSingularity.lean`
  - Trapped surface definition: closed 2-surface with both null-congruence expansions negative
  - Raychaudhuri equation + expansion focusing under NEC
  - Geodesic incompleteness predicate
  - Penrose theorem: `NEC ∧ trapped_surface ∧ global_hyperbolic ⇒ geodesic_incomplete`
  - **Correctness-push theorem:** `ADW_produces_classical_singularities_iff_NEC_holds_on_T_emerg` — combined with 6f.3 NEC check. Either ADW → classical singularities (UV-completion claim enters) OR NEC violated (no singularity in that regime; DE-supportive).
  - Applications to Schwarzschild interior, Kerr inner horizon, FLRW big bang
- Target ~18–22 theorems.

**Python side:**
- `src/global_gr/penrose_singularity.py` — trapped-surface check on representative spacetimes; NEC numerical check on `T_μν^emerg` when available

**Bridges:**
- Depends on 6f.3, 6g.1
- Cross-references 6e.4 (`T_μν^emerg` for NEC input)
- Feeds 6g.3, 6g.4

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_penrose_singularity.py`
- Paper `papers/paper44_penrose_singularity/paper_draft.tex`
- **Mathlib PR:** Penrose singularity theorem (major PR candidate)
- Inventory update: +18–22 theorems, +1 Lean module, +1 Python script, +1 paper

**Estimated LOE:** 6–10 person-months
**Risk:** High. Raychaudhuri + focusing theorem require heavy differential-geometry machinery. Mathlib dependency is significant.

**Correctness-push highlight.** NEC-on-`T_μν^emerg` (from 6f.3 + 6e.4) combined with Penrose → determines classical-singularity status of ADW. Headline result of 6g.

### Wave 3 — `HawkingPenroseSingularity.lean` (6g.3) [Pipeline: Stages 1–8]

**Goal:** Hawking-Penrose 1970 singularity theorem — SEC-based, covers cosmological + gravitational-collapse.

**Prerequisites:** 6f.3 (`EnergyConditions.lean` — SEC), 6g.2 (`PenroseSingularity`) complete.

**Module structure:**
- `lean/SKEFTHawking/HawkingPenroseSingularity.lean`
  - SEC-based focusing theorem
  - Hawking-Penrose theorem: SEC + generic condition + ... ⇒ geodesic incompleteness
  - Cosmological singularity application (big bang)
  - Black-hole formation application
  - Comparison / contrast with Penrose (when each applies)
- Target ~16–20 theorems.

**Python side:**
- `src/global_gr/hawking_penrose.py` — SEC check on representative spacetimes

**Bridges:**
- Depends on 6f.3, 6g.2
- Feeds 6g.4

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_hawking_penrose.py`
- **Mathlib PR:** Hawking-Penrose (possibly bundled with 6g.2)
- Inventory update: +16–20 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 6–10 person-months
**Risk:** High. Similar technical depth to 6g.2.

---

## Track C: Area Theorem (6g.4)

### Wave 4 — `AreaTheorem.lean` (6g.4) [Pipeline: Stages 1–8]

**Goal:** Hawking 1971 classical area theorem `dA ≥ 0` under NEC + cosmic censorship. Complements 6a.5 thermodynamic 2nd law.

**Prerequisites:** 6a.5 (`BHThermodynamicsFourLaws`), 6f.3 (`EnergyConditions`), 6g.1 (`CausalStructure`).

**Module structure:**
- `lean/SKEFTHawking/AreaTheorem.lean`
  - Event horizon definition (requires asymptotic flatness + causal structure)
  - Area monotonicity: null-generator expansion bound under NEC
  - Classical area theorem: `dA/dt ≥ 0` under NEC + cosmic censorship hypothesis (tracked Prop)
  - Bridge to 6a.5 thermodynamic 2nd law (derivation vs statement)
  - **Cross-reference theorem:** `area_theorem_classical_matches_6a5_thermodynamic` — consistency between classical (6g.4) and emergent-thermodynamic (6a.5) 2nd laws
- Target ~10–14 theorems.

**Python side:**
- `src/global_gr/area_theorem.py` — area monotonicity check on representative BH solutions

**Bridges:**
- Depends on 6a.5, 6f.3, 6g.1
- Feeds 6g.6 (no-hair uses area arguments)

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_area_theorem.py`
- **Mathlib PR:** Area theorem
- Inventory update: +10–14 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium.

---

## Track D: Cauchy Problem (6g.5)

### Wave 5 — `CauchyProblem.lean` (6g.5) [Pipeline: Stages 1–12]

**Goal:** Einstein equations admit well-posed IVP in harmonic coordinates (Fourès-Bruhat 1952) or via Bel-Robinson energy. Requires PDE infrastructure Mathlib currently lacks. **Heaviest single wave in Phase 6g.**

**Prerequisites:** 6f.5 (`ADMFormalism`) complete. LeanMillenniumPrizeProblems PDE weak-solution framework coordinated. User authorization (heaviest 6g wave).

**Module structure:**
- `lean/SKEFTHawking/CauchyProblem.lean`
  - Harmonic gauge: `□ x^μ = 0`
  - Reduced Einstein equations in harmonic coords: quasilinear hyperbolic system
  - Existence theorem: initial data satisfying ADM constraints → local-in-time solution
  - Uniqueness theorem: two solutions from same data differ by gauge only
  - Cauchy stability / well-posedness: continuous dependence on data
  - (Global existence is much harder; flagged as 6g.7 backlog if pursued)
- Target ~20–28 theorems.

**Python side:**
- `src/global_gr/cauchy_problem.py` — numerical IVP on representative initial data; structural sanity only

**Bridges:**
- Depends on 6f.5
- Depends heavily on LeanMillenniumPrizeProblems
- Feeds 6g.6 (uniqueness arguments)

**Deliverables:**
- Module zero-sorry, building clean (aspirational)
- `tests/test_cauchy_problem.py`
- Paper `papers/paper45_cauchy_problem/paper_draft.tex` — substantial (PRD / Annals / foundations journal)
- **Mathlib PR sequence:** multiple PRs for prerequisite PDE infrastructure; coordinated
- Inventory update: +20–28 theorems, +1 Lean module, +1 Python script, +1 paper

**Estimated LOE:** 15–25 person-months
**Risk:** Very high. Mathlib PDE framework may require Wave 5 itself to build prerequisites. If LMPP not usable, scope is reduced to structural Prop-level statements.

---

## Track E: No-Hair (6g.6)

### Wave 6 — `NoHairTheorem.lean` (6g.6) [Pipeline: Stages 1–8]

**Goal:** Classical no-hair for vacuum stationary axisymmetric BH solutions.

**Prerequisites:** 6f.4 (`ExactSolutions.lean` — Kerr), 6g.1 (`CausalStructure`), 6g.4 (`AreaTheorem`).

**Module structure:**
- `lean/SKEFTHawking/NoHairTheorem.lean`
  - Stationary axisymmetric vacuum BH class
  - No-hair theorem: vacuum stationary axisymmetric BH = Kerr family
  - Mazur / Bunting / Israel proof structure
  - Specializations: `J = 0 → Schwarzschild`, `J ≠ 0 → Kerr`
- Target ~12–16 theorems.

**Python side:**
- `src/global_gr/no_hair.py` — Kerr-family parameter check on representative solutions

**Bridges:**
- Depends on 6f.4, 6g.1, 6g.4
- Cross-references existing `KerrSchild.lean`

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_no_hair.py`
- Paper (optional — may bundle with 6g.2/6g.3 into single 6g-closure paper)
- **Mathlib PR:** No-hair theorem
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 6–10 person-months
**Risk:** High.

---

## Decision Gates

**Gate G.1 — before Wave 1 begins:** Mathlib global-analysis + differential-geometry audit complete? 6f.4, 6f.5 substantially complete? User authorization. Gate determines whether 6g is a go-ahead or a deferred-priority.

**Gate G.2 — before Wave 2 (`PenroseSingularity`) begins:** User authorization (correctness-push wave; significant LOE).

**Gate G.3 — after Waves 2 + 3 ship:** Does NEC-on-`T_μν^emerg` (from 6f.3 + 6e.4) resolve? Document result; if YES → ADW produces classical singularities, UV-completion claim activates; if NO (NEC violated) → ADW permits NEC-violating regime, DE support without exotic matter supported.

**Gate G.4 — before Wave 5 (`CauchyProblem`) begins:** LMPP PDE framework confirmed usable? Mathlib PDE infrastructure audit shows feasibility? User explicit authorization — this is the heaviest 6g wave. If LMPP unusable, scope to structural Prop-level statements only (reduces LOE to 5–10 PM).

**Gate G.5 — after all 6g waves ship (or de-scoped):** 6g closure paper bundling 6g.2 + 6g.3 + 6g.4 + 6g.6 into a single "Classical Singularity Theorems + No-Hair in Lean" paper? User decision.

---

## Dependencies

```
6g.1 (CausalStructure) — depends on 6f.4, 6f.5
  ↓
6g.2 (PenroseSingularity) — depends on 6f.3, 6g.1 + user gate
  ↓
6g.3 (HawkingPenroseSingularity) — depends on 6f.3, 6g.2

6g.4 (AreaTheorem) — depends on 6a.5, 6f.3, 6g.1
  — parallel with 6g.3

6g.5 (CauchyProblem) — depends on 6f.5 + LMPP + user gate
  — parallel with 6g.3, 6g.4

6g.6 (NoHairTheorem) — depends on 6f.4, 6g.1, 6g.4
  — serial after 6g.4

Parallelism:
  6g.3, 6g.4, 6g.5 all parallel after 6g.2
  6g.6 after 6g.4
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6g.1 | `CausalStructure.lean` + Mathlib PR | 3–5 | 6f.4, 6f.5 + user gate | **TIER 0 — foundational** |
| 6g.2 | `PenroseSingularity.lean` + paper + Mathlib PR | 6–10 | 6f.3, 6g.1 + user gate | **TIER 0 — correctness-push** |
| 6g.3 | `HawkingPenroseSingularity.lean` + Mathlib PR | 6–10 | 6f.3, 6g.2 | **TIER 1** |
| 6g.4 | `AreaTheorem.lean` + Mathlib PR | 3–5 | 6a.5, 6f.3, 6g.1 | **TIER 1** |
| 6g.5 | `CauchyProblem.lean` + paper + Mathlib PR sequence | 15–25 | 6f.5 + LMPP + user gate | **TIER 2 — heaviest** |
| 6g.6 | `NoHairTheorem.lean` + Mathlib PR | 6–10 | 6f.4, 6g.1, 6g.4 | **TIER 1** |

**Total Phase 6g LOE:** 39–65 person-months. Limited parallelism after 6g.2: wall-clock 24–40 months minimum. The heaviest Mathlib-dependent phase.

**Deliverables cumulative:**
- 6 new Lean modules
- 6 new Python scripts (validation only)
- 2 papers (6g.2 Penrose + 6g.5 Cauchy; 6g.3/6g.4/6g.6 potentially bundled)
- ~86–120 new theorems; zero sorry target
- Multiple Mathlib PRs — major classical-GR community contribution

---

## Open Questions

**O.1 — LOAD-BEARING.** Mathlib global-analysis + differential-geometry audit: what's usable? What needs fresh? Drop deep-research prompt before Wave 1.

**O.2 — LOAD-BEARING.** LeanMillenniumPrizeProblems PDE framework: usable directly for 6g.5, or needs Einstein-specific additions? If the latter, Wave 5 includes LMPP-coordination as a sub-track.

**O.3** — 6g closure paper strategy: one paper per wave, or single "6g closure" paper bundling 6g.2–6g.6? User decision at Stage 12.

**O.4** — Cosmic censorship conjecture (strategy doc §14 backlog): if pursued, becomes 6g.7. Not scheduled as wave; revisit after 6g core waves.

**O.5** — 6g.6 scope: vacuum only or include charged extensions? Default vacuum; charged as 6g.6-extension if bandwidth permits.

---

## What Success Looks Like

**Per wave:**
- 6g.1: Causal-structure machinery; Mathlib contribution; foundation for all downstream 6g
- 6g.2: Penrose singularity formal; NEC-on-ADW check activated (correctness-push answer)
- 6g.3: Hawking-Penrose singularity formal; cosmological + BH cases covered
- 6g.4: Classical area theorem; consistency with 6a.5 thermodynamic 2nd law
- 6g.5: Cauchy problem well-posedness formalized; Mathlib PDE infrastructure built
- 6g.6: No-hair theorem for vacuum stationary axisymmetric BHs

**Cumulative:**
- 6 new Lean modules, Mathlib PRs (major)
- 2–6 papers depending on bundling strategy
- ~86–120 new theorems, zero sorry target (aspirational for 6g.5)
- Correctness-push anchor: ADW produces classical singularities iff NEC on `T_μν^emerg` (resolved through 6f.3 + 6e.4 + 6g.2)
- **Program-level value:** classical GR backbone machine-checked; ADW UV-completion positioning concrete

---

## Cross-References

**Prior phases this extends:**
- Phase 5 (Paper 5 KerrSchild) — `KerrSchild.lean` extension
- Phase 3/5d (tetrad infrastructure) — conventions
- Phase 6a.5 (BH thermodynamics 2nd law) — feeds into 6g.4
- Phase 6e.4 (`T_μν^emerg`) — NEC input via 6f.3

**Depends on:**
- Phase 6f (all waves) — foundational
- Phase 6a.5 — for 6g.4
- Phase 6e.4 — for 6f.3 NEC check that activates 6g.2 correctness-push

**Feeds downstream:**
- 6g.7 cosmic censorship (backlog, long-term)
- Mathlib community — major classical-GR PR contributions

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §10

**Correctness-push highlights from strategy doc §12:**
- 6f.3 + 6g.2: NEC for `T_μν^emerg` — determines classical-singularity status of ADW

---

*Phase 6g roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Six waves of global / nonperturbative GR: causal structure, Penrose + Hawking-Penrose singularities, area theorem, Cauchy problem, no-hair. Heaviest Mathlib-dependent phase. Correctness-push anchor at 6f.3 + 6g.2. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 39–65. User authorization required before every wave.*
