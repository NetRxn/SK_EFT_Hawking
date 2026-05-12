# Phase 6p: Fault-Tolerant Quantum Computation on the Topological Substrate (G5 AGP + FKLW)

## Technical Roadmap — May 2026

*Prepared 2026-05-12 at Phase 6o close. Sources: planning conversation 2026-05-12 (4-phase scoping pass); user direction "find good fits for our pipeline & investigate directions that may lead to strengthening of the program and investigations that could plausibly make significant contributions to the physics/math/qc communities, and/or contribute meaningful no-gos"; `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` (existing) §G5 surfacing AGP + FKLW as the natural "industrial reach" extension of D4's topological substrate.*

**Trigger condition:** Phase 6p opens at Phase 6o close (2026-05-08 Wave 4a SHIPPED; 14/14 bundles green; first-claim language scrubbed 2026-05-12). Phase 6p consumes Phase 5c/5i/5p categorical chain + Phase 6n Wave 1b SymTFT audit as substrates: paper11 (`Uqsl2`, `Uqsl3`, generic `Uqg`), paper14 (Ising + Fibonacci MTC + Müger center + decidable number-field arithmetic), paper16_wrt_tqft (Temperley-Lieb + Jones-Wenzl + Kirby moves + WRT formula + Fibonacci universality), and the broader SymTFTAudit/DrinfeldCenter/PseudoUnitary/WittClass stack.

**Status (2026-05-12, Phase 6p stub):** **Roadmap stub committed at Track / Wave level**. Three Tracks, six Waves. Convention matches Phase 6n/6o.

**Project rule (carried from Phase 6n/6o; user direction reaffirmed 2026-05-12):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** — Phase 6p stays at math/physics/Lean-substrate / infrastructure level; notes/outlines/working docs are fine. **No Mathlib PR drafts at this phase** — anything that might end up upstream is built internally first, using Mathlib naming/style conventions to make future PRs easier when authorized.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list. Read in order: WAVE_EXECUTION_PIPELINE → Inventory_Index → README → Lean Development Optimization → Aristotle reference doc.
> 2. **Read `Phase6n_Roadmap.md` + `Phase6o_Roadmap.md` end-to-end** before starting any Phase 6p work — both contain substrate Phase 6p consumes.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the planning brief `memory/project_phase_6p6q6r6s_planning.md`** for entry-state context on why these four phases were scoped together.
> 5. **Critical predecessor modules — read source directly:**
>    - **D4 substrate (heaviest dependency):** `lean/SKEFTHawking/Uqsl2/*.lean` (paper11; ~66 thms quantum group $U_q(\mathfrak{sl}_2)$), `lean/SKEFTHawking/Uqsl3/*.lean` (paper11 rank-2), `lean/SKEFTHawking/Uqg/*.lean` (paper11 generic), `lean/SKEFTHawking/MTCInstance/SU2k*.lean` + `lean/SKEFTHawking/MTCInstance/Fibonacci*.lean` (paper14 Ising + Fibonacci MTCs with F-symbols, hexagon, ribbon), `lean/SKEFTHawking/TemperleyLieb/*.lean` (paper14 Temperley-Lieb algebra), `lean/SKEFTHawking/JonesWenzl/*.lean` (paper14 Jones-Wenzl idempotents), `lean/SKEFTHawking/Surgery/*.lean` + `lean/SKEFTHawking/KirbyMoves/*.lean` (paper16_wrt_tqft surgery presentations), `lean/SKEFTHawking/WRTInvariant/*.lean` (paper16_wrt_tqft WRT formula), `lean/SKEFTHawking/FibonacciQutritUniversality.lean` (paper14 Fibonacci universality — direct AGP-adjacent substrate).
>    - **Categorical SymTFT substrate:** `lean/SKEFTHawking/SymTFTAudit/*.lean` (DrinfeldCenter, PseudoUnitary, FreeKLinearCategory, FreeKLinearMonoidal, DeligneTensor, WittClass, CrossBridges, Applicability).
>    - **Decidable number-field arithmetic:** `lean/SKEFTHawking/DecidableNumberField/*.lean` (paper14 `QSqrt2`, `QSqrt5`, `QZeta5`, `QZeta16`) — substrate for FKLW exact arithmetic if pursued at non-trivial number-field level.
>    - Mathlib4 quantum-information infrastructure (if any) + PhysLean quantum-circuit substrate (`PhysLean.Mathematics.QuantumCircuit` if present at scout time).
> 6. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.** Each Phase 6p wave's bundle absorption is pre-classified below as D.2 / D.3 / D.4 per the protocol's branch decision matrix.
> 7. **Apply preemptive-strengthening checklist** per `WAVE_EXECUTION_PIPELINE.md` Stage 3a + the five questions in `CLAUDE.md` "Preemptive-strengthening discipline" section. **Apply primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md` — default to descriptive content-first prose, NOT "first in any proof assistant" framing.
> 8. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback only after MCP-loop exhaustion + decomposition + user authorization. **Pre-flight Explore-agent dispatch IS authorized for substrate scouting.**
> 9. **No PM / time estimates anywhere** — by user direction.
> 10. **No manuscript drafting at this phase.** Working-doc-grade notes, outlines, and Lean-substrate work only. Bundle absorption (D.2/D.3 events) HELD per Phase 6n Session-5 convention; runs as one coherent pass after Phase 6p math closes.

---

## Wave catalog — Shape D (3 Tracks × 6 Waves; matches Phase 6n/6o format)

Six waves across three Tracks. Track 1 = AGP threshold theorem (2 waves; substrate + theorem). Track 2 = FKLW Fibonacci-anyon density (2 waves; algebraic universality + density). Track 3 = applications + cross-bridges (2 waves; concrete fault-tolerant gate compilation + cross-bridge to D4 / new-bundle decision).

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred per Phase 6p convention.
- 🟡 **IN-PROGRESS** — partial deliverables shipped; remaining sub-stages identified.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — AGP threshold theorem** | | | | | |
| **Wave 1a** | AGP substrate analysis + threshold-theorem predicate scaffolding | ⏳ NOT STARTED | TBD (D4 extension OR new bundle) — DEFERRED | **D.2 / D.4 candidate** | none |
| **Wave 1b** | AGP concatenated distance-3 threshold theorem (closed-form rigorous) | ⏳ NOT STARTED | TBD — DEFERRED | **D.2 / D.4 candidate** | none |
| **Track 2 — FKLW Fibonacci-anyon density** | | | | | |
| **Wave 2a** | Fibonacci-anyon density substrate analysis + Lie-algebra-spanning predicate scaffolding | ⏳ NOT STARTED | D4 extension — DEFERRED | **D.2** | none |
| **Wave 2b** | FKLW density theorem (dense braid subgroup of SU(2) via Fibonacci anyons) | ⏳ NOT STARTED | D4 extension — DEFERRED | **D.2** | none |
| **Track 3 — Applications + cross-bridges** | | | | | |
| **Wave 3a** | Concrete fault-tolerant gate compilation on Fibonacci MTC substrate (Solovay-Kitaev-flavored) | ⏳ NOT STARTED | D4 + possible new bundle — DEFERRED | **D.2 / D.4 candidate** | none |
| **Wave 3b** | Cross-bridge to D4 / new-bundle decision + flagship-F positioning | ⏳ NOT STARTED | D4 (refines + extends) + F flagship (positioning paragraph) — DEFERRED | **D.2** | possibly **YES** (new-bundle creation if decision is to spin off) |

**Wave dependencies:**
- Wave 1a (AGP substrate) and Wave 2a (FKLW substrate) are independent — can run in parallel.
- Wave 1b depends on Wave 1a (threshold theorem builds on threshold-predicate scaffolding).
- Wave 2b depends on Wave 2a (density theorem builds on Lie-algebra-spanning predicate); paper14's existing `FibonacciQutritUniversality.lean` already establishes the density argument for the qutrit case — Wave 2b lifts to the general FKLW statement.
- Wave 3a depends on Waves 2a-2b (gate compilation needs the density theorem operational).
- Wave 3b depends on all prior waves (cross-bridge / positioning decisions need the content shipped).

**Coherent sub-narrative.** The two tracks form a "fault-tolerant QC complete-stack" deliverable on the program's existing topological substrate. AGP threshold theorem says: *if* physical errors are below a threshold, arbitrarily long quantum computation is possible by concatenating error-correcting codes. FKLW density says: Fibonacci anyons can approximate any unitary to arbitrary precision via braiding. Together they give the **algebraic stack** for topologically-protected fault-tolerant universal quantum computation — directly readable as "what the program's MTC infrastructure enables, in QC terms."

**Recommended next-up order:**

1. **Wave 1a** AGP substrate analysis (substrate scout to determine threshold-theorem flavor most tractable in Lean — physical-CSS-code-flavor with explicit threshold p_th, or concatenated-distance-3-flavor closed-form proof; latter is what the planning conversation surfaced as the cleaner Lean target).
2. **Wave 2a** Fibonacci-anyon density substrate analysis (in parallel — substrate scout on whether to leverage `FibonacciQutritUniversality.lean` directly or rebuild for arbitrary qudit case).
3. **Wave 1b** AGP threshold theorem (after 1a substrate analysis identifies the cleanest theorem statement).
4. **Wave 2b** FKLW density theorem (after 2a substrate analysis).
5. **Wave 3a** concrete fault-tolerant gate compilation (after both density + threshold theorems shipped).
6. **Wave 3b** cross-bridge + new-bundle decision (closing positioning).

**Pre-Phase-7 bundle absorption gate:** all 6 Phase 6p Waves close → unified Phase 6p → Phase 7 absorption pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`. New-bundle creation decision (D4 extension vs. spin-off bundle) at Wave 3b close.

---

## Wave 1a — AGP substrate analysis + threshold-theorem predicate scaffolding ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1a.1 (deep-research dispatch):** Phase 6n-style DR task at `Lit-Search/Tasks/submitted/<date>_AGP_threshold_formalization_state.md` covering: (a) prior Lean / Coq / Isabelle / HOL Light formalizations of the AGP threshold theorem (Aharonov-Ben-Or 1997 STOC + 2008 quant-ph/9906129); (b) state-of-the-art simplifications since Knill-Laflamme-Zurek 1998 + Aliferis-Gottesman-Preskill 2006 quant-ph/0504218; (c) which concatenation distance (d=3 vs d=5 vs d=7) admits the cleanest closed-form threshold (the planning conversation flagged d=3 concatenation as the tractable target); (d) the relationship between AGP threshold and the program's existing MTC substrate (is the threshold theorem topologically-substrate-agnostic, or does it specialize to the Fibonacci-anyon braiding model?). Working doc at `temporary/working-docs/phase6p/wave_1a_AGP_substrate.md`.
- **Wave 1a.2 (Lean threshold-theorem predicate substrate):** `lean/SKEFTHawking/FaultTolerance/Threshold.lean` — `IsBelowThreshold p` Prop on physical error rate; `ConcatenatedCode d` data structure on concatenation depth; `AGPThresholdTheorem` statement template. Predicate-substrate level (`IsBelowThreshold p := p < p_th` for an abstract threshold; substantive structural content in `AGPThresholdTheorem` form). Cross-bridge stub to existing `SKEFTHawking/MTCInstance/*.lean` for the topological-protection case.
- **Wave 1a.3 (Lean error-model substrate):** `lean/SKEFTHawking/FaultTolerance/ErrorModel.lean` — stochastic-error-model data structure; `IsLocalStochasticError ε p` Prop ("each gate fails independently with probability ≤ p"); cross-bridge to Phase 6n Wave 2c Crooks-on-analog-Hawking quantum trajectory infrastructure (if appropriate; substrate scout decides at Wave 1a.1).
- **Wave 1a.4 (cross-prover-survey discipline check):** Apply primacy-claim discipline per `project_2026_05_12_first_claim_close.md` — DO NOT default to "first AGP threshold theorem formalization" framing. The deep-research dispatch (Wave 1a.1) will surface prior formalizations if they exist; the working doc records what was searched and what was found, framed as "Relation to existing libraries" not "Novelty claim."

**Three-question template:**

- *Integrates with:* Phase 5c/5i/5p categorical chain (paper11 + paper14 + paper16_wrt_tqft); Phase 6n Wave 1b SymTFT audit (`WittClass.lean`, `Applicability.lean`); existing `FibonacciQutritUniversality.lean`; Mathlib4 probability infrastructure (martingales / concentration inequalities — substrate for error-model bounds); Aliferis-Gottesman-Preskill quant-ph/0504218 (the standard cleanest threshold proof in the literature); PhysLean quantum-circuit substrate if present.
- *New constraint adds:* an explicit Lean formalization of the AGP threshold theorem on (a) abstract stochastic error model + (b) topological substrate model. Could be the first such formalization at non-trivial concatenation depth — but framing follows primacy-claim discipline (no "first" claim asserted without explicit cross-prover survey).
- *Tension surfaces:* (i) whether the AGP threshold theorem at d=3 admits a closed-form proof tractable in Lean without Mathlib infrastructure not currently present (Mathlib has concentration inequalities + martingale convergence, but doesn't have the full ICM-style noise-channel calculus); (ii) whether the topological-substrate specialization (Fibonacci anyons + braiding) admits cleaner threshold theorem (substantive question — the planning conversation noted threshold theorems for topological codes are sometimes cleaner than for arbitrary CSS codes); (iii) the cross-bridge to AGP via braiding-model error-correction is a sub-question that may itself surface a structural result.

**Substrate.** Aharonov-Ben-Or 1997/2008 threshold theorem; Aliferis-Gottesman-Preskill 2006 concatenated-distance-3 simplification; Mathlib4 probability theory + concentration inequalities; PhysLean quantum-circuit substrate if present at scout time.

**Module decomposition (Lean):**
```
SKEFTHawking/FaultTolerance/
  Threshold.lean            -- IsBelowThreshold, AGPThresholdTheorem statement template
  ErrorModel.lean           -- IsLocalStochasticError, stochastic-error-model data structure
  -- (Wave 1b will add:)
  -- ConcatenatedCode.lean  -- Distance-3 concatenation data structure
  -- AGP_Theorem.lean       -- The threshold theorem itself (substantive content)
```

**Bundle absorption.** D.2 / D.4 candidate; new bundle vs. D4 extension decision deferred to Wave 3b close. Substrate-data level for now.

**Risk axes.**
- Mathlib quantum-information infrastructure may be too thin to support the full AGP threshold theorem in Lean — in which case Wave 1b ships a "predicate-substrate operationalization" rather than substantive content (similar to I3's choice for Itô calculus).
- The "topological substrate" specialization may not be cleaner than the abstract CSS-code statement — substrate scout at Wave 1a.1 dispositive.
- AGP threshold theorem prior-art survey: there may already be a Lean formalization in PhysLean (low probability per current PhysLean roadmap) or a Coq formalization (medium probability per QuantumLib state). DR dispatch will surface this.

---

## Wave 1b — AGP concatenated distance-3 threshold theorem ⏳ NOT STARTED

**Sub-wave decomposition (proposed; matures after Wave 1a substrate analysis):**

- **Wave 1b.1 (substantive theorem at predicate-substrate level):** `lean/SKEFTHawking/FaultTolerance/ConcatenatedCode.lean` + `lean/SKEFTHawking/FaultTolerance/AGP_Theorem.lean` — distance-3 concatenated code data structure (Steane / Knill flavor; substrate scout at 1a.1 picks one) + the threshold theorem `IsBelowThreshold p → ∃ d (concatenation depth), arbitrarily long computation runs with error < ε`.
- **Wave 1b.2 (concrete witness on Fibonacci-anyon topological code):** substantive instance theorem: the Fibonacci-anyon topological code (via paper14's existing MTC substrate) satisfies the AGP threshold predicate at a specific concatenation depth. Substantive content: produces explicit threshold value.
- **Wave 1b.3 (cross-bridge to FKLW track):** `lean/SKEFTHawking/FaultTolerance/AGP_FKLW_Bridge.lean` — connects the AGP threshold (Track 1) to the FKLW density theorem (Track 2) via the observation that universal fault-tolerant computation requires both: a code with threshold below physical error rate, AND a universal gate set. The cross-bridge is the "complete stack" deliverable.

**Three-question template:**

- *Integrates with:* Wave 1a predicate substrate; Aliferis-Gottesman-Preskill 2006 quant-ph/0504218; paper14 Fibonacci-MTC substrate (cross-bridge); Mathlib martingale / concentration-inequality infrastructure.
- *New constraint adds:* a Lean formalization of the AGP threshold theorem on either abstract stochastic error model or topological substrate model. Framing: substantive content depending on Wave 1a.1 substrate-scout outcome (predicate-substrate operationalization if Mathlib infrastructure inadequate; substantive theorem if Mathlib substrate exists).
- *Tension surfaces:* (i) the substantive-vs-predicate-substrate decision is made at Wave 1a.1 dispositively; (ii) if substantive content is shipped, the natural Mathlib-PR target is a substantial follow-up wave (defer to Phase 6s consolidation); (iii) AGP threshold theorem proofs in the literature often invoke real-analytic content (geometric series, Chernoff bounds) that Mathlib supports — so substantive content may be more accessible than initially scoped.

**Substrate.** Aharonov-Ben-Or 1997/2008 + Aliferis-Gottesman-Preskill 2006; Mathlib4 concentration inequalities + martingale convergence; paper14 Fibonacci-MTC substrate for the concrete-witness instance.

**Bundle absorption.** D.2 additive into D4 (extension of paper14/paper16_wrt_tqft fault-tolerance line) OR new bundle. Decision deferred to Wave 3b close.

**Risk axes.**
- Substantive vs. predicate-substrate level of theorem statement (dispositive at Wave 1a.1).
- Concrete witness on Fibonacci-anyon topological code may surface that the explicit threshold value is harder to compute than the existence claim — in which case Wave 1b.2 ships a non-constructive existence theorem with the explicit value deferred.
- Concatenation depth (d=3 default; d=5 / d=7 alternatives) — picked at Wave 1a.1 substrate scout.

---

## Wave 2a — Fibonacci-anyon density substrate analysis + Lie-algebra-spanning predicate scaffolding ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2a.1 (deep-research dispatch):** DR task on (a) Freedman-Larsen-Wang 2002 quant-ph/0001108 + Freedman-Kitaev-Larsen-Wang 2002 quant-ph/0101025 — the original FKLW density theorem; (b) prior formalizations (likely zero per project's existing `FibonacciQutritUniversality.lean` which only handles the qutrit case); (c) Solovay-Kitaev approximation theorem dependencies (compilation of arbitrary unitaries from a dense gate set); (d) state of Mathlib4 Lie-algebra and density-in-Lie-group infrastructure. Working doc at `temporary/working-docs/phase6p/wave_2a_FKLW_substrate.md`.
- **Wave 2a.2 (Lean predicate substrate):** `lean/SKEFTHawking/FKLW/DensityPredicate.lean` — `IsDenseInSpecialUnitary G n` Prop on a subgroup `G ⊂ SU(n)`; `IsFibonacciBraidingSubgroup B_n n_anyons` Prop on the image of the n-strand braid group under the Fibonacci-anyon R-matrix representation. Predicate-substrate operationalization extending paper14's existing `FibonacciQutritUniversality.lean` from n=3 (qutrit) to arbitrary qudit dimension.
- **Wave 2a.3 (Lie-algebra-spanning substrate):** `lean/SKEFTHawking/FKLW/LieAlgebraSpanning.lean` — `IsLieSpanningSubset S G` Prop on subsets of a Lie algebra; substantive lemma "if the Lie subalgebra generated by braiding-generators of the Fibonacci anyon representation spans $\mathfrak{su}(n)$ for all n, then the braid-image is dense in SU(n)" — the core mechanism by which FKLW density follows from a finite Lie-algebra-spanning check.

**Three-question template:**

- *Integrates with:* paper14 `FibonacciQutritUniversality.lean` (existing qutrit case); paper14 Fibonacci MTC F-symbols + hexagon equations; paper11 quantum group $U_q(\mathfrak{sl}_2)$ at $q = e^{i\pi/5}$ (Fibonacci modular data origin); Mathlib4 Lie algebra infrastructure if present at scout time.
- *New constraint adds:* a Lean formalization of the FKLW Fibonacci-anyon density theorem on arbitrary qudit dimension, extending paper14's qutrit special case. Framing per primacy-claim discipline.
- *Tension surfaces:* (i) Mathlib4 may not ship Lie-algebra-density-in-Lie-group infrastructure — in which case Wave 2b ships predicate-substrate operationalization (with Lie-algebra-spanning hypothesis bundled into the predicate, leaving the substantive density theorem as a downstream-consumer interface deferral); (ii) extending the qutrit case to arbitrary qudit dimension may surface explicit algebraic obstructions (specific n where the spanning property fails) — if so, the wave produces a structural finding (clean characterization of which n admit Fibonacci-anyon universality) rather than the expected universal claim; (iii) the bridge between F-symbols + R-matrices (algebraic substrate) and Lie-algebra-spanning (analytic substrate) is non-trivial in Lean — substrate scout at 2a.1 dispositive.

**Substrate.** Freedman-Larsen-Wang 2002 + Freedman-Kitaev-Larsen-Wang 2002; paper14 `FibonacciQutritUniversality.lean` (existing qutrit case); paper14 Fibonacci MTC infrastructure (F-symbols, hexagon, ribbon); paper11 quantum group $U_q(\mathfrak{sl}_2)$ at $q = e^{i\pi/5}$.

**Bundle absorption.** D.2 additive into D4 (extension of paper14 fault-tolerance / universality line).

**Risk axes.**
- Mathlib4 Lie-algebra-density infrastructure may be inadequate (predicate-substrate operationalization fallback).
- Extension of qutrit case to arbitrary qudit may surface algebraic obstructions (structural finding alternative deliverable).
- Algebraic-to-analytic bridge (F-symbols/R-matrices → Lie-algebra-spanning) is non-trivial.

---

## Wave 2b — FKLW density theorem ⏳ NOT STARTED

**Sub-wave decomposition (proposed; matures after Wave 2a substrate analysis):**

- **Wave 2b.1 (substantive theorem at predicate-substrate level):** `lean/SKEFTHawking/FKLW/DensityTheorem.lean` — the FKLW density theorem statement on the predicate substrate, with substantive proof at level dispositive per Wave 2a.1 outcome.
- **Wave 2b.2 (Solovay-Kitaev compilation):** `lean/SKEFTHawking/FKLW/SolovayKitaev.lean` — substantive lemma: density in SU(n) implies efficient Solovay-Kitaev compilation of any unitary to within ε in time polylog(1/ε). Substrate-data level.
- **Wave 2b.3 (concrete witness on Fibonacci-MTC qudit dimensions):** explicit instance theorem: for specific qudit dimensions (n=4, n=5, n=6 plausible — substrate scout at 2a.1 picks), the Fibonacci-anyon braiding subgroup is dense in SU(n).

**Three-question template:**

- *Integrates with:* Wave 2a substrate; paper14 Fibonacci universality; Mathlib4 Solovay-Kitaev infrastructure if present.
- *New constraint adds:* a Lean formalization of the FKLW density theorem on arbitrary qudit dimension. Substantive vs. predicate-substrate level dispositive at Wave 2a.1.
- *Tension surfaces:* see Wave 2a tension surfaces (same dispositive question on substantive vs. predicate-substrate level).

**Substrate.** Wave 2a substrate; Solovay-Kitaev 1997 quant-ph/9610011; paper14 Fibonacci MTC.

**Bundle absorption.** D.2 additive into D4.

**Risk axes.** Same as Wave 2a.

---

## Wave 3a — Concrete fault-tolerant gate compilation on Fibonacci MTC substrate ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 3a.1 (substrate analysis + working doc):** identify a concrete short gate (Hadamard, T-gate, CNOT) and a concrete Fibonacci-MTC braid encoding the gate. Working doc at `temporary/working-docs/phase6p/wave_3a_gate_compilation_substrate.md`.
- **Wave 3a.2 (Lean explicit gate compilation):** `lean/SKEFTHawking/FaultTolerance/GateCompilation.lean` — explicit Lean theorems: "this specific braid in the Fibonacci MTC computes the Hadamard gate to precision ε in N braid generators." Substantive content: explicit braid-word with verified F-symbol/R-matrix product.
- **Wave 3a.3 (fault-tolerance composition):** combine Wave 3a.2 explicit gate compilations with Wave 1b AGP threshold + Wave 2b FKLW density to produce a "fault-tolerant Hadamard + T-gate + CNEOT" complete substrate. Substantive content: end-to-end fault-tolerant universal-gate-set theorem on the program's existing topological substrate.

**Three-question template:**

- *Integrates with:* Wave 1b AGP threshold; Wave 2b FKLW density; paper14 Fibonacci MTC F-symbols + R-matrices + braiding; paper16_wrt_tqft Temperley-Lieb + Jones-Wenzl + braiding.
- *New constraint adds:* an explicit end-to-end fault-tolerant universal-gate-set theorem on the program's existing topological substrate — a concrete deliverable readable as "the program's MTC infrastructure enables fault-tolerant universal quantum computation, here are the explicit gates and the threshold proof."
- *Tension surfaces:* (i) the explicit braid-words may surface that some standard gates require unexpectedly long braid sequences — interesting structural finding (specifically: the T-gate is famously expensive in Fibonacci universal-gate-set compilations, with the Solovay-Kitaev compiler producing braids of length 30+ for ε ∼ 10^-3); (ii) end-to-end composition with AGP threshold requires the error model on the braid-word level to match the error model assumed by AGP — substrate scout at Wave 3a.1 dispositive.

**Substrate.** Wave 1b + Wave 2b; paper14 Fibonacci MTC; paper16_wrt_tqft Temperley-Lieb + braiding; Solovay-Kitaev compilation; Kitaev-Shen-Vyalyi 2002 quantum computation textbook for the explicit gate-compilation patterns.

**Bundle absorption.** D.2 additive into D4 + possible new bundle (Wave 3b dispositive).

**Risk axes.**
- Explicit braid-word verification may be Mathlib4-heavy — substrate scout at Wave 3a.1 picks tractable subset.
- End-to-end composition requires careful error-model alignment.

---

## Wave 3b — Cross-bridge to D4 / new-bundle decision + flagship-F positioning ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 3b.1 (bundle decision):** working doc at `temporary/working-docs/phase6p/wave_3b_bundle_decision.md` analyzing: (a) does the Phase 6p content fit naturally as an extension of D4 (which already covers topological QC foundations: paper11 + paper14 + paper16_wrt_tqft), or does it warrant a new bundle (working title "D6" or "F2 — Fault-tolerant quantum computation on the topological substrate")? (b) cross-bundle cluster impact — D2 ↔ D4 ↔ L2 currently exact-cluster-bonded on Z₁₆ anomaly + generation constraint; does Phase 6p touch those clusters? Substrate scout dispositive.
- **Wave 3b.2 (flagship-F positioning):** flagship F cross-bridge — short positioning paragraph identifying where Phase 6p sits in the broader emergent-physics-from-substrate narrative. The "topological substrate enables fault-tolerant universal QC" line is a substantive emergent-from-substrate result that the flagship paper should mention; positioning under "what the program's substrate enables, in QC terms" or "applied consequences" section.
- **Wave 3b.3 (bundle architecture update — if new bundle):** if new bundle decision: update `PAPER_STRATEGY.md` + `PAPER_DRAFT_MAPPING.md` + `BUNDLE_DIRECTORY_SCHEMA.md` (if needed) to add the new bundle target; `scripts/sentence_state.py` `_VALID_BUNDLE_TARGETS` accordingly. **User-authorization gate REQUIRED here** — new-bundle creation changes the canonical bundle list and is a strategic-architecture decision.

**Three-question template:**

- *Integrates with:* `PAPER_STRATEGY.md` 14-bundle architecture; `PAPER_DRAFT_MAPPING.md` per-paper assignments; D4 existing structure; F flagship narrative.
- *New constraint adds:* bundle-architecture decision for the Phase 6p content; flagship-F positioning paragraph.
- *Tension surfaces:* (i) D4 extension keeps the bundle list at 14 (clean); new-bundle creation grows the list to 15 (changes downstream tooling assumptions — sentence_state, bundle_readiness, validate.py, bundle_append.py); (ii) the new bundle vs. extension decision depends on substantive scope (if Phase 6p produces "another chapter of D4" the extension is right; if Phase 6p produces a genuinely-distinct deliverable readable independently the new bundle is right); (iii) user-authorization gate is required for new-bundle creation.

**Substrate.** All prior Phase 6p wave deliverables; `PAPER_STRATEGY.md`; `PAPER_DRAFT_MAPPING.md`.

**Bundle absorption.** D.2 into D4 + F flagship positioning; possibly new bundle creation.

**Risk axes.**
- Bundle-architecture decision is strategic; should not be pre-judged.
- Cross-bundle cluster impact analysis needed before changing bundle assignments.

---

## User authorization gates — consolidated

| Wave | Authorization point | Authorization required for | Status |
|---|---|---|---|
| **Wave 1b** AGP threshold theorem | Substantive vs. predicate-substrate level decision | none (decision is implementation-level, not strategic) | n/a |
| **Wave 3b** Bundle decision | New-bundle creation vs. D4 extension | **YES — user-authorization required for new-bundle creation per `PAPER_STRATEGY.md`** | 🔒 **PENDING** Wave 3b.1 close |

---

## Phase 6q+ preview (related deferred tracks)

The following tracks are scoped as Phase 6q (transport bootstrap) / 6r (SymTFT) / 6s (1c bootstrap + I3) per `Phase6{q,r,s}_Roadmap.md` and `memory/project_phase_6p6q6r6s_planning.md`. They are independent of Phase 6p; can run in parallel.

Phase 6p-internal further-deferred tracks:
- **G6c+d Aristotle++ domain-fine-tuned prover** — revisit when current Opus + lean4-plugin + MCP + Aristotle stack capacity is binding (currently it is not).
- **G8 Mathlib AS refactor** — multi-year community coordination; track van Doorn / Rothgang / Tooby-Smith infrastructure progress; consider for Phase 6s consolidation.

---

## Cross-references

- `docs/roadmaps/Phase6n_Roadmap.md` — Phase 6n math substrate (paper11/14/16_wrt_tqft); Wave 1b SymTFT audit substrate.
- `docs/roadmaps/Phase6o_Roadmap.md` — Phase 6o completion (closed 2026-05-08); substrate baseline.
- `docs/roadmaps/Phase6q_Roadmap.md` — sibling phase (DKM transport bootstrap).
- `docs/roadmaps/Phase6r_Roadmap.md` — sibling phase (SymTFT formalization).
- `docs/roadmaps/Phase6s_Roadmap.md` — sibling phase (1c bootstrap + I3 substantive lift).
- `memory/project_phase_6p6q6r6s_planning.md` — strategic entry-state brief.
- `memory/feedback_loe_calibration.md` — pipeline speed calibration.
- `docs/PAPER_STRATEGY.md` — 14-bundle architecture (gets potential extension at Wave 3b).
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle mapping; Phase 6p rows added at Stage 12 close.
- `docs/BUNDLE_LIFT_PROCEDURE.md` — frozen lift workflow (§3d `--bookkeeping-only` mode applies to non-content Phase 6p drift events).
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — D.2 / D.3 / D.4 branches.
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage process.
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list (gets Phase 6p entry when D4 gets extension).
- `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` §G5 — substrate for AGP + FKLW Phase 6p scoping.

---

*Created 2026-05-12 at Phase 6o close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes (matches Phase 6n/6o format). Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6p has not yet been dispatched.*
