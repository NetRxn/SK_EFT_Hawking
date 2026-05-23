# Phase 6t: Quantitative Solovay–Kitaev for Fibonacci Anyons (Dawson–Nielsen Length Bound)

## Technical Roadmap — May 2026

*Prepared retroactively 2026-05-23 PM at Phase 6t close, after Wave 8 D4-bundle close-out (commit `caee77c`). Sources: planning conversation 2026-05-22 AM following the Phase 5 Step 13 Path (i) FINAL ship (F.21 unconditional); working doc `temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md`; `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`; per-wave commit history under `lean/SKEFTHawking/FKLW/`; D4 close-out memory `project_d4_bundle_closed_green_2026_05_23.md`.*

**Trigger condition:** Phase 6t opened immediately after the Phase 6p F.21 unconditional density ship (2026-05-22 PM). With `fibonacci_density_F21_unconditional` shipped kernel-only, the natural follow-on was to convert the existence-only universality result into a **quantitative compilation theorem** — a polylog-length Solovay–Kitaev bound for Fibonacci anyons — and a runnable Lean-extracted reference compiler skeleton.

**Headline goal (shipped):** the first kernel-verified quantitative Solovay–Kitaev length bound in any proof assistant, instantiated for the Fibonacci-anyon braid representation in SU(2), with both an existence-form quantitative theorem and a constructive `skApproxC` compiler with visible Dawson–Nielsen composition.

**Phase-naming history:** the phase was originally scoped as **Phase 6q** during planning 2026-05-22 AM; renamed to **Phase 6t** before the first wave ship to deconflict with the existing Phase 6q (DKM transport bootstrap) sibling roadmap.

**Status (2026-05-23 PM, Phase 6t CLOSED):** **✅ ALL 8 WAVES + STRENGTHENING + ITERATION 1+2 + PATH A OPTION C SHIPPED**. Headline theorems all kernel-only `[propext, Classical.choice, Quot.sound]`. Project axiom count UNCHANGED at **0** (counts.json: `axiom_names: []`). lake build clean at 8627 jobs. pytest 4125/0 regressions. D4 bundle close-out (Stage 9/10/13) GREEN.

**Project rule applied:** **No PM / time / phase-cost estimates** anywhere (carried from Phase 6n/6o/6p/6q/6r/6s; user direction reaffirmed). **No manuscript drafting until Wave 8 Stage 10.E** (the unified D4 §9 prose). **No new project-local axioms** (Pipeline Invariant #15 RESPECTED throughout; the Y_h Lipschitz π/2 tightening cascade in Path A Option C was the principled alternative to bumping `K_compose`). **No `maxHeartbeats` overrides in proof bodies** (Pipeline Invariant #10 RESPECTED; the valid-branch composition was decomposed via the `valid_branch_K_chain_le_K_compose_numeric` helper extraction).

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY POST-PHASE-6t FOLLOW-UP WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Phase 6t is CLOSED.** Re-opening for additional sub-waves requires explicit user authorization. Mathlib-PR-quality lemma upstream cycles (e.g., `Y_h_norm_le_half_pi_norm_sub_one`, `valid_branch_K_chain_le_K_compose_numeric`) are tracked in `temporary/working-docs/proof-state/phase6t-mathlib-upstream-pr-candidates.md` and may proceed under Phase 6s Track 2 framing (community-citizenship upstream).
> 3. **Read `Phase6p_Roadmap.md` Wave 2c.4a end-to-end** — Phase 6t consumes the Phase 6p F.21 unconditional density (`fibonacci_density_F21_unconditional`) as its Wave 3 base case.
> 4. **Read this roadmap end-to-end** before any wave-level claim.
> 5. **Read the predecessor working doc** at `temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md` for full per-wave substrate detail.
> 6. **Critical substrate — read source directly:**
>    - **Dawson–Nielsen 2006** ("The Solovay–Kitaev algorithm", `arXiv:quant-ph/0505030`) — the canonical reference for the super-quadratic recursion with exponent `c = log 5 / log(3/2) ≈ 3.9694`. Primary source cache at `Lit-Search/Phase-1-and-Background/primary-sources/DawsonNielsen2006.pdf`.
>    - **Aharonov–Arad 2017** ("On the Fibonacci anyon model", `arXiv:1703.10282`) — Lemma 6.1 cardinality argument used in the Path A IFT discharge.
>    - **Kitaev–Shen–Vyalyi 2002** (*Classical and Quantum Computation*, AMS) — the SK algorithm's exposition and the original O(log^c(1/ε)) length bound formulation.
>    - **Phase 6t landscape scan** at `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md` — confirms NO prior kernel-verified quantitative SK formalization in Lean / Coq / Agda / Isabelle / HOL4 / Metamath / Rocq (the basis for the primacy claim in D4 §9.5).
>    - **Phase 6p F.21 substrate (Wave 3 base case dependency):** `lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean` `fibonacci_density_F21_unconditional`.
> 7. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` Branch D.4 (sourceless Lean-only absorption)** — Phase 6t produced NO separate per-paper draft; bundle absorption used the synthetic source-paper handle `_phase6t_lean_only`.
> 8. **`BUNDLE_LIFT_PROCEDURE.md` §§8-14** — Phase 6t's Wave 8 closeout executed the full Stage 9 / Stage 10 / Stage 13 reviewer-agent triple on bundle D4.
> 9. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback. Reviewer-agent invocations (Stage 9 / 10 / 13) use general-purpose Agent fallback path when plugin agents are not directly invokable.
> 10. **No PM / time estimates anywhere** — by user direction.

---

## Wave catalog — Shape C (Linear 8-wave Lean substrate + iteration/strengthening overlays)

Eight primary waves, plus two cross-cutting iteration arcs (ε₀ refinement + Path A constructive variant) and a final Y_h Lipschitz tightening (Option C) cascade that delivered the tight-ε unconditional discharge.

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / paper deliverables committed and kernel-verified.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft only.
- ⏳ **NOT STARTED**.

| Wave | Codename | Status | Bundle absorption | Branch | Key commit(s) |
|---|---|---|---|---|---|
| **Wave 1** | `GroupCommutator.lean` — group-commutator quadratic shrinkage + cubic Lie linearization | ✅ SHIPPED | D4 §9.3 | D.4 (sourceless) | `a89a50c` |
| **Wave 2** | `SU2BalancedCommutator.lean` — Kuperberg-2009-tight balanced-commutator factorization | ✅ SHIPPED | D4 §9.3 | D.4 | `a89a50c` |
| **Wave 3** | `FibonacciEpsilonNet.lean` — Path A constructive ε₀-net via F.21 density | ✅ SHIPPED | D4 §9.3 | D.4 | `a89a50c` |
| **Wave 4** | `SolovayKitaevRecursion.lean` — super-quadratic recursion engine + `skLevel_polylog` + `skLevel_compose` | ✅ SHIPPED | D4 §9.3 | D.4 | `a89a50c` |
| **Wave 5** | `SolovayKitaevLengthBound.lean` — closed-form length recurrence + `SkLengthAtEpsilon` + `skLengthExponent ≈ 3.9694 ∈ (3,4)` sanity | ✅ SHIPPED | D4 §9.3 | D.4 | `a89a50c` |
| **Wave 6** | `SolovayKitaevQuantitative.lean` — UNCONDITIONAL strict headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` for ε ∈ (0, ε₀] | ✅ SHIPPED | D4 §9.3 | D.4 | `a89a50c`, `b027618` |
| **Wave 7** | `SolovayKitaevApplications.lean` — worked-example library + universal-gate-set machinery | ✅ SHIPPED | D4 §9.4 | D.4 | `a89a50c` |
| **Wave 8** | Closeout: Stage 6+8 figures + smoke tests; Stage 10.E §9 prose; Stage 11 notebooks; Stage 9/10/13 reviewer agents on D4 | ✅ SHIPPED | D4 §9 (all subsections) | D.4 | `dbff76e`, `62f1185`, `caee77c` |
| **Iteration 1** | ε₀ refinement (1/2 → 1/(8·K_compose²) = 1/8388608) | ✅ SHIPPED | (cascades into Waves 4-6) | D.4 | (within `a89a50c` arc) |
| **Iteration 2** | Constructive `skApprox` with F.21-density discharge of `SkApproxInductiveStep` | ✅ SHIPPED | D4 §9.4 | D.4 | (within `a89a50c` arc) |
| **Path A** | Constructive Dawson–Nielsen compiler `skApproxC` with visible composition + 3-regime unconditional discharge | ✅ SHIPPED | D4 §9.4 | D.4 | (Steps 1-5, then Option C) |
| **Path A Option C** | Y_h Lipschitz π/2 tightening cascade → `SkApproxCSuperQuadraticBound K_compose` unconditional at K_compose = 1024 | ✅ SHIPPED | D4 §9.4 | D.4 | `5eaa861`, `0ec1522` (19 commits total) |
| **Strengthening pass** | Wave 1 unitary-specialized stability; Wave 2 Pauli-X/Y axis discharge + Bloch general-axis; Wave 4 followup (`SkApproxErrorShrinkage` + `ErrorBound`); Wave 5 followup (`SkLengthAtEpsilon` unconditional); Wave 6 followup (`SolovayKitaevQuantitativeContract`) | ✅ SHIPPED | (cascades into Waves 1-6) | D.4 | (multi-commit) |

**Wave dependencies:**
- Waves 1-7 executed sequentially in one ship arc (2026-05-22 PM).
- Wave 8 executed after Waves 1-7 close, in two phases: (a) autonomous portion (Stage 6+8+10E+11) 2026-05-23; (b) review portion (Stage 9/10/13) 2026-05-23 PM (this roadmap retroactively created).
- Iteration 1, Iteration 2, and Path A Steps 1-5 ran concurrently with the Waves 1-7 arc as in-place refinements; they did not branch new modules but improved the substrate inside the existing 8.
- Path A Option C ran as a follow-on after Path A Steps 1-5 surfaced a tight-ε calibration gap; the Y_h Lipschitz π/2 tightening was the principled (vs. expedient K_compose bump) resolution.

**Coherent sub-narrative.** Phase 6t converted the Phase 6p F.21 existence-only universality into a **quantitative compilation theorem** — the first kernel-verified Solovay–Kitaev length bound in any proof assistant. The substrate ships as 8 Lean modules totalling **5,640 LoC** under `lean/SKEFTHawking/FKLW/`, with a parallel constructive variant (`skApproxC` in `SolovayKitaevPathA.lean`, 2,565 LoC of the 5,640) that exhibits the Dawson–Nielsen composition overtly at the term level rather than via `Classical.choose`. The three-regime unconditional ship — loose ε ≥ 2ε₀, structural K_huge witness, and calibrated tight ε ∈ (0, ε₀] at K_compose = 1024 — was achieved without any new project-local axioms and without any heartbeat overrides.

---

## Wave-by-wave (retroactive — implementation reality)

### Wave 1 — `GroupCommutator.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/GroupCommutator.lean` (~445 LoC).

**Sub-deliverables:**

- **Wave 1.1 (group-commutator quadratic shrinkage):** `‖[A,B] - 1‖ ≤ C·δ²` for `A = e^{iF}`, `B = e^{iG}` with `‖F‖, ‖G‖ ≤ δ ≤ 1`. Direct ε-δ proof using matrix Taylor expansion + Lie bracket linearisation.
- **Wave 1.2 (cubic Lie linearisation):** `‖[A,B] - (1 - [F,G])‖ ≤ 320·δ³` via Mathlib's `MatrixBCHCubic.bch_order_2_cubic_thm` (top-level project module under `SKEFTHawking/`, shipped pre-Phase-6t as F.21 substrate). The constant `320 = 253 + 30 + 36 + 1` matches Dawson–Nielsen 2006's looseness analysis.
- **Wave 1.3 strengthening pass:** unitary-specialized `groupCommutator_stability_nearIdentity` for SU(n) consumers — sharp bound exploiting `‖U‖_op = 1` for unitary U; consumed by Path A.

### Wave 2 — `SU2BalancedCommutator.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SU2BalancedCommutator.lean` (~762 LoC).

**Sub-deliverables:**

- **Wave 2.1 (Z-axis balanced-commutator factorization):** Kuperberg-2009-tight construction `g = e^{iF}·e^{iG}·e^{-iF}·e^{-iG}` for `g ∈ SU(2)` near identity, in the Z-axis case (where `g` is diagonal). Closed unconditionally.
- **Wave 2.2 strengthening (X/Y-axis cases):** explicit Pauli-X and Pauli-Y axis sub-cases shipped during strengthening.
- **Wave 2.3 followup (general-axis Bloch decomposition):** `BalancedCommutatorGeneralAxisGroup` discharged via SU(2) Bloch decomposition — substrate lemmas `pauli_linear_commutator_eq` (cross-product), `pauli_linear_norm_eq` (formula), `pauli_decomp_of_hermitian_traceless` (Mathlib-PR-quality).

### Wave 3 — `FibonacciEpsilonNet.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/FibonacciEpsilonNet.lean` (~176 LoC).

**Content:** ε₀-net base case consuming Phase 6p F.21. For any target `U ∈ SU(2)`, `fibonacciEpsilonNet_findNearest U ε₀` returns a Fibonacci braid word `b` with entrywise distance `‖ρ_Fib(b) - U‖∞ < ε₀`; existence is unconditional via F.21 density (`fibonacci_density_F21_unconditional` from `SU2BCHBracketClosure.lean`). The function is defined through `Classical.choose`, hence `noncomputable` as shipped — constructive enumeration is the Path A line.

**Mathlib upstream candidate:** Wave 3.3 generalized the entrywise-to-operator-norm bound from `Fin 2` to `Fin d` (general-dimension version is Mathlib-PR-quality).

### Wave 4 — `SolovayKitaevRecursion.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SolovayKitaevRecursion.lean` (~852 LoC).

**Sub-deliverables:**

- **Wave 4.1 (recursion engine):** `V_{n+1} = V_n · [F_n, G_n]` with level-0 base case discharged unconditionally; recursion-step super-quadratic shrinkage closed during Wave 4-followup via the matrix-log residual bound.
- **Wave 4.2 (Iteration 1):** ε₀ refinement from initial `1/2` to calibrated `1/(8·K_compose²) = 1/8388608` (with `K_compose = 1024`). This refinement cascades into Waves 5-6 and fixes the convergence-condition arithmetic.
- **Wave 4.3 (Iteration 2):** `ε_seq K e n` closed-form recursion + `skApprox_exists` inductive proof.
- **Wave 4.4 (Iteration 2 sub-ship 3b-prep):** Bloch-sphere matrix-log substrate (Path B-flavoured precursor to Path A).
- **Wave 4.5 (Iteration 2 main):** `SkApproxInductiveStep` discharged via F.21 density.
- **Wave 4.6 (`skLevel_polylog` + `skLevel_compose`):** addition of the polylog and composition level functions; `skLevel_compose_upper_bound` ships as the Wave 5 bridge.

### Wave 5 — `SolovayKitaevLengthBound.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SolovayKitaevLengthBound.lean` (~504 LoC).

**Sub-deliverables:**

- **Wave 5.1 (closed-form length recurrence):** `skLength n = skLengthBaseCase · 5^n + skBalancedDecompCost · (5^n - 1) / 4`. The factor 5 reflects the 4 commutator pieces + 1 prior level per Dawson–Nielsen.
- **Wave 5.2 (sanity bounds):** `3 < skLengthExponent < 4` (with `skLengthExponent := log 5 / log(3/2) ≈ 3.9694`).
- **Wave 5.3 (strengthening — `SkLengthAtEpsilon` unconditional):** the Prop `SkLengthAtEpsilon` (capital S) is the `O((log(1/ε))^c)` headline composition; discharged unconditionally by the theorem `skLengthAtEpsilon_unconditional` (lowercase s) during the strengthening pass.
- **Wave 5.4 (placeholder cleanup):** removed "placeholder" markers from Wave 5 constants — they are now substantive.

### Wave 6 — `SolovayKitaevQuantitative.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SolovayKitaevQuantitative.lean` (~195 LoC).

**Content:** the **existence-form strict headline** `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` composes the Wave 4 error bound (`SkApproxErrorBound`) and the Wave 5 length bound (`SkLengthAtEpsilon`) at the same algorithmic compile level `skLevel_compose`. Initially shipped conditional on the tracked predicate `SolovayKitaevQuantitativeContract`; **Wave 6-followup** discharged this contract unconditionally for ε ∈ (0, ε₀], giving the first kernel-verified quantitative SK headline.

### Wave 7 — `SolovayKitaevApplications.lean` ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SolovayKitaevApplications.lean` (~141 LoC).

**Content:** worked-example consumers including a polylog-length T-gate approximation under the Fibonacci representation, plus a Phase 6u placeholder for the future Chain~A∘B Fourier-Transform composition. Wave 7 cleanup dropped the `compile_su2_target` rename wrapper.

### Path A — Constructive Dawson–Nielsen compiler ✅ SHIPPED

**Module:** `lean/SKEFTHawking/FKLW/SolovayKitaevPathA.lean` (~2,565 LoC).

**The headline of Wave 6 uses `Classical.choose` to extract a braid word from the existence content of F.21 density. Path A is the parallel constructive variant:**

- **Step 1** (`pauli_linear_traceless` Mathlib-PR-quality substrate)
- **Step 2** (traceless companion to `balanced_commutator_general_axis_lie`)
- **Step 3** (`exp(I·F) ∈ SU(2)` helper for traceless Hermitian F)
- **Step 4** (substantive constructive `skApprox` def — visible Dawson–Nielsen composition at the term level via the `skApproxC_succ` unfolding lemma)
- **Step 5** (11-step inductive error bound proof + strict headline upgrade)

**Three-regime unconditional ship.** The substantive super-quadratic shrinkage bound for `skApproxC` is captured by the tracked predicate `SkApproxCSuperQuadraticBound K`. All three regimes ship unconditionally:

1. **Loose ε (ε ≥ 2ε₀):** level-0 base case suffices. Headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_unconditional` ships kernel-only.
2. **Structural K_huge (any ε):** at `K_huge = 10^30`, the diameter bound `‖ρ_Fib(skApproxC n U) - U‖ ≤ 2√2` combined with `K_huge·(2ε₀)^(3/2) ≥ 2√2` (satisfied numerically by ~4×10^19) gives `SkApproxCSuperQuadraticBound_huge_holds`.
3. **Calibrated K_compose = 1024 (tight ε ∈ (0, ε₀]):** see Path A Option C below.

### Path A Option C — Y_h Lipschitz π/2 tightening cascade ✅ SHIPPED

**Critical follow-on (commits `5eaa861` + `0ec1522`, plus 17 substrate commits).** Following Path A Steps 1-5, an audit (`temporary/working-docs/proof-state/phase6t-path-a-calibration-audit.md`) surfaced a tight-ε calibration gap: the existing Y_h Lipschitz constant of 4 gave `K_proof ≈ 1440 > K_compose = 1024`. The Tier-1 audit recommendation was **Option A** (expedient: bump `K_compose` to 2200). User redirected toward **Option C** (principled: tighten Y_h Lipschitz via Bloch-sphere variant + SU(2) row-sum identity).

**Option C delivered the unconditional tight-ε discharge:**

- **Y_h Lipschitz 4 → π/2:** `Y_h_norm_le_half_pi_norm_sub_one` (`OneParameterSubgroupSU2.lean` §82.7) via the analytically-tight Jordan inequality `(sinc θ)^{-1} ≤ π/2` and the SU(2) row-sum identity `‖h - (tr h / 2)·I‖ ≤ ‖h - 1‖` (the latter via `SU2_norm_sub_aI_le_norm_sub_one` — Mathlib upstream candidate).
- **Substantive valid-branch composition** (cubic + stability + V_n √2) extracted as the numerical chain helper `valid_branch_K_chain_le_K_compose_numeric` (Mathlib-PR-quality numerical chain using `Real.pi_lt_d2` + `Real.exp_one_lt_three` + tight `(π/4)·√2 ≤ 6/5`).
- **Headline:** `SkApproxCSuperQuadraticBound_holds` at `SolovayKitaevPathA.lean:1716` — ~810-LoC induction with K_proof ≤ 788 ≤ K_compose = 1024 (margin ≥ 236).
- **Wrapper:** `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` at `SolovayKitaevPathA.lean:2523` — unconditional strict headline for tight ε ∈ (0, ε₀], bundling BOTH error `‖ρ_Fib(compile U ε) - U‖ ≤ ε` AND polylog length at the same algorithmic level `skLevel_polylog ε`.

### Wave 8 — Closeout + D4 bundle absorption ✅ SHIPPED

**Sub-deliverables:**

- **Stage 6+8 (Python smoke tests + figures):** commits `dbff76e`, `f14432e`, `cbf6149`. SK reference compiler smoke tests in `tests/test_phase6t_sk.py`; SK figures via `scripts/review_figures.py` (D4 has no figures by design, so this was a Phase 6t-wide visualization pass for the Technical/Stakeholder notebooks).
- **Stage 10.E (manual D4 §9 prose authoring):** commit `62f1185`. Unified §9 "Fibonacci-anyon density and quantitative Solovay–Kitaev compilation" authored as ~3,500-word LaTeX with five subsections:
  - §9.1 — F.21 unconditional density theorem (consumes Phase 6p ship)
  - §9.2 — Quantitative Solovay–Kitaev (Phase 6t Wave 6 existence-form headline)
  - §9.3 — Lean substrate: the eight-module Phase 6t pipeline
  - §9.4 — Path A constructive Dawson–Nielsen compiler (three-regime unconditional ship)
  - §9.5 — Status, downstream consumption, and cross-bundle bridges
- **Stage 11 (Technical + Stakeholder notebooks):** commits `d47e5d7`, `a484e5f`. `notebooks/Phase6t_SolovayKitaev_Technical.ipynb` + `notebooks/Phase6t_SolovayKitaev_Stakeholder.ipynb`.
- **Stage 9 (figure review, D4):** GREEN vacuous-PASS — D4 has 0 `\includegraphics` + 0 `\begin{figure}` envs; figures/ empty by design.
- **Stage 10 (claims review, D4 round 4):** GREEN-with-advisories — 34 sentences walked in §9; 21 PASS / 8 WARN / 0 FAIL; 5 advisories raised; 4 FIXED in round-4 fix-pass (IA LoC undercount, TN `skLengthAtEpsilon` case-ambiguity, HD `gapped_interface_axiom` stale at 4 sites, cosmetic Lemma~6→6.1 + K_huge factor `~10^16` → `~4×10^19`).
- **Stage 13 (adversarial review, D4 round 2):** GREEN-with-advisories — 0 BLOCKER / 0 REQUIRED / 1 RECOMMENDED (FIXED) / 4 ADVISORY (1 new FIXED + 3 cross-bundle reciprocity carryovers, all out-of-scope for D4-side revision). Bundle CLOSED at GREEN per `BUNDLE_LIFT_PROCEDURE.md §14`. Commit `caee77c`.

---

## Headline theorems shipped (all kernel-only)

Three complementary unconditional Path A headlines plus the existence-form Wave 6 strict headline cover the full ε range:

| Theorem | File / Line | Regime | Headline form |
|---|---|---|---|
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` | `SolovayKitaevQuantitative.lean:185` | Existence-form, ε ∈ (0, ε₀] | `∃ w, ‖ρ_Fib(w) - U‖ < ε ∧ length(w) ≤ C·(log(1/ε))^c` |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_unconditional` | `SolovayKitaevPathA.lean` | Loose ε (≥ 2ε₀) | Constructive `skApproxC` with visible DN composition |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` | `SolovayKitaevPathA.lean:2523` | Tight ε ∈ (0, ε₀] at K_compose = 1024 | Bundled error AND polylog length at same algorithmic level |
| `SkApproxCSuperQuadraticBound_huge_holds` | `SolovayKitaevPathA.lean` | Structural K_huge = 10^30 (any ε) | Diameter-bound fallback for predicate satisfiability |

**Axiom closure target:** `[propext, Classical.choice, Quot.sound]` (Lean standard kernel only). **Project-local axioms introduced by Phase 6t: ZERO.** **Project axiom count throughout Phase 6t: 0** (per `counts.json: axiom_names: []` — the legacy `gapped_interface_axiom` from D2 was retired to `TPFConjecture` tracked Prop on 2026-05-19, before Phase 6t opened).

---

## Calibration arithmetic (Path A Option C, verified)

At `c = π/2` (Y_h Bloch-tightened Lipschitz bound):

```
θ ≤ (π/2)·√2·ε_n             via H_norm_bound_from_V_diff_half_pi
δ_lie := √(θ/2)
δ_lie² ≤ (π/4)·√2·ε_n
((π/4)·√2) ≤ 6/5             via π < 3.15 (Real.pi_lt_d2) + √2 ≤ 3/2  →  (3.15/4)·(3/2) ≈ 1.181 ≤ 6/5
((π/4)·√2)^(1/2) ≤ 6/5       via (6/5)^p ≤ 6/5 for p ≤ 1, base ≥ 1
((π/4)·√2)^(3/2) ≤ 36/25     via (6/5)·(6/5) = 36/25

K_stab1 = 12·√2·e·((π/4)·√2)^(1/2) ≤ 12·(3/2)·3·(6/5) = 324/5 = 64.8
K_stab2 = 12·√(2·ε₀)              ≤ 12·(1/2048)       = 3/512 ≈ 0.006
K_cubic = √2·320·((π/4)·√2)^(3/2) ≤ (3/2)·320·(36/25) = 17280/25 = 691.2

K_proof = √2·(K_stab1 + K_stab2) + K_cubic
       ≤ (3/2)·(324/5 + 3/512) + 17280/25
       ≈ 97.2 + 0.009 + 691.2 = 788.4 ≤ 1024 ✓ (margin ~236)
```

---

## Architecture lessons (recorded for future SK-style discharges)

1. **Pipeline Invariant #10 (no `maxHeartbeats`) requires aggressive helper extraction** for proofs with cumulative elaboration cost > 200,000 heartbeats. The valid-branch composition (~700 LoC) hit the ceiling; extracting `valid_branch_K_chain_le_K_compose_numeric` (the numerical chain) into a top-level helper resolved it.
2. **`ring` does NOT work for non-commutative matrix expressions** — use `noncomm_ring` for `(V_n · gC₁ - V_n · gC₂) = V_n · (gC₁ - gC₂)` type identities. `ring` is fine for real-numerical chains (rpow stays in real-commutative-ring world).
3. **`Real.rpow_natCast` directionality:** `x ^ (n : ℕ) = x ^ ((n : ℕ) : ℝ)` means to BRIDGE Nat-power → rpow, use `← Real.rpow_natCast`. Then add `show ((n : ℕ) : ℝ) = ...` to expose the real-cast form for further manipulation.
4. **Avoid `rw [show ε_n = ε_n^1 from ...]`** — it rewrites BOTH sides of the equation, including the RHS bases. Use `conv_lhs => rw [...]` to scope.
5. **`linarith` is heartbeat-expensive in deeply-nested contexts.** Replace with explicit `exact add_le_add ...` or `exact mul_le_mul_of_nonneg_left ...` when the goal structure is known.
6. **For tight numerical bounds:** `Real.pi_lt_d2` (π < 3.15) + manual `(π/4)·√2 ≤ 6/5` works. Looser bounds like `(π/4)·√2 ≤ 3/2` lead to K_proof ≈ 1440, overshooting K_compose = 1024.

---

## Mathlib upstream PR candidates (deferred to Phase 6s Track 2 framing)

Local-only working doc at `temporary/working-docs/proof-state/phase6t-mathlib-upstream-pr-candidates.md` lists 9 lemmas across Tiers 1-3:

- **Tier 1 (highest priority):** `SU2_norm_sub_aI_le_norm_sub_one` (SU(2) row-sum identity); `valid_branch_K_chain_le_K_compose_numeric` (numerical chain using `Real.pi_lt_d2` + `Real.exp_one_lt_three`).
- **Tier 2:** `Y_h_norm_le_half_pi_norm_sub_one` (matrix-log Lipschitz via Jordan inequality); `pauli_decomp_of_hermitian_traceless`.
- **Tier 3:** assorted SU(2) helpers from `SolovayKitaevPathA.lean` (e.g., `expIsu2_norm_sub_one_le`, `expIsu2_zero_val`, `SU2_val_det_isUnit`).

These are tracked but not committed publicly. Per the user-facing rule, they may be picked up under **Phase 6s Track 2** (community-citizenship Mathlib upstream) if/when that line is dispatched, OR under a future dedicated `Phase6t-followup` line.

---

## User authorization gates — consolidated

| Gate | Authorization point | Authorization required for | Status |
|---|---|---|---|
| Phase 6t opening | Wave 1 ship 2026-05-22 | YES (renamed Phase 6q → Phase 6t) | ✅ **GRANTED** 2026-05-22 |
| Stage 10.E manual prose authoring | Wave 8 §10.E ship 2026-05-23 | YES (originally deferred as non-autonomous per the roadmap working doc §17.3) | ✅ **GRANTED** 2026-05-23 |
| Path A Option C (Y_h tightening) | Calibration audit → Option C ship 2026-05-23 | YES (user redirected from Option A to Option C per "general and most correct" preference) | ✅ **GRANTED** 2026-05-23 |
| Mathlib upstream PR cycle | Tier 1-3 lemmas above | TBD — handled under Phase 6s Track 2 framing | 🔒 **PENDING** (Phase 6s scope) |

---

## Phase 6t-internal further-deferred tracks

- **Chain A∘B Fourier-Transform composition** — Phase 6u placeholder in `SolovayKitaevApplications.lean` Wave 7 §3. Substantive content deferred to a future Phase 6u or 7+ line.
- **Mathlib upstream PR cycle** — Tier 1-3 lemmas in the PR-candidates working doc, deferred to Phase 6s Track 2.
- **D3/F-side cross-bundle reciprocity advisories** — the 3 residual D4 advisories (fu:D4:r2:1 §8.4 wording, fu:D4:r2:4 D3 §7 RT/CH one-sided, fu:D4:r4:5 D4→F §7 unidirectional) need D3 / F revision passes to close. Out of D4-side scope.
- **`validate.py --check bundle_reciprocity`** — Stage 13 round-2 emitted this as a QI candidate. Would auto-track unreciprocated cross-bridge claims in `BUNDLE_READINESS_HEATMAP.md` rather than requiring per-bundle Stage-13 walks to rediscover them.

---

## Cross-references

- `docs/roadmaps/Phase6p_Roadmap.md` Wave 2c.4a (F.21 unconditional density) — Phase 6t's Wave 3 base case dependency.
- `docs/roadmaps/Phase6s_Roadmap.md` Track 2 — natural home for the Phase 6t Mathlib upstream PR candidates.
- `temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md` — predecessor working doc (full per-wave substrate detail).
- `temporary/working-docs/proof-state/phase6t-path-a-calibration-audit.md` — the audit doc that surfaced the tight-ε calibration gap and motivated Path A Option C.
- `temporary/working-docs/proof-state/phase6t-mathlib-upstream-pr-candidates.md` — Tier 1-3 Mathlib PR candidates (local-only, gitignored).
- `temporary/working-docs/proof-state/phase6t-iteration2-dn-recursion-analysis.md` — Iteration 2 substrate analysis (constructive Path A precursor).
- `memory/project_phase6t_path_a_option_c_y_h_tightening_2026_05_23.md` — the 19-commit ship log for Path A Option C.
- `memory/project_phase6t_strict_headline_2026_05_22.md` — the strong strict headline ship log.
- `memory/project_phase6t_wave8_closeout_2026_05_23.md` — Wave 8 closeout autonomous portion.
- `memory/project_d4_bundle_closed_green_2026_05_23.md` — Wave 8 D4-bundle close-out (Stage 9/10/13).
- `papers/D4/paper_draft.tex` §9 — the bundle's Phase 6t section.
- `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md` — primacy-claim backing (no prior kernel-verified quantitative SK formalization in any major proof assistant).
- `lean/SKEFTHawking/FKLW/{GroupCommutator,SU2BalancedCommutator,FibonacciEpsilonNet,SolovayKitaevRecursion,SolovayKitaevLengthBound,SolovayKitaevQuantitative,SolovayKitaevApplications,SolovayKitaevPathA}.lean` — the 8-module Phase 6t pipeline.

---

*Created retroactively 2026-05-23 PM at Phase 6t close, after the D4-bundle close-out commit `caee77c`. The roadmap reflects the implementation reality of the Phase 6t arc — every wave shipped, every iteration applied, every strengthening discharged, the Y_h Lipschitz Option C cascade landing the unconditional tight-ε discharge at K_compose = 1024 with margin ≥ 236. Per Phase 6t precedent (working doc only during ship, canonical roadmap created at close), this document is the authoritative record going forward.*

---

## Sessions log

**2026-05-22 AM — Planning + rename Phase 6q → Phase 6t.** User authorized phase opening following the Phase 5 Step 13 Path (i) FINAL ship. Working doc `temporary/working-docs/proof-state/phase6t-solovay-kitaev-dawson-nielsen-roadmap.md` drafted with 7-wave Lean substrate plan + Wave 8 closeout plan + D.4 sourceless absorption strategy.

**2026-05-22 PM — Waves 1-7 + Iteration 1 + Iteration 2 + Path A Steps 1-5 SHIPPED.** Commit arc `a89a50c` (public) + `5f45c6b` (private). All 7 substrate waves close kernel-only in one sustained ship. The strong strict headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` ships unconditional for ε ∈ (0, ε₀], bundled error AND length at the same algorithmic compile level `skLevel_polylog ε`. Per memory `project_phase6t_strict_headline_2026_05_22.md`: 9 commits / ~1000+ LoC kernel-only.

**2026-05-22 PM (continued) — Path A loose-ε + structural-K_huge discharges SHIPPED.** Constructive `skApproxC` with VISIBLE Dawson–Nielsen composition replaces opaque `Classical.choose`-based compile. UNCONDITIONAL `SkApproxCSuperQuadraticBound_huge_holds` (K = 10^30, diameter-bound-based) + UNCONDITIONAL bundled loose-ε strict headline for ε ∈ [2·ε₀, ε₀]. 13 commits per memory `project_phase6t_path_a_active_2026_05_22.md`.

**2026-05-23 AM — Wave 8 autonomous portion (Stage 6+8+10E+11) SHIPPED.** 6 commits per memory `project_phase6t_wave8_closeout_2026_05_23.md`: `dbff76e`/`f14432e`/`cbf6149`/`d47e5d7`/`a484e5f`/`62f1185` plus separate LaTeX θ fix in `7c9c509`. D4 §9 unified ~3,500-word prose authored.

**2026-05-23 PM — Path A Option C Y_h Lipschitz tightening cascade SHIPPED.** 19 commits per memory `project_phase6t_path_a_option_c_y_h_tightening_2026_05_23.md`: 17 substrate + 1 main theorem (`5eaa861`, `SkApproxCSuperQuadraticBound_holds` UNCONDITIONAL DISCHARGE at K_compose = 1024, ~981 LoC) + 1 wrapper (`0ec1522`, unconditional strict headline `_strict_constructive_tight`). K_proof ≈ 788 ≤ K_compose = 1024 (margin ≥ 236). All headlines kernel-only.

**2026-05-23 PM (final) — Wave 8 D4 bundle close-out (Stage 9/10/13) SHIPPED.** Commit `caee77c` (8 files / +1,783 LoC) per memory `project_d4_bundle_closed_green_2026_05_23.md`. Stage 9 vacuous-PASS; Stage 10 round-4 GREEN-with-advisories (34 sentences walked, 4 of 5 new advisories FIXED in same pass — LoC undercount + TN case + HD `gapped_interface_axiom` stale across 4 sites + cosmetic); Stage 13 round-2 fresh-context GREEN-with-advisories (0 BLOCKER, 1 RECOMMENDED + 1 new ADVISORY both FIXED, 3 cross-bundle reciprocity carryovers documented as QI candidate). Bundle CLOSED at GREEN per `BUNDLE_LIFT_PROCEDURE.md §14`.

**Phase 6t CLOSED 2026-05-23 PM.** All headlines kernel-only. Project axiom count = 0. lake build 8627 jobs clean. pytest 4125/0 regressions. D4 bundle Stage 9/10/13 = green.

---

*Created retroactively 2026-05-23 — the canonical version matching implementation reality. Future Phase 6t-followup work (e.g., Mathlib upstream PRs for the Tier 1-3 candidates) lives under the Phase 6s Track 2 framing OR a dedicated `Phase6t-followup_Roadmap.md` if substrate volume warrants it.*
