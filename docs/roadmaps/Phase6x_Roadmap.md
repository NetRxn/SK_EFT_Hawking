# Phase 6x: Additional-Alphabet Quantum-Compiler Instantiations + Mathlib Upstreaming

## Technical Roadmap — May 2026

*Prepared 2026-05-25 PM, following Phase 6u close (alphabet-independent generic Solovay-Kitaev substrate + Clifford+T instance shipped UNCONDITIONAL; commits `7ad8e55` through `137838e`; see `docs/roadmaps/Phase6u_Roadmap.md` for closure summary).*

---

> ## 🔄 RETROSPECTIVE ADDENDUM — 2026-05-26 PM (Lift/Shift Reframing)
>
> The original Phase 6x roadmap (below, as Sections "Track catalog" through "Cross-references") scoped T-A1 (trapped-ion) and T-A2 (Clifford+CCZ) as **full multi-qubit SU(d > 2) compilation** ships, with the SU(d) substrate extension under T-A2.0 estimated at ~1,000-2,000 LoC and the aggregate Phase 6x effort at multiple thousand LoC. The Phase 6x first-session ship (2026-05-26 AM) yielded heavily on this substrate (T-A1.{3,4,5} + T-A2.0 + T-A2.{1..5}) under a misapplication of the Invariant #15 pivot rule (yielded on "substantial work" grounds when the pivot rule's literal scope is "yield only when an axiom would be required").
>
> The retrospective audit (2026-05-26 PM) reframed Phase 6x along a **lift/shift, recycle-and-grow** interpretation that reuses the Phase 6u SU(2)-targeted substrate verbatim:
>
>   - **T-A1 lift/shift framing**: ship "1Q-rotations-on-each-ion compiled via Phase 6u Clifford+T substrate + MS(θ) emitted as primitive token." Matches how Quantinuum / IonQ production compilers actually work (MS is the physically-realized entangling primitive, not something compiled into 1Q gates). ~200-400 LoC, *not* ~1,200-2,500. The "full SU(4) compilation" is academic-completeness work *deferred to Phase 6y Track T-A1′*.
>
>   - **T-A2 lift/shift framing**: ship "CCZ-matrix substrate + CCZ-as-primitive interpretation" with the full SU(8) Clifford+CCZ compilation explicitly deferred to Phase 6y Track T-A2′. ~100-300 LoC at Phase 6x; the substantive SU(8) compile chain ships in Phase 6y after Track S (SU(d) extension).
>
>   - **M.1, M.2, M.4 ACTUAL EXTRACTION**: the Phase 6x first-session ship shipped Mathlib-PR-quality *aliases* rather than the de-privatized extracted lemmas the roadmap targeted. Phase 6x completion (this revised roadmap) ships the actual de-privatization + generic-type-parametrization + Mathlib filename submission targets, ~100-300 LoC of submission-step work per track.
>
>   - **T-S′ Ross-Selinger algorithmic refinement**: the Phase 6x first-session ship was *existential* (finite-Finset cover) rather than the *algorithmic* (Ross-Selinger ℤ[ω][1/√2] symbolic enumeration) the roadmap targeted. The algorithmic refinement is the actual deliverable; ships in this completion phase with a Lit-Search task drop if necessary.
>
>   - **M.4 headline-level integration**: the Phase 6x first-session ship shipped the per-step recurrence at cliffordTGeneratingSet only. The actual roadmap deliverable is the headline-level length conjunct `(compile U ε).toWord.length ≤ skLength (skLevel_polylog ε)` integrated into all per-alphabet T-X.5 headlines. Ships in this completion phase.
>
> The Phase 6y roadmap (`docs/roadmaps/Phase6y_Roadmap.md`) captures the SU(d > 2) academic-completeness work that the Phase 6x lift/shift framing now explicitly defers. The remaining Phase 6x work + Phase 6y together cover what the original Phase 6x roadmap (below) scoped.
>
> **Anti-patterns identified for the Phase 6x completion + Phase 6y consumers** (to avoid repeating):
>
>   1. **Pivot Rule #15 mis-scoping**: yielding on "substantial work" rather than "axiom required." The pivot rule fires ONLY when shipping would require an axiom. Substantial-but-doable multi-session work = ship it across multiple sessions; don't yield.
>   2. **Heavy-interpretation default**: when the roadmap presents architectural options, check whether a LIGHTER interpretation gives the same audience-relevant claim. Don't pick the heaviest by default.
>   3. **Alias-only Mathlib PRs**: the Mathlib-PR deliverable is the de-privatized, generic-typed, docstring-equipped extracted lemma. A renaming alias of the existing project lemma is NOT a Mathlib PR.
>   4. **Substrate-only-shipped vs. headline-integrated**: per-step lemmas need to integrate into HEADLINE theorems for downstream consumption. Stopping at substrate is incomplete.
>   5. **Existential vs. algorithmic**: when the roadmap calls for "genuinely runnable" / "algorithmic" / "constructive," existential proofs do not satisfy the deliverable.
>
> The retrospective is documented in full at `docs/stakeholder/Phase6x_Implications.md` + `docs/stakeholder/Phase6x_Strategic_Positioning.md`.

---

**Trigger condition:** Phase 6u shipped the alphabet-independent `GeneratingSet` substrate (Waves 1–6 + Wave 4b) and validated it via the Clifford+T instance (Track T-S). The Lie-algebraic core (Dawson–Nielsen recursion, Cartan v4 closed-subgroup classification, BCH bracket-closure, ε₀-net, super-quadratic discharge) is fully generic. Phase 6x picks up the additional-alphabet instantiations that were re-slotted from Phase 6u (per ADR 008: T-A1/T-A2/T-B do not fit Phase 6v/6w scope) **plus** three Mathlib-upstream-PR-quality lemma extractions identified in the Phase 6u Strategic Positioning memo.

**Headline goal:** ship 3 additional alphabet instantiations on the Phase 6u substrate (Read-Rezayi `SU(2)_k` for `k ∈ {5, 7}` as Tier B; Clifford+CCZ as Tier A2; trapped-ion MS+1Q as Tier A1) **plus** 3 Mathlib upstream contributions extracting generic SU(2)-Lie-group infrastructure currently sitting inside the FKLW substrate. The per-alphabet work budget is ~few hundred to ~1000 LoC per Phase 6u Strategic Positioning's empirical pattern (vs. the multi-thousand-LoC original Phase 6t Fibonacci ascent), with the largest cost component being the per-alphabet density proof tackled in 1–3 sessions following the Niven-based template.

**Predecessor:** Phase 6u (`docs/roadmaps/Phase6u_Roadmap.md`). Phase 6x is **alphabet-instance + community-citizenship work**; no new generic-substrate refactoring required. Track T-A2's "SU(8) substrate extension" sub-track is the one exception — it requires extending the SU(2)-targeted substrate to higher-rank, which IS substrate work but is alphabet-driven (not a general refactor).

**Project rule applied:** No new project-local axioms (Pipeline Invariant #15 RESPECTED). No `maxHeartbeats` overrides in proof bodies (Invariant #10). Standard kernel only on headlines.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6x WAVE WORK:**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6u_Roadmap.md` end-to-end** — Phase 6x's track instantiations follow the Phase 6u Track T-S (Clifford+T) template directly. The 5-sub-wave alphabet pattern (T-X.1 gen set + T-X.2 closure-density witness + T-X.3 ε₀-net + T-X.4 calibration + T-X.5 headline) was established there.
> 3. **Read `Phase6u_Implications.md` + `Phase6u_Strategic_Positioning.md`** in `docs/stakeholder/` for the per-track audience positioning, Mathlib-upstream rationale, and the Niven-based density methodology template.
> 4. **Critical substrate — read source directly:**
>    - **Boykin–Mor–Pulver–Roychowdhury–Vatan 1999** (`arXiv:quant-ph/9906054`) for the Niven-based template (now formalized for Clifford+T in `CliffordTInfiniteOrder.lean`).
>    - **Mathlib4 `NumberTheory.Niven`** (`Mathlib/NumberTheory/Niven.lean`) — `Real.isIntegral_two_mul_cos_rat_mul_pi`, `niven`, plus the `Real.isAlgebraic_cos_rat_mul_pi` / `Complex.isAlgebraic_cos_rat_mul_pi` family.
>    - **Read-Rezayi 1999** (`arXiv:cond-mat/9809384`) for the `SU(2)_k` anyon model substrate.
>    - **Kliuchnikov–Maslov–Mosca 2013** (`arXiv:1206.5236`) + **Ross-Selinger 2014** (`arXiv:1403.2975`) for exact Clifford+T synthesis (relevant if Phase 6x ships a constructive ε₀-net follow-on).
>    - **Phase 6u substrate**: `lean/SKEFTHawking/FKLW/Generic*.lean` (7 files, ~2,400 LoC) — the entire alphabet-agnostic chain.
>    - **Phase 6u Clifford+T instance**: `lean/SKEFTHawking/FKLW/CliffordT*.lean` (8 files, ~1,460 LoC) — the canonical first instance template for any new alphabet.
> 5. **Do not delegate substantive theorem proving to subagents** for the load-bearing density-proof sub-waves. MCP loop default; Aristotle is fallback. Background agents OK for substrate refactoring + composition work.
> 6. **No PM / time estimates anywhere** — by user direction.
> 7. **Pivot rule:** if a Wave's closure-density witness for a target alphabet requires a tracked Prop or a Mathlib-substrate-not-present-in-v4.29.1 substrate piece (e.g., the SU(d) Cartan classification for Track T-A2), YIELD for user sign-off per Pipeline Invariant #15. Do NOT ship a project-local axiom.

---

## Track catalog

Four primary tracks, organized by per-track substrate-reuse level (highest reuse first) and audience priority:

  - **Track T-B (Read-Rezayi `SU(2)_k`)**: highest-substrate-reuse (target group remains SU(2); only generators change). Multiple instances (k ∈ {5, 7}) share substrate. Topological-QC-research audience.
  - **Track T-A1 (Trapped-ion native gates)**: medium-substrate-reuse (requires discretization layer + target-group decision: SU(2) restriction vs. SU(4) extension). Industry-quantum-compiler audience (Quantinuum, IonQ).
  - **Track T-A2 (Clifford+CCZ at SU(8))**: lowest-substrate-reuse (requires substantive SU(2)→SU(d) substrate extension, ~1,000-2,000 LoC). Fault-tolerant-architecture-research audience.
  - **Track M (Mathlib upstreaming)**: independent of T-B/T-A1/T-A2; can run in parallel. Community-citizenship.

**Status legend** (matches Phase 6u):
- ✅ **SHIPPED** — Lean / numerical deliverables committed and kernel-verified.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft only.
- ⏳ **NOT STARTED**.

| Track | Codename | Status | Bundle absorption |
|---|---|---|---|
| **Track T-B (Tier B)** | Read-Rezayi `SU(2)_k` instances for `k ∈ {5, 7}` — next-universal-anyon family beyond Fibonacci (`k = 3`). Highest substrate-reuse: ~80-90% of Phase 6t Fibonacci substrate transfers near-mechanically with σ_k generators replacing σ_Fib. Density via Niven-style on the per-`k` trace identity. | ✅ SHIPPED 2026-05-26 PM (T-B.5 + T-B.7 UNCONDITIONAL bundled-strict headlines) | D4 §9.8 (Read-Rezayi-extended multi-alphabet showcase) |
| **Track T-A1 (Tier A) — LIFT/SHIFT** | Trapped-ion native gate set under the **production-aligned reading**: 1Q rotations compiled via Phase 6u Clifford+T substrate; MS(θ) as primitive token (not compiled). Full SU(4) compilation deferred to Phase 6y Track T-A1′. | 🟡 SUBSTRATE SHIPPED 2026-05-26 PM (MS matrix + grid); chain integration pending Phase 6x completion | D4 §9.8 + E1 polariton/trapped-ion cross-bridge |
| **Track T-A2 (Tier A) — ALPHABET SUBSTRATE** | Clifford+CCZ matrix definition substrate at SU(8); CCZ-as-primitive interpretation. Full SU(8) Clifford+CCZ compilation deferred to Phase 6y Track T-A2′ (requires Phase 6y Track S SU(d) substrate extension as prerequisite). | ✅ SHIPPED 2026-05-26 PM (CCZ matrix + diagonal identities) | D4 §9.8 (substrate-level showcase entry; full-compile entry via Phase 6y) |
| **Track M (Mathlib upstream)** | Three lemma extractions from FKLW substrate to Mathlib4 PR-quality: (M.1) Generic BCH order-2 cubic bound; (M.2) Generic Cartan v4 density-from-witness; (M.3) three-direction-product strict differentiability. **ACTUAL EXTRACTION required** (not alias-only): de-privatized + generic-typed + Mathlib filenames. | 🟡 PR-PRESENTATIONS SHIPPED 2026-05-26 PM (M.3 NO-OP confirmed); actual extractions pending Phase 6x completion | (Mathlib4 upstream; no project-bundle absorption) |
| **Track T-S′ (Constructive ε₀-net)** | Replace Phase 6u T-S `Classical.choose`-based ε₀-net with Ross-Selinger 2014 `ℤ[ω][1/√2]` symbolic enumeration. **Genuinely runnable** required (not just existential). | 🟡 EXISTENTIAL FINITE-FINSET COVER SHIPPED 2026-05-26 PM; algorithmic Ross-Selinger refinement pending Phase 6x completion (Lit-Search task drop in scope) | (Compiler-side strengthening) |
| **Track M.4 (Concrete-word length-bound)** | Tighten T-S.5 length conjunct from abstract `skLength` to concrete `(compile U ε).toWord.length ≤ skLength (skLevel_polylog ε)`. **Headline-level integration** at all GeneratingSet instances required. | 🟡 PER-STEP RECURRENCE SHIPPED AT CLIFFORDT 2026-05-26 PM; headline-level integration + per-alphabet specializations pending Phase 6x completion | (Compiler-side strengthening) |

**Track dependencies:**
- T-B, T-A1, T-A2, and M can all run **in parallel** — they touch disjoint files/areas of the Phase 6u substrate.
- T-A2 has an internal dependency: T-A2.0 (SU(d) substrate extension) must precede T-A2.1–T-A2.5 (instantiation sub-waves).
- Track M's three lemmas can each be shipped independently. M.1 and M.2 are extract-and-generalize work; M.3 may already be complete in the technique sense (the existing private lemma in `SU2BCHBracketClosure.lean` is the SU(2) specialization; if the generic technique is what's wanted, the work is bounded to de-privatize + generalize the type).
- All tracks can run after Phase 6u substrate (already shipped). No cross-track dependencies.

---

## Track T-B detail — Read-Rezayi `SU(2)_k` for `k ∈ {5, 7}` (Tier B)

### Goal

Instantiate the Phase 6u substrate at the next universal Read-Rezayi anyon levels beyond Fibonacci (`k = 3`). Each `k ∈ {5, 7}` (and potentially `k ∈ {11, 13, …}` future) gets the bundled-strict quantitative Solovay-Kitaev headline at the `SU(2)_k` braiding representation.

### Key advantage

**Highest substrate-reuse of all the Phase 6x tracks (~80-90% direct transfer).** Target group remains SU(2); only the generators change. The Phase 6t Fibonacci-specific machinery transfers near-mechanically with σ_k generators replacing σ_Fib generators. The Cartan v4 closed-subgroup classification is unchanged (still SU(2)). The BCH cubic bound + Y_h Lipschitz + super-quadratic recursion are all reusable verbatim.

### Per-`k` sub-wave decomposition (mirrors Phase 6u Track T-S)

**T-B.k.1 — Generators** (~50-100 LoC per `k`). Define `σ_k_1, σ_k_2 ∈ SU(2)` for the SU(2)_k braid representation. The 2-strand representation of `B_n` at SU(2)_k generates a subgroup of SU(2) with explicit closure structure (Jones-Wenzl projectors, F-symbols computable from the SU(2)_k quantum-group data already shipped in `SKEFTHawking.SU2kMTC.lean` / `SU2kSMatrix.lean`).

**T-B.k.2 — Closure-density witness** (~150-300 LoC per `k`). Replicate the Phase 6u Niven-based density template with σ_k generators. The non-cyclotomic-trace argument differs per `k`:
- For `k = 3` (Fibonacci): trace involves golden-ratio quantities (already done in Phase 6t / 6p via Cartan v4).
- For `k = 5`: trace involves `2cos(πj/(k+2))` quantities for various `j`; for `k = 5` this is `2cos(πj/7)`. Niven-style obstruction: verify the trace's minimal polynomial is not of cyclotomic form.
- For `k = 7`: analogous with `2cos(πj/9)`.

**T-B.k.3 — ε₀-net** (~50-100 LoC per `k`). Existential via Classical.choose from Wave 2 density (mirrors Phase 6u Track T-S.3). Constructive form (Ross-Selinger-style symbolic enumeration on the SU(2)_k algebraic-number-theoretic structure) deferred.

**T-B.k.4 — Calibration** (~5-10 LoC per `k`). Immediate via Wave 4b's `SkApproxCSuperQuadraticBound_generic_holds`.

**T-B.k.5 — Bundled-strict headline** (~50-100 LoC per `k`). Direct instantiation of the Wave 6 generic headline at the per-`k` `GeneratingSet`. Conditional only on the per-`k` density witness, which T-B.k.2 discharges.

### Aggregate Track T-B effort

~400-800 LoC per `k`; multiple `k` values can be shipped in sequence. `SU(2)_5` alone: ~500 LoC.

### Audience and bundle absorption

**Audience**: topological-quantum-computing researchers in the Freedman-Kitaev-Larsen-Wang lineage; Read-Rezayi 1999 / Nayak-Simon-Stern-Freedman-Das Sarma 2008 review community; fault-tolerant-architecture researchers comparing topological vs. fault-tolerant resource costs.

**Bundle absorption**: D4 §9.8 — extend the multi-alphabet showcase from {Fibonacci, Clifford+T} to {Fibonacci, Clifford+T, RR `k=5`, RR `k=7`}.

### Risk

LOW per `k`. The Phase 6u Fibonacci-template transfer is well-validated by the Clifford+T instance.

---

## Track T-A1 detail — Trapped-ion native gate set (LIFT/SHIFT FRAMING; full SU(4) → Phase 6y)

### Goal

Instantiate the Phase 6u substrate at the Quantinuum / IonQ native gate set: Mølmer-Sørensen MS(θ) + arbitrary 1Q rotations. **Lift/shift framing (the Phase 6x completion target)**: kernel-verify the **per-ion 1Q-rotation compilation** via the Phase 6u Clifford+T substrate, with MS(θ) emitted as a primitive token (not compiled into 1Q gates). This matches how Quantinuum H1, IonQ Aria, and AQT production compilers actually work — MS is the physically-realized entangling primitive, not something the compiler decomposes.

### Key distinction (clarified per 2026-05-26 PM retrospective)

The original roadmap (above) presented T-A1.2 as a three-way decision: (a) 1Q-only-no-MS, (b) extend substrate to SU(4), (c) KAK decomposition. The retrospective reframing reads option (a) **NOT** as "ignore MS entirely" (commercially useless) but as **"1Q-compiled + MS-primitive"** — the production-aligned interpretation. The full SU(4) compilation (original options (b) + (c)) is academic-completeness work deferred to Phase 6y Track T-A1′.

### Sub-wave decomposition (lift/shift framing)

**T-A1.1 — Trapped-ion alphabet skeleton** (~100-200 LoC). Define `trappedIonGeneratingSet : GeneratingSet` with:
  - Word type `W := FreeGroup ((Fin n_ions) × Fin 2 ⊕ MSPrimitiveToken)` where `MSPrimitiveToken` encodes the MS(θ) gates at rational-π/N grid.
  - Representation `ρ_hom` mapping `(ion_i, j) ↦ <per-ion 1Q gate at index j on ion i>` and `MS_θ ↦ MSGateMat(θ)`.
  - Generator set: H_SU and T_SU lifted per-ion + MS primitives.

The substrate skeleton already shipped in Phase 6x first session (`TrappedIonAlphabet.lean`) — MS matrix + grid + identity sanity-checks.

**T-A1.2 — Per-ion 1Q-compilation reduction** (~100-200 LoC). Show that any unitary acting non-trivially on a single ion's 1Q subspace decomposes into a product of `H_SU` and `T_SU` operators on that ion via the Phase 6u Clifford+T substrate (`cliffordTGeneratingSet` directly applies). The reduction is essentially a re-indexing: each per-ion 1Q rotation compile-call invokes Phase 6u verbatim.

**T-A1.3 — ε₀-net at the per-ion level** (~30-50 LoC). Phase 6u Wave 3's ε₀-net composed with `trappedIonGeneratingSet`'s per-ion 1Q substructure. Existential (Classical.choose) or constructive (Phase 6x T-S′ finite-Finset cover) — either is acceptable per the trapped-ion lift/shift framing.

**T-A1.4 — Calibration via Phase 6u Wave 4b** (~30-50 LoC). Direct instantiation; no new analytic work.

**T-A1.5 — Bundled-strict headline** (~50-100 LoC). The per-ion-1Q-compile bundled-strict headline at `trappedIonGeneratingSet`. Statement form: for any U ∈ SU(2) (single-ion target) and ε ∈ (0, ε₀], the compiled trapped-ion word approximates U to error ≤ ε at length ≤ polylog(1/ε) — with the MS(θ) primitives passed through unchanged.

### Aggregate Track T-A1 effort (lift/shift framing)

~250-400 LoC across ~1-2 sessions (Phase 6x completion). The substrate skeleton is already shipped; the remaining work is the re-indexing + headline integration.

### Deferred to Phase 6y Track T-A1′ (academic completeness)

The full SU(4) compilation (where MS(θ) is in the discrete alphabet and the compiler decomposes any 2-qubit unitary into MS + 1Q sequences) requires the Phase 6y SU(d) substrate extension. ~600-1,100 LoC across 2-4 Phase 6y sessions.

### Audience and bundle absorption

**Audience**: industry quantum-compiler teams at Quantinuum, IonQ, AQT, Universal Quantum; trapped-ion-architecture-research community. The lift/shift framing addresses the per-ion 1Q compilation that production code needs verified; the full SU(4) academic-completeness ship (Phase 6y) addresses the verified-compiler-for-arbitrary-2-qubit-gates narrative.

**Bundle absorption**: D4 §9.8 + E1 (Paris-LKB polariton experimental letter cross-bridge — the trapped-ion and polariton communities share gate-set discretization concerns).

### Risk (lift/shift framing)

LOW. The lift/shift framing is mostly re-indexing of the Phase 6u Clifford+T substrate; no new analytic work.

---

## Track T-A2 detail — Clifford+CCZ alphabet substrate (FULL SU(8) → Phase 6y)

### Goal (Phase 6x scope after retrospective reframing)

Ship the **Clifford+CCZ alphabet substrate** at the matrix-definition level: `CCZ_mat : Matrix (Fin 8) (Fin 8) ℂ` with explicit diagonal-entry verification (`CCZ_mat_apply_7_7 = -1`, `CCZ_mat_apply_diag_ne_7 = 1` for `i ≠ 7`). This is the in-scope deliverable for Phase 6x — already shipped in Phase 6x first session (`CliffordCCZAlphabet.lean`).

The **full SU(8) compilation** (`U ∈ SU(8) → Clifford+CCZ word with ε-error + polylog length`) is the academic-completeness work deferred to **Phase 6y Track T-A2′** because:

  - The Phase 6u SU(2)-targeted substrate does not directly compile arbitrary SU(8) unitaries.
  - The Phase 6y Track S (SU(d > 2) substrate extension) is the prerequisite for any SU(8) compilation ship.
  - Treating CCZ as a *primitive token* in Phase 6x (analogous to MS(θ) in T-A1 lift/shift) doesn't yield a non-trivial verified ship because Cliffords are EXACT (no SK approximation needed) — the SK compilation only kicks in when arbitrary SU(8) is the target.

### Phase 6x completion deliverables (this revised scope)

Already shipped in Phase 6x first session — no additional T-A2 work required at the Phase 6x scope:

  - `CCZ_mat` matrix definition.
  - `CCZ_mat_apply_7_7 : CCZ_mat ⟨7, _⟩ ⟨7, _⟩ = -1`.
  - `CCZ_mat_apply_diag_ne_7 : ∀ i, i ≠ ⟨7, _⟩ → CCZ_mat i i = 1`.

### Deferred to Phase 6y Track T-A2′ (academic completeness)

Per Phase 6y Roadmap §"Track T-A2′ detail":

  - SU(8) `GeneratingSet` instance consuming Phase 6y Track S substrate.
  - Clifford+CCZ closure-density at SU(8) (~400-700 LoC).
  - ε₀-net + calibration + bundled-strict headline at SU(8) (~300-600 LoC).

Aggregate Phase 6y T-A2′ effort: ~700-1,300 LoC across 3-5 Phase 6y sessions.

### Audience and bundle absorption

**Audience**: fault-tolerant-architecture researchers (Litinski, O'Gorman, Babbush, Beverland); magic-state-distillation researchers.

**Bundle absorption**: D4 §9.8 — multi-alphabet showcase. The Phase 6x in-scope ship adds CCZ as the substrate-level entry; the Phase 6y T-A2′ ship adds Clifford+CCZ as the full-compile entry.

### Risk

Phase 6x scope: LOW (already shipped).
Phase 6y T-A2′ scope: MEDIUM, addressed in Phase 6y Roadmap.

---

## Track M detail — Mathlib4 upstream contributions

### Goal

Extract three generic SU(2)-Lie-group / matrix-Lie-theory lemmas currently sitting inside the FKLW substrate to Mathlib4-upstream-PR-quality form. These are **Phase 6s Track 2 (community-citizenship)** style work — strengthening Mathlib4's coverage in ways that benefit the broader formal-methods community.

### M.1 — Generic BCH order-2 cubic bound

**Statement (to ship in Mathlib upstream form)**:

> *For any complex matrix Lie algebra `𝔤` with norm `‖·‖` and matrices `A, B ∈ 𝔤` with `‖A‖, ‖B‖ ≤ δ`, the BCH order-2 remainder satisfies*
> 
> *  `‖exp(A) · exp(B) · exp(−A) · exp(−B) − exp([A, B])‖ ≤ K_BCH · (‖A‖³ + ‖B‖³)`
> 
> *for an explicit constant `K_BCH`.*

**Current state**: shipped SU(2)-specific in `lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean` (the `fourfoldComm_norm_le` chain). The proof is generic at the technique level — it's just `exp`-power-series manipulation + commutator algebra. The SU(2) specialization is mostly type-restriction; the generalization to any matrix Lie algebra over ℂ should be a syntactic refactor (replace `Matrix (Fin 2) (Fin 2) ℂ` with `Matrix (Fin n) (Fin n) ℂ` or even `Matrix m m ℂ`).

**Work estimate**: ~200-400 LoC to extract, generalize, de-privatize, and add Mathlib-style docstrings + examples.

### M.2 — Generic density-from-Cartan-v4-witness lemma

**Statement (to ship in Mathlib upstream form)**:

> *Any closed subgroup `H` of a compact connected matrix Lie group `G` containing two ℝ-linearly-independent 1-parameter subgroups equals the whole group: `H = G`.*

**Current state**: shipped SU(2)-specific in `lean/SKEFTHawking/FKLW/CartanSubstrate.lean` (`CartanFinalStep_SU2_v4_holds`). The mathematical content is Cartan's closed-subgroup theorem specialized to compact connected groups; the SU(2) version uses BCH bracket closure (Phase 5 Step 13 substrate) + the 3-dim SU(2)-specific argument.

**Generalization path**: the technique extends to any compact connected matrix Lie group. For SU(d), the analog uses the same BCH chain + a d-dependent Cartan dimension count. For arbitrary compact connected matrix Lie group, the substrate is heavier (general Lie-algebra dimension count). Mathlib4 v4.29.1 has `Mathlib/Topology/Algebra/Group/Basic.lean` with `Subgroup.topologicalClosure` and related, but the substantive Cartan-theorem content is absent.

**Work estimate**: ~300-600 LoC to extract and ship at the SU(d) level. Full compact-connected-matrix-Lie-group version is a much larger lift (~1,000-2,000 LoC; deferred).

### M.3 — Three-direction-product strict differentiability

**Statement (already shipped)**:

> *For Banach spaces `E_1, E_2, E_3` and `F`, and a function `f : E_1 × E_2 × E_3 → F` that is `C¹` in each variable separately at zero with directional derivatives `D_1 f, D_2 f, D_3 f : F`, the three-direction product map satisfies `HasStrictFDerivAt` at zero with derivative `λ (x_1, x_2, x_3) → D_1 f · x_1 + D_2 f · x_2 + D_3 f · x_3`.*

**Current state**: shipped as `private lemma threeDirProduct_hasStrictFDerivAt_zero` in `SU2BCHBracketClosure.lean:910`. Used at line 1239 of the same file. The technique is generic — the SU(2)-specific context only enters through the input space's matrix typing.

**Work assessment**: per the Phase 6u Strategic Positioning user-note, this one "may already be complete" — i.e., the technique is generic, the only Mathlib-upstream work is de-privatizing + generalizing the typed (matrix Lie group) input space to a Banach-space input space. If Mathlib4 already has the general `HasStrictFDerivAt` 3-direction product (let me check), the SU(2) usage is a specialization and no upstream work is needed. If Mathlib4 doesn't have it, the extraction is ~100-200 LoC.

**Sub-wave M.3.0**: investigate Mathlib4 v4.29.1 coverage. Search for `HasStrictFDerivAt.prod` chains, `ContinuousLinearMap` 3-direction product lemmas. If existing coverage suffices, M.3 is **NO-OP** — the SU(2)-specific use is correct, just a private specialization of an upstream API. If not, ship the extraction (~100-200 LoC).

### Aggregate Track M effort

~600-1,200 LoC across M.1 + M.2 + M.3 (with M.3 plausibly NO-OP after investigation). Each PR is independently shippable.

### Audience

Mathlib4 working groups on Lie theory / matrix exponentials / topological groups; the broader formal-methods quantum-computing community (these lemmas enable other groups to do similar verified-quantum-compiler work without re-deriving SU(d) substrate).

### Risk

LOW. The lemmas are well-understood mathematically; the work is extract + generalize + upstream-format. The main risk is Mathlib stylistic-review iteration cost (typical for Mathlib PRs).

---

## Cross-cutting work

### Constructive ε₀-net follow-on (deferred from Phase 6u Wave 3)

Phase 6u Wave 3 shipped the **existential** form (Classical.choose extraction from density). The **constructive** finite-Finset coverage form (originally documented but deferred per `GenericEpsilonNet.lean` Status note) is per-alphabet:

  - For Clifford+T: Ross-Selinger 2014 symbolic ℤ[ω][1/√2] discharge gives a constructive ε₀-net via the algebraic-number-theoretic structure of Clifford+T words.
  - For Fibonacci: existing `FibonacciEpsilonNet.lean` is also existential; constructive Path-A enumeration per Phase 6t Wave 3 user lock-in §13.2.

Phase 6x can pick up the constructive ε₀-net for Clifford+T as a substantive ship (~250-500 LoC) — moves the Track T-S compiler from `Classical.choose`-noncomputable to genuinely-runnable. Not blocking; deferred to per-alphabet engineering preference.

### Length-bound concrete-word coupling (CP2 RC2 from Phase 6u)

CP2 RC2 flagged that the length-bound conjunct in the Wave 6 / Track-T-S.5 headline references `skLength` (abstract recursion-depth length), not the concrete compiled `FreeGroup` word length. The tightened version — `(compile U ε).toWord.length ≤ skLength (skLevel_polylog ε)` chained with the existing bound — is **Mathlib-PR-quality follow-up** that affects all generating-set instances. Could be picked up in Phase 6x as Track M.4 if desired; flagged here for explicit visibility.

### Adversarial-review checkpoints

Per `BUNDLE_LIFT_PROCEDURE.md` Stage 13 hard gate, each Phase 6x track gets its own checkpoint:

  - **CP-B** — after Track T-B (Read-Rezayi instances).
  - **CP-A1** — after Track T-A1 (trapped-ion).
  - **CP-A2** — after Track T-A2 (Clifford+CCZ + SU(d) extension).
  - **CP-M** — after each Mathlib upstream PR is accepted (or after the project-side Lean ship if Mathlib review takes a while).

### Pipeline Invariants

- **#10 (no `maxHeartbeats`)**: RESPECTED throughout. The Phase 6u Wave 4b discharge pattern (extract `valid_branch_K_chain_le_K_compose_numeric` helper to top level rather than override the heartbeat budget) applies to Phase 6x — if any track's main theorem hits the heartbeat budget, decompose via top-level numerical helpers.
- **#15 (no new axioms without user sign-off)**: RESPECTED. Pivot rule explicit: if any track's closure-density witness requires substrate beyond Mathlib4 v4.29.1, YIELD for user sign-off.

---

## Cross-references

- **Phase 6u roadmap** (`docs/roadmaps/Phase6u_Roadmap.md`) — generic-substrate predecessor; the W1-W6 substrate that Phase 6x track instantiations inherit.
- **Phase 6u Implications** (`docs/stakeholder/Phase6u_Implications.md`) — accessible technical overview of what the Phase 6u substrate ships; useful for stakeholder positioning of Phase 6x tracks.
- **Phase 6u Strategic Positioning** (`docs/stakeholder/Phase6u_Strategic_Positioning.md`) — audience targeting + Mathlib upstream rationale (the basis for Phase 6x Track M).
- **Phase 6t roadmap** (`docs/roadmaps/Phase6t_Roadmap.md`) — Fibonacci-specific predecessor providing the "canonical first alphabet instance" template that Phase 6u generalized and Phase 6x replicates per alphabet.
- **Phase 6u Generic substrate**: `lean/SKEFTHawking/FKLW/Generic*.lean` (7 files) — the alphabet-agnostic chain that every Phase 6x track instantiation consumes.
- **Phase 6u Clifford+T instance**: `lean/SKEFTHawking/FKLW/CliffordT*.lean` (8 files) — the canonical 5-sub-wave template per Phase 6x track.
- **Bundle Readiness Heatmap** (`docs/BUNDLE_READINESS_HEATMAP.md`) — for tracking D4 §9.8 absorption status as Phase 6x tracks ship.
- **Phase 6u Roadmap** (`docs/roadmaps/Phase6u_Roadmap.md`) "Track T-A1/T-A2/T-B" rows — original re-slot decision documenting why these tracks did not fit Phase 6v / 6w scope (Phase 6v + 6w committed to other strategic content per the 2026-05-25 scope finalization).
