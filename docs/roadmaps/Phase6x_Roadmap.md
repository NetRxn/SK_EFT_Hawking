# Phase 6x: Additional-Alphabet Quantum-Compiler Instantiations + Mathlib Upstreaming

## Technical Roadmap — May 2026

*Prepared 2026-05-25 PM, following Phase 6u close (alphabet-independent generic Solovay-Kitaev substrate + Clifford+T instance shipped UNCONDITIONAL; commits `7ad8e55` through `137838e`; see `docs/roadmaps/Phase6u_Roadmap.md` for closure summary).*

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
| **Track T-B (Tier B)** | Read-Rezayi `SU(2)_k` instances for `k ∈ {5, 7}` — next-universal-anyon family beyond Fibonacci (`k = 3`). Highest substrate-reuse: ~80-90% of Phase 6t Fibonacci substrate transfers near-mechanically with σ_k generators replacing σ_Fib. Density via Niven-style on the per-`k` trace identity. | ⏳ NOT STARTED | D4 §9.8 (Read-Rezayi-extended multi-alphabet showcase) |
| **Track T-A1 (Tier A)** | Trapped-ion native gate set (Mølmer-Sørensen MS(θ) discretized + arbitrary 1Q rotations). Requires discretization layer + target-group decision (SU(2) restriction vs. SU(4) extension). | ⏳ NOT STARTED | D4 §9.8 + E1 polariton/trapped-ion cross-bridge |
| **Track T-A2 (Tier A)** | Clifford+CCZ at SU(8) for 3-qubit primitives. Requires extending Phase 6u's SU(2)-targeted substrate to SU(d>2) — substantial substrate extension. | ⏳ NOT STARTED | D4 §9.8 (higher-rank alphabet showcase, with caveat about SU(d) extension cost) |
| **Track M (Mathlib upstream)** | Three lemma extractions from FKLW substrate to Mathlib4 PR-quality: (M.1) Generic BCH order-2 cubic bound; (M.2) Generic Cartan v4 density-from-witness; (M.3) three-direction-product strict differentiability. | ⏳ NOT STARTED | (Mathlib4 upstream; no project-bundle absorption) |

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

## Track T-A1 detail — Trapped-ion native gate set

### Goal

Instantiate the Phase 6u substrate at the Quantinuum / IonQ native gate set: Mølmer-Sørensen MS(θ) + arbitrary 1Q rotations. This is the gate set actually used in production trapped-ion quantum hardware.

### Key distinction

Trapped-ion alphabets are **continuous-parameter** — MS(θ) is one gate per angle θ ∈ [0, 2π), and arbitrary 1Q rotations are parametrized by Euler angles. The Phase 6u `GeneratingSet` abstraction assumes a **finite** generating set; pre-processing is required.

### Sub-wave decomposition

**T-A1.1 — Discretization layer** (~200-400 LoC). Define a finite subset `MS_grid ⊂ {MS(θ) : θ ∈ rational multiples of π/N for some grid N}` plus a finite 1Q rotation grid. Prove that the discretized alphabet has closure dense in SU(2) (or in the relevant 2-qubit subspace — see T-A1.2 decision).

**T-A1.2 — Target group decision** (architectural). MS(θ) is intrinsically 2-qubit (acts on SU(4) for 2 ions). The Phase 6u substrate is currently SU(2)-targeted. Three options:
  - **(a)** Restrict to single-qubit compilations (use only the 1Q rotation part of the trapped-ion alphabet, ignore MS): trivial substrate reuse but **not commercially useful**.
  - **(b)** Extend Phase 6u substrate to SU(4): substantial Lie-algebra work (`𝔰𝔲(4)` is dim 15, not 3; v4 IFT 3-direction discharge becomes 15-direction).
  - **(c)** Decompose target SU(4) compilation into a sequence of 2-qubit subspaces: needs KAK decomposition / cosine-sine decomposition infrastructure. This is Mathlib-PR-quality lift (the underlying math — block-ZXZ + cosine-sine landscape — is public-domain; the substrate would need to be built out in Mathlib4).

**Recommended path**: Option (c) — KAK decomposition gives a clean factorization of any SU(4) into 2-qubit subspaces; the Phase 6u SU(2) substrate then applies subspace-by-subspace. Option (b) is the upstream-clean alternative if the KAK decomposition substrate proves heavy.

**T-A1.3-5 — Closure-density witness + ε₀-net + headline**. Pattern matches Phase 6u Track T-S, but conditioned on the T-A1.2 decision. If (a): standard SU(2) pattern. If (b) or (c): SU(4) or per-subspace SU(2) variants.

### Aggregate Track T-A1 effort

~1,200-2,500 LoC depending on T-A1.2 choice. (a) is ~300-500 LoC but commercially-useless; (b) or (c) is the substantive ship.

### Audience and bundle absorption

**Audience**: industry quantum-compiler teams at Quantinuum, IonQ, AQT, Universal Quantum; trapped-ion-architecture-research community.

**Bundle absorption**: D4 §9.8 + E1 (Paris-LKB polariton experimental letter cross-bridge — the trapped-ion and polariton communities share gate-set discretization concerns).

### Risk

MEDIUM. The discretization layer + target-group decision are substantive architectural calls. The pre-existing Phase 6u substrate gives strong leverage but the SU(d>2) extension (under option (b)) is non-trivial.

---

## Track T-A2 detail — Clifford+CCZ at SU(8) for 3-qubit primitives

### Goal

Instantiate at `G = {H ⊗ I ⊗ I, I ⊗ H ⊗ I, I ⊗ I ⊗ H, CCZ}` — the Clifford+CCZ universal gate set on 3 qubits. Target group is SU(8).

### Key challenge

Target group is SU(8), NOT SU(2). Substantial Phase 6u substrate extension required:

  - `𝔰𝔲(8)` is dim 63 (not 3). The Cartan v4 3-direction IFT discharge becomes a **63-direction discharge**. The Phase 6u Wave 1-2 substrate generalizes but is non-trivial work.
  - BCH cubic bound for SU(d) general `d`: Mathlib-PR-quality but currently absent. Phase 6x Track T-A2 substrate would need to ship this (overlap with Mathlib upstreaming Track M.1).
  - Y_h Lipschitz pullback for SU(d): generalizes from π/2 (SU(2) Bloch) to a `d`-dependent constant. Needs new derivation.

### Sub-wave decomposition

**T-A2.0 — SU(d) substrate extension** (~1,000-2,000 LoC). The substrate-extension prerequisite:
  - Generalize `tracelessSkewHermitian (Fin 2)` to `tracelessSkewHermitian (Fin d)` (~50 LoC; mostly available in Mathlib).
  - Generalize `SU2BCHBracketClosure` cubic bound to SU(d) (~400-700 LoC; this is the major substantive piece).
  - Generalize `CartanFinalStep_SU2_v4` to a multi-direction Cartan classification for SU(d) (~300-600 LoC; this is the **Mathlib-PR-quality** substrate piece that Track M.2 would parallel).
  - Generalize `Y_h` matrix-log Lipschitz from π/2 (SU(2)-Bloch) to d-dependent (~150-300 LoC).

**T-A2.1-5** (each ~50-200 LoC): standard alphabet instantiation pattern at SU(8) using the generalized substrate.

### Aggregate Track T-A2 effort

~2,000-4,000 LoC total (largest of the four Phase 6x tracks).

### Audience and bundle absorption

**Audience**: fault-tolerant-architecture researchers focused on 3-qubit primitives (Litinski, O'Gorman, Babbush, Beverland); magic-state-distillation researchers (the CCZ gate is the canonical "magic" gate for 3-qubit fault-tolerance schemes).

**Bundle absorption**: D4 §9.8 — higher-rank alphabet showcase with caveat documenting the SU(d) extension cost.

### Risk

HIGH. The T-A2.0 substrate extension is genuine multi-session work. Recommendation: dispatch as background agents heavily.

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
