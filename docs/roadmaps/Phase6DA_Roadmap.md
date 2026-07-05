# Phase 6DA — Fine-Structure Constant: Determination-Chain Assumption Audit & Kernel-Checked Correction-Factor Map

**Status: PLANNED (authorized 2026-07-02; reframed 2026-07-04).** Opens the **new `6D*` thematic series** (theme: *dimensionless-constant determination-chain provenance & correction-factor mapping*), independent of the `6B*` (comp-chem/OQS → D10) and `6C*` (band-theory/metamaterials → D11) series and of the single-letter `6a/6b/6c`.

**Thesis (two intertwined deliverables).**
1. **A machine-checked audit of the assumption stack that determines α** — the two precision routes (atom-recoil and electron g−2) formalized as tagged dependency chains, every relation labelled `theorem` / `hypothesis` / `axiom` / `empirical-input` via the existing `ExtractDeps` + registry pipeline. The residue — the links that can only be *tagged*, not proven — is the precise map of where genuine theoretical/experimental corrections could still live.
2. **A kernel-checked *partial map* of the correction-factor parameter space** — for each place a correction could enter, either **kernel-verify a bound** on it or **kernel-refute** a principled *swath* of candidate corrections, with the un-excluded complement tagged as the live frontier. The golden ratio φ enters only as a **legible anchor point** subsumed by the closed-form swath — never as a foregrounded hypothesis (see §Framing).

Clean whitespace: no reproducible machine-checked assumption-audit of a measured fundamental constant's determination chain, and no kernel-checked exclusion of correction-factor swaths, exists in any prover.

> **A kernel no-go of a *principled swath* is a first-class deliverable.** This phase is *expected* to refute broad regions of the correction-factor space and to bound most assumption-gap corrections well below measurement precision. A clean partial map — principled swaths refuted, the live complement (the genuine open frontier) sharply localized — **is** the success condition, independent of whether any correction survives. A well-grounded null over a broad, honestly-defined region is the win; a strawman exclusion of one gerrymandered formula is not.

> **⚠️ GUARDRAIL — audit-and-map, do NOT attempt to *derive* α.** This phase does **not** try to derive α from first principles (an acknowledged open problem) and does **not** attempt a transcendence proof for α (out of substrate reach and not required). Its objects are the *provenance* of the measured value and a *partial map* of the correction space. **You can never kernel-exclude the whole space — α may be derivable; that is open.** Every swath no-go is explicitly *conditional* on its parametrization + constraints, and the complement is the tagged live frontier. Any wave drifting toward "we derived α" or "we proved α is/ isn't φ-related" is out of scope.

> **⚠️ GUARDRAIL — the swath-exclusion constraints (a `PRE_DECISIONS.md` entry; applied WITHOUT asking).** A candidate correction is inside an *excludable* swath when it fails at least one principled constraint, and a swath is worth a kernel no-go only when its exclusion follows from one: **(a)** it forces its factor with **no free parameter tuned to α**; **(b)** it must land within the **measurement uncertainty** of the required shift (LKB: 81 ppt ≈ 8.1×10⁻¹¹ relative; Berkeley-Cs: 2.0×10⁻¹⁰), *not* a ~0.3% gap; **(c)** it must **survive the running** — a scale-independent number can match α⁻¹ at one renormalization point at most (α⁻¹(0) ≈ 137.036 vs α⁻¹(M_Z) ≈ 128); **(d)** it must live in the **right domain/gauge** (α is the U(1) EM coupling; an analog effective coupling with no U(1) is not α). A theorem that merely places a target inside its own error band is a self-discharging tautology (forbidden by preemptive-strengthening) — a swath exclusion must show the miss **exceeds** the bar, or the constraint is **structurally** violated.

> **⚠️ GUARDRAIL — relevance filter for upstream links (a `PRE_DECISIONS.md` entry).** Audit an upstream link (R∞, mass ratios, h, the electrical chain) **only if** its uncertainty or structural assumptions propagate into an α determination at ~10⁻¹⁰ relative, **or** it places an un-machine-checked theoretical relation on the critical path. The wider metrology audit is **deferred** — targeted over broad.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`. Pre-decisions: `docs/dev-loops/PRE_DECISIONS.md` (the swath-exclusion constraints + relevance filter above land there at W0).
> 2. **Read this roadmap end-to-end** before claiming a wave. Each wave's **Bricks** names *exact* project declarations (verified 2026-07-02) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — no publication/bundle target assigned (deferred; operator's call).** This phase produces Lean substrate + a tagged audit graph, **not** paper-shaped output — so no bundle is assigned and none gates any wave. Invariant #14 (bundle assignment) applies only *if/when* the work is later taken toward a paper, as a separate operator decision — not made here. Do **not** create `papers/*` scaffolding, a `PAPER_STRATEGY` row, or claim a bundle. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct · falsifiable `norm_num` content · cross-module bridge · no trivial/tautological discharge · not-defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`; **zero `sorry`/`native_decide` regression** (`lean_verify`) — project is currently **0 sorry / 0 axioms**, so any new project-local `axiom` is a regression needing **explicit user sign-off + discharge plan (Invariant #15)**. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** all numeric bounds follow the **`NumericalBounds` rational-enclosure + `norm_num`** pattern — **not** `native_decide` (the grandfathered `QSqrt5` native_decide φ-lemmas are *cited*, not extended). See guardrails above.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** the *mathematics* (recoil algebra, series-remainder bounds, swath-exclusion arithmetic, the dispersion identity) is Lean-verified; the *physical inputs and identifications* (measured values; which relation each team uses; the QED coefficient-growth bound; the HVP dispersion integral) stay literature-cited in the module headers and, where unproven, live as tiered `HYPOTHESIS_REGISTRY` entries. Wave sizing ≈ one `/goal` (≤ ~5M tokens).

**Framing (keep every wave on-frame).** Precision-metrology assumption audit + formal methods. φ enters *only* as a legible anchor point subsumed by the closed-form swath — never foregrounded as a hypothesis; the specific closed-form correction-factor claims are the *subject of exclusion*, not endorsement. The repo separately proves φ arises for a genuine structural reason (a Fibonacci quantum dimension forced by `τ⊗τ = 1+τ`) that is **unrelated to α** — that contrast is the honest use of φ.

---

## What the kernel proves vs. what stays cited

Be precise about what the Lean kernel actually establishes, so no reader can read an epistemic overclaim into it. (Complements the two-layer-honesty note above.)

- **Kernel-verified (Lean, kernel-pure):** (i) the recoil α²-relation as an **exact** algebraic identity among {α, R∞, mass ratios, h/m_X}; (ii) the g−2 asymptotic-series **truncation-remainder bound** — *conditional on* an imported coefficient-growth bound — showing the truncation correction sits far below measurement precision; (iii) the **negligibility bounds** for a_weak (and, at the electron's precision, the bracketing of a_had); (iv) the α↔a_e **inversion**, conditional on the tagged hypotheses; (v) the recoil-vs-recoil (>5σ) and recoil-vs-g−2 (2.5σ) **tensions**; (vi) a **finite, pre-registered complexity-bounded closed-form family** — none of whose members land within u(α⁻¹); (vii) the **mechanism-swath** exclusions (scale-independent → fails running; wrong-domain → no U(1)); (viii) the general **Kramers–Kronig / dispersion** identity and its two instantiations.
- **Stays literature-cited / registry-tagged (not kernel content):** the measured values (α⁻¹, R∞, h/m, g/2); the **QED coefficient-growth bound** (imported unless a rigorous large-order bound is itself formalized — see UNKNOWNs); the **HVP dispersion-integral** value (dispersive vs lattice, currently contested); the physical identifications (that the measured frequency *is* h/m_X; that QED is the operative theory); and the **information-theoretic non-predictivity frame** below — an epistemics argument (a closed-form matching α⁻¹ to n bits while costing ≥ n bits to specify has compressed nothing), *not* a physics theorem.
- **Explicitly NOT proven (guardrail against overreach):** that α is or isn't derivable (open); that φ *cannot* relate to α (we exclude bounded swaths + specific claims — **not** an impossibility theorem); that the correction-factor space is empty (it is only *partially* mapped); any transcendence claim about α.

**Novelty, stated precisely:** the first reproducible machine-checked audit of a measured constant's determination-chain assumptions, plus a kernel-checked *partial map* of its correction-factor space (principled swaths refuted, live complement tagged). The method is reusable for any dimensionless constant; α is the demonstration.

**Substrate (verified 2026-07-02 — repo clone read + lean source + `NumericalBounds` header):**
- **Reuse (exists — cite, do not re-prove):**
  - `SKEFTHawking.QuantumNetwork.NumericalBounds.expNeg_enclosure` / `expNeg046_tight` — **the kernel-pure rational two-sided enclosure exemplar** (header: *"no `native_decide`, no external"*; brackets from Mathlib exp lemmas + `norm_num`). This is the pattern all α numeric bounds + the finite family sweep follow.
  - `SKEFTHawking.QSqrt5.phi` / `phi_sq : phi * phi = phi + 1`; `SKEFTHawking.QLevel3` (`d₁ = t/s = φ`); `SKEFTHawking.FKLW.FibSU2Rep` (`φ²=φ+1`, `φInv⁵<1`) — φ as a **genuinely derived** Fibonacci quantum dimension, *unrelated to α*. Cited as the honest contrast anchor, and as a source of exact φ-arithmetic for the closed-form family.
  - `SKEFTHawking.CGLTransform` (Crossley–Glorioso–Liu FDR, even-ω/odd-ω decomposition), `SKEFTHawking.SKDoubling` (SK doubling + dynamical KMS) — analyticity/FDR backbone; the same dispersion structure that underlies the QED vacuum-polarization correction (W3).
  - PhysLib CPTP/Choi/Kraus (open-system machinery); Mathlib field/interval arithmetic + complex analysis.
  - Registry pipeline: `HYPOTHESIS_REGISTRY` (constants.py, single source of truth; tiers headline/external_boundary/discharge_future/local; `dependent_theorems` → `ASSUMES` edges); `PARAMETER_PROVENANCE`; `citations.py`; `ExtractDeps.lean` + `build_graph.py` (the tagged dependency graph is **emergent** — it appears on the next `build_graph.py` run, no manual construction).
- **Absent → build:** no α determination-chain formalization anywhere; no recoil-route or g−2-route relation as a Lean statement; no general Kramers–Kronig/dispersion lemma; no complexity-bounded closed-form-exclusion family. Mathlib `goldenRatio` exists (`Mathlib.Data.Real.GoldenRatio` — INFERRED, confirm at Stage 2) but is not wired to the project φ; no transcendence machinery (not needed — see guardrail).
- **New content:** the recoil α²-relation; the a_e QED-series structural relation with its asymptoticity/HVP assumptions as explicit tracked hypotheses + the truncation-remainder bound; the general dispersion/KK lemma + two instantiations; the closed-form family exclusion; the mechanism-swath exclusions; the assumption-gap bounds; the synthesis + map.

**Publication target:** **DEFERRED — none assigned.** Not calling the publication shot on this phase: it produces Lean substrate + a tagged audit graph, and whether/where any of it becomes paper-shaped output is an explicit later operator decision (no bundle, no `PAPER_STRATEGY` row, no `papers/*` scaffolding here). Method-first framing is noted for context only — *if* later published, the defensible content is the reproducible assumption-audit + correction-factor-map methodology, demonstrated on α — but that disposition is not made now.

**Disposition of the seed deep-research doc's "Paths" (grounded against actual substrate):**
- **Recoil + g−2 determination-chain audit (W1, W2)** — the substantive core the seed doc's assumption table pointed at; promoted to the spine.
- **Dispersion / Kramers–Kronig structure (W3)** — the seed doc's "deepest connection." Held to rigor it yields *reusable substrate* (a KK lemma the project lacks) and the genuine bridge: the HVP running-of-α correction and the repo's dissipative machinery share one dispersion structure. Real physics; **not** a claim that dissipation produces α.
- **Correction-factor swath map (W4)** — generalizes the seed doc's "algebraic-number exclusion" from named formulas to principled swaths (closed-form/complexity, mechanism, assumption-gap). φ subsumed.
- **α_eff RG fixed-point "with golden structure" — ELIMINATED.** No RG-flow / β-function module exists in the substrate; the "fixed point exhibits φ" claim has no toehold and no *forced* φ. Documented as an honest structural NO-GO in W5's coda.

---

## Wave 0 — Scaffold + pre-decisions + registry seed  *(serial; critical-path root; wt-main)*
- **Goal:** land the phase's trust-boundary scaffolding so the parallel tracks fan out without registry-write contention. **Verdict: reachable.**
- **Why:** the only hard serialization point. `constants.py` / `formulas.py` / `citations.py` are canonical shared files; concurrent writes collide. Seed all registries once, up front — the tagging convention already exists as the KG node/edge schema; W0 only *conforms* to it.
- **Bricks:** `HYPOTHESIS_REGISTRY`, `PARAMETER_PROVENANCE`, `CITATION_REGISTRY` (constants.py / citations.py); `PRE_DECISIONS.md`; `PAPER_STRATEGY.md`; research-scout / `Lit-Search/` provenance discipline.
- **Done (AC / `/goal` condition):**
  - [ ] Swath-exclusion constraints (a)-(d) + relevance filter landed as entries in `docs/dev-loops/PRE_DECISIONS.md` (Core keystones for this phase).
  - [ ] **Pre-registered closed-form family definition** landed in `PRE_DECISIONS.md` — the generator set + complexity measure fixed *before* proving, so W4's exclusion is a principled swath, not cherry-picked.
  - [ ] **No bundle/publication target assigned** — publication disposition explicitly deferred (operator's call); no `PAPER_STRATEGY` row, no `papers/*` scaffolding. Invariant #14 applies only if the work is later taken toward a paper.
  - [ ] α **authoritative** primary sources filed under `Lit-Search/Phase-6DA/` with DOIs + provenance headers and registered in `CITATION_REGISTRY` as verified `PrimarySource` nodes (all four verified against primary sources 2026-07-02 — see §Citation provenance):
    - **CODATA 2022** (Mohr, Newell, Taylor, Tiesinga): α⁻¹ = 137.035999177(21), α = 7.2973525643(11)×10⁻³, RSU 1.5×10⁻¹⁰. *J. Phys. Chem. Ref. Data* **54**, 033105 (2025) / *Rev. Mod. Phys.* **97**, 025002 (2025). [VERIFIED]
    - **LKB/Paris 2020** (Morel, Yao, Cladé, Guellati-Khélifa): α⁻¹ = 137.035999206(11), 81 ppt — **⁸⁷Rb** recoil; datum `h/m(⁸⁷Rb) = 4.59135925890(65)×10⁻⁹ m²/s`. *Nature* **588**, 61–65 (2020), DOI 10.1038/s41586-020-2964-7. [VERIFIED]
    - **Berkeley 2018** (Parker, Yu, Zhong, Estey, Müller): α⁻¹ = 137.035999046(27), 0.20 ppb — **¹³³Cs** recoil; datum `h/m(¹³³Cs) = 3.0023694721(12)×10⁻⁹ m²/s`. *Science* **360** (6385), 191–195 (2018), DOI 10.1126/science.aap7706, arXiv:1812.04130. [VERIFIED]
    - **Harvard 2023** (Fan, Myers, Sukra, Gabrielse): the **electron magnetic moment** g/2 = 1.00115965218059(13) [0.13 ppt]. *Phys. Rev. Lett.* **130**, 071801 (2023), DOI 10.1103/PhysRevLett.130.071801. **Note:** the α⁻¹ = 137.035999166(15) "from g−2" is a **QED-inferred** value (Kinoshita–Nio series), *not* a direct α measurement — registered as a **derived** node whose provenance runs through the Wave-2 tracked hypotheses, never as a direct empirical input. [VERIFIED]
  - [ ] **Tension facts registered correctly** (both verified from primary sources): the **2.5σ** tension is Berkeley-Cs-2018 vs the g−2/Penning-trap route; the **>5σ** disagreement is LKB-Rb-2020 vs Berkeley-Cs-2018 (recoil-vs-recoil). Do not conflate them.
  - [ ] **Closed-form correction-factor claims registered as claims-under-test, NOT authoritative sources** — any specific published formula (e.g. golden-angle / quartic expressions) is tagged `external_boundary` / claim-under-test (a subsumed point of W4's closed-form swath), never as a verified `PrimarySource`/physics.
  - [ ] α inputs seeded as `Parameter` nodes with `verification` status + `SOURCED_FROM` edges; empty `Hypothesis` stubs reserved for the chain-audit residue.
  - [ ] `validate.py --check parameter_provenance` (CHECK 15) green; `build_graph.py` shows the α source/parameter seed subgraph.
- **Contention note:** the ONLY wave that writes all three canonical registries. W1–W4 then write worktree-isolated Lean modules; their registry writes are sequenced through the lead per §Sequencing.

---

## Wave 1 — Recoil-route determination-chain audit  *(wt2; audit spine; critical path; fast clean win)*
- **Goal:** formalize the LKB/Berkeley recoil determination `α² = (2R∞/c)·(A_r(X)/A_r(e))·(h/m_X)` as a tagged chain — the relation is an *exact* algebraic identity (it is `R∞ ≡ α²m_e c/2h` unfolded), so the kinematic combination is a `theorem`; each factor is an `empirical-input` Parameter; the recoil systematics are tagged `Hypothesis`. **Verdict: reachable (fastest clean kernel win).**
- **Why:** the cleaner chain — a product of measured dimensionless ratios × an exact kinematic relation — builds the audit substrate + the enclosure-arithmetic muscle the g−2 route (W2) consumes, and yields a small, sharp hypothesis residue. Dependency-order-first ⇒ flywheel.
- **Bricks:** W0 α parameters; `NumericalBounds` enclosure pattern (dimensionless-ratio product bounds); `HYPOTHESIS_REGISTRY` tiering; `ExtractDeps`/`build_graph` (auto-tag).
- **Done (AC / `/goal` condition):**
  - [ ] `RecoilChain.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), **no `native_decide`**, no new axiom.
  - [ ] `recoil_alpha_sq_relation`: the α²-product stated as an **exact identity** with each input an explicit `Parameter` (R∞, A_r(Cs/Rb), A_r(e), h/m) carrying provenance, and the kinematic combination discharged to `theorem`.
  - [ ] The photon-recoil / Bloch-oscillation identification, the higher-order recoil corrections, and the R∞ import registered as tiered `HYPOTHESIS_REGISTRY` entries where not machine-checked (relevance-filter-gated); `render_tracked_hypotheses --check` green.
  - [ ] **`recoil_measurements_in_tension` (headline audit fact):** `|α⁻¹(LKB-Rb-2020) − α⁻¹(Berkeley-Cs-2018)| > 5·√(u_LKB² + u_Cs²)` — the two best recoil determinations disagree at **5.49σ** (kernel-pure `norm_num` on the published rationals: 1.60×10⁻⁷ split vs 2.92×10⁻⁸ combined σ). **Not** a within-own-band tautology (it asserts the miss *exceeds* 5σ — the falsifiable direction).
  - [ ] `build_graph.py` shows the recoil subgraph with every node tagged (Parameter/Formula/LeanTheorem/Hypothesis/PrimarySource); `graph_integrity` clean.
- **Verdict:** audit output — the tagged recoil subgraph; a small hypothesis residue (route is kinematic); the machine-checked >5σ experimental tension.

---

## Wave 2 — g−2-route determination-chain audit  *(wt2; audit spine; depends on W1)*
- **Goal:** formalize `a_e = (g−2)/2 = Σ_n C_{2n}(α/π)ⁿ + a_had + a_weak` with the QED series' **asymptoticity/truncation** and the **hadronic** contribution as explicit tracked hypotheses, and **kernel-bound the truncation remainder** — the theoretically-loaded route where any real correction channel would live. **Verdict: reachable (structural — not all diagrams).**
- **Why:** this is where the un-machine-checked *theoretical* assumptions concentrate (asymptotic series, scheme dependence, HVP dispersion integral). The truncation-remainder bound turns the "the series is only asymptotic" worry into a machine-checked statement: given a coefficient-growth bound, the remainder after 5 loops ≈ 10⁻¹⁶ ≪ the ~10⁻¹² precision — i.e. **kernel-refute "series non-convergence is a loophole for a large correction."**
- **Bricks:** W1 substrate + `NumericalBounds`; `HYPOTHESIS_REGISTRY` (headline tier for asymptoticity); Aoyama–Kinoshita–Nio coefficient values + a citable large-order growth bound as provenance-carrying Parameters/Hypotheses.
- **Done (AC / `/goal` condition):**
  - [ ] `G2Chain.lean` builds clean — 0 sorry, kernel-pure, no `native_decide`, no new axiom.
  - [ ] `ae_qed_series_structural`: the series form stated with the **truncation/asymptoticity** assumption an explicit **headline-tier** `Hypothesis` (a published-value headline rides on it); `C₂, C₄, …` as `Parameter` nodes with uncertainties + provenance; `a_had` flagged (relevance-filter: it propagates at ≥10⁻¹⁰ for the electron).
  - [ ] `ae_truncation_remainder_bounded`: **conditional on** an imported coefficient-growth bound, the 5-loop truncation remainder is `< 10⁻¹⁵` (rational enclosure + `norm_num`), i.e. below the measurement precision — the swath "corrections >10⁻¹⁵ from series truncation" is refuted. The coefficient-growth bound is an explicit `ASSUMES` edge (headline tier).
  - [ ] `a_weak` (and the electron `a_had` bracket) discharged to a negligibility/enclosure bound where it sits below threshold; `a_had` value tagged as the dispersive-vs-lattice `Hypothesis`.
  - [ ] The α↔a_e inversion discharged to `theorem` conditional on the tracked hypotheses (explicit `ASSUMES` edges).
  - [ ] `build_graph.py` shows the g−2 subgraph tagged; the hypothesis-tagged links enumerated.
- **Verdict:** **NEEDS-MONITORING** on the asymptoticity + HVP links — *genuine open theoretical assumptions*, not woo; flagging them precisely is the audit's value. Sync gate: starts only after W1 lands on main (ff-only).

---

## Wave 3 — Dispersion / Kramers–Kronig structure  *(wt3; substrate bridge; parallel after W0)*
- **Goal:** prove one general **dispersion/analyticity lemma** (causality → analyticity → Re↔Im via Kramers–Kronig) and instantiate it on **both** the CGL-FDR even/odd-ω structure **and** a vacuum-polarization-shaped self-energy — showing the HVP running-of-α correction (W2) and the repo's dissipative machinery are two faces of one theorem. **Verdict: reachable (reusable public substrate).**
- **Why:** held to rigor this yields *reusable substrate* the project lacks (a KK lemma) **and** the genuine structural bridge behind the g−2/HVP audit. Honest scoping: the analyticity math is verified; the physical identification is literature-cited. This is real substrate physics, not an "analogy for α."
- **Bricks:** `CGLTransform` (FDR even/odd-ω); `SKDoubling` (KMS); PhysLib CPTP/Choi/Kraus; Mathlib complex-analysis (Hilbert-transform/Cauchy-integral primitives — confirm availability at Stage 2; **if absent at the pin, build them in-tree as Mathlib-grade, kernel-pure infrastructure — expected/authorized work, *not* a de-scope trigger**).
- **Done (AC / `/goal` condition):**
  - [ ] `KKDispersion.lean` builds clean — 0 sorry, kernel-pure, no `native_decide`, no new axiom.
  - [ ] `kramersKronig_dispersion`: the general Re↔Im dispersion relation, proven.
  - [ ] Two instantiations: `cglFDR_is_dispersion` (on the CGL even/odd-ω decomposition) and `vacuumPol_is_dispersion` (on a vacuum-polarization-shaped Π) — establishing the shared analyticity structure that carries the W2 HVP correction.
  - [ ] Module header states two-layer honesty explicitly (verified math vs cited physical identification).
- **Verdict:** **reusable substrate** — a KK lemma the project lacks + the honest structural bridge; does **not** bridge to α alone. Logically dependency-free after W0 (reads CGL/SK/PhysLib + W0 only) — but subject to the ≤2-slot concurrency cap (see §Sequencing).

---

## Wave 4 — Correction-factor swath map  *(wt1; depends on W1+W2 for the assumption-gap axis)*
- **Goal:** map the correction-factor parameter space along three axes and kernel-refute the principled swaths, tagging the live complement. **Verdict: reachable (a partial map, honestly bounded).**
- **Why:** the payoff — the correction search is now *bounded* to principled swaths, not "any plausible mechanism." φ is the anchor point that sits in the closed-form + mechanism swaths and is subsumed.
- **Bricks:** W1/W2 `HYPOTHESIS_REGISTRY` entries + tagged subgraphs; the pre-registered family (W0); `NumericalBounds`; `QSqrt5`/`FKLW` φ-arithmetic; `phi_forced_by_fibonacci_fusion` (the honest φ contrast).
- **Done (AC / `/goal` condition):**
  - [ ] `CorrectionFactorMap.lean` builds clean — 0 sorry, kernel-pure, no `native_decide`, no new axiom.
  - [ ] **Closed-form / complexity axis — `closed_form_family_excluded`:** the **pre-registered** finite complexity-bounded family (generator set + tree-size ≤ K, fixed at W0) — **no member** lands within u(α⁻¹) of CODATA. Push for the **largest kernel-pure K** via a structured rational-enclosure decomposition (no `maxHeartbeats`); the reusable finite-family-exclusion lemma is itself a methodological deliverable. Size/decomposition determined at Stage 2 (see UNKNOWNs). The information-theoretic non-predictivity **frame** (matching to n bits at description-length ≥ n bits is vacuous) is stated in the module header as the epistemic argument for why K near the precision's information content is the natural boundary — labelled a frame, **not** a kernel theorem.
  - [ ] **Mechanism axis:** `correction_scale_independent_excluded` — a fixed number cannot match α⁻¹ at both q²=0 (137.036) and M_Z (≈128), margin ≈ 9 ≫ 10⁴·u (kernel `norm_num`; explicit cited scale-independence premise, non-tautological); plus a documented structural exclusion of wrong-domain (no-U(1)) and free-parameter-tuned corrections (constraints (a),(d)).
  - [ ] **Assumption-gap axis:** each idealization's correction carries a verified upper bound (reusing W1/W2 results) — a swath exclusion ("no correction > X from this gap"); the un-excluded complement (HVP integral, coefficient-growth bound, the >5σ experimental split) is tagged as the live frontier.
  - [ ] **The honest partiality statement** recorded: excluded swaths + live complement; the space is *partially* mapped, not closed.
- **Verdict:** a kernel-checked **partial map** — principled swaths refuted (closed-form family, scale-independent, wrong-domain), the live complement (asymptoticity, HVP, experimental tension) carried forward as **NEEDS-MONITORING**. Sync gate: needs W1 + W2 on main.

---

## Wave 5 — Synthesis + correction-factor map writeup  *(serial; critical-path close; wt-main)*
- **Goal:** a synthesis module + stakeholder note tying the findings into the assumption-audit + the correction-factor partial map. **Verdict: reachable.**
- **Bricks:** all prior waves; `provenance_dashboard` (Trace/Impact on the α subgraph); stakeholder-doc discipline.
- **Done (AC / `/goal` condition):**
  - [ ] `AlphaDeterminationSynthesis.lean` builds clean — 0 sorry, kernel-pure, no new axiom.
  - [ ] Synthesis records the findings: (1) the α determination-chain **dependency graph** with every node tagged (theorem/hypothesis/axiom/empirical-input); (2) the recoil route as **exact** algebra + tagged empirical residue; (3) the g−2 route as `theorem` **conditional on** the asymptoticity + HVP hypotheses, with the truncation-remainder bound machine-checked; (4) the correction-factor **partial map** — principled swaths refuted (closed-form family, scale-independent, wrong-domain), φ subsumed as the anchor; (5) the **live frontier localized** to the HVP dispersion integral, the QED coefficient-growth bound, and the **>5σ recoil-vs-recoil experimental tension** (`recoil_measurements_in_tension`) — the real open problem is experimental + a few genuine theoretical assumptions, not closed-form coincidence; (6) the α_eff-RG-fixed-point "with golden structure" **ELIMINATED** (no RG module; no forced φ) — honest structural NO-GO.
  - [ ] `docs/stakeholder/Phase6DA_*.md` non-technical note (neutral metrology + formal-methods framing); counts + Inventory refreshed; `validate.py` green; roadmap status → shipped.

---

## Sequencing & parallelism (3 worktrees)

**Critical path (serial):** `W0 → (W1 → W2) → W4 → W5`.

**Track fan-out after W0** *(logical dependencies; see the concurrency cap below):*
- **wt2 (audit spine):** W1 → W2.
- **wt1 (correction map):** W4 (after W1+W2).
- **wt3 (dispersion substrate):** W3 (logically dependency-free after W0).

**⚠️ Concurrency cap (operational — hard):** at most **2** Lean slots active at once. 3+ concurrent slot LSP+build stacks exhaust the macOS file table (ENFILE; memory `feedback_parallel_slot_concurrency_enfile`). So although W1/W3/W4 are *logically* independent, **run at most two slots simultaneously** — keep wt2 (the W1→W2 critical-path spine) resident and alternate the second slot between {wt3:W3, wt1:W4}; workers stay LSP-only, the lead builds on main.

**Contention map (grounded in the canonical-file invariants):**
- **Serialize (lead-sequenced writes to the three canonical shared files):** W0 (all three); the *registry additions* of W1/W2 (new `Parameter`/`Hypothesis` in `constants.py`, new `Formula` in `formulas.py`) and W4 (any new `formulas.py` entry). The lead merges these ff-only in a fixed order (W0 → W1 params → W2 params → W4 entries) to avoid `constants.py`/`formulas.py` collisions.
- **No contention (worktree-isolated):** every new `lean/SKEFTHawking/*.lean` module — `RecoilChain.lean` + `G2Chain.lean` (wt2), `KKDispersion.lean` (wt3), `CorrectionFactorMap.lean` (wt1), `AlphaDeterminationSynthesis.lean` (wt-main). Each slot builds against its COW-cloned `.lake`; the lead syncs slot source to main with `git -C .claude/worktrees/wtN merge --ff-only main` before each dependent wave.

**Sync gates:** W2 ⟸ W1 on main. W4 ⟸ W1+W2 on main. W5 ⟸ all. W3 gated only by W0.

---

## Phase Definition of Done (`/goal` exit — every wave AC green, then:)
`lake build` + `ExtractDeps` clean; `validate.py` green (incl. CHECK 15 provenance, CHECK 16 graph integrity, `tracked_hypotheses_fresh`); counts + Inventory refreshed; root module imports the new modules; preemptive-strengthening post-wave audit done; **decisive success recorded** — the α determination-chain graph fully tagged **and** the correction-factor space partially mapped (principled swaths kernel-refuted, live complement sharply localized). Roadmap status updated. **(No publication/bundle disposition — deliberately deferred.)**

**Decisive success:** the tagged α-determination graph exists + the recoil route is exact + the g−2 route is conditional-on-tagged with the truncation-remainder bound machine-checked + the correction-factor partial map (swaths refuted, complement tagged) exists — regardless of whether any correction survives.
**Decisive failure (only):** the substrate cannot express/tag the α relations at all — unlikely given `NumericalBounds` + the number-field substrate. **A clean partial map with everything real still open is NOT failure; it is the expected, valuable outcome.**

---

## Open UNKNOWNs (resolve at Stage 2, before the wave they gate)
- **QED coefficient-growth bound (W2):** whether any rigorous large-order bound on the QED series coefficients is itself kernel-provable, or must be imported as a citable `Hypothesis` (headline tier). Default: import + kernel-verify the *downstream* remainder arithmetic. Confirm the citable bound (renormalon/large-order literature) at Stage 2.
- **Largest kernel-pure closed-form family (W4):** the sweep size + structured rational-enclosure decomposition that stays kernel-pure **without `maxHeartbeats`** (the reusable finite-family-exclusion lemma is itself a deliverable). Fix the pre-registered family definition at W0; determine the feasible bound + decomposition at Stage 2 before claiming `closed_form_family_excluded`.
- **Mathlib complex-analysis primitives for the KK lemma (W3):** Hilbert transform / Cauchy principal value at the pin — UNKNOWN; **if thin, W3 builds the missing primitives in-tree (Mathlib-grade, kernel-pure) — expected/authorized work, not a de-scope trigger.** The continuum integral is the target; a finite/rational dispersion-sum form is a last resort only. May carry the **largest in-tree analytic build** of the phase — surface its scope up front.
- Mathlib `goldenRatio` (`Mathlib.Data.Real.GoldenRatio`) availability at pin `5e932f97` — INFERRED; if absent, use the project `QSqrt5.phi` throughout (W4). Confirm via `lean_file_outline`.
- **Publication disposition is deliberately deferred** — no bundle target, and this is *not* a gate on any wave. If the audit is later taken toward a paper, bundle assignment (Invariant #14) + `PAPER_STRATEGY` happen then, as a separate operator decision.
