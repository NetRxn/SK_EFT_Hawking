---
paper: phase6EA_substrate
reviewer: adversarial-reviewer
model: claude-opus-5
review_date: 2026-07-28T18:39:00Z
readiness_gates_version: 1
scope: substrate phase, no paper target (bundle D12 authorized, no on-disk draft)
---

# Adversarial Review — Phase 6EA (kernel-verified photodetection statistics)

## Summary

16 findings: **2 BLOCKER, 5 MAJOR, 5 MINOR, 4 INFO**. The *statement set itself is
substantively sound* — I found no vacuous theorem, no tautology masquerading as physics, no
empty quantifier, no `rfl`/`decide` body, and no floor whose RHS degenerates in its operating
regime; the Wave-3 freeze's headline vacuity flag (`shot_variance_eq_mean` vacuous if
`poissonVariance := N`) is genuinely discharged. Every deviation I was asked to audit (D10
sharp-vs-half, dropped `η ≤ 1`, dropped `0 ≤ η`) is a **verified strengthening**, confirmed by
compiling the derivations against the pinned toolchain. The blocking failures are in **prose
attached to the artifacts**: a shipped module docstring names a declaration that does not exist
and misdescribes it, and the governing roadmap still carries the exact PhysLib
`HypothesisTesting` claim its own binding Stage-2 sign-off prohibited and assigned to Stage 13.
Both are mechanical edits; neither touches a proof.

Method note: all Mathlib claims verified by reading `lean/.lake/packages/mathlib` at pin
`5e932f97`; all "is this hypothesis load-bearing / is this a wrapper" claims verified by
compiling scratch theorems with `lake env lean` (scratch file removed); all "is this docstring
reference backed by a call" claims verified against `lean/lean_deps.json` `value_deps_project`.

## Findings

### 1.1 — 🔴 BLOCKER — Module docstring names a non-existent declaration and misdescribes it

- **Gate:** LeanProofSubstance / bridge integrity (Stage-3a checklist #3)
- **Location:** `lean/SKEFTHawking/Detection/PoissonDiscrimination.lean:22-23`
- **Observed:** The "Main results" list reads
  `` `poisson_avgError_floor_equalRates` pins its constant to the falsifiable number `¼` ``.
  No such declaration exists. A scan of every backticked identifier in all three modules'
  doc-comment blocks against the project declaration graph returns exactly one unresolvable
  project name — this one.
- **Evidence:**
  - `grep -rn "poisson_avgError_floor_equalRates" lean/` → two hits, both prose:
    `Detection/PoissonDiscrimination.lean:23` and `docs/dev-loops/Phase6EA/LAB_NOTEBOOK.md:78`.
    Zero hits in `lean_deps.json` / `atlas_view.json`.
  - The shipped declaration is `SKEFTHawking.Detection.poisson_avgError_equalRates_eq_half`
    (`PoissonDiscrimination.lean:274`), type
    `… → avgAssignmentError (falseAlarm N δ) (missProb N δ) = 1 / 2`.
  - `LAB_NOTEBOOK.md:78-86` records the 2026-07-28 lead pass: "Repaired two module-docstring
    references left dangling by the drop." This one was not repaired.
- **Expected:** The bullet must name the live declaration and describe what it proves.
- **Why this is blocking, not cosmetic:** the description is not merely stale, it is *inverted*.
  `poisson_avgError_equalRates_eq_half` proves the equal-rate average error is **exactly ½** —
  i.e. that the Le Cam ¼ is *not* the truth and the floor is loose by exactly a factor of two.
  The docstring tells a reader the companion theorem "pins its constant to ¼". A reader of the
  headline module description of Wave 1 is handed a false statement about the substrate, in the
  shipped artifact that D12 will lift from.
- **Fix:** replace line 23 with
  `` `poisson_avgError_equalRates_eq_half` shows the equal-rate value is exactly `½`, so the
  universal `¼` floor is loose by exactly a factor of two at coincident rates ``; repair
  `LAB_NOTEBOOK.md:78` likewise.

### 1.2 — 🔴 BLOCKER — Roadmap still asserts the prohibited PhysLib `HypothesisTesting` claim

- **Gate:** NarrativeGrounding (first-claim / attribution)
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:25`, `:72`, `:152`
- **Observed:** three live assertions that Wave 3 consumes PhysLib's hypothesis-testing substrate:
  - L25: "**PhysLib seam (present, unused):** … `…ResourceTheory.HypothesisTesting`
    (`OptimalHypothesisRate`) — **Wave 3 connects the classical floors to this quantum
    hypothesis-testing substrate** rather than rebuilding it."
  - L72 (Wave-3 **Bricks**): "`Physlib.QuantumInfo.Finite.ResourceTheory.HypothesisTesting.OptimalHypothesisRate`
    **(first project consumption of this PhysLib substrate)**"
  - L152: "… requires reading `Physlib...HypothesisTesting` in full before freezing; **first
    project consumption of that module**."
- **Evidence:**
  - Dependency scan over all 254 `Detection.*` declarations in `lean/lean_deps.json`: **zero**
    reference to any `QuantumInfo.…HypothesisTesting` declaration. `ShotNoise.lean`'s import
    list is `PoissonDiscrimination`, `GaussianThreshold`, `QuantumNetwork.DiamondNormChoi`,
    `GrapheneNoiseFormula` — no PhysLib hypothesis-testing edge at all.
  - The roadmap's own binding block, 50 lines below L72, says the opposite and assigns the fix
    to this stage: L117-124, "**UNKNOWN-3 — RESOLVED; the roadmap's option (b) is TYPE-LEVEL
    IMPOSSIBLE** … ⚠ **Wave 3 must NOT be described as 'first project consumption of
    `HypothesisTesting`'** unless that consumption actually happens — **a claims-accuracy fix,
    per Stage 13.**" It is Stage 13. The fix was not made.
  - L72 additionally retains the module-path error that D2 (`Stage2StatementFreeze.md:887`)
    marked as a factual correction: `Physlib.QuantumInfo.…` vs the actual
    `QuantumInfo.Finite.ResourceTheory.HypothesisTesting` (PhysLib ships two `lean_lib`s;
    verified at `lean/.lake/packages/Physlib/QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean`).
  - `Phase6EA_Wave3_StatementFreeze.md:65-67` repeats the prohibition.
- **Expected:** The Wave-3 brick line names the project's own `QuantumNetwork` fidelity
  substrate (`sqrtFidelity`, `psdSqrt`, `traceNorm_posSemidef`, `posSemidef_eq_of_mul_self_eq`),
  with `OptimalHypothesisRate` listed only as a **settled-dead** route.
- **Fix:** edit L25 / L72 / L152. Three lines. L152 should also move out of "Open UNKNOWNs"
  (see 4.5).

### 2.1 — 🟡 MAJOR — `poissonMean_thinning`: the advertised bridge is not in the theorem

- **Gate:** LeanProofSubstance / bridge integrity (Stage-3a checklist #3)
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:388-395` (and the Main-results
  bullet at `:38`)
- **Observed:** the docstring makes three causal claims — "By `poisson_thinning` the thinned law
  of a `Poisson N` source is `Poisson (η·N)`…", "the *same* factor by which
  `shotPSD_plane_transfer` scales the one-sided shot PSD", and "**Without this the `η` in
  `shotPSD_plane_transfer` would be a bare algebraic parameter with no tie to the count
  model**". The theorem is `poissonMean (η * N) = (η : ℝ) * poissonMean N`, proved
  `rw [poissonMean_eq, poissonMean_eq, NNReal.coe_mul]`.
- **Evidence:** `lean_deps.json` `value_deps_project` for
  `SKEFTHawking.Detection.poissonMean_thinning` = `{poissonMean, poissonMean_eq}`. Neither
  `poisson_thinning` / `hasSum_poisson_thinning` nor `shotPSD` / `shotPSD_plane_transfer`
  appears in the statement, the proof, or the transitive value dependencies. After the two
  rewrites the residual content is `NNReal.coe_mul`. I reproduced the proof verbatim in a
  scratch theorem — it compiles with exactly those three rewrites.
- **Expected:** Per checklist #3, "every cross-reference in a docstring must be backed by a Lean
  call in the body." The claim "without this, `η` would be a bare algebraic parameter" is false
  as stated: this theorem creates no tie to `shotPSD_plane_transfer` whatsoever, so `η` there
  remains exactly as bare as before.
- **Fix (preferred):** restate so `poisson_thinning` is genuinely called — e.g. the mean of the
  *thinned* pmf, `∑' n, (∑' m, poissonPMFReal N m * (m.choose n) * η^n * (1-η)^(m-n)) * n
  = η * poissonMean N`, discharged by rewriting the inner `tsum` through `poisson_thinning`.
  **Fix (minimum):** delete the two causal sentences and the "one transfer factor, two carriers"
  claim from both the theorem docstring and the module Main-results bullet.

### 2.2 — 🟡 MAJOR — `shotGaussian_avgError_gt_leCam_floor`: the stated conclusion does not follow

- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:424-437`
- **Observed:** the docstring concludes "The floor is therefore a genuine *lower* bound with
  quantified slack, not an equality dressed as an inequality — which is what would make the
  whole floor family vacuous as a screen."
- **Evidence:** the theorem is
  `(3/2)·(¼·affinity(Poisson 1, Poisson 9)²) < avgAssignmentError (thrErr0 1 2 5) (thrErr1 9 2 5)`.
  The left side is the Le Cam floor for a **Poisson count experiment**; the right side is the
  average branch error of a **common-σ Gaussian threshold classifier**. No count rule
  `δ : ℕ → [0,1]` produces the error pair `(thrErr0 1 2 5, thrErr1 9 2 5)` — the Gaussian
  classifier is not an element of the quantifier `poisson_avgError_floor` ranges over. The
  inequality is therefore a comparison of two numbers belonging to two different experiments,
  and carries no information about whether the Poisson floor is attained by any Poisson rule.
  (Arithmetic checks out: LHS = 1.5·0.25·e⁻⁴ = 6.868e−3, RHS = Q(2) = 2.2750e−2; true ratio
  3.31, so the shipped `3/2` is limited by the crude rational bracket `Q(2) ≥ 1/125`, not by
  the physics.)
- **Also:** the physical framing is inconsistent with its own numbers — "the shot-limited width
  `σ = 2` (= `√N` at the decision level `N = 4`)" while the stated threshold is `t = 5`
  (√5 = 2.236), and the two hypotheses carry shot widths √1 = 1 and √9 = 3, neither of which is
  2. Asserting σ = 2 is "the shot-limited width" is a physical identification the module's own
  guardrail (`:44-50`) reserves to the consuming phase.
- **Expected:** either state what the witness actually shows ("at this operating point a
  shot-limited Gaussian threshold model errs by >3/2 of the Poisson Le Cam floor, so the floor
  does not already exclude this design point"), or point the slack claim at the theorem that
  does establish it — `poisson_avgError_equalRates_eq_half` (floor ¼, exact value ½, both over
  the *same* experiment).
- **Fix:** rewrite the two concluding sentences; delete or correct the "√N at the decision
  level N = 4" parenthetical.

### 2.3 — 🟡 MAJOR — Notebook INDEX records a retracted, non-existent Mathlib route as CHOSEN

- **Gate:** ProcessIntegrity / settled-fork hygiene
- **Location:** `docs/dev-loops/Phase6EA/LAB_NOTEBOOK_INDEX.md`, "⚖ Decisions & dead-ends"
- **Observed:** "2026-07-28 — W3 `psdSqrt_diagonal` via `Matrix.PosSemidef.sq_eq_sq_iff` →
  **CHOSEN**; do not unfold the project `cfc` … [W3 freeze §2.1 G7/G8]".
- **Evidence:** `Matrix.PosSemidef.sq_eq_sq_iff` **does not exist at pin `5e932f97`**. This is
  precisely the error `Phase6EA_Wave3_StatementFreeze.md:94-110` retracts ("⚠ CORRECTED
  2026-07-28 (my error; caught by the executing slot) … I treated a semantic-search hit as
  pin-verified grounding"). The shipped proof
  (`ShotNoise.lean:83-88`) uses `SKEFTHawking.QuantumNetwork.posSemidef_eq_of_mul_self_eq`
  (`DiamondNormChoi.lean:93`) — confirmed by `value_deps_project` for `psdSqrt_diagonal`.
  The INDEX's own header says "**Read this FIRST every session / post-compaction**", and the
  DECISIONS register is described as append-only — so a fresh-context session is steered to a
  non-existent lemma by the very artifact meant to prevent goldfish-reseeding.
- **Also stale in the same file:** `- [ ] **W3** … — 7 decls per Wave-3 freeze *(frozen;
  consumes W1 — NEXT)*` (W3 merged at `0531c786`; `ShotNoise` ships 28 declarations per the dep
  graph); "Commit state: main `c386610e`" (actual `0af953df`); Frontier "NEXT BRICK: dispatch
  6EA W3".
- **Fix:** correct the DECISIONS line to name `posSemidef_eq_of_mul_self_eq` and record
  `Matrix.PosSemidef.sq_eq_sq_iff` as **not-at-pin / retracted**; refresh the W3 checklist row,
  decl count, commit state, and Frontier.

### 2.4 — 🟡 MAJOR — No per-wave ruthless post-strengthening audit exists (Phase DoD item 3)

- **Gate:** ProcessIntegrity
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:93`; `docs/dev-loops/Phase6EA/LAB_NOTEBOOK.md`
- **Observed:** DoD item 3 requires "per-wave post-strengthening audits logged in the phase
  notebook." No such audit is logged for any wave. `LAB_NOTEBOOK.md`'s last entry is the W1+W2
  merge; **there is no Wave-3 entry at all**, despite W3 having merged (`0531c786`) plus a
  follow-up reconciliation commit (`25307cf6`).
- **Evidence:** both freezes explicitly disclaim their own tables as prospective only —
  `Stage2StatementFreeze.md:928` ("Run the ruthless post-wave strengthening audit (mandatory,
  §8 is the *prospective* pass only)") and `Wave3_StatementFreeze.md:259-264` ("**Two flags
  carried forward to the post-wave audit.** `shotPSD_plane_transfer` and `shot_variance_eq_mean`
  are the wave's tautology risks"). Neither flag has a recorded adjudication anywhere. (I
  adjudicated both in this review — see 3.3 and 4.1 — but that is a backstop, not the wave's
  own audit.)
- **Fix:** append a Wave-3 notebook entry and a per-wave audit block recording the disposition
  of every checklist-#1…#5 flag, including the two carried-forward tautology risks and the
  findings in this report.

### 2.5 — 🟡 MAJOR — "Clean whitespace" novelty claim is undocumented, overbroad, and the
substrate sweep missed Mathlib's own decision-theory module

- **Gate:** NarrativeGrounding (first-claim)
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:7` and `:24`
- **Observed (a) — no prior-art search is documented.** L7 claims "no theorem prover has a
  kernel-checked Poisson discrimination-floor family … packaged as reusable metrology
  substrate." No search of Isabelle/AFP, Coq (`infotheo`), Agda, or Mizar is recorded in the
  roadmap, either freeze, the notebook, or the notebook index.
- **Observed (b) — the claimed family includes something not shipped.** L7 enumerates the family
  as "(Bhattacharyya coefficient closed form, Le Cam two-point bound, dark-baseline exact
  optimum, **counting-test monotone-likelihood-ratio structure**)". The MLR item was explicitly
  demoted and not built (D3 / `Stage2StatementFreeze.md:542-563`: "it needs the sup over rules
  to be *attained*, i.e. an explicit monotone-likelihood-ratio argument … **not in the
  roadmap's brick list**"). The novelty claim therefore describes a package broader than what
  exists.
- **Observed (c) — sweep miss.** L24 says "Absent → build (confirmed by sweep 2026-07-27): …
  no Neyman–Pearson/likelihood-ratio structure; no Le Cam two-point bound. Mathlib carries the
  Poisson pmf … but none of the discrimination bounds." The sweep did not surface
  **`Mathlib.Probability.Decision.Risk`**, present at pin (`Defs.lean`, `Basic.lean`; Degenne &
  Luccioli, 2025): `ProbabilityTheory.avgRisk`, `bayesRisk` (infimum of average risk over **all
  randomized estimator kernels**), `minimaxRisk`, plus the data-processing inequalities
  `bayesRisk_le_bayesRisk_comp` / `bayesRisk_le_bayesRisk_map`. That is exactly the
  decision-theoretic scaffold that `IsCountRule` + `falseAlarm` + `missProb` +
  `avgAssignmentError` re-invents at 0-1 loss with a two-point prior.
- **What I verified in the other direction (the claim's core survives):** at pin, Mathlib has
  **no** Hellinger/Bhattacharyya (declaration-level grep: zero hits), **no** Le Cam / two-point
  bound (grep "le cam"/"leCam"/"two-point bound": zero hits), **no** simple-binary-hypothesis
  specialization, and **no** `erf`/`erfc`/Gaussian CDF/Q-function (zero hits — the Wave-2
  header's claim at `GaussianThreshold.lean:15-19` is accurate). `Mathlib/InformationTheory`
  contains only `Coding`, `Hamming`, `KullbackLeibler`. So the *bounds* are genuine whitespace;
  the *framework* is not.
- **Fix:** (i) document a prior-art search (Coq `infotheo` — Affeldt et al. — formalizes
  Bhattacharyya-type channel bounds and is the most likely counter-example; Isabelle AFP
  probability/concentration entries) before any D12-facing repetition; (ii) strike the MLR item
  from the enumerated family or ship it; (iii) restate L24 as "Mathlib carries a Bayes/minimax
  risk framework (`Probability.Decision.Risk`) but no Le Cam bound, no Hellinger/Bhattacharyya
  affinity, and no Gaussian tail function", and add a one-line note on why the `ℕ → ℝ` carrier
  was still the right call (the same `ℝ≥0∞` objection that rejected `PMF ℕ` in §2.2 applies to
  `bayesRisk`, which is `ℝ≥0∞`-valued).

### 3.1 — 🔵 MINOR — `midpoint_threshold_symmetric` ships an unused hypothesis

- **Gate:** AssumptionDisclosure / Stage-3a checklist #4
- **Location:** `lean/SKEFTHawking/Detection/GaussianThreshold.lean:502`
- **Observed:** `(hσ : 0 < σ)` is not load-bearing. The statement is true for **every** real σ,
  including σ = 0 (both sides collapse to `gaussianQ 0` under Lean's `x / 0 = 0`) and σ < 0.
- **Evidence:** compiled against the pinned toolchain (`lake env lean`, clean):
  ```lean
  theorem T1_midpoint_no_sigma_hyp (μ₀ μ₁ σ : ℝ) :
      thrErr0 μ₀ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ)) ∧
        thrErr1 μ₁ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ)) := by
    unfold thrErr0 thrErr1
    rcases eq_or_ne σ 0 with h | h
    · subst h; norm_num
    · refine ⟨congrArg gaussianQ ?_, congrArg gaussianQ ?_⟩ <;> (field_simp; ring)
  ```
  plus the σ = −3 instantiation. `value_deps_project` for the shipped theorem is
  `{eq_1, gaussianQ, thrErr0, thrErr1}` — consistent with `hσ` being inert.
- **Contrast (verified load-bearing, no finding):** `hσ` genuinely bites in
  `thrErr0_mono_in_sigma` / `thrErr1_mono_in_sigma` (σ = −1 vs σ′ = 1, μ₀ = 0, t = 1 gives
  Q(−1) = 0.841 ≤ Q(1) = 0.159, false), in `offCenter_threshold_tradeoff` (both `gcongr` steps
  need a positive denominator), and in `avgError_ge_gaussianQ_sharp`.
- **Fix:** drop `hσ` (strengthening), or — if the binder is wanted for call-site uniformity with
  the rest of the threshold algebra — say in the docstring that it is carried for signature
  uniformity and is not used.

### 3.2 — 🔵 MINOR — `offCenter_threshold_tradeoff` docstring claims independence that is false

- **Gate:** NarrativeGrounding / Stage-3a checklist #1
- **Location:** `lean/SKEFTHawking/Detection/GaussianThreshold.lean:489-491`
- **Observed:** "The two conjuncts are logically independent (they concern different branches
  under different means)."
- **Evidence:** as universally quantified statements, conjunct 2 is an **instance** of conjunct 1
  under `μ₀ := −μ₁`, `t := −t′`, `t′ := −t`. Compiled clean:
  ```lean
  theorem T7_conj2_from_conj1 {μ₁ σ t t' : ℝ} (hσ : 0 < σ) (h : t ≤ t') :
      thrErr1 μ₁ σ t ≤ thrErr1 μ₁ σ t' := by
    have := (offCenter_threshold_tradeoff (μ₀ := -μ₁) (μ₁ := 0) (σ := σ) (t := -t') (t' := -t)
      hσ (by linarith)).1
    unfold thrErr0 at this; unfold thrErr1; convert this using 3 <;> ring
  ```
- **Expected:** the bundle is still defensible for consumer convenience (a consumer sweeping `t`
  wants both shapes without applying a reflection), but "logically independent" is not true.
- **Fix:** reword to "both shapes are kept because a consumer sweeping `t` needs both without
  applying the reflection `μ₀ ↦ −μ₁, t ↦ −t′`", or split.

### 3.3 — 🔵 MINOR — `shotPSD_plane_transfer`: the disclosed mitigation is misattributed

- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:239-244`
- **Observed:** "The *content* of this theorem is the convention (the `2` inside `shotPSD`,
  pinned by `shotPSD_eq_hawkingNoisePSD`) and the placement of `η` outside the definition."
- **Evidence:** the statement is invariant under any change to that constant — verified by
  compiling the identical theorem for `fakePSD E_ph P := 7 * E_ph * P`:
  ```lean
  theorem T4_fake_transfer (E_ph P η : ℝ) : fakePSD E_ph (η * P) = η * fakePSD E_ph P := by
    unfold fakePSD; ring
  ```
  `value_deps_project` = `{_proof_1, shotPSD}` — the theorem touches nothing else. The
  convention content lives entirely in `shotPSD_eq_hawkingNoisePSD` and `shotPSD_pos` (which
  *does* route through it — verified: `value_deps` includes `hawkingNoisePSD_pos` and
  `shotPSD_eq_hawkingNoisePSD`). So the disclosure ("cheap by `ring`") is honest, but the
  specific attribution of *content* to the one-sided `2` is not: nothing here exercises it.
- **Fix:** reword to "the content is the *placement* of `η` outside the definition; the one-sided
  `2` is pinned separately by `shotPSD_eq_hawkingNoisePSD`, which this statement does not test."

### 3.4 — 🔵 MINOR — `shotPSD_eq_hawkingNoisePSD` asserts a specialization that identifies power with conductance

- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:225-233`
- **Observed:** "`shotPSD` is the unit-greybody, unit-occupation case of
  `GrapheneNoiseFormula.hawkingNoisePSD`".
- **Evidence:** `hawkingNoisePSD (hbar_omega sigma_Q greybody n_H : ℝ) := 2 * hbar_omega *
  sigma_Q * greybody * n_H` (`GrapheneNoiseFormula.lean:50`) — the second parameter is the
  **quantum conductance** σ_Q. The theorem substitutes optical power `P` for it. That is not a
  specialization of the Hawking-noise formula; it is an unrelated formula that happens to share
  the shape `2·a·b` and typecheck because both parameters are `ℝ`.
- **Mitigation is partly real (hence MINOR, not MAJOR):** the line does mechanically pin the
  leading constant — changing either definition's `2` breaks it, as claimed — and
  `GrapheneNoiseFormula`'s own docstring declares its inputs to be dimensionless magnitudes.
- **Fix:** reword to "shares the repository's one-sided leading constant `2` (contrast
  `johnsonNyquistPSD = 4·k_BT·σ_Q`); the equation is a constant check, not a physical
  specialization — `hawkingNoisePSD`'s second slot is a conductance, not a power."

### 3.5 — 🔵 MINOR — Roadmap bookkeeping: resolved UNKNOWNs still listed as Open; DoD boxes unchecked

- **Gate:** ProcessIntegrity
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:1`, `:89-95`, `:148-152`
- **Observed:** (a) §"Open UNKNOWNs (resolve at Stage 2 …)" still lists UNKNOWN-1/2/3, all three
  of which are resolved in the binding sign-off 50 lines above — and UNKNOWN-3's text is one of
  the three carriers of the prohibited claim in 1.2. (b) All five Phase-DoD boxes are `[ ]`
  while items 1-2 are demonstrably satisfied. (c) Status line still reads "PLANNED".
- **Evidence:** `validate.py --check counts_fresh` → **PASS**, `staleness: fresh`,
  `theorems=25459 (substantive=25433, placeholder=26) | modules=1998 | sorry=0`;
  `--check count_literals` → PASS (17 pre-existing warnings, none in `Detection`);
  `SK_EFT_Hawking_Inventory_Index.md:111,157` carries the `Detection` family (5 modules);
  `git status` clean at `0af953df`.
- **Fix:** move the three UNKNOWNs into a "Resolved at Stage 2" section (or delete, pointing at
  the sign-off block); tick DoD 1-3 once 2.4 is logged; flip PLANNED → COMPLETE with the dated
  shipped-declarations list once the blockers close.

### 4.1 — ℹ️ INFO — `shot_variance_eq_mean`: the freeze's headline vacuity flag is genuinely discharged

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:334-420`
- **Verified:** `Wave3_StatementFreeze.md:261-264` warned that `shot_variance_eq_mean` is
  "**vacuous if `poissonVariance N := N`**". It is not so defined. `poissonVariance N :=
  ∑' n, poissonPMFReal N n * ((n : ℝ) - poissonMean N)^2` — the second central moment about
  the independently-defined `poissonMean N := ∑' n, poissonPMFReal N n * n`. `poissonVariance_eq`
  is proved from `hasSum_poissonPMFReal_mul_descFactorial` (E[n(n−1)] = N², a genuine two-step
  reindex) plus `hasSum_poissonPMFReal_mul_id` (E[n] = N). Mitigation is real, not cosmetic.
- **One observation for the record:** `shot_variance_eq_mean` is itself a two-`rw` consequence
  of two shipped theorems (`value_deps` = `{poissonMean, poissonMean_eq, poissonVariance,
  poissonVariance_eq}`) — the same shape for which `avgError_ge_half_gaussianQ` was dropped
  under D10. The asymmetry is defensible (it relates two independently-*defined* quantities and
  does not mention the rate, so it is not a weakening of either parent), but it should be
  recorded in the Wave-3 audit so the discipline reads as consistently applied rather than
  case-by-case.

### 4.2 — ℹ️ INFO — Deviation integrity: all four audited deviations verified as strengthenings

- **Gate:** LeanProofSubstance
- **D10 (dropping `avgError_ge_half_gaussianQ`).** Verified: the sharp form implies the dropped
  half form pointwise at an **identical** signature. Compiled clean:
  ```lean
  theorem T2_half_form_from_sharp {μ₀ μ₁ σ t z₀ : ℝ}
      (hσ : 0 < σ) (hμ : μ₀ ≤ μ₁) (hz : (μ₁ - μ₀) / (2 * σ) ≤ z₀) :
      (1 / 2) * gaussianQ z₀ ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
    have h := avgError_ge_gaussianQ_sharp (t := t) hσ hμ hz
    have hq := gaussianQ_nonneg z₀
    linarith
  ```
  Nothing is lost. The drop is correct.
- **Dropped `η ≤ 1` on `hasSum_poisson_thinning` / `poisson_thinning`.** Genuinely stronger, not
  a silent weakening: `η : ℝ≥0` supplies `0 ≤ η` for free, and the reindexed series
  `∑ⱼ (N(1−η))ʲ / j!` is the exponential series, absolutely convergent for **every** real
  argument — so the `HasSum` holds for all η ≥ 0, including η > 1 where `(1−η)^(m−n)`
  alternates. The truncated ℕ subtraction is handled by `Nat.choose_eq_zero_of_lt`. The claimed
  reason (the algebra never consults `η ≤ 1`) is exactly right.
- **Dropped `0 ≤ η` on `shotPSD_plane_transfer`.** A pure ring identity over ℝ; genuinely
  stronger.
- **Wave-3 (S2) reshaped from the frozen §2.3 two-conjunct form to a sandwich.** Coverage is
  complete and strictly larger: composing the shipped sandwich's two conjuncts gives the frozen
  left conjunct, and the frozen right conjunct ships separately as
  `pushforwardFidelity_eq_binaryAffinity`.

### 4.3 — ℹ️ INFO — The seam does not call FvdG; the freeze's import-cost note is stale

- **Gate:** LeanProofSubstance
- **Observed:** `Wave3_StatementFreeze.md:39-44` and G5 state that Wave 3 "**pays** the
  `FidelityUpperBound` import — the seam *is* the tower's consumption", and §2.3's recipe chains
  (S2) through the project's proven `traceDist_le_sqrt_one_sub_sqrtFidelity_sq`.
- **Evidence:** dependency scan — **zero** `Detection.*` declaration references
  `traceDist_le_sqrt_one_sub_sqrtFidelity_sq`, and `ShotNoise.lean` does not import
  `FidelityUpperBound` (it imports `QuantumNetwork.DiamondNormChoi` for
  `posSemidef_eq_of_mul_self_eq`).
- **Assessment: no statement is weaker for it, and the lighter import is an improvement.** The
  seam still makes real cross-module calls — `diagonalState_sqrtFidelity_eq_affinity`'s
  `value_deps` are `{diagonalPSD, psdSqrt, psdSqrt_diagonal, sqrtFidelity, traceNorm,
  traceNorm_posSemidef}`, and `psdSqrt_diagonal`'s are `{diagonalPSD,
  posSemidef_eq_of_mul_self_eq, psdSqrt, psdSqrt_mul_self, psdSqrt_posSemidef}`. Both are
  genuine bridges. Only the freeze's prose is stale; correct it in the Wave-3 audit entry.

### 4.4 — ℹ️ INFO — Out-of-scope pointer for 6EB's own Stage-13

- `nepOfOutput_of_responsivity_eq_zero` (`Detection/NEPAlgebra.lean:190-196`) — the disclosure is
  **real, not cosmetic**: "A chain of zero responsivity has no signal path, so the
  input-referred NEP is undefined; Lean's total division returns `0`. Stated so consumers cannot
  mistake the junk value for a physical noise density." Good practice; no action.
- `snrChain_eq_of_responsivity` (`:588-592`) — a two-`rw` corollary of
  `snrChain_independent_of_responsivity` with **no** triviality disclosure in its docstring.
  Same identity-wrapper shape as the D10 drop. 6EB's own review should adjudicate.

### 4.5 — ℹ️ INFO — What I attacked and found clean (recorded so it is not re-attacked)

- **No trivial bodies.** Zero `rfl` / `trivial` / `decide` / `native_decide` / `Equiv.refl`
  proof bodies across all three modules; no structural-tautology anonymous constructors
  returning a hypothesis as an output field.
- **No placeholders, kernel-pure.** All 254 `Detection.*` declarations: 248 with axiom set
  `{Classical.choice, Quot.sound, propext}`, 6 with `{propext}` only, **0** project axioms,
  **0** declarations of type `True`.
- **No empty quantifiers.** Every hypothesis bundle is witnessed in-file: `IsCountRule` by
  `isCountRule_thresholdRule`; the zero-false-alarm pair by `poisson_darkBaseline_miss_optimum`;
  the brightness condition of `folklore_avgFloor_unsound_of_bright` by `folklore_avg_floor_unsound`
  via `brightGap_5060`.
- **No vacuous floor.** Every floor's LHS is strictly positive in its regime: `gaussianQ_pos`
  (proved, so no `Q`-stated floor can degenerate to `0 ≤ ·`); `¼·exp(−(√Nₐ−√N_b)²) ∈ (0, ¼]`;
  `c·φ(z+c) > 0`. `avgError_ge_gaussianQ_sharp` cannot degenerate the other way either: its
  hypotheses force `z₀ ≥ 0`, hence `Q(z₀) ≤ ½`.
- **`hz : 0 ≤ z` in `gaussianTail_ge_window` is load-bearing** — counterexample at `z = −3,
  c = 3`: LHS = 3·φ(0) = 1.1968 > Q(−3) = 0.99865. (The bound needs `φ` antitone across the
  whole window.)
- **Other hypotheses spot-checked and confirmed load-bearing:** `hδ` in
  `poisson_avgError_equalRates_eq_half` (without it an unbounded `δ` makes both `tsum`s default
  to 0, giving avg = 0 ≠ ½) and in `poisson_darkBaseline_miss_floor` (δ₀ = 0, δ₁ = 100 breaks
  the floor); `hFA` (refuted by the shipped `darkBaseline_zeroFalseAlarm_load_bearing` +
  `isCountRule_thresholdRule` + `falseAlarm_thresholdRule_zero` triple — a genuinely complete
  hypothesis-drop refutation); `h₁` in `binaryAffinity_sq_le_two_mul_add` (e₀ = ½, e₁ = −1 gives
  1 ≤ −1); `hh` in `gaussianQ_two_le_add` (h = −1, u = 0 gives 1.683 ≤ 1.477); `hμ` in
  `avgError_ge_gaussianQ_sharp` (μ₀ = 10, μ₁ = 0, σ = 1, t = 0, z₀ = −5 gives 0.99999997 ≤ 0.75);
  `ha`/`hb` in `folkloreGap_split`; `ht` in `thrErr0_mono_in_sigma`.
- **No definition swallows its theorem's conclusion.** `gaussianQ` is the bare tail integral of
  Mathlib's `gaussianPDFReal 0 1`, with its normalization pinned *externally* by
  `gaussianQ_zero = ½` through Mathlib's `Real.integral_gaussian_Ioi` — the cleanest possible
  answer to checklist #5. `affinity`, `IsCountRule`, `falseAlarm`, `missProb` are the textbook
  definitions. `poissonVariance` is independent of the mean (4.1). `shotPSD` is the only
  definition carrying a convention, and that convention is externally checked (3.4).
- **Rational brackets non-degenerate:** `1/125 ≤ Q(2) ≤ 1/6` (0.008 / 0.1667) against the true
  0.022750 — a live, two-sided, floating-point-free enclosure; the upper witness genuinely
  calls `expNeg_enclosure`.
- **Wave-2 header claim re-verified at pin:** declaration-level grep over
  `lean/.lake/packages/mathlib` (rev `5e932f97`) for `erf`/`erfc`/Gaussian CDF/Q-function →
  zero hits; `Mathlib/InformationTheory/` contains only `Coding`, `Hamming`, `KullbackLeibler`;
  no Hellinger/Bhattacharyya anywhere. The project-local `gaussianQ` was necessary.
- **Counts fresh** (`counts_fresh` PASS, `count_literals` PASS), Inventory Index carries the
  `Detection` family, working tree clean at `0af953df`.
- **No module docstring claims PhysLib `HypothesisTesting` consumption.** `ShotNoise.lean:188-190`
  correctly states the opposite and gives the type-level reason. The prohibited claim survives
  only in the roadmap (1.2).

## QI Candidate

**Systemic: a prose-repair pass that is not machine-checked leaves dangling references, and a
retracted route survives in the append-only decisions register.**

Two of this review's findings (1.1, 2.3) are the same failure in two artifacts: a correction was
made in one place (the theorem was renamed; the Wave-3 freeze retracted G8) and not propagated to
the pointer that a fresh context reads first (the module docstring's Main-results list; the
notebook INDEX's DECISIONS block). Both are mechanically detectable:

1. **Docstring reference linter.** Extract every backticked identifier from Lean doc-comment
   blocks, resolve against `lean_deps.json` (project names) with a Mathlib/tactic allowlist, and
   fail on unresolvable project-namespace names. My ad-hoc version of this found exactly one
   false positive class (module/namespace names such as `GrapheneNoiseFormula`, `NumericalBounds`)
   and one true positive — a ~30-line `validate.py` check with a high signal-to-noise ratio, and
   the natural home for the existing checklist-#3 rule ("every docstring cross-reference must be
   backed by a call"), which is currently enforced only by human reading. The stronger version
   also cross-checks that a docstring naming a *project* declaration corresponds to an entry in
   that declaration's `value_deps_project` — which is what would have caught 2.1
   (`poissonMean_thinning`).
2. **Notebook-INDEX freshness check.** Flag a DECISIONS line naming a Mathlib declaration that
   does not resolve at pin, and flag a checklist row marked unchecked/"NEXT" whose named artifact
   already exists on `main`. The INDEX is the designated post-compaction entry point; a stale
   entry there is a reseeding hazard by construction, which is precisely the failure mode
   `SETTLED_FORKS` / the negative frontier exist to prevent.
