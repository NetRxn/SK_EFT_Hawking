---
paper: phase6EA_substrate
reviewer: adversarial-reviewer
model: claude-opus-5
review_date: 2026-07-28T19:24:00Z
readiness_gates_version: 1
round: 2
prior_review: papers/AutomatedReviews/2026-07-28-1839-internal-adversarial/phase6EA_substrate.md
remediation_commit: 7e4c012d
scope: substrate phase, no paper target (bundle D12 authorized, no on-disk draft)
---

# Adversarial Review — Phase 6EA, Round 2 (remediation verification)

## Summary

**ZERO BLOCKER survives.** Both round-1 BLOCKERs are independently verified closed:
`poisson_avgError_equalRates_eq_half` resolves and the replacement description is
*correct* (exact `1/2` vs. the headline floor's `¼` — the factor-two slack), and no live
claim of PhysLib `HypothesisTesting` consumption remains anywhere in-tree (every surviving
occurrence is the prohibition or a path correction). **13 findings: 0 BLOCKER, 3 MAJOR,
5 MINOR, 5 INFO.** The three MAJORs are all *incomplete* remediations, not new breakage:
the non-vacuity scope note still draws the attainability inference it disclaims two
sentences earlier; the roadmap's Thesis (L5) still enumerates a deliverable the phase
never shipped, one line above the L7 enumeration that was fixed for exactly that reason;
and the cross-prover prior-art search behind the "no theorem prover has…" claim is still
undocumented. One new defect *was* introduced by a fix (`definitionally`, refuted by
`rfl`). The statement set itself remains sound — my independent scans found no dangling
project identifier, no inert hypothesis, no placeholder, no `True`-typed statement, and
`thinnedMean_eq_eta_mul` genuinely calls `poisson_thinning`.

Method: every claim below verified against the source at `7e4c012d` (working tree), the
pinned Mathlib at `lean/.lake/packages/mathlib` rev `5e932f97` (never leansearch/loogle),
`lean/lean_deps.json` `value_deps_project`, and — where a hypothesis-droppability or
definitional-equality claim is made — by compiling scratch theorems with `lake env lean`
against the project's own toolchain (scratch file removed).

---

## Verified closed (round-1 BLOCKERs)

### V1 — ✅ CLOSED — BLOCKER 1.1 (dangling + inverted module-docstring reference)

- **Location:** `lean/SKEFTHawking/Detection/PoissonDiscrimination.lean:22-25`
- **Verified:** the bullet now names `poisson_avgError_equalRates_eq_half`, which exists
  (`PoissonDiscrimination.lean:276`, `lean_deps.json` type
  `… IsCountRule δ → avgAssignmentError (falseAlarm N δ) (missProb N δ) = 1 / 2`).
  The description is now *correct in direction*: at `N_a = N_b` the headline floor
  `¼·exp(−(√N_a−√N_b)²)` evaluates to exactly `¼`, the shipped theorem gives `1/2`, and
  the stated "factor of two" slack is arithmetically right. The theorem's own docstring
  (`:268-275`) says the same thing, so header and body now agree.
- **Re-scan (the brief's explicit ask):** I re-ran a docstring-identifier scan over **all
  three** modules — every backticked identifier in every `/-- -/` and `/-! -/` block,
  resolved against the 39,516-entry declaration graph plus module/namespace names. Exactly
  **two** project-namespace names fail to resolve, both intentionally:
  `avgError_ge_half_gaussianQ` (`GaussianThreshold.lean:596`, in a section headed
  "deliberately NOT shipped") and `OptimalHypothesisRate` (`ShotNoise.lean:191`, in a
  sentence stating it is *not* available and not attempted — confirmed a real PhysLib
  declaration at `QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean:48`). All other
  flags are tactic names, Lean concepts (`HasSum`, `tsum`), local hypothesis names, freeze
  IDs (`D7`, `D10`) or Mathlib names that all resolve at pin (`Real.integral_gaussian_Ioi`,
  `Real.exp_one_gt_d9`, `Real.pi_lt_d2`, `Real.add_one_le_exp`,
  `Matrix.diagonal_mul_diagonal`, `Real.mul_self_sqrt` — each also *called* in a proof).
  **No fix introduced a new dangling reference.**

### V2 — ✅ CLOSED — BLOCKER 1.2 (roadmap's prohibited `HypothesisTesting` claim)

- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:25`, `:72`, `:152`
- **Verified:** L25 now states the type-level impossibility (`[Fintype d]`-bound;
  `ProbDistribution α` likewise) and asserts "Zero `Detection.*` declarations reference
  `OptimalHypothesisRate`"; L72 strikes the brick and names the shipped seam bricks; L152
  marks UNKNOWN-3 resolved. Every type-level assertion checks out at pin:
  `OptimalHypothesisRate (ρ : MState d)` under `variable {d : Type*} [Fintype d]`
  (`HypothesisTesting.lean:44,48`) and `def ProbDistribution (α : Type u) [Fintype α]`
  (`ClassicalInfo/Distribution.lean:37`). The `SETTLED_FORKS.md#6ea-optimalhypothesisrate-quantum-seam`
  anchor the bullet cites exists (`SETTLED_FORKS.md:1314`).
- **Surviving occurrences audited (the brief's "four by design"):** grep over all in-tree
  `.md`/`.lean`/`.py` (excluding `.lake/`) returns the phrase-bearing hits at
  `Phase6EA_Roadmap.md:123`, `SETTLED_FORKS.md:1319`, `Phase6EA_Stage2_StatementFreeze.md:357`,
  `Phase6EA_Wave3_StatementFreeze.md:67`, and `goal_prompt_20260728T114358.md:97` — **five**,
  not four, and every one is the *prohibition* ("must NOT be described as…"), never a claim.
  Two further hits (`Roadmap.md:146`, `Stage2StatementFreeze.md:37,887`) are the module-path
  correction. `ShotNoise.lean:191-193` states the opposite of consumption and gives the
  type-level reason. **No live consumption claim survives.** (The count discrepancy is
  bookkeeping only; the reading the brief asked me to confirm holds.)

---

## Findings

### 2.1 — 🟡 MAJOR — The non-vacuity scope note draws the attainability inference it disclaims

- **Gate:** NarrativeGrounding (residual of round-1 2.2)
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:460-466` (and the module
  Main-results bullet at `:41-45`)
- **Observed:** the new scope note says, in order: (a) "The Gaussian error pair
  `(thrErr0 1 2 5, thrErr1 9 2 5)` is NOT claimed to be realizable by any count rule `δ`,
  so this does **not** exhibit a count rule whose error strictly exceeds its own floor";
  then (b) "What it certifies is that `¼·exp(−(√N_a−√N_b)²)` is not an equality in
  disguise at this operating point — **a floor that coincided with attainable error
  everywhere would be useless as a screen**".
- **Evidence:** (b) is exactly the inference (a) forbids. "The floor is not an equality in
  disguise" is a statement about the floor versus the *attainable* error — i.e. about
  `inf over δ of avgAssignmentError (falseAlarm Nb δ) (missProb Na δ)`. The shipped
  theorem is `(3/2)·(¼·affinity(Poisson 1, Poisson 9)²) < avgAssignmentError (thrErr0 1 2 5)
  (thrErr1 9 2 5)` — a comparison between the floor value and a number produced by a
  *different experiment* whose realizability by any `δ` the note itself declines to claim.
  Strike the realizability disclaimer and the conclusion evaporates; keep it and the
  conclusion does not follow. Nothing in `Detection/` establishes non-tightness at
  `(N_b, N_a) = (1, 9)`.
- **What the project *does* have:** `poisson_avgError_equalRates_eq_half`
  (`PoissonDiscrimination.lean:276`) establishes exactly this — floor `¼`, exact value
  `1/2`, **same experiment, every admissible `δ`**. That is the theorem the slack claim
  belongs to, and round 1 said so.
- **Expected:** state what the witness gives — "at this design point the Le Cam screen does
  not already exclude a shot-limited Gaussian readout: the model's error exceeds the floor
  by more than 3/2, so the floor is not binding here" — and point "not an equality in
  disguise" at `poisson_avgError_equalRates_eq_half`.
- **Fix:** rewrite sentence (b); delete the "attainable error" gloss or move it to the
- **Lane:** `lean`
  equal-rates theorem.

### 2.2 — 🟡 MAJOR — The roadmap Thesis still promises a deliverable the phase never shipped

- **Gate:** NarrativeGrounding (unfixed twin of round-1 2.5(b))
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:5`
- **Observed:** the Thesis enumerates four floors "routinely *cited* in device papers but
  [that] have never been *kernel-checked* anywhere: the Bhattacharyya/Le Cam universal
  floor…, the zero-false-alarm dark-baseline optimum, **the Neyman–Pearson structure of
  counting tests**, and Gaussian threshold-error algebra…", then says "**This phase builds
  that layer once, exactly**."
- **Evidence:** no Neyman–Pearson / likelihood-ratio / monotone-likelihood theorem ships.
  `grep -niE "neyman|likelihood|MLR"` over all three modules returns exactly two hits, both
  *disclaimers* (`PoissonDiscrimination.lean:252` "no monotone-likelihood assumption";
  `ShotNoise.lean:192` naming NP as the thing the seam is *not*). The roadmap's own D3
  demotion (`:42`, `:125-129`) records the MLR argument as "not in the roadmap's brick
  list". The dark-baseline optimum is listed separately in the same sentence, so it cannot
  double as the NP item.
- **Why this is a fresh finding, not a repeat:** the remediation struck "counting-test
  monotone-likelihood-ratio structure" from the novelty claim at **L7** — for precisely
  this reason — while leaving the identical overstatement at **L5**, one line above, in the
  sentence most likely to be lifted verbatim into D12 prose.
- **Fix:** strike "the Neyman–Pearson structure of counting tests" from L5, or replace with
- **Lane:** `infra`
  the shipped dark-baseline zero-false-alarm optimum (already listed) and say the general
  NP/MLR layer is future work.

### 2.3 — 🟡 MAJOR — The cross-prover novelty claim still rests on a Mathlib-only sweep

- **Gate:** NarrativeGrounding (first-claim; round-1 2.5(a), **unremediated**)
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:5` ("never been *kernel-checked*
  anywhere") and `:7` ("**no theorem prover** has a kernel-checked Poisson
  discrimination-**bound** family … packaged as reusable metrology substrate")
- **Observed:** these are claims about *every* proof assistant. The only evidence recorded
  anywhere in the phase's artifacts is a Mathlib grep. `grep -niE
  "isabelle|afp|infotheo|coq|rocq|agda|mizar|prior art"` over `Phase6EA_Roadmap.md` and the
  entire `docs/dev-loops/Phase6EA/` tree returns **zero hits**. The remediation commit's
  message asserts the 2.5 finding was addressed; it addressed 2.5(b) and 2.5(c) only.
- **What I could verify myself:** the Lean half is solid — at pin, `Mathlib/` has zero
  declaration-level hits for Hellinger (only "Hellinger–Toeplitz" in
  `InnerProductSpace/`), zero for Bhattacharyya (only an author name in
  `MeasureTheory/Measure/Tight.lean:4`), zero for "Le Cam", zero word-boundary `erf`/`erfc`,
  and no Neyman–Pearson lemma. The **non-Lean** half is unverified: `isa-afp.org` is
  denied by the repo's own egress guard (`[web-egress] non-whitelisted domain`), and the
  two arXiv API queries I could run (`abs:"Isabelle" AND abs:"hypothesis testing"` → 0
  results; `abs:"infotheo" OR abs:"formalization of information theory"` → 2 irrelevant
  hits) are far too weak an index of AFP/Coq library contents to license "no theorem
  prover".
- **Expected:** either a documented search of Isabelle/AFP (probability + concentration
  entries), Coq/Rocq `infotheo` (Affeldt et al. — the most likely counter-example, it
  formalizes channel error-probability bounds), Agda, and Mizar; or the claim narrowed to
  what was actually checked ("absent from Mathlib at pin `5e932f97`").
- **Fix:** dispatch a Tier-1 `research-scout` for the four ecosystems and record the result
- **Lane:** `research`
  in the roadmap, or narrow both L5 and L7 to Mathlib. This blocks any D12-facing repetition
  of the claim, not the phase's substrate gate.

### 3.1 — 🔵 MINOR — A fix introduced a false definitional claim (`definitionally`)

- **Gate:** LeanProofSubstance / bridge integrity
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:228-229`
- **Observed:** the remediated docstring now opens "`shotPSD E_ph P` is **definitionally**
  the unit-greybody, unit-occupation case of `GrapheneNoiseFormula.hawkingNoisePSD`". The
  word `definitionally` is new in `7e4c012d` (the pre-fix text said only "is the
  unit-greybody, unit-occupation case").
- **Evidence:** it is not definitional. Compiled against the project toolchain:
  ```lean
  example (E P : ℝ) : shotPSD E P
      = SKEFTHawking.GrapheneNoiseFormula.hawkingNoisePSD E P 1 1 := rfl
  -- error: Type mismatch — rfl has type ?m = ?m but is expected to have type
  --        shotPSD E P = GrapheneNoiseFormula.hawkingNoisePSD E P 1 1
  ```
  The shipped proof is `unfold …; ring` — it needs `mul_one` twice, which is a propositional
  lemma for `ℝ`, not a reduction. The rest of the scope note is accurate and is a genuine
  improvement (the σ_Q-vs-P disclaimer answers round-1 3.4 squarely).
- **Fix:** delete `definitionally` (or replace with "is the … case, up to `mul_one`").

### 3.2 — 🔵 MINOR — "Shot-limited" survived the deletion of its (wrong) justification

- **Gate:** NarrativeGrounding / the module's own guardrail (residual of round-1 2.2 "Also")
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:454` and `:41`
- **Observed:** the spurious parenthetical "σ = 2 (= √N at the decision level N = 4)" was
  correctly removed, but the physical adjective it was there to justify was kept: the
  theorem docstring still reads "strictly exceeded by a **shot-limited** Gaussian model" and
  the module bullet still reads "a **shot-limited** Gaussian threshold model".
- **Evidence:** the two hypotheses carry Poisson rates 1 and 9, whose shot widths are
  `√1 = 1` and `√9 = 3`. The theorem uses a common `σ = 2`, which equals neither. Nothing in
  the file relates `σ` to either rate. The module guardrail (`:49-53`) reserves exactly this
  kind of identification to the consuming phase: "physical identification of an abstract
  parameter with a measured quantity is the consuming phase's declared hypothesis."
  Removing the justification while keeping the adjective leaves the claim *less* supported
  than before, not more.
- **Note for the author:** a correct justification was available and is worth stating if the
  adjective is kept — `σ = 2` is exactly the arithmetic mean of the two shot widths,
  `(√N_b + √N_a)/2 = (1+3)/2 = 2`.
- **Fix:** either state that rationale in the docstring, or drop "shot-limited" from `:454`
  and `:41` and call it what the statement says: a common-σ Gaussian threshold model.

### 3.3 — 🔵 MINOR — Round-1 3.5 (roadmap bookkeeping) was not remediated, and the commit says otherwise

- **Gate:** ProcessIntegrity
- **Location:** `docs/roadmaps/Phase6EA_Roadmap.md:1`, `:89-95`, `:148-151`; commit
  `7e4c012d` message
- **Observed:**
  - `:148` — the section "**Open UNKNOWNs** (resolve at Stage 2 before the consuming wave
    freezes statements)" still lists **UNKNOWN-1** (`:150`) and **UNKNOWN-2** (`:151`) in
    their original unresolved wording, though both are resolved in the binding sign-off 30
    lines above (`:102-116`). Only UNKNOWN-3 was updated.
  - `:91-95` — all five Phase-DoD boxes remain `[ ]`, though items 1 and 2 are demonstrably
    satisfied (build clean per the brief; `counts_fresh` PASS; Inventory Index carries the
    `Detection` family) and item 3 is now satisfied (see 4.5).
  - `:1` — Status still reads **PLANNED** with all three waves merged. (This one is
    *legitimately* pending: the notebook INDEX gates PLANNED → COMPLETE on a zero-BLOCKER
    round 2. It is now unblocked.)
  - The commit message states "**MINOR (all fixed, none skipped)**" and then enumerates
    four MINORs. Round 1 filed five. 3.5 was skipped, and the message asserts it was not.
- **Fix:** move UNKNOWN-1/2 into a "Resolved at Stage 2" pointer; tick DoD 1–3; flip Status
  with the dated shipped-declarations list now that no BLOCKER survives.

### 3.4 — 🔵 MINOR — The remediation shipped a new theorem without its counts/graph sync

- **Gate:** CountFreshness (Stage-12 hygiene)
- **Location:** commit `7e4c012d` (4 files); working tree
- **Observed:** `7e4c012d` adds `thinnedMean_eq_eta_mul` to `ShotNoise.lean` but does not
  update `lean/lean_deps.json`, `lean/lean_deps.json.hash`, `docs/counts.json`, or
  `docs/counts.tex`. The committed `lean_deps.json` at HEAD contains **159** `Detection.*`
  declarations and does **not** contain `thinnedMean_eq_eta_mul`; committed `counts.json`
  says `theorems_total: 25459`.
- **Evidence:** `git show HEAD:lean/lean_deps.json` → 39,515 decls, `thinnedMean` absent.
  Working tree (regenerated 14:07, four minutes after the 14:03 commit, **uncommitted**) →
  39,516 decls, `thinnedMean_eq_eta_mul` present with
  `value_deps_project = [poisson_thinning, poissonMean, poissonMean_eq]`;
  `counts.json` `25459 → 25460`. `validate.py --check counts_fresh` PASSes **in the working
  tree** (`staleness: fresh`, `theorems=25460 | modules=1998 | sorry=0`) and
  `--check count_literals` PASSes (17 pre-existing warnings, none in `Detection`; no D12
  draft exists to carry literals). So the *tree* is fresh and the *commit* is not
  self-consistent, and `git status` is dirty with four generated artifacts.
- **Fix:** commit the regenerated artifacts (or amend), so `main` is internally consistent.

### 3.5 — 🔵 MINOR — "The *same* η" is still prose, not a theorem — and the two η's are different types

- **Gate:** NarrativeGrounding (residual of round-1 2.1, largely fixed)
- **Location:** `lean/SKEFTHawking/Detection/ShotNoise.lean:409-419`, `:255-259`
- **Verified first (the fix works):** `thinnedMean_eq_eta_mul` is real. Its statement is the
  actual thinning sum, `∑' n, (∑' m, poissonPMFReal N m · C(m,n) · η^n · (1−η)^(m−n)) · n
  = η · poissonMean N`, and `lean_deps.json` `value_deps_project` for it is
  `[poisson_thinning, poissonMean, poissonMean_eq]` — it **does** call `poisson_thinning`,
  as claimed, and it is not vacuous. `poissonMean_thinning`'s docstring is now accurate
  ("Pure consequence of `poissonMean_eq`; it says nothing on its own about *thinning*").
  This is the right remediation posture: the bridge was built, not the sentence deleted.
- **Residual:** the docstring still concludes "`shotPSD_plane_transfer` scales the one-sided
  shot PSD by `η`, and this scales the count mean by the *same* `η`", and `:257-259` repeats
  it. No theorem binds the two. They are not even the same type:
  `shotPSD_plane_transfer (E_ph P η : ℝ)` quantifies `η : ℝ`;
  `thinnedMean_eq_eta_mul (N η : ℝ≥0)` quantifies `η : ℝ≥0`. "The same η" is a modelling
  identification of two independently bound variables — the class of claim the module
  guardrail (`:49-53`) assigns to the consuming phase.
- **Also:** the new docstring glosses the thinned law as "built by independently retaining
  each count with probability `η`" without repeating the file's own `η > 1` disclaimer
  (`hasSum_poisson_thinning`, `:281-283`, and the module guardrail state that reading `η` as
  a probability is a consumer-side condition, deliberately not a hypothesis). At `η > 1` —
  which the statement admits — that gloss is unlicensed.
- **Fix (cheap, and it would make the claim a theorem):** state the conjunction once over a
  single `η : ℝ≥0`, e.g.
  `shotPSD E_ph ((η:ℝ) * P) = (η:ℝ) * shotPSD E_ph P ∧ (thinning sum) = (η:ℝ) * poissonMean N`.
  Otherwise reword to "both scale by their respective transfer factor" and re-attach the
  probability caveat.

---

### 4.1 — ℹ️ INFO — Unused-hypothesis sweep across all three modules: clean

- **Gate:** AssumptionDisclosure
- **Verified:** I extracted every binder named `h*` from every `theorem`/`lemma` in the three
  modules and checked textual usage in the proof body. Five theorems have a hypothesis that
  never appears by name — `gaussianPDF_le_of_sq_le` (`h`), `gaussianTail_ge_window`
  (`hz`, `hc`), `thrErr0_mono_in_sigma` (`ht`), `thrErr1_mono_in_sigma` (`ht`),
  `offCenter_threshold_tradeoff` (`h`) — and **every one is consumed by a context-reading
  tactic** (`linarith`, `nlinarith`, `gcongr`) in the body. No theorem in the three modules
  carries an inert hypothesis. The dropped `hσ` in `midpoint_threshold_symmetric` is the
  only one there ever was, and it is gone.
- **Round-1 3.1 double-checked from the other side:** the *old* proof script
  (`rw [thrErr0]; congr 1; field_simp; ring`) compiles verbatim on the hypothesis-free
  statement — so `hσ` was inert in the proof term too, not merely unnecessary for truth.
  Round-1 3.1 was right on both criteria and the remediation is a genuine strengthening. The
  new `div_div` route is correct and unconditional (`a / b / c = a / (b * c)` holds in any
  `DivisionRing`, so the `σ = 0` case goes through with `x / 0 = 0` on both sides).

### 4.2 — ℹ️ INFO — Two strengthening opportunities the round-1 criterion implies but nobody took

- **Gate:** AssumptionDisclosure (advisory; no action required)
- `gaussianTail_ge_window`'s `hc : 0 < c` is droppable *for truth* by the same criterion
  that condemned `midpoint_threshold_symmetric`'s `hσ` — for `c < 0` the LHS is negative and
  for `c = 0` it is zero, both below `gaussianQ_nonneg`. Compiled clean:
  ```lean
  theorem window_no_hc {z c : ℝ} (hz : 0 ≤ z) : c * gaussianPDFReal 0 1 (z + c) ≤ gaussianQ z
  ```
  I do **not** recommend dropping it: the extension is vacuous and the hypothesis is
  genuinely used in the proof. I record it because it shows "the statement is true without
  it" is the *wrong* test on its own — the right test is "the proof term does not depend on
  it" (which is what makes a hypothesis falsely advertised). Both tests agreed on `hσ`.
- `thrErr0_mono_in_sigma`'s `ht : μ₀ < t` and `thrErr1_mono_in_sigma`'s `ht : t < μ₁` can
  each be weakened to `≤` with the identical proof script; both compiled clean. Free
  generality if a consumer ever sits at the mean.

### 4.3 — ℹ️ INFO — Mathlib substrate claims re-verified at pin, both halves

- **Gate:** NarrativeGrounding
- **Half 1 — `Probability.Decision.Risk` exists (the retraction is correct).** At
  `5e932f97`: `Mathlib/Probability/Decision/Risk/{Defs,Basic}.lean` (Degenne & Luccioli,
  2025) define `avgRisk`, `bayesRisk` (infimum over **all Markov estimator kernels**),
  `minimaxRisk`, all with loss `ℓ : Θ → 𝓨 → ℝ≥0∞` over `Kernel Θ 𝓧` — exactly as the
  roadmap now states — plus the data-processing lemmas `bayesRisk_le_bayesRisk_comp`
  (`Basic.lean:236`) and `bayesRisk_le_bayesRisk_map` (`:246`). The `ℝ≥0∞` typing is real,
  so the roadmap's "not usable here" justification (truncated arithmetic vs. real-valued
  `exp` floors over `δ : ℕ → ℝ`) is sound.
- **Half 2 — the bound layer is absent (the surviving claim is correct).** Zero
  declaration-level hits in all of `Mathlib/` for Hellinger (only the Hellinger–Toeplitz
  theorem in `InnerProductSpace/{Adjoint,Symmetric}.lean`), zero for Bhattacharyya (only an
  author name in `MeasureTheory/Measure/Tight.lean:4`), zero for "Le Cam", zero
  word-boundary `erf`/`erfc`, zero Neyman–Pearson, and no gaussian-specific CDF under
  `Probability/Distributions/Gaussian/`. Only `MeasureTheory/Measure/LogLikelihoodRatio.lean`'s
  `llr` is adjacent.
- **One looseness, not worth a finding:** "zero for … Gaussian CDF anywhere in Mathlib"
  (`Roadmap.md:7`) is true at declaration level but `Mathlib/Probability/CDF.lean` defines a
  general `cdf` that instantiates at `gaussianReal 0 1`. The project-local `gaussianQ` is
  still necessary — a bare `cdf` carries none of the tail bounds this phase needs — and
  `gaussianQ_zero` pins its normalisation to Mathlib's own `Real.integral_gaussian_Ioi`.

### 4.4 — ℹ️ INFO — Statement-set integrity re-confirmed independently (no regression)

- **Gate:** LeanProofSubstance
- All **160** `SKEFTHawking.Detection.*` declarations carry axiom set
  `{Classical.choice, Quot.sound, propext}` and **zero** project axioms. No declaration has
  a `True`-typed statement; no PlaceholderMarker touches `Detection`. `count_literals` PASS,
  `counts_fresh` PASS (in-tree).
- **Note on a number round 1 got wrong, now propagated:** round 1 reported "254 `Detection.*`
  declarations" and that figure was copied into the remediation commit message, the phase
  notebook (`LAB_NOTEBOOK.md:154`), and the round-1 report's evidence for BLOCKER 1.2. The
  graph says **159** at `0af953df` and **160** now. The *conclusion* (zero references to
  `OptimalHypothesisRate`) is unaffected — I re-derived it — but the number is wrong in
  three artifacts.

### 4.5 — ℹ️ INFO — Notebook + INDEX remediation verified; three small residuals

- **Gate:** ProcessIntegrity
- **Verified (round-1 2.3):** `LAB_NOTEBOOK_INDEX.md:45-48` now names
  `QuantumNetwork.posSemidef_eq_of_mul_self_eq` as the chosen route and marks
  "`Matrix.PosSemidef.sq_eq_sq_iff`" as **RETRACTED — that decl does NOT exist at pin
  `5e932f97`**, with the standing "leansearch hits are candidates" lesson appended as its
  own DECISIONS line (`:49-51`). The W3 checklist row is `[x]` (`:23`), commit state and
  Frontier are current, and the pending item is correctly stated as "round 2, ZERO BLOCKER →
  flip PLANNED to COMPLETE".
- **Verified (round-1 2.4):** `LAB_NOTEBOOK.md` has a Wave-3 entry (`:117-138`), a Stage-13
  round-1 entry (`:140-186`), and an explicit "**Per-wave post-strengthening audits (the
  mandated log)**" block (`:180-186`) covering W1/W2/W3 plus the lead-side drops. DoD item 3
  is now satisfied in substance.
- **Residuals (all minor, all carried from round-1 INFO items):**
  1. Round-1 4.1 asked that `shot_variance_eq_mean`'s two-`rw`-corollary shape be recorded
     against the D10 identity-wrapper drop so the discipline reads as consistently applied.
     Not logged.
  2. Round-1 4.3's stale claim that Wave 3 "**pays** the `FidelityUpperBound` import" still
     stands uncorrected in `Phase6EA_Wave3_StatementFreeze.md:39-44` and is repeated in the
     notebook's historical W3-freeze entry (`:47-49`). `ShotNoise.lean:1-4` imports
     `PoissonDiscrimination`, `GaussianThreshold`, `QuantumNetwork.DiamondNormChoi`,
     `GrapheneNoiseFormula` — the lighter route.
  3. The audit block is a summary of strengthenings rather than a per-wave disposition of
     strengthening-checklist items #1–#5. Adequate for the DoD as written; note if the DoD
     is meant to be stricter.

---

## Blocker verdict

**No BLOCKER survives.** Round-1 1.1 and 1.2 are both independently verified closed against
the source, the declaration graph, the pinned Mathlib, and the pinned PhysLib. Nothing in
this round rises to BLOCKER: the three MAJORs are incomplete remediations of prose claims
(one Lean docstring, two roadmap lines), none of which touches a proof, a statement, or a
kernel dependency. On the phase's own gate wording — "fresh-context `adversarial-reviewer`,
ZERO BLOCKER · roadmap PLANNED → COMPLETE" (`LAB_NOTEBOOK_INDEX.md:27`) — the phase is clear
to flip. The three MAJORs must close before any of this content is lifted into D12.

## QI Candidate

**Systemic: partial remediation reported as complete, and review numerics that nobody
re-derives.**

Three independent instances in one remediation cycle:

1. The commit message asserts "MINOR (all fixed, none skipped)" while enumerating four of
   five; round-1 3.5 was skipped (finding 3.3).
2. The MAJOR 2.5 remediation fixed sub-items (b) and (c) and left (a) — the actual
   cross-prover prior-art search — undone, while the commit message describes 2.5 as
   handled (finding 2.3).
3. The same overstatement was fixed at `Roadmap.md:7` and left at `Roadmap.md:5`, one line
   above (finding 2.2).

Round 1's own QI candidate (a docstring-reference linter) would have caught **none** of
these: this is not reference rot, it is a remediation-coverage gap. Two mechanical fixes:

- **A Stage-13 remediation manifest.** The reviewer's report already numbers every finding.
  Require the remediation commit to carry a machine-readable block — one line per finding ID
  with `fixed | deferred | rejected` plus the touched path — and have `validate.py` (or the
  round-N+1 reviewer's harness) diff that manifest against the finding IDs in the report it
  claims to answer. "All fixed, none skipped" then becomes checkable instead of asserted.
- **Re-derive every number a review cites.** Round 1's "254 `Detection.*` declarations" was
  wrong by ~60% and propagated unchallenged into the commit message, the phase notebook, and
  the BLOCKER's evidence line (finding 4.4). Any count in a review report should be emitted
  by a query against `lean_deps.json` / the graph, with the query recorded next to it, not
  typed by hand.
