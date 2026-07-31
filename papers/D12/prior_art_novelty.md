# D12 — Prior Art & Novelty Record

**Bundle:** D12 — Kernel-Verified Detector & Readout Metrology
**Compiled:** 2026-07-30, at first content-lift.
**Method:** `skeft-qa:research-scout` sweep over whitelisted scholarly sources
(arXiv API, DOI resolution), **plus direct source reading of the pinned local
Mathlib and PhysLib checkouts** — the latter is the strongest evidence class
here and is why the Lean-side negatives are high-confidence rather than merely
"search found nothing."

**Pin at time of survey:** Mathlib `81a5d257` (v4.32.0), PhysLib `c4843367`.

> **⚠️ THIS BUNDLE'S NOVELTY CLAIM HAS ALREADY BEEN REFUTED ONCE.** Phase 6EA's
> original claim — "no theorem prover has a kernel-checked [discrimination-bound]
> family" — was falsified on 2026-07-28 by a live prior-art sweep, and falsified
> *inside our own dependency tree*. Only the narrowed, knowledge-hedged form
> below may be used. An unhedged "first in a proof assistant" anywhere in the
> D12 draft is a Stage-13 **BLOCKER**, not a stylistic note.

---

## 1. What may be claimed (narrowed, hedged)

Safe to state as *first in any interactive theorem prover, to our knowledge*,
subject to §4:

| # | Claim | Strength |
|---|---|---|
| N1 | **Detection-theoretic** photon counting — miss probability, false alarm, dark counts. Formalized Poisson *distributions* are common (Mathlib, Isabelle, HOL4, Mizar); formalized photon-counting *discrimination* is not. **State it as detection-theoretic**, or a referee will counterexample with the distribution formalizations. | High — cleanest "first" available |
| N2 | Bhattacharyya / Le Cam average-error discrimination bounds for Poisson hypotheses. | High, but see the blocking check in §3 |
| N3 | ENBW, NEP, matched-filter optimality, and a bandwidth–duration realizability bound on a filter. Grep for `bolomet\|Johnson noise\|noise-equivalent\|matched filter\|responsivity\|transition-edge` over the **entire** `.lake/packages` tree returns **zero** matches. | High (Lean), medium (other ecosystems) |
| N4 | An electrothermal **device** model — loop gain, responsivity, thermal and Johnson noise floors. | **Strongest claim in the bundle** |
| N5 | Rotating-wave approximation with an explicit Bloch–Siegert-scale error bound; ODE averaging in Banach algebras. Word-boundary grep for `\bRabi\b\|rotating.{0,5}wave\|Siegert\|Jaynes\|Cummings` across all packages returns only `rwa`-the-tactic and a publisher name. | High |

---

## 2. Mandatory carve-outs

### C1 — Quantum channels: CPTP / Kraus / Choi / POVM **exist in three ecosystems**

This is the largest carve-out and D12 claims **none** of it.

- **Lean / PhysLib** (most complete, finite-dimensional): `MatrixMap` channels;
  Choi matrix with `choi_equiv`; Kraus representation `of_kraus` with
  `of_kraus_isTracePreserving`; the property hierarchy `IsTracePreserving` /
  `Unital` / `IsHermitianPreserving` / `IsPositive` / `IsCompletelyPositive`;
  **Choi's theorem** `choi_PSD_iff_CP_map`; bundled `CPTPMap`; Stinespring
  dilation; and on top of it von Neumann / relative / Rényi entropy, DPI, SSA,
  trace distance, fidelity, Fuchs–van de Graaf, Holevo capacity.
  (arXiv:2510.08672)
- **Coq / CoqQ**: super-operator denotational semantics on finite-dimensional
  Hilbert spaces, quantum operations as CP trace-nonincreasing super-operators,
  labelled Dirac notation, a soundness-proved quantum Hoare logic.
  (arXiv:2207.11350)
- **Isabelle/HOL**: Unruh's Complex Bounded Operators (arXiv:2512.05878);
  projective measurements and CHSH (arXiv:2103.08535).

### C2 — **Quantum** hypothesis testing exists; D12 does not consume it

PhysLib formalizes `OptimalHypothesisRate` (`QuantumInfo/ResourceTheory/
HypothesisTesting.lean`), the infimum over POVM elements of the worst-case
Type-II error subject to a Type-I constraint, with compactness of the strategy
set proved.

**D12 must not claim to consume it.** Zero `Detection.*` declarations reference
`OptimalHypothesisRate`; the single occurrence in `Detection/` is a docstring
*disclaiming* it. The registered kernel no-go
`6ea-optimalhypothesisrate-quantum-seam` (verdict `dead`) records the reason as
type-level impossible two independent ways: Poisson on ℕ is not a `Fintype`, and
asymmetric Neyman–Pearson versus symmetric Bayes/Le Cam is a category error.

**Related correction:** the POVM layer D12 *does* consume is the **project's own**
D9-family `QuantumNetwork/HelstromDiscrimination.lean` (`IsBinaryPOVM`,
`quarter_sqrtFidelity_sq_le_povmAvgError`) — a D12→D9 edge, **not** a PhysLib
first. `PAPER_STRATEGY.md` claimed otherwise until corrected 2026-07-30.

### C3 — Chernoff bounds exist; ours is a **sharpening, not a first**

Mathlib carries `ProbabilityTheory.measure_ge_le_exp_mul_mgf`,
`measure_le_le_exp_mul_mgf`, `measure_ge_le_exp_cgf` (explicitly docstringed
"Chernoff bound") plus `Moments/SubGaussian.lean`. At `c = 1` the sub-Gaussian
constant is a **factor 2 weaker** than our `gaussianTail_chernoff`, so ours is a
genuine refinement — and must be positioned as one. Isabelle's AFP
*Concentration Inequalities* likewise carries Bennett/Bernstein/McDiarmid
(⚠️ unverified — see §4).

The in-Lean docstring at `Detection/GaussianThreshold.lean` already states this:
*"this is a refinement, not a first … never as the first kernel-checked Chernoff
bound."*

### C4 — Divergences exist

Mathlib has Kullback–Leibler divergence (`Mathlib/InformationTheory/
KullbackLeibler/`, `klDiv`, Gibbs' inequality) and
`SignedMeasure.totalVariation` (as a Jordan-decomposition measure, **not** a
statistical distance between probability measures, and with no testing
corollary). HOL4 has KL via Lebesgue integration (Mhamdi et al., ITP 2011).
Isabelle `HOL-Probability` has entropy/mutual information.

Mathlib does **not** have Hellinger divergence, Hellinger affinity, or a
Bhattacharyya coefficient: the only `Hellinger` occurrences are the
Hellinger–Toeplitz theorem, and the only `Bhattacharyya` occurrence is an author
name. There is **no** Neyman–Pearson lemma, hypothesis test, likelihood-ratio
test, or error probability anywhere in Mathlib.

⚠️ PhysLib's `Fidelity.lean` documents fidelity as "the quantum version of the
Bhattacharyya coefficient" and carries a **TODO** at line 137 reading "Matches
with classical (squared) Bhattacharyya coefficient" — i.e. the classical
correspondence is *not proved* there. The file also still contains at least one
`sorry`.

### C5 — Transform methods and transfer functions exist

HOL Light formalizes Laplace and Fourier transforms for transfer-function and
frequency-response analysis (arXiv:1705.10050); its abstract mentions no noise,
bandwidth, matched filter, or detection. Related Concordia HVG work covers
Z-transforms and photonic signal-flow graphs (Mason's gain formula) — all
transfer-function algebra, no stochastic noise model.

**Carve-out wording:** transform methods and transfer-function algebra *are*
formalized; the stochastic noise-metrology layer built on top of them is not.

### C6 — Operator uncertainty relations exist

PhysLib proves Robertson and Robertson–Schrödinger uncertainty bounds
(`QuantumMechanics/Operators/Uncertainty.lean`). These are commutator/operator
relations, **not** a time–bandwidth or ENBW·T bound on a filter impulse
response. Mathlib has Cauchy–Schwarz but no Fourier uncertainty principle.

### C7 — Adjacent, must be acknowledged: PhysLib thermoelectrics

`CondensedMatter/Thermoelectric/Basic.lean` formalizes linear-response Onsager
relations, `powerFactor`, and the figure of merit `zT` with
`figureOfMerit_pos`. This is a **material** figure of merit, not a device
thermal circuit: no heat capacity, no conductance to a bath, no bias circuit, no
feedback loop gain, no responsivity, no noise floor. PhysLib has **no**
`Detectors`, `Metrology`, or `Instrumentation` namespace at all.

---

## 3. ⛔ TWO BLOCKING PRE-SUBMISSION CHECKS

These are gates, not suggestions. D12 may not be submitted until both are run.

1. **`RemyDegenne/testing-lower-bounds`** ("Information theory and hypothesis
   testing, in Lean") — an out-of-Mathlib Lean project targeting f-divergences
   and hypothesis-testing error bounds. **A Bayes-binary-risk ↔ divergence lower
   bound there would be substantially our Le Cam floor.** This remains the
   **highest prior-art risk in the bundle**.

   **PARTIALLY RESOLVED 2026-07-31 — one genuine hit, from a whitelisted
   primary.** The repository itself is on `github.com`, still outside this
   repo's egress whitelist, so it has *not* been inspected. But
   `Degenne2025Kernels` (arXiv:2510.04070, §on entropy/KL) states the project's
   headline content directly, and it is now citable:

   > "The Kullback-Leibler divergence definition now in MATHLIB was developed in
   > the TestingLowerBounds project [LD24]. A highlight of the project is a proof
   > of the **data-processing inequality for f-divergences**, a class of
   > divergences between probability distributions that includes KL, as well as
   > the chain rule for KL."

   with `[LD24] = L. Luccioli and R. Degenne, TestingLowerBounds, 2024`.

   **Consequence — this is a real prior-art relationship and must be disclosed,
   not argued away.** The squared Hellinger distance is an f-divergence
   (`f(t) = (√t − 1)²`), and the Bhattacharyya affinity is its complement. So a
   *general* f-divergence data-processing inequality there plausibly **subsumes
   our `affinity_le_binaryAffinity`** — one of the two load-bearing lemmas under
   `poisson_avgError_floor`. The draft must cite `LuccioliDegenne2024` for that
   lemma's context rather than presenting the affinity DPI as unprecedented.

   **Still unresolved (needs the repo):** whether the project carries (a) the
   Poisson closed form `poissonBhattacharyya_hasSum`, (b) a Le Cam two-point
   *average-error* floor of the `P_e ≥ ¼exp(−(√Nₐ−√N_b)²)` shape, or (c) a
   Bhattacharyya coefficient as a named object. The Degenne paper names neither
   a Le Cam bound nor any Poisson-specific result, but it is a Markov-kernels
   paper and its silence is **not** evidence of absence in the downstream repo.
   Absence must not be asserted for any of (a)–(c).
2. **Isabelle/AFP `Error_Function` + `Probability`, and Coq `infotheo`** —
   **wholly unassessed.** That is a gap in the evidence, not a finding of
   absence. The draft must not assert absence in these ecosystems.

Mathlib's probability/information-theory area is under active development by
Degenne and Luccioli. **Re-run the greps immediately before submission** and
date-stamp every novelty claim to the pin.

### 3a. Sweeps run 2026-07-31 (previously asserted without running them)

Three claims in the draft were hedged or withdrawn on the strength of a sweep
that had **never actually been run**. They were run on 2026-07-31; two resolve
*in favour* of the original claim and one produced the genuine hit above.

| Claim | Sweep result |
|---|---|
| Classical↔quantum Bhattacharyya correspondence (`diagonalState_sqrtFidelity_eq_affinity`) | **Stands, and was understated.** Verified by direct read of the pinned PhysLib checkout: `QuantumInfo/States/Mixed/Fidelity.lean:136-139` is a four-item `--TODO:` list whose second item is "Matches with classical (squared) Bhattacharyya coefficient" — i.e. PhysLib lists this correspondence as **open**. Our theorem also assumes only non-negativity, not normalisation, so it is *strictly more general* than the `MState`-bound version that TODO contemplates. Separately, PhysLib's `fidelity_channel_nondecreasing:133` is `@[sorryful]` — its fidelity data-processing inequality is an open `sorry` at pin `c4843367`, and we consume none of it (our axiom closures are exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`). |
| `ENBW·T ≥ 1/2` has no canonical primary source | **Stands.** The engineering literature carries the relation only as a *convention* tied to particular filters — `t_int = 1/(2·ENBW)`, and `ENBW = 1/4T` for a single-pole lock-in filter — never as a proved inequality, and never with a sharpness/least-element characterisation. Gabor (1946) remains the right antecedent to cite, and remains a *different* Cauchy–Schwarz statement. Proving it self-contained is correct. |
| `RemyDegenne/testing-lower-bounds` | **One genuine hit — see §3.1 above.** The f-divergence DPI plausibly subsumes `affinity_le_binaryAffinity`. Cite `LuccioliDegenne2024`. |

---

## 4. Honest coverage gaps

1. **Egress-blocked, therefore `unverified-primary`:** every Isabelle **AFP**
   entry (`isa-afp.org` is denied by this repo's egress guard) — *Kraus Maps*,
   *Concentration Inequalities*, *Projective Measurements*, *Isabelle Marries
   Dirac*. The arXiv companions that *were* fetched (2512.05878, 2103.08535)
   partly cover the last two. **Do not cite an AFP entry** until re-verified
   from an unblocked host.
2. **Network-blocked (not policy):** `leanprover-community.github.io`,
   `projecteuclid.org`, `link.aps.org`, `github.com`. The Mathlib-docs loss was
   fully compensated by reading the pinned source on disk.
3. **Ten DOIs are flagged must-verify-before-bibliography** and are consequently
   **not cited** in the D12 draft: 10.1007/s10817-013-9298-1 (infotheo/Shannon),
   10.1007/s10817-020-09584-7 (Isabelle Marries Dirac),
   10.1007/978-3-319-19458-5_11, 10.1007/978-3-642-45221-5_50,
   10.1007/978-3-319-08970-6_31, 10.1007/978-3-642-22863-6_18 (Mhamdi entropy —
   chapter number especially uncertain), 10.1109/PROC.1963.2383 (North),
   10.1364/JOSA.39.000327 (Jones), 10.1214/aos/1176342380 (Le Cam 1973),
   10.4230/LIPIcs.ITP.2026.3.
4. **Absence claims for HOL4 / PVS / Mizar / Agda are search-index-based only.**
   Use *"we are aware of no formalization in …"*, never *"there is no
   formalization in …"* for those four.
5. **DOIs marked verified were verified by resolution, not by reading the
   landing page** — most publishers return 403 to automated fetches. For
   `Irwin1995` the redirect slug additionally confirmed title, volume, issue and
   page; that is the best-verified citation in the bundle.

---

## 5. Citation cautions carried into the draft

- **`Gabor1946` is the VARIANCE-based uncertainty product** (ΔtΔf ≥ ½, equality
  for Gaussians). The D12 theorem is the *filter* statement ENBW·T ≥ 1/2, a
  **different** Cauchy–Schwarz consequence. No canonical primary for the ENBW·T
  form was located, so the draft proves it self-contained and cites Gabor only
  as the classical antecedent. Citing Gabor *as* the source of the ENBW bound
  would be a misattribution.
- **`Kailath1967` is the resolvable anchor** for the Bhattacharyya bound.
  Bhattacharyya's 1943 original (Bull. Calcutta Math. Soc. **35**, 99) has **no
  DOI** and should appear only as a historical reference, if at all.
- **`LeCam1986`** is the preferred Le Cam anchor; the 1973 *Ann. Statist.*
  alternative is unverified (Project Euclid unreachable).

---

*Companion to `papers/D12/paper_draft.tex`. Consumed by
`skeft-qa:claims-reviewer` and the Stage-13 adversarial reviewer via the D12
anchor block in `docs/agents/claims-reviewer-bundle-prompts.md`.*
