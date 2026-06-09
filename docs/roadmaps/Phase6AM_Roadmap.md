# Phase 6AM — Adopt PhysLib (DPI / Lieb / SSA / REE) + close the 6AN/6AL substrate residuals (quantum-FDT floor · Ross–Selinger optimal synthesis · sharp Fannes–Audenaert)

**Status: REVISED 2026-06-09 — scope expanded. (a) Adopt PhysLib for the entropy/capacity cluster
(was the 2026-06-04 revision); (b) ADD waves closing the Phase-6AN residuals — the quantum-FDT
(Callen–Welton) amplifier/detector floor (W4) and the Ross–Selinger O(log 1/ε) optimal Clifford+T
synthesis (W5); (c) ADD the 6AL Gap-1 cleanup — the sharp Fannes–Audenaert `log(d−1)` constant (W6),
discharging `hAud`. Do NOT hand-roll DPI / Lieb concavity / SSA / REE.
**Full-strength budget: ~50k LoC for the whole phase** (W2–W7, all cleanup included) — generous
**by design** to remove LOE/budget guesswork; build every wave at full strength now, in-context.**

> **⚠️ AGENTS IN FLIGHT — READ THIS FIRST.** An earlier draft of this phase planned to build the
> data-processing inequality (DPI) from scratch (vendor-in operator concavity of log → construct the
> relative modular operator → discharge joint convexity → REE). **That plan is SUPERSEDED.** The entire
> cluster is already proven, complete and kernel-clean, in **PhysLib** (`leanprover-community/physlib`,
> arXiv:2510.08672), which is pinned to **Mathlib v4.29.1 / 5e932f97 — our exact toolchain pin**. Do not
> reinvent any of it. This phase is now: *adopt PhysLib and bridge to it* (W1–W3), *close the 6AN
> residuals* (W4 quantum-FDT floor, W5 Ross–Selinger), and *optionally migrate* (W6).

## Gate-strength discipline + no-effort-based deferral (READ BEFORE EVERY WAVE — 2026-06-09)

This phase was hardened after a review found two recurring failure modes. Both are **forbidden here:**

1. **No weak-form / vacuous / definitional-only deliverable.** Every gate below specifies the
   *strength* of what ships, not just its shape. A bridge that round-trips only on a trivial channel
   class, a corollary stated so weakly it is `True`-adjacent, an FQN **cited in a docstring but never
   invoked in the proof body** (the CLAUDE.md **P6** anti-pattern), or a "REE" that delivers only the
   *definition* and not an *operational bound on a concrete channel* — all FAIL the gate. Apply the
   five preemptive-strengthening questions (CLAUDE.md) to every theorem statement before writing it.
2. **Effort/LoC is NEVER a reason to defer, ask, down-scope, OR gate.** The project ships ~15k LoC/day;
   this phase has a deliberately generous **~50k LoC full-strength budget** (covers W2–W7 including all
   cleanup), set high precisely to **remove LOE/budget guesswork** — which in a long auto-dev session is
   far more expensive than building at full strength from the start. **Do NOT introduce LoC thresholds
   or "stop if > N lines" gates anywhere** (e.g. build the W6 finite-Fano scaffolding to whatever size
   it takes). The ONLY legitimate pause is a **genuine wall** (axiom-needing, or machinery that truly
   cannot be built — established by decompose → Mathlib-MCP/PhysLib-search → Explore-fan-out) or a true
   product tradeoff only the user can make. **"Absent from Mathlib" is a BUILD instruction, not a wall.**
   A "documented-gap / awaiting-sign-off / stop-at-N-LoC" note whose only blocker is effort is the
   antipattern (it silently makes the user the bottleneck). **Do the work now, in context — do not ship
   loose ends to circle back to.** Each wave states its real-world reason so it can't be re-deferred.
   See memory `feedback-no-hypothesis-based-descope`.

## What PhysLib already provides (verified complete, 0 axiom)

| PhysLib module | content | thms | sorry |
|---|---|---|---|
| `QuantumInfo/Finite/Entropy/DPI.lean` | **data-processing inequality** (sandwiched-Rényi, strong form) | 45 | 0 |
| `QuantumInfo/Finite/Entropy/SSA.lean` | **strong subadditivity** | 34 | 0 |
| `…/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean` | **Lieb / Lieb–Ando trace concavity** | 6 | 0 |
| `…/TraceInequality/GeneralizedPerspectiveFunction.lean` | **operator perspective** (the joint-convexity route) | 4 | 0 |
| `…/TraceInequality/LownerHeinzTheorem.lean`, `JensenOperatorInequality*.lean` | operator monotone / operator Jensen | — | 0 |
| `QuantumInfo/Finite/Entropy/VonNeumann.lean` | von Neumann entropy | 18 | 0 |
| `QuantumInfo/Finite/Entropy/Relative.lean` | quantum relative entropy | 51 | 1 |
| `QuantumInfo/Finite/ResourceTheory/FreeState.lean` | **separable / free-state framework** (the REE substrate) | 33 | 0 |
| `QuantumInfo/Finite/Distance/{Fidelity,TraceDistance}.lean`, `Entanglement.lean`, `Capacity.lean` | fidelity, trace distance, entanglement measures, capacity | — | — |

**Consequence:** the "genuine walls" the entropy work previously deferred — DPI, strong subadditivity, and
the relative entropy of entanglement (REE, `inf` over the separable set) — are **not walls**: PhysLib has DPI,
SSA, and the free-state/separable framework already. The remaining content is **interoperation**, not proof.

## The actual work: adopt + bridge

The existing in-repo QI substrate (`QuantumNetwork/*`: diamond/fidelity/entropy/negativity) is built on raw
**Kraus families** (`Fin m → Matrix`); PhysLib is built on `MState` / `CPTPMap`. The work is to connect them.

### Wave 1 — add PhysLib as a project dependency  ✅ DONE (2026-06-04, commit `f7a0add4`)
- ✅ Added `[[require]] Physlib` to `lean/lakefile.toml`, pinned to `69197c5449929b4949d1ec2326fb6a5c3f04eac5`
  (git `leanprover-community/physlib`). **Validated** before adding: that commit's `lake-manifest` Mathlib rev ==
  `5e932f97…` and toolchain == `leanprover/lean4:v4.29.1` — **identical to ours**, so NO toolchain/pin bump.
- ✅ `lake update Physlib` resolved cleanly: core dep revs (mathlib `5e932f97`, batteries `756e3321`, aesop
  `7152850e`, Qq `707efb56`, proofwidgets `4dd0959c`) **UNCHANGED**; only `Physlib` + its doc-gen4 transitive deps
  (doc-gen4, leansqlite, Cli, UnicodeBasic, BibtexQuery, MD4Lean) added to the manifest. Our build still resolves
  (`SKEFTHawking.QuantumNetwork.MirskyUnconditional`, 3364 jobs). Apache-2.0.
- ⏳ **REMAINING gate (not yet run):** nothing imports PhysLib yet, so it hasn't been *built*. Before relying on
  any PhysLib theorem, `lake build` a PhysLib target and run `#print axioms` on the DPI/SSA headlines to confirm
  kernel-pure `{propext, Classical.choice, Quot.sound}` AT THIS COMMIT (the 0-sorry/0-axiom counts in the table
  above were read from the GitHub tree / a sibling copy — re-verify against `69197c54` locally). Module paths at
  this commit: `QuantumInfo/Finite/Entropy/{DPI,SSA,Relative,VonNeumann}.lean`,
  `QuantumInfo/Finite/Distance/{Fidelity,TraceDistance}.lean`.

### ⚠️ Note: PhysLib does NOT close 6AL Gap 1 (sharp Fannes–Audenaert `log(d−1)`)
PhysLib has only **qualitative** entropy continuity (`Sᵥₙ_continuous`), no quantitative Fannes–Audenaert bound, and
no Fannes/Audenaert file in the pinned tree. So adoption does **not** discharge the sharp-Audenaert hypothesis
`hAud`. That is a **6AL item** — full DR findings + the recommended Fano-grouping staged plan live in
**`Phase6AL_Roadmap.md` (Gap 1)**; the unconditional `log d` Fannes certificate ships meanwhile.

### Wave 2 — Kraus ↔ MState bridge *(the real LOE)*
- Provide the translation between the repo's Kraus-family channels / density matrices and PhysLib's
  `CPTPMap` / `MState`, so existing in-repo objects can be fed to PhysLib's DPI/SSA/entropy theorems and
  PhysLib results can be read back as statements about the repo's representation.
- **Gate (strength-pinned):** (i) a **faithful** round-trip bridge `repo channel → CPTPMap → repo`
  proven `= id` on the **full** in-repo Kraus-channel class (NOT a trivial/identity-only subclass),
  plus the matching state bridge `IsDensityOperator ↔ MState`, both kernel-pure; (ii) a **non-trivial
  transfer witness** — a real repo channel (e.g. a dephasing/depolarizing Kraus family) fed through the
  bridge into a named PhysLib entropy/DPI theorem **actually invoked in the proof body** so that
  `#print axioms` shows the PhysLib FQN in the closure. A docstring-only citation does NOT satisfy this
  gate (CLAUDE.md P6).

### Wave 3 — consume PhysLib for the downstream goals
- Discharge the previously-deferred targets by consuming PhysLib **by FQN** through the Wave-2 bridge:
  DPI for the repo's channels, strong subadditivity, relative-entropy monotonicity, and the
  relative-entropy-of-entanglement via the free-state framework. State the repo-facing corollaries.
- **Real-world reason:** the relative-entropy-of-entanglement / relative-entropy rate-ceiling is the
  downstream-blocking quantity for repeaterless entanglement-distribution and secret-key rate ceilings
  — the operational statement that the 6AK.2 PLOB surrogate and the negativity ladder could only
  *surrogate*, never prove. A merely-definitional REE does not unblock it.
- **Gate (strength-pinned):**
  - **DPI / SSA**: monotonicity corollary stated on the repo's representation for a **non-trivial**
    channel / tripartite state, PhysLib FQN invoked in the proof body.
  - **REE — OPERATIONAL, not definitional**: ship a **numeric/operational bound** `E_R(ρ) ≤/= <value>`
    on at least one **concrete** state (e.g. a Bell-diagonal / Werner state), evaluating the `inf` over
    the separable set through PhysLib's free-state framework — NOT merely "`E_R` is well-defined". The
    falsifiable comparison is the deliverable; a definition-only ship FAILS.
  - **Kernel-purity fence**: PhysLib `Entropy/Relative.lean` carries **1 sorry** at the pinned commit.
    NO consumed corollary may depend on the sorried declaration. `#print axioms` every consumed FQN; if
    a target routes through the sorry, route around it or stop and flag — never ship a corollary whose
    axiom closure is not `{propext, Classical.choice, Quot.sound}`.

### Wave 4 — quantum-FDT (Callen–Welton) amplifier/detector floor *(closes 6AN W4 residual)*
- **What:** Phase 6AN W4 (`QuantumNetwork/FDTNoiseFloor.lean`) used the *classical* Johnson–Nyquist
  floor `S_JN = 4 kB_T σ_Q`. Replace it with the **exact quantum (Callen–Welton) floor**
  `(ℏω/2)·coth(ℏω / 2kB_T)` — **derived, not assumed** — by instantiating a `CanonicalEnsemble` over the
  quantum-harmonic-oscillator level spectrum `Eₙ = ℏω(n+½)` and computing its `meanEnergy`
  (`Z = e^{-βℏω/2}/(1−e^{-βℏω})`, `⟨E⟩ = −∂_β log Z = (ℏω/2)coth(βℏω/2)`) via PhysLib's
  `CanonicalEnsemble.{meanEnergy,partitionFunction}` (consumed by FQN).
- **Real-world reason:** the amplifier/detector operating points that consume the 6AN W4 bound live in
  the cryogenic-mK / GHz regime where `ℏω ≳ kB_T`. There the classical `4kB_Tσ` floor is the **wrong
  asymptote** (it → 0, missing the zero-point `ℏω/2` that actually dominates). The quantum floor is the
  physically correct certificate floor for that regime.
- **Stays a cited hypothesis (the one textbook tracked hypothesis in the 6AN line — by design):** the
  **Caves** phase-insensitive-amplifier added-noise inequality `A ≥ ℏω/2`. It requires the bosonic CCR
  ladder algebra `[a,a†]=1`, which PhysLib does **not** provide (its `CreateAnnihilate` is a 2-element
  Wick-ordering label, `card = 2` — verified — not the ladder algebra), and a from-scratch CCR build is
  disproportionate to the certificate value. So: the **floor is derived**; the **added-noise inequality
  is cited**. This is a genuine wall, not an effort deferral — document it as such.
- **Gate (strength-pinned):** `(ℏω/2)coth(βℏω/2)` derived from the PhysLib `CanonicalEnsemble` HO mean
  energy (FQN invoked in proof), kernel-pure; a theorem that the quantum floor **strictly exceeds** the
  classical `4kB_Tσ`-equivalent in the `ℏω > 0` / `ℏω ≳ kB_T` regime; the 6AN detector/amplifier
  operating-point results re-anchored on the quantum floor (companion theorems). `#print axioms` clean.
- **Depends on:** W1 only (PhysLib importable). Independent of the W2/W3 QI bridge — can run in parallel.

### Wave 5 — Ross–Selinger O(log 1/ε) optimal Clifford+T synthesis *(closes 6AN W5 residual)*
- **What:** build the ℤ[ω][1/√2] exact-synthesis substrate and ship an **unconditional** Clifford+T
  compiler with **output word length `O(log(1/ε))`** (exponent **1**), replacing the Phase 6AN W5
  brute-force ε-cover base finder (correct + length-bounded, but at the standard SK
  `O(log^{log5/log(3/2)} (1/ε)) ≈ O(log^{3.97})` and computed by enumeration — a proof artifact, not a
  runnable compiler).
- **Real-world reason:** RS is the algorithm real compilers use (Gridsynth / Microsoft QDK). It gives
  the information-theoretically **optimal** `O(log 1/ε)` T-count (~10⁴× fewer gates than SK at
  ε = 10⁻¹⁰) **and** polynomial compile time. This is what lets a compiled-gate certificate report a
  **competitive (near-optimal) T-count**, not merely a correct one — i.e. it unblocks resource/cost
  estimation, which the SK form cannot support. Audience per the task: industry quantum-compiler teams.
- **Research is COMPLETE & de-risked** (not a research gap, not an effort deferral):
  `Lit-Search/Tasks/complete/ross_selinger_arxiv_1403_2975_zomega_invsqrt2_synthesis.md` +
  `Lit-Search/Phase-6x/Ross-Selinger Clifford+T Synthesis- A Pre-Implementation Research Dossier.md` +
  the §5/§6/§7 grid-problem-finder-completeness and KMM proof-mechanism docs.
- **LoC:** ~2,000–3,000 (auto-approved per the gate-strength discipline above; size is NOT a defer
  reason). The largest wave; may span several `/goal` continuations — that is sequencing, not de-scope.
- **Decomposition (from the task):** (1) ring `ℤ[ω]` (degree-8 cyclotomic; constructive `+,·`,
  `Decidable =/≤`); (2) `ℤ[ω][1/√2]` extension + `Decidable` Clifford+T-entry membership; (3) RS
  approximate synthesis (paper §7.4): `θ,ε ↦ ZOmegaSqrt2` unitary within ε, poly-time in `log(1/ε)`;
  (4) Kliuchnikov–Maslov–Mosca exact synthesis (arXiv:1206.5236): `ZOmegaSqrt2` unitary ↦ Clifford+T
  word + length bound; (5) compose → `RossSelinger.compile : SU(2) → FreeGroup (Fin 2)` discharging
  `BaseFinder_length_bounded` + `BaseFinder_approximates_within … (2·ε₀)`; (6) the unconditional
  `O(log 1/ε)` headline.
- **Gate (strength-pinned):** `RossSelinger.compile` shipped; the **unconditional** Clifford+T headline
  with an **`O(log(1/ε))`** word-length conjunct (exponent **1**, not 3.97); kernel-pure
  `{propext, Classical.choice, Quot.sound}`, no new project-local axioms (#15), no `native_decide`, no
  `maxHeartbeats` (#10); full lib + `ExtractDeps` build green; Stage-13 adversarial review.
- **Depends on:** nothing in 6AM — self-contained (number theory + the existing FKLW SK substrate
  `RossSelingerLightweight.lean` / `CliffordTQuantitative.lean`). Independent of PhysLib.

### Wave 6 — sharp Fannes–Audenaert `log(d−1)` constant *(closes 6AL Gap 1)*
- **What:** discharge the `hAud` hypothesis in `QuantumNetwork/MirskyUnconditional.lean`'s
  `quantum_fannes_audenaert`, shipping it **unconditional** with the sharp **Audenaert `log(d−1)`**
  constant: `|S(ρ)−S(σ)| ≤ T·log(d−1) + H₂(T)`, `T = ½‖ρ−σ‖₁` (= `Real.qaryEntropy d T`). NOTE the
  unconditional `log d` (Fannes) trace-distance certificate (`quantum_fannes_trace_distance` /
  `quantum_fannes_certificate`) is ALREADY shipped (the `hB3`/Wielandt residual was eliminated by
  `mirsky_unconditional`) — this wave is the **sharper constant**, NOT a missing capability.
- **Real-world reason:** the gap `log d → log(d−1)` is largest exactly in the **few-qubit regime** where
  hardware certification lives — for a qubit (d=2) the leading term **vanishes** (`log 1 = 0`; the bound
  becomes `H₂(T)` alone); d=4 ≈21% tighter, d=8 ≈6%; negligible for large d. ⟹ tighter, less-conservative
  entropy/entanglement certificates for noisy few-qubit states, in the **textbook-standard
  Fannes–Audenaert form** (the canonical citeable bound). Spin-off: a reusable **finite-alphabet Fano
  inequality + discrete conditional-entropy layer** — verified ABSENT from Mathlib (`Real.qaryEntropy` +
  mono/concave lemmas are PRESENT; `Fano` / `conditionalEntropy` are ABSENT) → a genuine Mathlib
  contribution + the first machine-verified sharp Fannes–Audenaert in any prover.
- **DR done & de-risked** (it corrected the earlier "simplex-optimization" framing → the proof is
  *elementary* = Fano via maximal coupling): `Lit-Search/Phase-6AL/Formalizing the Sharp (Audenaert)
  Classical Fannes Bound…md`.
- **Build plan (NOT gated — build each stage to whatever size it needs; no LoC threshold):**
  S1 spreading estimate `H(p) ≤ (1−p₁)·log(d−1) + h(1−p₁)` (Jensen on the `d−1` tail via
  `strictConcaveOn_negMulLog` + `qaryEntropy` monotone packaging — in reach now, reuses shipped assets);
  S2 a `Fin`-indexed conditional-entropy layer + **Fano-by-grouping** `H(X|Y) ≤ P(X≠Y)·log(|𝒜|−1)+h(·)`
  — **build it from scratch** (Fin-indexed preferred; if a measure-theoretic `measureEntropy` bridge is
  the cleaner route, build that too — it is absent-machinery, **not** a wall); S3 assemble + WLOG/`abs`
  glue → discharge `hAud`.
- **Gate (strength-pinned):** `quantum_fannes_audenaert` shipped **UNCONDITIONAL** (`hAud` removed, sharp
  `log(d−1)`); the Fano / conditional-entropy layer is real (non-vacuous, invoked in the proof body, not
  a restated hypothesis); kernel-pure `{propext,Classical.choice,Quot.sound}`, no new axioms (#15), no
  `native_decide`, no `maxHeartbeats` (#10); `#print axioms` clean; full lib + `ExtractDeps` green;
  Stage-13 review.
- **Depends on:** nothing in 6AM — self-contained (classical analysis on the eigenvalue distributions;
  builds on the existing 6AL `FannesAudenaert.lean` / `MirskyUnconditional.lean` substrate + Mathlib
  `qaryEntropy`). Independent of PhysLib.

### Wave 7 — (optional, longer-term) substrate migration
- Where it reduces maintenance, migrate the ad-hoc in-repo QI substrate (diamond/fidelity/entropy/negativity)
  onto PhysLib's `MState`/`CPTPMap` rather than maintaining a parallel formalization. This is a deliberate,
  incremental decision per module — not required to land Waves 1–6. Leave dual + bridged where migration cost
  exceeds benefit. (Genuinely optional — this is per-module hygiene, not a value-bearing deliverable.)

## Standing invariants
Kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (Invariant #15); no
`native_decide`; no `maxHeartbeats` in proof bodies; do **not** bump the Mathlib pin; never push.

## Sequencing
**Critical path (entropy/capacity unblock):** W1 (dependency add — small, DONE) → W2 (the bridge) → W3
(consume; ships the previously-walled REE / DPI / SSA results). Start at W1; it unblocks the QI cluster.
**W4 (quantum-FDT floor)** needs only W1 (PhysLib importable) — runs in parallel with W2/W3.
**W5 (Ross–Selinger)** and **W6 (sharp Fannes–Audenaert)** are each self-contained and independent of
PhysLib (W5: number theory + the FKLW SK substrate; W6: classical analysis + the 6AL
`FannesAudenaert.lean` / `MirskyUnconditional.lean` substrate + Mathlib `qaryEntropy`) — start either
whenever; both may span several `/goal` continuations. W7 (optional migration) last.
**Full-phase budget ~50k LoC (generous-by-design; do NOT gate on LoC anywhere).** No wave may ship a
weak-form, definitional-only, or docstring-cited deliverable (see the gate-strength discipline up top).

## Note for coordination
Several adjacent phases (entropy/entanglement strengthening; channel-composition substrate, Phase 6AN W1)
overlap PhysLib's `Distance.lean` / `Entropy/*` — **check PhysLib before proving any QI lemma from scratch.**
The previous from-scratch DPI/modular-operator plan is retained only in version history; do not resurrect it.
