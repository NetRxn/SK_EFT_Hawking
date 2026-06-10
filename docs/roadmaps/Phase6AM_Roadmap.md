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
- **Gate (strength-pinned — ORIGINAL):** `RossSelinger.compile` shipped; the **unconditional** Clifford+T
  headline with an **`O(log(1/ε))`** word-length conjunct (exponent **1**, not 3.97); kernel-pure
  `{propext, Classical.choice, Quot.sound}`, no new project-local axioms (#15), no `native_decide`, no
  `maxHeartbeats` (#10); full lib + `ExtractDeps` build green; Stage-13 adversarial review.
- **✅ WALL VERDICT RE-INVESTIGATED + RESOLVED (2026-06-09 PM; DR `Lit-Search/Phase-6AM/Is the Ross–Selinger
  O(log 1:ε) existence guarantee conditional…md` + Mathlib dig).** The earlier "prime-density wall" was
  **mis-framed** (it anchored on the sparse prime-`β•β` sufficient condition + a Dirichlet framing). Corrected
  status of the **ancilla-free** O(log 1/ε) *existence* (route B): it needs only that the residual be a
  *relative norm* (positive density) — **strictly weaker than RS's actual Hypothesis 29** (which demands
  *primality* of `β•β`). So (B) is **plausibly unconditional**, but its load-bearing step is a
  Friedlander–Iwaniec / half-dimensional-sieve lower bound over a *structured* candidate set — **not a citable
  theorem and not in Mathlib** (Landau–Ramanujan absent; Selberg sieve is upper-bound-only). Verdict:
  **"unconditional-but-needs-large-analytic-NT" → in Lean a tracked `Prop`, NEVER an axiom** (NOT a clean
  hard wall, NOT Lean-buildable short-term). **The genuinely-unconditional O(log 1/ε) path that IS
  Lean-buildable is KMM-with-≤2-ancillas** (arXiv:1212.0822) — mechanism: ancillas add variables so the
  norm equation is always solvable (Lagrange four-squares, `Nat.sum_four_squares`, IS in Mathlib). Both
  routes are scoped into the next `/goal` (see "Tracked future dedicated /goals" below). The amendment
  immediately below remains the correct statement for THIS (now-closed) phase.
- **🔒 GATE AMENDMENT (2026-06-09, user-approved after full diligence + fresh-context Opus 4.8 adversarial
  review).** The ORIGINAL "unconditional / no-native_decide" gate is **NOT achievable in this phase** for
  reasons established (not effort) by decompose → primary-DR read → independent review:
  - **Full ∀U-unconditionality is blocked by a genuine, literature-open analytic-NT wall.** Removing the
    `gridFindT … = some t` hypothesis bottoms out at the §6 existence that *some* grid candidate's residual
    `√2^{2k}−u·u*` is a relative norm — a **prime-of-given-norm-in-a-growing-grid-window** (Bunyakovsky /
    short-interval) statement. Mathlib's Dirichlet (`NumberTheory.LSeries.PrimesInAP`) is present but
    **insufficient** (gives a prime *somewhere above a bound*, not localized to the scaled disk); the result
    is **absent from Mathlib and open in the literature** — the source (Selinger arXiv:1212.6253, Ross thesis
    Prop 3.2.9) realizes it only **randomized under a prime-distribution hypothesis.** Disposition:
    **Caves-precedent tracked `Prop`, never an axiom** (#15 preserved).
  - **The 4 KMM `native_decide` axioms** in the consumed substrate are empirically un-eliminable by kernel
    `decide` under #10 (the enumerations blow the 200k-heartbeat budget; `maxHeartbeats` is forbidden) — they
    need structural reproofs, a separate program. **Project-TOLERATED** (`axiom_closure_allowlist`
    tracks-not-fails them); this phase does not eliminate them.
  - **ACCEPTED W5 DELIVERABLE (what this phase ships, gate MET as amended):** (i) the **efficiency headline**
    `rossSelinger_log_length_explicit` — output word length `≤ N₃ + 16·log₂(1/δ) + C`, i.e. **O(log 1/ε)
    exponent 1** vs SK `O(log^{3.97})` (the wave's raison d'être — practical T-count, RESOLVED); (ii) the
    **§6-gate made explicit + axiom-free**: `gridFindT_isSome_of_residual` (kernel-pure) +
    `rossSelinger_synth_of_residual` replace the opaque `gridFindT=some t` with the precise relative-norm
    existence `Prop`. No new axioms; no Mathlib-pin bump.
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

## Execution status (2026-06-09 — pre-adversarial-review snapshot; gates above are UNCHANGED)

- **W1 ✅ / W2 ✅ (`599c3be9`) / W3 ✅ (`c7fc6863`) / W4 ✅ (`b0bd8a8b`)** — meet their strength gates
  (per prior-session verification + #print axioms FQN checks).
- **W6 ✅ COMPLETE (`846f2ccf`)** — `SharpFannesAudenaert.lean`: `sharp_fannes_classical`
  (`|H(p)−H(q)| ≤ qaryEntropy d T`, maximal-coupling + per-column `spreading_bound` + `sum_g_le_binEntropy`
  conditional-entropy Jensen, the finite-Fano layer built from scratch) and the **fully unconditional**
  density-operator headline `quantum_fannes_audenaert_sharp` (`hAud` discharged, sharp `log(d−1)`, no
  residual). Kernel-pure `{propext,Classical.choice,Quot.sound}`, 0 axiom / 0 native_decide / 0
  maxHeartbeats; wired; lib+ExtractDeps green (9204); axiom_closure_allowlist + graph_integrity + counts
  pass. **Gate MET.**
- **W5 — efficiency ✅ delivered; full unconditionality blocked by a GENUINE analytic-NT wall (NOT effort).**
  Re-evaluated with the full protocol (decompose → read primary DR `Phase-6x/Ross–Selinger §5:§6:§7 grid-FINDER
  completeness.md` directly → ℤ[√2]-EuclideanDomain + ℤ[√2][i] substrate read). Findings:
  - **Efficiency (the W5 raison d'être) is shipped** (prior `ebbec284`): `rossSelinger_log_length_explicit`
    gives output word length `≤ N₃ + 16·log₂(1/δ) + C`, i.e. **O(log 1/ε) exponent 1**, vs SK `O(log^{3.97})`.
  - **§6-gate made explicit + axiom-free (this session):** `gridFindT_isSome_of_residual` /
    `rossSelinger_synth_of_residual` (LogLengthHeadline.lean) replace the opaque `gridFindT = some t`
    with the precise relative-norm existence (Ross Problem 3.2.4), reducible via
    `RelativeNorm.exists_relativeNorm_of_real_sumSq` to two-squares-over-ℤ[√2].
  - **The wall:** full ∀U unconditionality bottoms out at the §6 *existence* that, among the grid candidates
    (supplied unconditionally by the §5 scaled-two-disk convex geometry, Ross Lemma 5.2.38), *some* residual
    is a relative norm — a **prime-density** input the source literature itself (Selinger arXiv:1212.6253,
    Ross Prop 3.2.9) realizes only **randomized under a prime-distribution hypothesis**. This is a genuine,
    primary-source-confirmed analytic-NT gate, NOT a Mathlib gap and NOT effort → **Caves-precedent tracked
    `Prop` (never an axiom).** The constructive scaffolding that would thin it — §5 grid-FINDER convex
    geometry (ellipse uprightness / Step-Lemma 0.9 / Prop 5.2.36 enumeration completeness) + §6
    two-squares-over-ℤ[√2] (GaussInt2 EuclideanDomain + prime-splitting descent on the shipped
    `Zsqrt2EuclideanDomain`) — is a **dedicated multi-thousand-LoC sub-program (its own `/goal`)**, per the
    "large sub-programs get their own /goal, never dropped" discipline.
- **native_decide elimination (4 KMM sites) — kernel-`decide` confirmed INFEASIBLE under no-maxHeartbeats;
  needs structural reproofs (a dedicated sub-program).** Empirically sized: `cliffordBase_box_core` /
  `bridge_box_core` (`zomBox²×8`, matrix-interp / kSO3), `kmm_lemma3_alg2` (`(ZMod 8)⁴²` = 16.7M Coord4
  pairs), `maStep_exists_core` (`validCol³`; validCol filtered to 18/42/90 for t=2/4/8 ⟹ **~809k triples**,
  NOT the earlier "244M" — corrected by the adversarial review). All exceed the elaborator heartbeat budget
  for kernel `decide` (empirically demonstrated: even a t=2-only slice blows the 200k budget; `maxHeartbeats 0`
  finishes t=2 in ~45s — a *budget* wall, and #10 forbids `maxHeartbeats`), so each requires a STRUCTURAL
  reproof (KMM Lemma-3 mod-8 algebra [genuinely research-flavoured]; Giles–Selinger sde↔kSO3; Clifford-group
  ≤6-word coverage; MA-step orbit-closure [mechanical-tedious, not deep]) — the structural-KMM-correctness
  theory the KMM authors used `native_decide` to bypass.
  **Project-TOLERATED meanwhile** (`validate.py --check axiom_closure_allowlist` tracks-not-fails them).
  A dedicated `/goal` (structural KMM purity); not a wall, not dropped.

**Net (adversarial review 2026-06-09, fresh-context Opus 4.8 subagent — independently confirmed):**
W2, W3, W4, W6 **genuinely meet their strength-pinned gates and are kernel-pure** `{propext,
Classical.choice, Quot.sound}` (verified by independent `#print axioms` on 13 headlines; W3 routes around
the PhysLib `Relative.lean` sorry; W6 maximal-coupling math checked correct). **W5 does NOT meet its gate
as written** — the efficiency headlines remain (a) conditional on the residual existence and (b) carry the
4 KMM `native_decide` axioms in their closure, both explicitly forbidden by the W5 gate. This is an HONEST
tracked residual, NOT papered over: the descope rests on a **genuine, correctly-located prime-density wall**
(the review independently confirmed Mathlib's Dirichlet [`NumberTheory.LSeries.PrimesInAP`] is present but
**insufficient** — the need is primes-of-a-given-norm in a *growing grid window*, a Bunyakovsky/short-interval
statement absent from Mathlib and open in the literature), with the right axiom-free disposition (Caves-precedent
`Prop`, never an axiom). **DISPOSITION OPTIONS (user call):** (a) formally amend the W5 gate to accept the
tracked-`native_decide` + conditional-on-residual posture as the deliverable (efficiency met; full
unconditionality blocked by a literature-open conjecture); or (b) keep W5 open and spin the two constructive
sub-programs — §5/§6 grid-FINDER (convex geometry + two-squares-over-ℤ[√2]; thins but cannot remove the wall)
and structural-KMM `native_decide` elimination — into dedicated `/goal`s. Also flagged: the §5/§6/§7 RS
citation scaffolding (`Phase-6x` DR) is self-flagged PARTIAL-VIABLE (§6 iff-criterion / §7.2 constant
unconfirmed vs primary `1403.2975v3`) — verify before any RS claim is load-bearing in a published bundle.
No axioms added anywhere; no Mathlib-pin bump; never pushed.

> **[2026-06-09 PM — post-review DR update]** The user chose disposition (a). A follow-up DR then **refined
> the "prime-density wall"** above: the ancilla-free existence needs only *relative-norm* density (NOT
> primality), so it is **strictly weaker than RS Hypothesis 29** and *plausibly unconditional* — but
> Lean-impractical (Friedlander–Iwaniec lower bound; Landau–Ramanujan + lower-bound sieve absent from
> Mathlib) → tracked `Prop`, never an axiom. The genuinely-unconditional Lean-buildable path is
> **KMM-with-ancillas** (Lagrange four-squares core, in Mathlib). Read the "✅ WALL VERDICT RESOLVED" flag in
> the W5 section + the "Next /goal" tracks below as the current truth; this review paragraph is the
> as-of-review snapshot it supersedes.

## ✅ PHASE 6AM CLOSED (2026-06-09, user-approved)

Value-bearing work complete and gate-met (W2, W3, W4 per their original gates; **W6** fully — sharp
Fannes–Audenaert `log(d−1)`, `hAud` discharged, unconditional, kernel-pure; **W5** per the amended gate —
O(log 1/ε) efficiency + axiom-free §6-gate `Prop`). All kernel-pure `{propext, Classical.choice, Quot.sound}`
where claimed (independently `#print axioms`-verified by the closure adversarial review); lib + ExtractDeps
green (9204); axiom_closure_allowlist + graph_integrity + counts_fresh pass; counts refreshed. Commits
(NOT pushed): `599c3be9` `c7fc6863` `b0bd8a8b` `846f2ccf` `f16c3f81` `be40ce07`. W7 (migration) was optional,
not required — not done.

### → Next `/goal`: the W5-residual program (DR-sharpened 2026-06-09; see goal statement below)
The DR (`Lit-Search/Phase-6AM/Is the Ross–Selinger O(log 1:ε) existence…md`) sharpened the three strands.
Treat the DR as suggestion, not fact (the requesting side has the Mathlib/Lean access it lacked).

- **Track 2 — KMM-ancilla UNCONDITIONAL O(log 1/ε) Clifford+T (THE PRIZE; genuinely removes the wall).**
  KMM (arXiv:1212.0822, PRL 110:190502) gives unconditional O(log 1/ε) Clifford+T with ≤2 ancillas;
  mechanism = ancillas add variables ⟹ the norm/Diophantine equation is *always* solvable (Lagrange
  four-squares, `Nat.sum_four_squares`, IS in Mathlib). Map the exact KMM rounding+ancilla construction
  onto the shipped KMM exact-synthesis substrate (`KMMCompleteness`); ship the unconditional headline.
  This is NOT the BRS/RUS protocols (those keep a runtime hypothesis) — KMM specifically.
- **Track 1 — unconditional scaffolding + thin the bare-CT `Prop`.** (a) ℤ[√2] norm-Euclidean — ALREADY
  shipped (`Zsqrt2EuclideanDomain`; the DR listed it as a missing build — we're ahead). (b) finish
  ℤ[ω]=ℤ[√2][i] relative norm (`GaussInt2` + `RelativeNorm`). (c) the **even-power relative-norm criterion**
  (β a relative norm ⟺ every inert ℤ[√2]-prime to even power) — lift Mathlib `Nat.eq_sq_add_sq_iff`
  (ℤ template, PRESENT) over `Zsqrt2EuclideanDomain`; splitting law = `x²+1` mod π (split/inert ⟺ −1 is a
  square/non-square; ramified ⟺ residue char 2, π~√2 — DR-corrected). (d) §5 grid existence (Ross
  Lemma 4.4 / Thm 5.18 — paper numbering DR-confirmed). The terminal ancilla-free existence stays a tracked
  `Prop`: *"∃ k=log₂(1/ε)+O(loglog) with a relative-norm-solvable residual in R_ε"* — **strictly weaker
  than RS Hypothesis 29** (relative-norm, not primality), plausibly unconditional but its lower bound is a
  Friedlander–Iwaniec/half-dimensional-sieve statement (Landau–Ramanujan absent from Mathlib; Selberg sieve
  is upper-bound-only) → tracked `Prop`, NEVER an axiom.
- **Track 3 — structural-KMM `native_decide` elimination** (4 sites; project-tolerated meanwhile). Per-site:
  `cliffordBase_box_core` (Clifford ≤6-word coverage), `bridge_box_core` (Giles–Selinger sde↔kSO3 + column
  bounds), `kmm_lemma3_alg2` (mod-8 algebra — research-flavoured), `maStep_exists_core` (MA-step
  orthogonality-class orbit-closure — mechanical-tedious, ~809k triples). NO trusted-oracle/checksum fallback
  (= `native_decide` by another name). Benefits all KMM consumers.

## Phase 6AO execution log (the W5-residual `/goal`, started 2026-06-09)

### Track 2 — KMM ancilla (PRIORITIZED). Increments 1–2 shipped (kernel-pure, green).

- **Increment 1 ✅ — the unconditional number-theoretic keystone (`a8cf2f3d`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaCompletion.lean`:
  - `exists_two_relativeNorms_of_nat (r : ℕ) : ∃ t₁ t₂, normSq t₁ + normSq t₂ = (r:ZOmega)` — **every
    `r:ℕ` is a sum of two ℤ[ω] relative norms**, via Lagrange `Nat.sum_four_squares` (`r=a²+b²+c²+d²` →
    `t₁=a+bω²`, `t₂=c+dω²`, `normSq_real_sumSq`). **This is the wall-removing core**: the ancilla turns
    the single-relative-norm condition (sum of 2 squares over ℤ[√2], conditional/prime-density) into a
    sum-of-4-integer-squares condition — ALWAYS solvable. No Hypothesis 29, no prime density.
  - `ancilla_completion_of_nat_residual` — for an approximant `u` with integer `normSq u = m ≤ 2^k`,
    `∃ t₁ t₂, normSq u + normSq t₁ + normSq t₂ = 2^k` UNCONDITIONALLY (the (1+ancilla)-qubit unit column
    closes), vs the ancilla-free `rossSelinger_synth_of_residual` which REQUIRES a single relative norm.
  - `conj_intCast`/`conj_natCast` — rational integers are `conj`-fixed (real in ℤ[ω]).
  - Both headlines `#print axioms`-clean `{propext, Classical.choice, Quot.sound}`.
- **Increment 2 ✅ — two-qubit Clifford+T gate semantics (circuit-layer foundation) (`c787a24b`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/CliffordTGate2.lean` (`Matrix (Fin 2 × Fin 2)`, kronecker-native):
  `Gate2` ADT (onFst/onSnd single-qubit + cx01/cx10 cnots), `gateMatrix2`/`interp2`, `embedFst`/`embedSnd`
  (proven monoid homs via `Matrix.mul_kronecker_mul`), **`embedFst_interp`/`embedSnd_interp` — the
  load-bearing realizability transport** (single-qubit Clifford+T word → 2-qubit word, SAME length;
  so the shipped single-qubit `kmmReduce` transports onto the system/ancilla line at no length cost),
  `interp2_append`, `cnot{01,10}_mul_cnot{01,10}` involutions (kernel `decide`). Kernel-pure; cnot
  `decide` is KERNEL `decide` (native_decide count unchanged at 592).
- **Increment 3 ✅ — unconditional normalized ancilla state column (`3757096f`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaState.lean`: lifts the inc-1 integer identity to the
  ℤ[ω][1/√2] amplitude level. `ZOmegaSqrt2.mk_add_same`; `ancillaColNormSq` (3-entry extension of the
  shipped `KMM.colNormSq`); **`exists_ancilla_normalized_column`** — for an integer-residual approximant
  `u` (`normSq u = m ≤ 2^k`), the cleared column `(u,t₁,t₂)/√2^k` is a UNIT vector UNCONDITIONALLY (the
  KMM-ancilla existence, DR rec. #3, at the amplitude level — no relative-norm hypothesis). Kernel-pure.
- **Increment 4 ✅ — system-line synthesis on the two-qubit register (`bd6fd333`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaSynthesisBridge.lean`: `embedFst_kmmReduce_interp`
  (`interp2 ((kmmReduce M).map onFst) = embedFst M` — the shipped single-qubit KMM synthesis realizes
  `M⊗I` on the system line) + `embedFst_kmmReduce_length` (same `N₃+4·denExp` bound, no length cost).
  Connects inc-2 semantics to the verified `kmmReduce`; consumes the 4 TOLERATED native_decide
  (Track-3 targets), no new project-local axiom (native_decide decl-count 592→594, as any kmmReduce
  consumer). The building block for the ancilla circuit's system-line ops.
- **Increment 5 ✅ — two-qubit Clifford+T realizable class + closure (`0086d83f`).** `Gate2.IsRealizable`
  (`∃ w, interp2 w = M`) + `.one`/`.mul` (monoid closure)/`gateMatrix2_isRealizable`/cnot realizability;
  `embedFst_isRealizable` (single→2-qubit transport). The codomain 2-qubit synthesis targets.
- **Increment 6 ✅ — length-tracked realizability, the O(log 1/ε) composition law (`b3babeec`).**
  `Gate2.IsRealizableWithin M L` + **`IsRealizableWithin.mul` (budgets ADD under product)** + `.mono`/
  `.isRealizable`/`gateMatrix2_realizableWithin_one`; `embedFst_kmmReduce_realizableWithin` (system-line
  `M⊗I` within `N₃+4·denExp` = O(log 1/ε)). **This is the precise abstraction the headline needs**: a
  circuit assembled from O(log)-length pieces is O(log) overall.
- **✅ Construction RESOLVED via web search (2026-06-09; DR delayed, user-directed) —
  `Lit-Search/Phase-6AO/KMM-1212.0822-ancilla-construction-websearch.md`.** The KMM §2.1 Diophantine
  `a²+b²+c²+d² = 4^k − ⌊2^k cos φ⌋² − ⌊2^k sin φ⌋²` with `|v⟩ = (1/2^k)(⌊2^k cosφ⌋+i⌊2^k sinφ⌋, 0, a+ib,
  c+id)` **IS EXACTLY** the Phase-6AO keystone (inc 1) + normalized state (inc 3) at `K=2k`: `a+ib`,
  `c+id` = our `t₁=a+bω²`, `t₂=c+dω²`; `u=⌊2^k cosφ⌋+⌊2^k sinφ⌋i ∈ ℤ[i]`; residual `4^k−|u|² = 2^K−normSq u`.
  **Inc 1–6 confirmed faithful to the primary source — no correction.** **CRUX resolved:** *deterministic*
  unitary (no measurement/post-selection); the ancilla-|1⟩ leakage `|g⟩` is *bounded and folded into the
  ε error* `O(2^{−0.5k})` — so the headline is `‖W − Λ(e^{iφ})⊗I‖ ≤ ε` for a deterministic Clifford+T `W`
  (the naive-column "post-selection" worry is settled). **2 ancillas.** **Brick B (now unblocked)** =
  circuit C preparing `|v⟩` via O(k) Clifford+T (= 2-qubit exact synthesis of a ℤ[ω][1/√2] unit column,
  the Giles–Selinger/KMM-1206.5236 Column-Lemma at dim 4) + controlled-C (Column Lemma, no extra ancilla)
  + the leakage error bound. ~~Rounding-into-disk (`|u|²≤4^k`) stays the §5-style tracked hypothesis.~~
  **[UPDATED inc 8] The rounding is NO LONGER a hypothesis — inc 8 `exists_round_toward_zero` +
  `kmm_amplitude_approx` PROVE it unconditionally (∀φ,k ∃ disk-bounded `m₁,m₂` with `‖u/2^k − e^{iφ}‖ ≤
  √2/2^k`). So the z-rotation headline carries NO rounding hypothesis — stronger than this inc-6-era plan.**
- **Increment 7 ✅ — the KMM z-rotation ancilla state exists unconditionally (`21804cab`).**
  `AncillaState.lean`: `kmm_ancilla_state_exists (m₁ m₂ : ℤ) (k) (h : m₁²+m₂² ≤ 4^k) : ∃ t₁ t₂,
  Σ normSq((m₁+m₂ω², t₁, t₂)/√2^{2k}) = 1` — the exact KMM target column `|v⟩` is a UNIT vector for the
  Gaussian approximant `u = m₁+m₂i` in the disk, completion `t₁,t₂` by Lagrange four-squares (keystone).
- **Increment 8 ✅ — the unconditional amplitude approximation (rounding → ε) (`33f4700b`).**
  `AmplitudeApprox.lean`: `exists_round_toward_zero` (∃ m, m²≤x² ∧ |x−m|≤1 — disk-preserving rounding);
  `toComplex_gaussian_approx` (the shipped `ZOmegaSqrt2 →+* ℂ` embedding sends `mk (m₁+m₂ω²) (2k)` to its
  analytic amplitude `(m₁+m₂i)/2^k` via `s2C²=2`, `ω²↦i`); **`kmm_amplitude_approx`** (∀φ,k a disk-bounded
  approximant with `‖u/2^k − e^{iφ}‖ ≤ √2/2^k`, UNCONDITIONAL); **`kmm_ancilla_state_approx`** (milestone:
  inc-7 state + this amplitude bound). Kernel-pure; native_decide unchanged 596.
- **Increment 9 ✅ — the KMM leakage bound, the dominant `O(2^{−0.5k})` error (`38126592`).**
  `AncillaLeakage.lean`: `toComplex_normSq` (ring norm → complex squared modulus, `toComplex` is a *-hom);
  **`kmm_ancilla_state_full`** (∀φ,k: normalized + `|00⟩`-amplitude within √2/2^k of `e^{iφ}` + total
  ancilla-|1⟩ leakage `≤ 2·√2/2^k`, UNCONDITIONAL — leakage² = 1−|amp|², bounded via inc-8 + reverse
  triangle, `‖e^{iφ}‖=1`). **This completes the ERROR-BUDGET half of `‖W − Λ(e^{iφ})⊗I‖ ≤ ε`** (both the
  amplitude error and the leakage are now quantitative + unconditional). Kernel-pure; native_decide 596.

**REMAINING Track-2 brick = the CIRCUIT SYNTHESIS only** (multi-increment sub-program, NOT de-scoped):
the `O(k)` Clifford+T word that realizes a unitary preparing `|v⟩`, + its assembly into the operator-norm
headline + the length-`O(log 1/ε)` corollary (inc 6's composition law makes length automatic once the
synthesis is O(k)-piece-assembled). Per the websearch resolution, KMM §2.2 does NOT give a new explicit
circuit — it *invokes* the Giles–Selinger/KMM-1206.5236 **Column Lemma at dim 4** (no shortcut via a
guessable §2.2 gate sequence; the faithful route is the correct-by-construction exact synthesis). Structure
(reuse the dim-2 `KMMReduce`/`MAStep`/`*Column` machinery at dim 4 on the shipped `Gate2`/`Mat4` semantics):
(1) `colDenExp` of a 4-column; (2) base case `colDenExp v = 0` ∧ unit ⟹ `v = ωʲ·eᵢ` realizable by Clifford
`Gate2`; (3) reduction step `colDenExp = k+1 ⟹ ∃ O(1) Gate2 word g, colDenExp (g·v) ≤ k` (the residue/
syndrome lemma at dim 4 — the hard core); (4) induct ⟹ any unit column realizable in `O(colDenExp)` =
`O(k)` = `O(log 1/ε)` `Gate2` gates. Then controlled-C + operator-norm assembly on inc-8/9's error budget.

**Circuit-synthesis progress (inc 10–13, all kernel-pure, native_decide stays 596):**
- inc 10 (`77a3b91a`, `ColumnSynthesis.lean`): `IsColRealizableWithin` (column = `M·e₀` of a `Gate2`
  word ≤ L) + **`smul_left`** (the induction backbone: `G` realizable + `v` col-realizable ⟹ `G·v`
  col-realizable, budgets add) + base anchor `e₀`. inc 10b (`ad051faa`): all basis states `|a,b⟩`
  realizable within 2 (X-permutation, kernel `decide`).
- inc 11 (`55679480`, `ColumnBaseCase.lean`): `normSq_eq_one_iff_omega_pow` (`|z|²=1 ⟺ z=ωᵏ`) +
  `normSq_eq_zero_iff`. **Key simplification: the base case needs NO total-positivity / Galois /
  Kronecker** — `normSq` lands in ℤ[ω] with `(|z|²).d = a²+b²+c²+d²`, so `|z|²=1` ⟹ elementary
  sum-of-four-squares =1.
- inc 12 (`b0e7a345`): `unit_col_zero_denExp_structure` (`Σ|vᵢ|²=1 ⟹` one unit entry, rest 0) +
  `normSq_d_eq_zero_imp`. inc 13 (`3ebe0904`): `isColRealizableWithin_omega_pow_basis` (`ωᵏ·eᵢ`
  realizable within `k+2`, via `smul_omega`/`smul_omega_pow`). **⟹ base case (step 2) essentially
  DONE** — remaining = the `of`/`normSq` bridge (denExp-0 ⟹ ℤ[ω] entries via `denExp_le_iff` k=0;
  `normSq(of z)=of(normSq z)`) assembling `base_case : denExp-0 unit column ⟹ IsColRealizableWithin`.

**🔑 KEY DEPENDENCY (decomposition-backed, surfaced inc-reduction-step depth-read):** the reduction
step (3) reuses the dim-2 `reduceStep` (`H·Tᵏ`, col → `(z+ωᵏw)/√2`) + **`kmm_lemma3_column`**, whose
existence-of-reducing-`k` is the `native_decide` `kmm_lemma3_alg2` (KMM Algorithm 2; **no published
closed-form proof** — `(ZMod 8)⁴×(ZMod 8)⁴` computer check). So a **fully kernel-pure** Track-2 synthesis
shares its hardest dependency with **Track 3's hardest site** (`kmm_lemma3_alg2`). Efficient architecture
(matches "build on KMMCompleteness substrate"): **ship the synthesis reusing the tolerated-native_decide
dim-2 reduction** (exactly as inc-4 `AncillaSynthesisBridge` already consumes the 4 sites), then **Track 3
eliminates `kmm_lemma3_alg2`** (structural mod-8 / symmetry-reduced kernel-decide) ⟹ retroactively
kernel-pure. NOT a wall (provable, not axiom-needing) — sequencing, not de-scope.

**↑ inc 15 + inc 16 (the latter's framing CORRECTED — `kmm_lemma3` IS needed; see ⚠ below):**
- inc 15 (`ad3d7c77`): `colDenExp` measure + `ReductionStep C` predicate + **`colLemma_of_reductionStep`**
  (the column lemma by strong induction on `colDenExp`, reduced to `ReductionStep` alone — base case at 0,
  else `v=g·v'` climbs via `smul_left`). The ENTIRE remaining circuit-`C` synthesis is now the single
  `ReductionStep` brick (then controlled-C + operator-norm assembly).
- inc 16 (`6b7e337d`, `MatchingResidue.lean`): `dividesSqrt2_add_of_dividesSqrt2_sub` + `denExp_mk_succ_
  le_of_dividesSqrt2` — CORRECT facts, part of the elementary residue toolkit.

**✅ DEFINITIVE (web-verified 2026-06-09, `Lit-Search/Phase-6AO/GilesSelinger-1212.0506-column-lemma-
mechanism-websearch.md`): the `ReductionStep` is the GILES–SELINGER column lemma — ELEMENTARY, kernel-
pure, optimal O(lde), and INDEPENDENT of `kmm_lemma3`/Track 3.** This supersedes the inc-16 back-and-
forth below (both the v1 "elementary mod-√2" mechanism AND the v2 "kmm_lemma3 needed" walk-back were
off; the v2 conflated `kmm_lemma3` with the column lemma).
  - **Two ar5iv fetches settle it.** KMM 1212.0822: circuit C = "Lemma 20 (Column lemma) from [8]",
    [8] = **Giles–Selinger 1212.0506** "Exact synthesis of multiqubit Clifford+T circuits". Giles–Selinger
    reduction = **purely elementary**: Lemma 5 parity (`Σ xⱼ†xⱼ = 0000` over residues in `𝔽₂[x]/(x⁴+1)`;
    each summand ∈ {`0000`,`0001`,`1010`}; EVEN count of `0001` ⟹ a matching-residue-norm pair exists)
    + Lemma 4 row operation (3 explicit cases by residue norm, H/T 2-level word, denExp drops by 1).
    **"No algebraic number theory, class field theory, or number-theoretic decision procedures." NO
    `native_decide`.**
  - **`kmm_lemma3` is a DIFFERENT result** (KMM Algorithm 2: the SO(3)/`|·|²`-valuation optimal-T-count
    for ANCILLA-FREE single-qubit synthesis) — NOT what circuit C uses. The project's dim-2 column
    reduction happens to use it (a choice for the finer SO(3) optimality); the dim-4 KMM-ancilla circuit C
    does NOT. So the dim-4 `ReductionStep` neither needs nor reuses `kmm_lemma3`.
  - **Optimal T-count preserved**: Giles–Selinger gives O(lde) = O(log 1/ε) gates (exponent 1) — the
    headline's asymptotic optimality (saturates the constant-ancilla lower bound, per KMM). The finer
    kmm_lemma3/SO(3) optimality is ancilla-free-only and not required.
  - **⟹ kernel-pure `ReductionStep` is achievable via Giles–Selinger, independent of Track 3.** Build
    plan (elementary): (i) residue map `ZOmega → ℤ[ω]/√2 ≅ 𝔽₂[x]/(x⁴+1)` + residue-norm `x†x ∈
    {0000,0001,1010}`; (ii) Lemma-4 3-case row operation (matching pair → H/T word via `onFst`/`onSnd`/
    CNOT + the inc-17 block-action + inc-16 `√2`-clearing; denExp drops by 1); (iii) Lemma-5 parity
    (even count of `0001` ⟹ matching pair) ⟹ `ReductionStep`; (iv) inc-15 `colLemma_of_reductionStep`
    ⟹ unconditional column lemma. All kernel-pure. THIS is the next build (elementary, NOT research-grade).

**Giles–Selinger build PROGRESS (inc 18–21, `GilesSelingerResidue.lean`, ALL kernel `decide` only —
native_decide held at 596, confirming Track-3 independence):**
- inc 18 (`47c2a5fd`): `normSq_cd_not_both_odd` — residue-norm classification (`{0000,0001,1010}`, never
  `1011`: `(|z|²).c`,`(|z|²).d` never both odd; `Q≡(a+c)(b+d)`, `P≡(a+c)+(b+d)`).
- inc 19 (`ba635d43`): `cHom`/`dHom`+`sum_c`/`sum_d` (coord sums distribute) + `dividesSqrt2_iff_normSq_
  cd_even` (active = not-√2-divisible ⟺ residue norm ≠ 0000).
- inc 20 (`0e200ed6`): parity engine — `emod_two_eq_zero_iff_zmod`, `intCast_zmod2_eq_ite`,
  **`even_card_filter_of_sum_even`** (even ℤ-sum ⟹ even count of odd summands).
- inc 21 (`0552a469`): **`exists_matching_residue_pair` = GILES–SELINGER LEMMA 5 DONE** — unit column +
  active entry ⟹ two distinct entries with matching residue norm mod 2, both active.
- **inc 22 (`GilesSelingerRowOp.lean`): LEMMA-4 CORE STEP + kernel-confirmed 3-case structure.** Settled
  via `#eval` over `ℤ[ω]/2` (`ω`-action `(a,b,c,d)↦(b,c,d,a)`, period 4): the active residues split by
  residue norm — `(P,Q)=(0,1)` ["1010"] = the SINGLE `ω`-orbit `{3,6,9,12}`; `(P,Q)=(1,0)` ["0001"] =
  TWO orbits `O₁={1,2,4,8}`, `O₂={7,11,13,14}=O₁⊕1111` (exactly Giles–Selinger's Case-3 sets). So Lemma 4
  is: **same-orbit (`x≡ωᵐy mod 2`) ⟹ single `H·Tᵐ`** (`core_step`: drops BOTH entries one denExp level,
  `(x±ωᵐy)/√2` at `denExp≤t` from level `t+1`, via `2 ∣ x±ωᵐy` ⟹ `√2²`-clear); **cross-orbit `0001` ⟹
  2-step `1111`-bridge** (follow-on). `core_step`+`denExp_mk_le_of_two_dvd`+`two_dvd_add_of_two_dvd_sub`+
  `mk_sub_same` all kernel-pure `{propext,Quot.sound}`; native_decide held at 596; lib+ExtractDeps green
  (9218). **CONFIRMS the settled plan** — "mechanical-concrete, NOT research-grade" = elementary multi-case
  (incl. the 2-step), exactly as designed; the single-`H·Tᵐ` insufficiency was always known (inc-16). Also
  corrected the stale inc-16 `MatchingResidue` docstring (the v2 "`kmm_lemma3` IS needed" conflation).
- **VALIDATED Lemma-4 construction (kernel `#eval` over `{-1,0,1}⁴`, 0 failures — the recipe for the next
  increment).** The UNIFORM 2-step handles BOTH same- and cross-orbit matched-active pairs:
  - **(A) √2-match always exists:** every matched-active pair has `∃m∈{0,1}, √2 ∣ (w_p − ωᵐw_q)`. **Clean
    proof (no big decide):** the mod-`√2` residue `r(z) := (a+c, b+d) mod 2 ∈ (ZMod 2)²` (so `√2∣z ⟺ r(z)=0`)
    is *determined by the norm class* — `1010` `(P,Q)=(0,1)` ⟹ `r=(1,1)`; `0001` `(1,0)` ⟹ `r∈{(0,1),(1,0)}`
    (since `P≡u+v`, `Q≡uv` with `u=a+c=r.1`, `v=b+d=r.2`). And `ω` acts on `r` by SWAPPING its two components
    (`r(ωz)=(b+d,a+c)=swap r(z)`, so `ω²` fixes `r`). Swap-orbits: `{(1,1)}`, `{(0,1),(1,0)}` — so matched-norm
    ⟹ same swap-orbit ⟹ `r(w_p)=r(ω^m w_q)` for `m=0` (if `r` equal) or `m=1` (if swapped). Step1 = `H·Tᵐ`
    keeps both entries at level `k` (`√2 ∣ w_p ± ωᵐw_q`), giving `(u₁,u₂)=(divSqrt2(w_p+ωᵐw_q),divSqrt2(w_p−ωᵐw_q))`.
    (Corollary: `1010` pairs have `r=(1,1)` always ⟹ √2-matched at `m=0`; consistent with `1010` = single ω-orbit.)
  - **(B) post-step1 is mod-2 aligned:** `∃m', 2 ∣ (u₁ − ωᵐ'u₂)` — so `core_step` (inc 22) is step2, dropping
    both to `denExp ≤ k-1`. (Same-orbit pairs also satisfy this directly via `core_step` alone — the 2-step is
    a uniform superset.)
  - **CAUTION (kernel-disproven shortcut):** the tempting "after step1, `u₁ = ωᵏu₂` EXACTLY" is FALSE
    (256/512 cross-orbit pairs fail it). (B) genuinely needs mod-`2√2` (`√2³`) residue analysis — the `u`'s
    depend on `w_p,w_q` mod 4 through `divSqrt2`'s `/2`. The structural proof tracks that; a single big decide
    over `ℤ[ω]/√2³` (64²·64 ≈ 262k) exceeds the kernel heartbeat budget (#10), so NOT a decide — structural.
- **inc 23 ✅ (`GilesSelingerRowOp.lean` `exists_sqrt2_match`): brick (A) DONE** — every matched-active pair is
  √2-matchable `∃m∈{0,1}, √2∣(w_p−ωᵐw_q)`, via the clean swap-orbit proof (norm class ⟹ mod-√2 residue; `ω`
  swaps its components; matched ⟹ same swap-orbit). `ZMod 2` kernel `decide` (256 cases) + parity bridge;
  kernel-pure `{propext,Classical.choice,Quot.sound}`; native_decide 596; lib+ExtractDeps green (9218).
- **Brick (B) DECOMPOSED + VALIDATED (kernel `#eval`, 0/512 cross-orbit failures — the recipe for the next
  increment).** The post-step1 mod-2 alignment splits into two clean halves:
  - **(B′) step1 lands the `u`'s in the `1010` class:** for cross-orbit `0001` matched-active pairs there is a
    √2-matching `m` (brick A) with BOTH `u₁=divSqrt2(w_p+ωᵐw_q)`, `u₂=divSqrt2(w_p−ωᵐw_q)` in the `1010`
    norm-class (`(normSq uᵢ).c` odd). This is the **mod-4 core** (`uᵢ` depend on `w`'s mod 4 via `divSqrt2`'s
    `/2`; `|uᵢ|² = |w_p±ωᵐw_q|²/2`, so the class is a `|·|²`-mod-4 fact). Strengthen brick A to deliver this `m`.
  - **(B″) `1010` ⟹ mod-2 aligned:** the `1010` class is the single ω-orbit `{3,6,9,12}`, so any two `1010`
    elements satisfy `∃m', 2∣(u₁−ωᵐ'u₂)` — a clean `ZMod 2` decide + bridge, exactly like brick A. (B″ also
    closes the `1010` case of Lemma 4 directly via `core_step`, single step.)
- **NEXT (Lemma-4 completion → `ReductionStep`):** prove (B″) [clean mod-2, ship first] then (B′) [the mod-4
  core] → assemble brick A + (B′) + (B″) + `core_step` into the uniform Lemma 4 "matched-active pair ⟹ both
  drop to `denExp ≤ k-1`"; (iii) wrap into the realizable `Gate2` two-level op (embed `H·Tᵐ` via
  `embedFst`/`embedSnd` + index permutation X/CNOT, inc-17 block-action); (iv) inner induction on
  count-at-max-level + factor `√2` ⟹ `ReductionStep` → inc-15 `colLemma_of_reductionStep` (unconditional dim-4
  column lemma) → controlled-C (Amy et al.) + operator-norm on inc-8/9 ⟹ the `∀U∈SU(2)` headline.

### Track 1 — unconditional scaffolding (paper-independent; advanced while the Track-2 DR is async)

### Track 3 + 2-qubit-synthesis JOINED PROGRAM (2026-06-09; user-approved, <10k LOC bar; method = my judgment, elegance-first)

**Reprioritization (user, upstream-driven):** `native_decide` blocks any Mathlib/physlib upstream;
Mathlib *also* rejects slow `decide` (CI), so the 4 sites + the 2-qubit synthesis must be kernel-pure.
Track 3 is therefore **critical path**, done jointly with the (fresh, kernel-pure-by-design) synthesis.

**Probe (sizes + method + LOC estimate ≈ 7.4k central, auto-approved <10k):**
- The 4 `native_decide` cores are consumed by structural wrappers (`KMMCompleteness.bridge_u`/
  `cliffordBase_u`/`ma_step_exists_u`, `KMMLemma3Column`) via `reconstruct_box_data_unitary` + the box
  check ⟹ eliminating a core upgrades its wrapper to fully kernel-pure.
- `bridge_box_core` (`KMMBridge.lean:132`): 1664 of `zomBox²×8` (zomBox=5⁴=625), checks `kSO3≤3`.
  **Method: structural `μ≤3 ⟹ kSO3≤3`** (sde↔kSO3 balancing; `muMeasure_le_kSO3_add_two_u` is the
  reverse, present). ~400–700 LOC. *Most tractable — START HERE.*
- `maStep_exists_core` (`MAStepExists.lean:256`): ~809k `validCol³`. **Method: orthogonality-class
  ORBIT reduction** (signed-perm/Clifford orbits of orthogonal triples → small reps + invariance lemma
  + small kernel `decide`). ~800–1500 LOC.
- `cliffordBase_box_core` (`CliffordBase.lean:291`): `zomBox²×8` filtered `kSO3=0`, ≤6-word coverage.
  **Method: Clifford-orbit coverage** (reduce to coset reps). ~800–1500 LOC.
- `kmm_lemma3_alg2` (`KMMLemma3.lean:113`): ~16.7M over `(ZMod 8)⁴²`. **Method: structural mod-8
  sde-reduction** (ω-action mod 8 symmetry; the gde valuation algebra). ~1000–2000 LOC. *Hardest
  (research-flavoured) — LAST.*
- **2-qubit synthesis (circuit C + controlled-C + leakage bound):** no existing multi-qubit substrate;
  Giles–Selinger column lemma at dim 4 (cleaner than the single-qubit SO(3) route), designed kernel-pure.
  ~3,000–5,000 LOC.

**Build order:** bridge (tractable win + valuation machinery) → maStep → cliffordBase → kmm_lemma3 →
the 2-qubit synthesis (reusing the kernel-pure base-case machinery). Each a complete kernel-pure unit;
ship incrementally. Construction reference: `Lit-Search/Phase-6AO/KMM-1212.0822-...-websearch.md`.

- **Track 1(b) brick ✅ — `GaussInt2 = ℤ[√2][i]` is an integral domain (`b5123126`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/Zsqrt2GaussInt2Domain.lean`: `zsqrt2_sq_add_sq_eq_zero`
  (`a²+b²=0 ⟺ a=b=0` over ℤ[√2] — formal reality at the integer-coordinate level via `nlinarith`, **no
  real embedding** needed, which Mathlib lacks for `Zsqrtd 2`) + `GaussInt2.norm_eq_zero` +
  `Nontrivial`/`NoZeroDivisors`/`instIsDomain`. **Fully kernel-pure** (native_decide unchanged at 596).
  Next Track-1 bricks: GaussInt2 `EuclideanDomain` (mirrors the shipped `Zsqrt2EuclideanDomain`) → PID/UFD
  → the splitting law (`x²+1` mod π) → the even-power relative-norm criterion 1(c) → "ancilla strictly
  helps". Track 1(a) ℤ[√2]-ED already shipped.

### Track 2 — remaining circuit layer (faithful factorization; sequenced, NOT de-scoped)

> **⚠ SUPERSEDED (inc-1–6 era snapshot; kept for history).** Two statements below are now STALE and would
> UNDER-claim if read as current: (i) "(5) rounding … hypothesized project-wide … carry it as a tracked
> input" — **inc 8 DISCHARGED the rounding unconditionally** (`kmm_amplitude_approx`); the z-rotation
> headline carries NO rounding hypothesis. (ii) "the precise KMM-1212.0822 construction → DR dispatched" —
> **RESOLVED by the inc-6 web search** (construction = the dim-4 Column Lemma; no DR pending). Current truth
> = the inc 7–16 log + the corrected inc-15/16 block above.

The full `∀U∈SU(2)` O(log 1/ε)-with-≤2-ancillas headline factors as: **(1) keystone ✅ → (2) 2-qubit
semantics ✅ → (3) state-column → ring-unitary (orthonormal completion over ℤ[ω][1/√2]) → (4) 2-qubit
exact synthesis (`Gate2`-word, length O(sde) — the general KMM multi-qubit row-reduction; the major
remaining build) → (5) rounding (target → integer-residual approximant within ε)**. (3)/(4) are general
ring linear algebra + general 2-qubit synthesis — they do NOT need the paper-specific KMM-1212.0822
gate sequence, so they are buildable faithfully. (5) is the §5 grid analysis — already **hypothesized
project-wide** (even the single-qubit `rossSelinger_compile_log_length` takes the rounding quality
`h00` as a hypothesis), so it is consistent to carry it as a tracked input and prove the unconditional
completion+synthesis around it. **Status (inc 1–6 above):** the entire FOUNDATION is built and verified —
the unconditional NT core (1), 2-qubit semantics (2), the unconditional normalized ancilla *state*
existence (3), system-line synthesis at the KMM length (4), the realizable class (5), and the
**O(log 1/ε) length-composition law** (6). **The single remaining Track-2 piece** is brick (B): the
explicit ancilla *unitary* that block-encodes `U` with the ancilla restored to |0⟩ **deterministically**
(NOT the naive (u,v,t₁,t₂) column, which leaks into ancilla-|1⟩ = a post-selected scheme), then its
two-qubit exact synthesis into a `Gate2`-word — which, by inc 6, is then O(log 1/ε) automatically. This
needs the **precise KMM-1212.0822 construction** to formalize faithfully (the project does not guess a
published circuit) → **DR dispatched** (see execution log). Once back, brick B + the synthesis assemble
the full `∀U` headline on the inc-1–6 foundation. Tracks 1 (b/c/d) + 3 (native_decide ×4) remain in scope
and untouched (paper-independent; available for continuations while the DR is async).
