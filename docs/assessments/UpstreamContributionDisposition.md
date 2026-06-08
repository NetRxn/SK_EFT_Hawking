# Upstream Contribution & Duplication Disposition

**Status:** Long-term scoping assessment — **planning/scouting only, not a near-term upstreaming plan.** Sets the long-term disposition for (a) what to eventually upstream and (b) what parallel infrastructure to systematically retire in favor of physlib/Mathlib.
**Date:** 2026-06-08
**Author:** Claude (Opus 4.8) for John Roehm
**Scope:** This document concerns **only the public `SK_EFT_Hawking` repo.** It routes the public repo's reusable Lean content to its correct long-term home (Mathlib / physlib / keep-local) and audits where the public repo independently re-developed mathematics physlib already had.
**Ground truth:** physlib ([`leanprover-community/physlib`](https://github.com/leanprover-community/physlib), Apache-2.0, pinned rev `69197c54`, 2026-05-14) was inspected directly this session. Load-bearing "physlib has / lacks X" claims were additionally re-confirmed by **semantic Lean search** (`lean_local_search` / `lean_leansearch` over a build that includes physlib + Mathlib), which catches differently-named equivalents that grep would miss. Every grep verdict held under semantic search; no flips. See §7.

---

## 0. Framing & decision rules

1. **Scouting, not executing.** Goal is a settled long-term plan, not PRs now.
2. **Don't carry parallel infra out of sunk cost.** Where the repo re-developed something physlib already has and physlib's is similar-or-better, **physlib is canonical and ours should be retired/frozen.** Only if the repo *replicated and genuinely improved on an existing physlib declaration* is it "a different story." (Finding: that case is essentially empty — see §2.) Every duplication is catalogued here so it can be addressed systematically.
3. **Mathlib vs physlib routing is by object kind:** pure mathematics with a natural home in Mathlib's taxonomy → Mathlib; inherently physics objects (quantum channels, entanglement measures, curvature tensors) → physlib. physlib itself depends on Mathlib and routes general math down to Mathlib, so the split matters.

---

## 1. Why this document exists

Since Phase 6f the project has packaged "Mathlib-upstream-PR-quality" modules (Apache-2.0 + `Authors: John Roehm` headers, Mathlib-namespaced presentations, target-path mirrors). **That planning predated awareness of physlib** — confirmed: no file in this repo mentions physlib/PhysLean/QuantumInfo. So a large amount of reusable work was aimed at Mathlib, including content Mathlib would reject as domain-specific (GR tensor algebra, QI operator theory, Solovay–Kitaev compilation), **and** a large amount of QI work was built from scratch that physlib already had. This document reconciles the public inventory against physlib.

The public repo is already on **Lean / Mathlib v4.29.1**, which matches physlib's pin — so a future physlib/Mathlib engagement is toolchain-compatible today.

### physlib ground truth (verified this session)

`leanprover-community/physlib` (Apache-2.0), two build targets:
- **`QuantumInfo`** — *much* more mature than its README implies. Has bundled `MState`, full `CPTPMap/*`, `ForMathlib/MatrixNorm/TraceNorm` (SVD-based), a large `ForMathlib/HermitianMat/*` (CFC, **LogExp**, Sqrt, Rpow, Schatten, LiebConcavity, Majorization, Peierls), `Finite/Entropy/{VonNeumann,Relative,SSA,DPI}`, `AxiomatizedEntropy/Renyi`, `Finite/Distance/{Fidelity,TraceDistance}`, `Finite/Entanglement` (convex-roof / **Entanglement-of-Formation**), `POVM`, `Pinching`, `ResourceTheory/SteinsLemma`, `Regularized`, and a `TraceInequality/*` group (Jensen operator, Lieb–Ando, Löwner–Heinz, BlockDiagonal).
- **`Physlib`** (physics) — SR/Lorentz-tensor heavy, flat `SpaceAndTime/SpaceTime`, plus **foundational differential geometry** (`Mathematics/Geometry/Metric/{Riemannian,PseudoRiemannian}/Defs` — metric structures, musical isomorphisms `flat`/`sharp`, `curveLength`) and an **in-progress FLRW cosmology** (`Cosmology/FLRW/Basic` — Friedmann equations, but the `FLRW` type itself is `:= sorry`). **No** Ricci tensor, Christoffel symbols, Einstein tensor, Schwarzschild, energy conditions, or stress-energy anywhere.

It **depends on Mathlib** and routes general math down to Mathlib — so the pure-math/physics split governs the long-term routing.

---

## 2. The big picture in one table

| Cluster (public repo) | physlib status | Disposition |
|---|---|---|
| **QI entropy / relative entropy / matrix-log / fidelity-core+DPI** | physlib **HAS, strictly more complete** | **Retire/freeze ours; physlib canonical** (§3.1) |
| **QI negativity / PPT / partial-transpose / log-negativity / distillation-rate ladder** | physlib **ABSENT** (uses convex-roof/EoF instead) | **Novel — keep; long-term physlib-contribution candidate** (§3.2) |
| **Diamond norm + Choi + SDP cluster** | physlib **ABSENT** (CPTP exists, diamond norm doesn't) | **Novel — keep** (§3.2) |
| **Gaussian / Isserlis scalar moments** | physlib **ABSENT** (its "Wick" is QFT operator-contraction, different object) | **Novel — keep** (§3.2) |
| **Kronecker spectral theory + `kroneckerPow` + `traceNorm_kronecker`** | physlib & Mathlib **ABSENT** | **Novel pure-math — Mathlib candidate** (§3.2 / §3.3) |
| **Pure-math: matrix-exp homeomorphism, SU(d) compactness, BCH, Mercator log, RP⁴ manifold, bordism, E₈/lattice, biproduct half-braiding** | Mathlib & physlib **ABSENT** (all confirmed still-gaps) | **Mathlib candidates (long-term)** (§3.3) |
| **GR algebra: curvature/Einstein/energy-conditions/exact-solutions/ADM/tetrad** | physlib has only the **manifold-metric foundation + FLRW-stub**, none of this content | **Novel content — long-term physlib candidate, but re-home onto physlib's `PseudoRiemannianMetric` substrate** (§3.4) |
| **Headline results, tracked-Props, FT witnesses** | n/a | **Keep-local, never upstream** (§3.5) |

**Two findings that shape everything:**
- **There is essentially no "we improved physlib's version" case.** Every overlap is either *physlib-is-better* (entropy, fidelity) or *physlib-absent* (everything else). That makes the cleanup clean: retire the duplicates wholesale; there are no "but ours is better" exceptions to litigate. The one nuance is dimension-generality on things physlib *doesn't have at all* (negativity ladder) — that's novelty, not improvement.
- **Architectural mismatch.** The public QI modules use a **bare-matrix predicate `IsDensityOperator ρ : Prop`** on `Matrix ι ι ℂ`; physlib uses a **bundled `structure MState d`**. So "adopt physlib" is *not* a drop-in import — it needs a state-representation bridge. This raises the cost of the §3.1 retirements and argues for **freeze-don't-rip** (stop developing the duplicates; treat physlib as canonical going forward; bridge opportunistically).

---

## 3. The duplication register & disposition

### 3.1 Retire / freeze — physlib is canonical and more complete

These were built from scratch (physlib-blind) and **duplicate physlib, which is strictly more mature.** Recommendation: **freeze** (stop extending), mark as superseded, and migrate consumers to physlib when the `MState` bridge is built — don't keep developing parallel infra.

| Public module + headline | physlib equivalent (verified) | Why physlib wins |
|---|---|---|
| `VonNeumannEntropy.lean` (`vonNeumannEntropy`, `_nonneg`, `_le_log_card`) | `QuantumInfo/Finite/Entropy/VonNeumann.lean` `Sᵥₙ`, `Sᵥₙ_nonneg`, `Sᵥₙ_le_log_d` | Same eigenvalue-`negMulLog`-via-cfc construction; physlib adds continuity, conditional/mutual info, pure-state=0, SWAP/relabel invariance. |
| `QuantumRelativeEntropy.lean` (`matrixLog := cfc Real.log`, `relativeEntropy`, `classical_gibbs`) | `ForMathlib/HermitianMat/LogExp.lean` `HermitianMat.log` + `Finite/Entropy/Relative.lean` `qRelativeEnt` | physlib's `HermitianMat.log` is the same cfc-log with commute/reindex/smul API ours lacks; relative entropy is full sandwiched-Rényi-derived. |
| `QuantumKlein.lean` (`relativeEntropy_nonneg`, two-eigenbasis spectral expansion) | `Finite/Entropy/Relative.lean` `qRelativeEnt` (ENNReal-valued ⇒ ≥0 structurally) + `qRelativeEnt_joint_convexity` | Ours is a from-scratch finite-dim Klein; physlib gets nonnegativity structurally and adds joint convexity + data-processing. |
| `KroneckerEntropy.lean` — *entropy-additivity part* (`vonNeumannEntropy_kronecker_add`) | `Finite/Entropy/Relative.lean` `qRelativeEnt_additive` (+ SSA) | Additivity under tensor already in physlib. **(But the eigenvalues-of-Kronecker *substrate* underneath is novel — see §3.2.)** |
| Fidelity cluster — *core + general DPI* (`FidelityBounds`, `FidelityDataProcessing`, the **fenced** general Uhlmann) | `Finite/Distance/Fidelity.lean` `fidelity`, `fidelity_eq_traceNorm_sqrt_mul_sqrt`, **`fidelity_channel_nondecreasing`** | **physlib already proves the *general* Uhlmann monotonicity the project explicitly *fenced*** (`FidelityBounds.lean:597,623` only does the mixed-unitary/reversible subclass). physlib resolves our open frontier. |
| trace-norm *base theory* (consumed throughout) | `ForMathlib/MatrixNorm/TraceNorm.lean` (SVD, singular values, submultiplicativity, Hölder) | physlib's base trace-norm theory is richer than what the project rebuilt incidentally. |

> **Note on the fidelity finding (row 5):** this is a *positive* discovery, not just a duplication — adopting physlib doesn't merely dedup, it **removes a real fence** (general Uhlmann DPI) the project had been unable to discharge. The project's Fannes–Audenaert / Fuchs–van de Graaf *numeric* bounds remain novel (physlib has those only as comments) and move to §3.2.

### 3.2 Keep — genuinely novel vs physlib (long-term contribution candidates)

Confirmed (grep + semantic Lean search) that physlib has **zero** declarations for these (only TODO comments in `Entanglement.lean`/`Qubit/Basic.lean`). These are the repo's real, defensible additions.

| Public cluster | Novelty (verified) | Long-term home |
|---|---|---|
| **Negativity / PPT / partial-transpose ladder**: `PartialTransposeGeneral` (`ptB`), `BellNegativity` (`negativityBellDiag_eq`, `ppt_bellDiagState_iff`), `LogNegativity{,General}`, `NegativityMonotone{,General}`, `NegativityContinuity`, `MaxEntNegativity`, `PauliChoiNegativity`, `DistillationRateBound`, `NCopyRateBound` | physlib has **no** partial transpose, negativity, log-negativity, or PPT criterion — it took the convex-roof/EoF route instead. Entire ladder is novel; dimension/party-general. | physlib `QuantumInfo` (new `Entanglement/Negativity` area) — strongest single contribution candidate. |
| **Diamond norm cluster**: `DiamondNorm`, `DiamondNormChoi{,Upper}`, SDP/attainment, `NamedChannelDiamondExact` | physlib has CPTP but **no diamond norm/distance** (prose only in capacity docs). | physlib `QuantumInfo`. |
| **Gaussian / Isserlis scalar moments**: `GaussianMoments`, `GaussianWick`, `GaussianPolar`, `GaussianComplex*`, `GaussianSphere` | physlib's "Wick" is QFT operator normal-ordering (`Physlib/QFT/.../WickContraction`), a *different object*; no Gaussian/Isserlis scalar moments. | Mathlib (`Probability`) or physlib — pure moment algebra. |
| **Kronecker spectral substrate**: `charpoly_kronecker_eq`, `map_eigenvalues_kronecker` (spectrum = {λᵢμⱼ}), `KroneckerPower` (`KronIdx`, `kronPow`, `traceNorm_kronPow`), `traceNorm_kronecker`, `absOp_kronecker` | Absent from **both** physlib and Mathlib (confirmed via `lean_local_search`). Built from scratch. | **Mathlib** (`LinearAlgebra.Matrix.Kronecker`) — highest-value pure-math item; underpins the ladder above. |
| **Phase 6AK applied device theorems**: `CoherenceFidelity`, `ErrorBasisDiamond`, `GeneralizedAmpDamp`, `QECSuppression`, `SpamProcessFidelity`, `QutritWeyl`, `PLOBRateBound` | No physlib analog (applied device physics). | Keep-local (project/papers); not library content. |

### 3.3 Pure mathematics → Mathlib (confirmed still-gaps; long-term)

All verified **absent from current Mathlib (v4.29.1 pin) and physlib** this session. These remain valid long-term Mathlib candidates (the existing `*MathlibPR.lean` packaging stands).

| Module → target | Confirmed gap | Value |
|---|---|---|
| `MatrixExpLocalHomeomorphMathlibPR` → `Matrix.exp_isLocalHomeomorph_zero` | Mathlib has only unrelated circle-exp; gap confirmed | **H** (smallest/cleanest) |
| `SU2CompactnessMathlibPR` → `specialUnitaryGroup_isCompact` + instance | `lean_leansearch`: Mathlib has `Matrix.specialUnitaryGroup` defined + `Group` instance, but **no compactness** | **H** |
| `MatrixBCHCubicMathlibPR` → `Matrix.BCH` order-2 + `linftyOpNorm_reindex` | gap | **H** |
| `FKLW/GenericSUdMatrixMercatorLog` → concrete-radius matrix log | gap (Mathlib has no concrete-radius matrix log) | **H** |
| Kronecker spectral theory (from §3.2) → `LinearAlgebra.Matrix.Kronecker` | gap in both | **H — top pick** |
| `CartanFinalStepSUd{,Generic}MathlibPR` (peel generic lemmas) | partial | **M** |
| Lattice-signature/E₈ (Phase 5q.B): `E8Signature`, `LatticeSignatureCongr`, `BlockSignature`, … → `QuadraticForm` | partial overlap with `QuadraticMap.Equivalent.sigPos_eq`; coordinate | **M–H** |
| `CenterBiproductsHalfBraiding` `biprodTensor_hom_ext` → `CategoryTheory.Monoidal` | gap | **M** |
| `RP4*` (5 modules) → `Geometry.Manifold` | no projective-space manifold instance in Mathlib | **M** (heavy/collaborative) |
| `StiefelWhitney`/`PinBordism`/`PinPlusBordism4` → `AlgebraicTopology` | research-frontier; thin Mathlib char-class infra | **L–M** (defer) |
| `LaplaceMethod` → `Analysis.Asymptotics` | blocked on integration machinery | **M** (deferred) |
| `BeliefPropagation` → `Combinatorics`/`Probability` | niche for Mathlib | **L** |

### 3.4 GR algebra → physlib (novel content, but re-home onto physlib's foundation)

The repo's GR suite (`Curvature`, `EinsteinTensor`, `EnergyConditions`, `ExactSolutions`, `ADMFormalism`, `TetradFormalism`) is **novel content** — physlib has none of Ricci/Einstein/energy-conditions/Schwarzschild. **But** physlib already has the more-canonical *foundation*: manifold-based `PseudoRiemannianMetric` (tangent inner products, musical isos, `curveLength`) and an FLRW cosmology start. The repo's version is **coordinate-based algebraic** (∂_μ machinery deliberately deferred).

So this is neither a clean "retire" nor a clean "upstream as-is": the content is a genuine physlib gap, but contributing it well means **rebuilding it on physlib's `PseudoRiemannianMetric` substrate** rather than donating the standalone coordinate-algebra layer. Disposition: **long-term physlib candidate, contingent on a foundation-bridge decision** (adopt physlib's manifold geometry vs. keep the algebraic shortcut). Low urgency; flag for when physlib's GR area matures (its FLRW is still `sorry`).

### 3.5 Keep-local / never upstream

Headline "first-verified-X" theorems (consume library lemmas, aren't library content); tracked-`Prop` scaffolds (`IsDMNOBiconditional`, Pin/Lagrangian forward directions); FT numerical witnesses (`ShorTGateCount`, `APMLdpcHashingBound`, `GaugingQEC`).

---

## 4. Release posture (public repo)

This repo is public and consists of pure-mathematics and physics-formalization results. Pure mathematical content is not patentable subject matter, so there is no IP cost to openness; upstreaming to Mathlib/physlib is consistent with — and a stronger form of — the repo's existing open posture. Both Mathlib and physlib are **Apache-2.0**, matching this repo's existing file headers, so no relicensing is needed. (Revisit the `Authors: …, Claude (Anthropic)` co-author line against upstream authorship norms before any actual PR.)

Under the scouting framing, physlib/Mathlib upstreaming is a *long-term* option, not a now-action. The near-term value is the remediation track below.

---

## 5. Systematic remediation & long-term sequence

**Track R (Remediation — address the duplications; do first, low effort, removes sunk-cost drag).**
- R1. **Mark §3.1 modules as superseded-by-physlib** (docstring banner + an inventory flag). Freeze further development on them. *No code deletion yet* — the `MState` bridge is a prerequisite for migration.
- R2. **Scope the `IsDensityOperator` → `MState` bridge** (one design doc): the single enabler for ever consuming physlib's entropy/fidelity layer. Decide freeze-forever vs migrate.
- R3. **Capture the fidelity win**: note that physlib's `fidelity_channel_nondecreasing` discharges the general-Uhlmann fence in `FidelityBounds.lean` — stop trying to prove it locally.

**Track U (Upstream — long-term, only when the project chooses to spend the bandwidth).**
- U1 (Mathlib quick wins, all confirmed gaps): matrix-exp homeomorphism → SU(d) compactness → BCH → Mercator log.
- U2 (Mathlib mid): **Kronecker spectral theory** (top value) → E₈/lattice bricks → biproduct half-braiding.
- U3 (physlib `QuantumInfo`, novel): negativity/PPT/partial-transpose ladder → diamond-norm cluster → Gaussian moments. (No dedup needed — confirmed novel.)
- U4 (physlib `Physlib`, contingent): GR suite, re-homed onto `PseudoRiemannianMetric`, when physlib's GR matures.
- U5 (long-horizon, maintainer-pulled): RP⁴ manifold, bordism, Laplace method, SK compilation.

Nothing in Track U is urgent under the scouting framing. Track R is the actionable near-term value (stop carrying parallel infra).

---

## 6. Open decisions

1. **`IsDensityOperator` → `MState`: freeze-forever or migrate?** Adopting physlib's (better) entropy/fidelity layer requires this bridge. Cheapest path is *freeze* ours (stop developing, keep as-is for existing consumers) and only bridge if a future need pulls it. Confirm freeze vs. migrate.
2. **GR foundation (§3.4):** when GR upstreaming eventually happens, rebuild on physlib's `PseudoRiemannianMetric` (better, slower) vs. contribute the standalone coordinate-algebra layer (faster, lower-quality fit)? Recommend the former; no action now.
3. **AI co-author line** in headers — keep/drop/adjust per Mathlib/physlib norms (only matters at actual-PR time).

---

## 7. Provenance

- physlib source (pinned `69197c54`, 2026-05-14): [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib) — QuantumInfo + Physlib trees inspected directly; GR/entropy/negativity/diamond/fidelity claims verified this session.
- Upstream refs: [HepLean arXiv:2405.08863](https://arxiv.org/abs/2405.08863); [Lean-QuantumInfo arXiv:2510.08672](https://github.com/Timeroot/Lean-QuantumInfo).
- Comparison method: workspace grep + Explore agent forensic diff of public QI modules vs physlib, **then re-verified with semantic Lean search** over a build including physlib + Mathlib. Confirmed: physlib/Mathlib have **no** `partialTranspose`, `negativity`, diamond norm, or `kroneckerPow` (only the project's own + unrelated Mathlib `diamond` instances) → negativity ladder + diamond cluster + Kronecker-power are genuinely novel; physlib **has** the full `qRelativeEnt` API (additive, joint-convexity, lower-semicontinuous) + `MState` → entropy/relative-entropy duplicate-and-physlib-better; Mathlib has `Matrix.specialUnitaryGroup` defined but **no** compactness instance → SU(d) compactness still a genuine gap.
