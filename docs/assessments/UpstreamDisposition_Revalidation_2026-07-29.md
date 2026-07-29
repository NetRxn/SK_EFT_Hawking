# Upstream / duplication disposition — re-validation at the v4.32.0 pin

**Date:** 2026-07-29
**Supersedes the ground truth of:** [`UpstreamContributionDisposition.md`](UpstreamContributionDisposition.md) (2026-06-08)
**Why:** that document's verdicts were established against **Mathlib v4.29.1 (`5e932f97`)** and
**PhysLib `69197c54`** (2026-05-14). We are now on **Mathlib `81a5d257` (v4.32.0)** and **PhysLib
`c4843367` (#1460)** — PhysLib moved **284 commits / 171 new files / 355 modified**. Every
"confirmed gap" and "physlib ABSENT" verdict was therefore unverified. This re-runs them.

**Method.** Direct inspection of the pinned sources in `lean/.lake/packages/{mathlib,Physlib}`,
plus — where an instance could be auto-named and grep-invisible — **typeclass synthesis asked of
Lean itself** (`by infer_instance`) and real `lake build`s. Grep-only verdicts are marked as such.
Two of the findings below were grep false-negatives caught only by asking Lean directly; treat a
bare grep on this substrate as a lead, not a result.

---

## 0. The correction that matters most

> **`fidelity_channel_nondecreasing` is `sorry`, and always was.**

The 2026-06-08 doc's headline "positive discovery" (§3.1 row 5, and Track **R3**) was that PhysLib
already proves the *general* Uhlmann/DPI monotonicity this project had explicitly fenced in
`FidelityBounds.lean`, and therefore that we should **"stop trying to prove it locally."**

At our pin, `QuantumInfo/States/Mixed/Fidelity.lean:132-134`:

```lean
@[sorryful]
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (Λ : CPTPMap d d₂) :
    fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry
```

Checked at the *original* assessed revision too (`git show 69197c54:QuantumInfo/Finite/Distance/
Fidelity.lean`): **also `sorry`**. So this was not a regression — the assessment verified that the
declaration *existed* without checking that it was *proved*.

**Consequences.**
- **Track R3 is withdrawn.** PhysLib does not discharge our fence. The general Uhlmann case is
  still open upstream *and* here.
- **No damage propagated.** Our tree never cited PhysLib for this: `FidelityBounds.lean` still
  records the fence honestly ("remains fenced (Uhlmann purification, above)"), no Lean docstring or
  paper draft claims otherwise, and `validate.py --check axiom_closure_allowlist` confirms **no
  `sorryAx` reaches our closure**. The error lived only in the assessment document.
- **Standing rule this re-proves:** presence of a declaration is not evidence of a proof. Grep for
  the name, then read the body. PhysLib marks these `@[sorryful]`, which makes the check cheap.

**PhysLib's `sorry` surface at `c4843367`: 29 sites across 12 files**, including
`ForMathlib/HermitianMat/CFC.lean`, `Entropy/Axiomatized/{Defs,Renyi}.lean`,
`Capacity/Capacity.lean`, `ResourceTheory/ResourceTheory.lean`, `States/Mixed/Fidelity.lean`.
Any future adoption must body-check the specific declarations consumed.

---

## 1. Real dividends from this bump

| # | Finding | Evidence | Action |
|---|---|---|---|
| **D1** | **PhysLib's spectral theory now compiles at our pin.** `MolecularHamiltonian.lean:27-32` builds Kato–Rellich in-tree because PhysLib's `SpectralTheory` "does not compile at the project's pinned PhysLib/Mathlib/Lean-4.29.1" **and** "bumping the shared PhysLib pin is disallowed". **Both premises are now void.** | `lake build Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint` → **2398 jobs, 11.4s, zero errors**. PhysLib ships `IsEssentiallySelfAdjoint`, `unique_self_adjoint_extension`, `IsSymmetric.isEssentiallySelfAdjoint_iff`, plus new `Mathematics/{LinearPMap,Resolvent}.lean`. | Wave-scoped decision: keep in-tree Kato–Rellich, or re-home 6BB onto PhysLib. **Not** a toolchain side effect — needs its own bridge + axiom check. |
| **D2** | **`PathConnectedSpace TorusFour` now synthesizes outright.** `KummerH0T4.lean` §0 hand-builds ~40 lines (`pathConnectedSpace_circle`, `joinedProdMk`, `pathConnectedSpace_prod`, `torusFour_pathConnected`) because "pinned Mathlib (v4.29.1) has neither… (a later Mathlib provides both)". It does now. | `example : PathConnectedSpace TorusFour := by infer_instance` **elaborates clean**. `instance : PathConnectedSpace Circle` is new in `Analysis/SpecialFunctions/Complex/Circle.lean:169` (0 occurrences at `5e932f97`, 1 now). The `Prod` instance was a **grep false-negative** — synthesis finds it. | Retire §0; keep the §1/§2 homology content. Small, clean, fully verified. |

Everything else the bump changed is friction, not dividend — catalogued in
[`docs/references/mathlib_bump_playbook.md`](../references/mathlib_bump_playbook.md).

---

## 2. Mathlib upstream candidates (§3.3) — re-verified, ALL still gaps

Grep over `mathlib/Mathlib/` at `81a5d257`. **Every §3.3 candidate remains a genuine gap.** The
existing `*MathlibPR.lean` packaging stands, and the bump neither helped nor invalidated it.

| Candidate | v4.32.0 status |
|---|---|
| matrix-exp local homeomorphism at 0 | **absent** — still a gap |
| `specialUnitaryGroup` compactness | **absent** — still a gap (also the blocker cited by `FKLW/ConstructiveEpsilonNet.lean`, which ships its ε₀-net theorem with SU(2)-compactness as an explicit hypothesis) |
| matrix BCH (cubic) | **absent** |
| concrete-radius matrix log / Mercator | **absent** |
| Kronecker spectral theory (`charpoly`, eigenvalues, `kroneckerPow`, `traceNorm_kronecker`) | **absent** — still the top-value pure-math item |
| Pfaffian, `Matrix.IsSkewSymmetric` | **absent** (`MathlibAux/Pfaffian.lean` stands) |
| Steenrod squares | **absent** — the "Steenrod" hits are *Eilenberg*–Steenrod axioms, a different object |
| Stiefel–Whitney classes | **absent** |
| projective-space manifold instance | **absent** |
| `Metric.closedBall` `ChartedSpace`/`IsManifold` | **absent** — `SphereProductBounding.lean`'s FROZEN item 1 stands (synthesis-tested, not grepped) |
| Laplace method / asymptotics | **absent** |
| Künneth / EZ cross product for singular homology | **absent** — the whole `SphereProdCross*` / `PoincareLefschetz*` justification stands |
| `erf` / `erfc` / Gaussian CDF | **absent** — `Detection/GaussianThreshold.lean` stands |
| Uhlmann purification | **absent** (see §0) |

**Not a gap, and not new:** `QuadraticForm.sigPos`/`sigNeg` + Sylvester's law of inertia exist in
`LinearAlgebra/QuadraticForm/Signature.lean` — but they were **already present at v4.29.1**. The
2026-06-08 "partial overlap, coordinate" verdict on the lattice-signature cluster is unchanged.

---

## 3. PhysLib novelty claims (§3.2) — re-verified, ALL still novel

Despite 284 commits, **every §3.2 novelty claim survives**. Verified by searching for
*declarations* (`^(theorem|lemma|def|…)`), not prose — the loose-word matches are all comments.

| Cluster | v4.32/`c4843367` status |
|---|---|
| partial transpose / negativity / log-negativity / PPT ladder | **no declarations.** The word hits are `nonnegativity` (8×) and a roadmap comment in `States/Pure/Qubit.lean:19` ("Completeness of the PPT test…"). Exactly the "TODO comments only" the 2026-06-08 doc predicted. Still the strongest contribution candidate. |
| diamond norm / Choi / SDP | **absent** |
| Gaussian / Isserlis scalar moments | **absent** — the hit is `QFT/PerturbationTheory/WickAlgebra`, operator normal-ordering, the known different object |
| `kroneckerPow` / Kronecker spectral | **absent** from both PhysLib and Mathlib |

**FLRW is still stubbed.** `Physlib/Cosmology/FLRW/Basic.lean:101-102` is still
`@[sorryful] def FLRW : Type := sorry`, despite six new FLRW files (Dynamics, Solutions, Distances,
DensityParameters, MatterContent, ConformalTime). §3.4's "wait for PhysLib's GR to mature" verdict
stands — do not build on it yet.

**New PhysLib areas worth a look (identified, not yet assessed for overlap depth):**
`FluidDynamics/*` (17 files — Navier–Stokes, Bernoulli, continuity, incompressible, Newtonian,
thermodynamic flow) is conspicuous for a fluid-based-physics project;
`CondensedMatter/Thermoelectric/Basic.lean` sits near `Electrothermal/ETFModel.lean` (D12/6E);
`Mathematics/{LinearPMap,Resolvent,Wirtinger,ParametricIntegration}.lean`.

---

## 4. `native_decide` — the honest answer

**The bump does not help here, but there is a large pre-existing opportunity.**

Current surface: **494 real tactic uses across 43 files** (the raw grep count of ~1539/826 is
misleading — most files merely *state* "no `native_decide`" in a docstring). ADR-002 tracks
`native_decide_decl_closure = 546`, clustered `anyon_mtc` 327 / `number_field_qgroup` 154 /
`other` 53 / `lattice_signature` 12.

**`decide +kernel` was already available at v4.29.1** — verified by running the same probe under
both installed toolchains. So this is *not* a bump dividend; it is an unexploited option that the
bump prompted us to test.

It does, however, appear to work. Whole-module swaps (`sed native_decide → decide +kernel`, then
re-elaborate), all at **default heartbeats**, no Invariant-#10 violation:

| Module | sites | baseline | `decide +kernel` | errors |
|---|---|---|---|---|
| `FibonacciMTC.lean` (anyon_mtc) | 11 | 5.4s | 17.2s | **0** |
| `KacWaltonFusion.lean` (anyon_mtc) | 58 | 5.2s | 5.5s | **0** |
| `QCyc40.lean` (number_field_qgroup) | 21 | 7.3s | 50.8s | **0** |
| `E8Lattice.lean` (lattice_signature) | 2 probed | — | clean | **0** |

**90 sites across three modules and two clusters converted with zero errors.** Cost ranges from
negligible (KacWalton) to ~7× (QCyc40, hinting at superlinear cost in cyclotomic arithmetic).

**Why it matters:** `decide +kernel` is kernel-checked, so converted declarations drop
`Lean.ofReduceBool` from their axiom closure — a direct reduction of the project's largest
soundness-surface concession.

**Caveat — not a completed result.** 90 of 494 sites tested, in 3 of 43 files. QCyc40's 7×
suggests the heavier cyclotomic modules may not all convert within default heartbeats, and
whole-build wall-clock impact is unmeasured. Treat this as a **validated-promising spike**, not a
finished migration. Natural next step: a ratchet-down wave taking `lattice_signature` (12) and
`other` (53) first, measuring build time, before touching `anyon_mtc`.

---

## 4b. The new PhysLib areas, assessed — **not a gold mine**

Straight answer: the `FluidDynamics/` tree is **not** the windfall its name suggests for this
project, and one of my own adjacency flags was wrong. All three areas are `sorry`-free.

### FluidDynamics/ — a classical continuum *definitional* layer

17 files, ~1345 lines, but the shape is **28 defs/abbrevs/structures vs. 12 theorems/lemmas**, and
the theorems are all conservative-⟺-convective restatements
(`navier_stokes_iff_convective_navier_stokes`, `euler_iff_convectiveEuler`,
`cauchyMomentumEquation_iff_convectiveCauchyMomentumEquation`), divergence computations, and
smooth⟹classical implications. `FluidDynamics/Basic.lean` is pure `abbrev` type synonyms
(`ScalarField d := Time → Space d → ℝ`, …). No well-posedness, no existence, no uniqueness.

**Every piece our analog-Hawking route actually needs is absent:**

| needed | PhysLib |
|---|---|
| sound speed | **absent** |
| acoustic metric / analog gravity | **absent** |
| Mach number / transonic | **absent** |
| Gross–Pitaevskii, Madelung, Bogoliubov, quantum pressure, condensate/superfluid | **all absent** |
| Hawking / Unruh | **absent** |
| Bernoulli | present only as `def LocalBernoulliLaw` / `def BernoulliLaw` — a **predicate**, not a proved law |

So there is **no duplication to retire and nothing to drop in**. PhysLib's fluid layer is purely
classical continuum mechanics; this project's is quantum-fluid (BEC) analog gravity.

**The one real opportunity is structural, not a reuse.** Our `AcousticMetric.lean` is *algebraic
and pointwise* — `acousticMetric (v cs rho : ℝ)` is a 2×2 real matrix with hand-rolled
`partialT`/`partialX` on `Spacetime1D`, and its own header lists the deferred gaps: *"PDE
well-posedness (existence/uniqueness of solutions to `□_g π = 0`)"* and *"regularity of the
background fields"*. PhysLib supplies exactly that missing layer — genuine time/space-dependent
fields with real derivative machinery, and continuity/Euler/Navier–Stokes stated as PDEs on them.

Re-homing onto it would let us **derive** the acoustic metric by linearising a `FluidFlow 1`
instead of positing it algebraically, closing our own stated gap. But PhysLib does not linearise,
so we would build that ourselves. This is the same shape as §3.4's GR recommendation: *a better
foundation to eventually rebuild on, not a result to import.* Low urgency, real value.

### CondensedMatter/Thermoelectric/ — **my adjacency flag was wrong**

I previously flagged this as sitting "next to" `Electrothermal/ETFModel.lean`. It does not.
PhysLib's module is the **thermoelectric figure of merit**: `ThermoelectricMaterial ⟨σ, S, κl, κe⟩`,
`powerFactor = σ·S²`, `figureOfMerit` (ZT) with positivity/monotonicity lemmas. Our `ETFModel` is
**electrothermal feedback in a TES/bolometer**: heat balance `C·Ṫ = P_bias(T) + P_signal − G(T−T_bath)`,
loop gain, and a stability dichotomy proved as an iff. Different physics, adjacent only in name.
**No overlap, no reuse, nothing to do.**

### CondensedMatter/TightBindingChain/ — the most substantive, but complementary

539 lines and genuinely proved: a `TightBindingChain` structure, orthonormal localized states, a
hermitian `hamiltonian`, `BrillouinZone`, `QuantaWaveNumber ⊆ BrillouinZone`, and
`energyEigenstate` / `energyEigenvalue` with `hamiltonian_energyEigenstate`. A complete finite 1D
band structure.

Overlap with D11 is **mild and encoding-divergent**: PhysLib uses
`BrillouinZone : Set ℝ := Set.Ico (-π/a) (π/a)` — a 1D fundamental domain carrying the physical
lattice constant `a`; our `LatticeHamiltonian.lean` uses
`BrillouinZone (d : ℕ) := Fin d → AddCircle (2π)` — the d-dimensional quotient. Ours is more
general and quotient-correct; theirs is concrete, finite, and carries physical spacing. Our
`TopologicalBand/{BlochFHS, BlochFrame, FHSLatticeGauge, FiniteTorus, PrincipalBranch}` already
landed the finite-lattice FHS/Chern substrate with a `Uwit` C=1 witness.

Plausible use: their chain as an **independent concrete instance** to check our abstract machinery
against. Not a substitute for anything we have.

### Other new `Mathematics/` modules

`Calculus/Wirtinger/Basic.lean` (31 decls) is the largest. `Calculus/ParametricIntegration.lean`
gives differentiation under the interval integral (`hasFDerivAt_parametric_intervalIntegral_of_contDiff`,
`contDiff_parametric_intervalIntegral_of_contDiff`) — real infrastructure, but it does **not**
unblock §3.3's `LaplaceMethod`, which needs *asymptotic expansion* of `∫ e^{-λf}g` as `λ → ∞`, a
different object. Adjacent, not an unblock. `CrossProduct` (3), `ConjModule` (5),
`OrthogonalMatrix` (1) are small.

---

## 5. What to do (proposed, none actioned)

**Cheap + fully verified.** Retire `KummerH0T4.lean` §0 (D2). Correct Track R3 in the 2026-06-08
doc (§0) so nobody acts on the withdrawn recommendation.

**Wave-scoped decisions.** 6BB re-home onto PhysLib spectral theory vs. keep in-tree (D1).
`native_decide` → `decide +kernel` ratchet-down, smallest clusters first (§4).

**Upstream track, unchanged and still valid.** U1 (matrix-exp homeomorphism → SU(d) compactness →
BCH → Mercator log) is the most actionable: the Fable portfolio records the *mathematics as
landed* ("remaining work is packaging/upstream review, not a Fable theorem program"), and this scan
confirms all four are **still genuine Mathlib gaps at v4.32.0**. U2's Kronecker spectral theory
remains the highest-value single item. U3 (negativity/diamond/Gaussian → PhysLib) is confirmed
still-novel and unblocked.

**Do not.** Build on PhysLib's FLRW (still `sorry`). Adopt any PhysLib declaration without reading
its body (§0).
