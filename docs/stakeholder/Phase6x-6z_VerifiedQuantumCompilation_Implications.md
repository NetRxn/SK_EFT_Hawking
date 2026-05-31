# Phase 6x–6z: Implications of the Verified Universal Quantum Compilation Arc

## Technical and Real-World Implications

**Status:** Phases 6x / 6x′ / 6y / 6z all SUBSTANTIVELY CLOSED at GREEN; Phase 6u closed UNCONDITIONAL (the arc's substrate). Every headline kernel-pure (`{propext, Classical.choice, Quot.sound}`), zero project-local axioms, zero sorries. Full build clean at **9,944 theorems / 0 axioms / 0 sorries / 751 modules** (`docs/counts.json`, regenerated 2026-05-30).
**Date:** 2026-05-31
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6t (quantitative Solovay-Kitaev at Fibonacci) and Phase 6u (alphabet-agnostic substrate + Clifford+T) — the foundation this arc lifts and instantiates; the Wave Execution Pipeline.
**Companion:** `Phase6x-6z_VerifiedQuantumCompilation_Strategic_Positioning.md`. This consolidated doc supersedes, for external communication, the in-progress `Phase6u_*` (May 25) and first-session `Phase6x_*` (May 26) stakeholder notes for everything past their snapshot; those remain as historical per-phase records.

---

## Executive Summary

Between Phase 6t (Fibonacci quantitative Solovay-Kitaev) and this arc, the project's *quantum-compilation* work crossed a threshold: it stopped being "a few showcase results" and became a **complete, machine-checked theory of universal gate compilation**. This consolidated note covers everything that landed after the 2026-05-26 stakeholder snapshot — the unconditional closure of Phase 6u, the completion of Phase 6x, and the three entirely-new phases 6x′, 6y, 6z.

The arc delivers six interlocking, kernel-verified results:

1. **An alphabet-agnostic quantitative Solovay-Kitaev substrate** (Phase 6u, closed UNCONDITIONAL): give it any sufficiently-rich gate set and the same verified quantitative compiler ships by *instantiation*, not re-derivation. Demonstrated on Clifford+T, the canonical fault-tolerant gate set.

2. **The lift of that substrate to arbitrary dimension SU(d)** (Phase 6y): the **first kernel-verified quantitative Solovay-Kitaev at general dimension** in any proof assistant, with the long-standing existential-radius blocker eliminated by a novel **concrete-radius matrix logarithm**.

3. **Five instantiated alphabets** spanning the field: Fibonacci, Clifford+T, Read-Rezayi `SU(2)_5`/`SU(2)_7`, trapped-ion Mølmer-Sørensen at SU(4), and Clifford+CCZ at SU(8).

4. **Two complementary, honest density mechanisms for the same SU(8) target** (Phase 6y per-qubit-T route vs Phase 6z **T-free, CCZ-essential** route) — a publishable pairing, not a redundancy.

5. **A machine-checked quantum resource theory** (Phase 6x′): an *unconditional* Toffoli-count lower bound `T^of(U) ≥ sde₂(Û)`, plus the converse that Clifford-only ⟨H,S,CNOT⟩ is **not** dense in SU(8) (CCZ is genuinely essential).

6. **A Mathlib-upstream contribution portfolio**: a concrete-radius matrix logarithm, a generic BCH cubic estimate, SU(d) Cartan density-from-witness, and matrix-exponential local-homeomorphism — substrate Mathlib currently lacks.

On the publication side, this corpus has outgrown the D4 §9.x "multi-alphabet showcase" container it was provisionally routed to. It is now authorized as a dedicated Tier-1 bundle, **D8 — "Kernel-Verified Universal Quantum Gate Compilation"** (Pipeline Invariant #14, 2026-05-31), with D4 retaining the Fibonacci/topological anchor and D6 consuming D8's compiler as its universal-compilation primitive.

---

## What This Arc Adds Beyond Phase 6t

Phase 6t shipped the first quantitative Solovay-Kitaev headline (Fibonacci, single-qubit SU(2)). The arc below turns that single result into a *theory*.

### Phase 6u — the alphabet-agnostic substrate, closed UNCONDITIONAL

Phase 6u factored the alphabet-specific from the alphabet-agnostic. The substrate — Dawson-Nielsen super-quadratic recursion, Cartan-v4 density-from-witness, BCH bracket-closure, ε₀-net — is now packaged behind a generic `GeneratingSet` abstraction. The fundamental claim: *adding a new universal alphabet is an instantiation problem, not a re-derivation problem.*

The May-25 stakeholder note caught Phase 6u mid-flight (substrate shipped, Clifford+T track conditional). It has since closed **fully unconditional**:

- **`solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional`** — the canonical Clifford+T quantitative SK headline, conjoining error bound `≤ ε` and polylog word-length bound at the same compile level, kernel-only.
- **`cliffordT_density_unconditional`** — ⟨H,T⟩ is dense in SU(2), via a Niven algebraic-integer obstruction on the trace `√2·sin(π/8)` of `H_SU·T_SU` (`cliffordT_accPt_one_unconditional`, `CliffordTInfiniteOrder.lean`). The 1999 Boykin-Mor-Pulver-Roychowdhury-Vatan folklore result, now machine-verified.

The closure passed CP1 + CP2 fresh-context adversarial reviews (0 BLOCKER, 0 REQUIRED) and a final strengthening sweep. The Niven discharge is the load-bearing novelty — an algebraic-integer obstruction with no cyclotomic machinery — and it is the *generic technique* the rest of the arc reuses.

### Phase 6x — the second-instance test, completed

Phase 6x is the decisive test of the Phase 6u abstraction: does a *new* universal alphabet ship by instantiation? The answer was yes, and the first-session note (May 26) has since been completed via the "lift/shift" reframing:

- **Read-Rezayi `SU(2)_5` and `SU(2)_7`** ship UNCONDITIONAL bundled-strict headlines. The Niven obstructions are genuinely new mathematics: the `k=5` case is discharged via the **Chebyshev `T₇` factorization** `T₇(x)+1 = (x+1)(8x³−4x²−4x+1)²` (forcing the level-5 cubic at `cos(π/7)`); the `k=7` case via the **triple-angle identity** `cos(3·π/9)=cos(π/3)=1/2`. These are the next universal-anyon family beyond Fibonacci, physically relevant to non-Abelian fractional quantum Hall states at filling `ν = k/(k+2)`.

- **Trapped-ion (Mølmer-Sørensen) and Clifford+CCZ matrix substrates** shipped (`MS(θ)`, `CCZ_mat` + diagonal identities). The T-A1 trapped-ion headline closed UNCONDITIONAL via factorization through the Phase 6u Clifford+T base; the *full* SU(4)/SU(8) multi-qubit compilation was deferred to Phase 6y.

- **Mathlib-upstream-PR presentations** (M.1 generic BCH order-2 cubic; M.2 Cartan-v4 density-from-witness; M.4 concrete word-length recurrence), each namespaced, docstring'd, and exampled for community submission. M.3 closed NO-OP after confirming Mathlib4 v4.29.1 already covers the generic 3-direction-product technique.

Phase 6x also documented six honest orphans (Tier-1 quick wins + the Tier-2 Ross-Selinger optimal-synthesis arc) — work explicitly *not* absorbed, recorded rather than silently dropped.

### Phase 6x′ — a machine-checked quantum resource theory (Mukhopadhyay)

Phase 6x′ formalizes the deep channel-representation layer of Mukhopadhyay 2024 (arXiv:2401.08950) for Clifford+CCZ in SU(8). It delivers three results that were not previously machine-checkable:

- **Unconditional Toffoli lower bound**: `channelSde2_le_toffoliCost`, i.e. `T^of(U) ≥ sde₂(Û)` — the Toffoli-gate count needed to implement `U` is bounded below by the signed-parity-invariant `sde₂` measure on its channel representation. The prior form of this bound was *parametric* (conditional on hypotheses about the measure); Phase 6x′ discharges those hypotheses (Clifford-preservation `hC`, CCZ-increment `hCCZ`) and makes the bound **unconditional**. A fully machine-checked unconditional resource lower bound for a fault-tolerant gate is a citable infrastructure artifact in its own right.

- **Lemma 3.10 — dyadic entries**: `channelRep_interp_isRat`, that the channel-representation entries of any Clifford+CCZ word lie in ℤ[1/2]; with Theorem 3.8 `channelRep_CCZ_isHalfInt` characterizing the CCZ row structure (entries in {0, ±1, ±1/2}).

- **The CCZ-essentiality converse**: `cliffordOnly_not_dense` — ⟨H,S,CNOT⟩ (no CCZ) generates a *finite* group (via a channel-rep morphism into signed-permutation matrices), hence is **not** dense in SU(8). This is the rigorous statement that CCZ is not redundant — it directly motivates Phase 6z.

Out of scope (documented permanent residual): full Toffoli *minimality* (Mukhopadhyay Conjecture 4.8, the matching meet-in-the-middle upper bound).

### Phase 6y — the first kernel-verified Solovay-Kitaev at arbitrary SU(d)

Phase 6y is the arc's deepest mathematical achievement. It lifts the entire Phase 6u substrate from SU(2) to general SU(d):

- **`solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`** — the generic SU(d) headline: for any `d ≥ 2`, any `U ∈ SU(d)`, any `ε > 0`, a compilation exists with error `≤ ε` and a polylog word-length bound. The first such theorem at arbitrary dimension in any proof assistant.

- **The concrete-radius matrix logarithm** (`matrixMercatorLog`, `exp_matrixMercatorLog`): Mathlib has no Banach-algebra logarithm with a *named* convergence radius. Phase 6y constructs one (`∑ (−1)ⁿ/(n+1)·Xⁿ⁺¹`, valid for `‖X‖<1`) and proves the exp round-trip. This is what eliminates the **existential-radius regime blocker** that had stalled the SU(d) lift — a genuine proof-technique novelty (escaping an existential wall by explicit construction) and a standalone Mathlib-PR-eligible contribution.

- **The length-exponent caveat, resolved**: a dev-time mis-transcription (`log 5/log 2`) was corrected to the honest Dawson-Nielsen value `log 5/log(3/2) ≈ 3.97`, single-sourced as `skLengthExponent_sud`, and the polylog bound `SkLengthPolylogBound_sud_holds` discharged unconditionally. Per the project's quality standard, the headline was *not* shipped at the over-optimistic exponent that would have required an unproven quadratic contraction.

- **Two instantiated multi-qubit alphabets**: SU(4) trapped-ion (`trappedIonSU4_solovayKitaev_headline_unconditional`, density via Brylinski-Brylinski) and SU(8) Clifford+T (`cliffordCCZSU8_solovayKitaev_headline_unconditional`, density via the {H,T,CNOT} sub-alphabet à la Aaronson-Gottesman). The SU(8) instance is honest-scoped: its density comes from {H,T,CNOT}, with CCZ present-but-over-complete — the *faithful* CCZ-essential route is Phase 6z.

The two Mathlib upstream tracks (SU(d) Cartan density, exp local-homeomorph) are alias-only at present (a thin-wrapper presentation, not yet PR-iterated).

### Phase 6z — the first T-free, CCZ-essential density in SU(8)

Phase 6z proves that the literal ⟨H,S,CNOT,CCZ⟩ gate set — **with no T-gate** — is dense in SU(8):

- **`cliffordCCZLiteral_dense`** + **`cliffordCCZLiteral_H_of_G_eq_top`** + the headline **`cliffordCCZLiteral_solovayKitaev_headline_unconditional`**.

The mechanism is fundamentally distinct from Phase 6y. Density does *not* come from a per-qubit infinite-order element; it comes from the seed `CCZ·(H⊗H⊗H)`, which has trace `1/√2 ∉ 𝒪` (algebraic-integer obstruction) and is therefore infinite-order. A von-Neumann first-flow argument then accumulates a one-parameter subgroup, and Clifford-conjugation irreducibility (`clifford_irreducible_spans`, `cliffOrbit_spans_su8` — the Clifford group acts transitively on all 63 non-identity Pauli lines) spreads it across the full algebra 𝔰𝔲(8). The Stage-13 review confirmed CCZ is **load-bearing**: it appears only in the seed, never in the spreading machinery — without it, density fails.

Together with Phase 6x′'s `cliffordOnly_not_dense`, this closes the CCZ-essentiality story end-to-end: Clifford-alone is finite (not dense); Clifford+CCZ is dense; CCZ is the unique resource that makes the difference.

---

## Result Highlights

| Phase | Headline (Lean theorem / artifact) | Status |
|---|---|---|
| **6u** | `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional` — Clifford+T quantitative SK | ✅ UNCONDITIONAL |
| **6u** | `cliffordT_density_unconditional` — ⟨H,T⟩ dense in SU(2) (Niven) | ✅ UNCONDITIONAL |
| **6x** | RR `SU(2)_5` + `SU(2)_7` bundled-strict headlines (Chebyshev-`T₇` + triple-angle) | ✅ UNCONDITIONAL |
| **6x** | M.1/M.2/M.4 Mathlib-PR presentations; T-A1 lift/shift unconditional | ✅ shipped |
| **6x′** | `channelSde2_le_toffoliCost` — unconditional Toffoli lower bound `T^of(U) ≥ sde₂(Û)` | ✅ UNCONDITIONAL |
| **6x′** | `cliffordOnly_not_dense` — ⟨H,S,CNOT⟩ finite, not dense in SU(8) (CCZ essential) | ✅ |
| **6y** | `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight` — first SU(d) SK | ✅ UNCONDITIONAL |
| **6y** | `matrixMercatorLog` / `exp_matrixMercatorLog` — concrete-radius matrix log (regime blocker eliminated) | ✅ (Mathlib-PR-quality) |
| **6y** | `trappedIonSU4_*` + `cliffordCCZSU8_*` headlines (SU(4) MS, SU(8) Clifford+T) | ✅ UNCONDITIONAL |
| **6z** | `cliffordCCZLiteral_dense` + `cliffordCCZLiteral_solovayKitaev_headline_unconditional` — first T-free CCZ-essential SU(8) density | ✅ UNCONDITIONAL |

**Project-wide totals (post-arc, 2026-05-30):** 9,944 theorems (9,919 substantive + 25 placeholder); **0 axioms**; **0 sorries**; **751 modules**; build clean (≈8,900+ jobs throughout). Toolchain: Lean v4.29.1, Mathlib `5e932f97` (v4.29.1 tag).

---

## Real-World Implications

### For the quantum-compilation / gate-synthesis community

The arc establishes, end-to-end and machine-checked, that *universal compilation exists with provable error and word-length bounds* for five distinct alphabets across dimensions 2, 4, and 8. The SU(d) generality means the result is no longer a per-alphabet artifact — it is the verified backbone any future gate set instantiates. The Mukhopadhyay Toffoli bound adds the *resource-theoretic* side: a verified lower bound on how cheaply a unitary can be implemented.

### For the fault-tolerant-architecture community

CCZ-essentiality is now settled rigorously (Clifford-alone finite; Clifford+CCZ dense). The two complementary SU(8) density mechanisms (per-qubit-T vs CCZ-seed) cover both the magic-state-distillation route (Clifford+T) and the native-CCZ route relevant to schemes that prefer a CCZ primitive. The unconditional Toffoli lower bound is directly usable in magic-state-distillation resource accounting.

### For trapped-ion and superconducting hardware-vendor research teams

The SU(4) Mølmer-Sørensen instance and the SU(8) multi-qubit instances target the gate sets *actually realized* on production hardware (trapped-ion MS entangler; superconducting Clifford+T / CCZ). The verified-compiler guarantee — error and length bounds proven to the Lean kernel — is the kind of correctness assurance the field has not previously had at this dimension. (Runtime implementation, vendor-specific tuning, and length-optimality engineering are deliberately outside the verified-existence scope; see the strategic-positioning companion.)

### For the topological-quantum-computing community

Read-Rezayi `SU(2)_5` / `SU(2)_7` now sit on the same formal footing as Fibonacci. The Fibonacci universality result remains the topological anchor (and the origin point of the whole substrate), with the new alphabets demonstrating that the machinery generalizes across the universal-anyon family.

### For Mathlib4 working groups

The arc surfaces a substantive contribution portfolio: a concrete-radius matrix logarithm (genuinely absent from Mathlib), a generic BCH order-2 cubic estimate, SU(d) Cartan density-from-witness, and matrix-exp local-homeomorphism. The matrix logarithm in particular solves a real substrate gap and is the cleanest standalone PR candidate.

### For the broader formal-methods community

The arc is a template: define an alphabet's generating set, discharge a closure-density witness (typically a Niven-style algebraic-integer obstruction), and auto-inherit the quantitative SK chain. The cost-per-new-alphabet is now dominated by the density witness, and the SU(d) lift means the substrate no longer caps at single-qubit targets.

---

## Pipeline Invariants Respected

- **#10 (no `maxHeartbeats`)**: respected throughout all five phases. Hard proofs are decomposed into sub-lemmas, not granted heartbeat budget.
- **#15 (no new project-local axioms)**: respected. Project axiom count is **0** across the arc (`counts.json::lean.axioms = 0`). Deferred work (full SU(4)/SU(8) in 6x, Ross-Selinger optimal synthesis, Toffoli minimality Conj 4.8) is honestly recorded as residual, never shipped as an axiom.
- **Strengthening discipline**: the preemptive 5-question checklist was applied at theorem-write time across the arc; reviewers independently confirmed the headlines are substantive (the Niven obstructions, the SU(d) regime discharge, the unconditional Toffoli bound are all load-bearing, not P3/P4/P5 tautologies).
- **Kernel purity**: every headline checks against `{propext, Classical.choice, Quot.sound}` only. Where `native_decide` appears in the broader library it is tracked separately (see the native-decide cleanup, which reduced the compiler-trust surface project-wide); the arc's headlines are not on that surface.

---

## Stage-13 Adversarial Review Verdicts

- **Phase 6u**: CP1 + CP2 GREEN (0 BLOCKER, 0 REQUIRED post-remediation); final strengthening sweep clean.
- **Phase 6x**: five checkpoints (CP-B, CP-A1, CP-A2, CP-M, CP-S′) all GREEN, 0 BLOCKER + 0 REQUIRED; the completion lift/shift session adhered to all five retrospective-addendum failure modes.
- **Phase 6x′**: Stage-13 GREEN on the capstone (`cliffordOnly_not_dense`); the Phase-2 full-discharge review verdict was dispatched at close.
- **Phase 6y**: Stage-13 fresh-context review returned GREEN / GREEN-WITH-RECOMMENDED, 0 BLOCKER (2026-05-30); confirmed the unconditional headlines and the honest SU(8) Clifford+T scoping.
- **Phase 6z**: Stage-13 GREEN — **0 BLOCKER / 0 REQUIRED / 0 ADVISORY**; statement honesty, non-vacuity, irreducibility completeness all PASS; CCZ-essentiality independently confirmed.

---

## What Comes Next

### Publication integration — the D8 bundle (authorized 2026-05-31)

The corpus is authorized as Tier-1 bundle **D8 — "Kernel-Verified Universal Quantum Gate Compilation: Alphabet-Agnostic Solovay-Kitaev across Dimensions"** (`PAPER_STRATEGY.md` §2.2). The draft-mapping rows (`PAPER_DRAFT_MAPPING.md`) re-point Phase 6p/6t from D4 §9.x into D8, and add 6u/6x/6x′/6y/6z. **D4** keeps the Fibonacci/topological-foundations focus (cross-referenced by D8); **D6** consumes D8's quantitative SK as its universal-compilation primitive. The next operational step is the Stage-1 bundle creation per `BUNDLE_LIFT_PROCEDURE.md`: `papers/D8/` skeleton + `bundle_metadata.json` + `paper_draft.tex` + a `claims-reviewer-bundle-prompts.md` D8 anchor entry, followed by the mandatory Stage-9/10/13 reviewer triple.

### Mathlib4 upstream submission

The strongest standalone PR is the **concrete-radius matrix logarithm** (`matrixMercatorLog`). The generic BCH cubic (M.1) and Cartan density-from-witness (M.2, both SU(2) and the SU(d) generalization) follow. The SU(d) M-S tracks need to advance from alias-only to PR-iterated.

### Honest residuals (recorded, not shipped as axioms)

- **Ross-Selinger optimal `ℤ[ω][1/√2]` synthesis** — replaces the existential ε₀-net with a genuinely-runnable polynomial-time algorithm; queued as a Lit-Search task.
- **Full Toffoli minimality** (Mukhopadhyay Conjecture 4.8, the matching meet-in-the-middle upper bound) — out of scope; the lower bound stands unconditionally.
- The **runnable compiler / vendor tuning / length-optimality** engineering layer is deliberately out of the verified-existence scope.

---

**The arc turns a single quantitative-Solovay-Kitaev result (Phase 6t, Fibonacci) into a complete, machine-checked theory of universal quantum gate compilation** — alphabet-agnostic, lifted to arbitrary dimension, instantiated on five alphabets, paired with a verified resource lower bound and a settled CCZ-essentiality result. It is the project's largest single body of verified *mathematics* and is now consolidated under a dedicated publication target.
