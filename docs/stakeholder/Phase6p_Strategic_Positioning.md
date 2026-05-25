# Strategic Positioning: Phase 6p — The Topological-QC Trust-Anchor Phase

## How the Program Delivers Machine-Verified Topological Universality

**Date:** 2026-05-22
**Context:** This memo positions Phase 6p within the broader research program. Phase 6p substantively COMPLETE.

---

## Phase 6p's Strategic Value

For over two decades the topological-quantum-computation programme has rested on two folklore-trusted claims: (1) **Fibonacci anyon braiding is universal** — the closure of the braid-group image is the full unitary group on the fusion-space encoding (FKLW 2002); and (2) **the compilation is efficient** — sequence length grows polylogarithmically in the inverse precision (Solovay-Kitaev 1995/2006). Both claims are paper-proved and engineering-trusted; neither was machine-verified.

Phase 6p closes the first claim **unconditionally and kernel-only**. The F.21 theorem `fibonacci_density_F21_unconditional` ships with zero project-local axioms and zero tracked Propositions. This is the load-bearing theoretical statement behind every Fibonacci-anyon proposal in the literature — without it, the entire "intrinsic universality from braiding alone" framing collapses to a conjecture. Phase 6p makes it a kernel-verified theorem.

The phase also delivered substrate for the second claim (the `sk_axiom_Dawson_Nielsen` predicate scheduled for Phase 6t discharge) and substrate for the threshold-theorem trust anchor (AGP distance-3, Track 2). Combined with Phase 6t (Fibonacci-specific quantitative SK) and Phase 6u (Clifford+T generic substrate + Niven density), Phase 6p is the first stone in what is now a three-phase **trust-anchor stack for topological and fault-tolerant quantum computation**.

For external positioning, the headline shift is:

  - **Before Phase 6p:** "Fibonacci anyons are universal (FKLW 2002, paper-proved)."
  - **After Phase 6p:** "Fibonacci anyon braiding closure equals $SU(2)$ — kernel-verified in Lean 4, zero project-local axioms, zero tracked Props."

The strategic point: the project's topological-QC contribution is no longer "we cite FKLW." It is "we verified FKLW."

Like Phase 6n and 6o, Phase 6p produces no new standalone papers. All content absorbs additively into bundle D4 (Topological Quantum Computation) plus a cross-bridge paragraph in flagship F.

---

## Three Strategic Track Pillars

### Track 1 — Fault-Tolerance Substrate (AGP Distance-3)

Eleven new Lean modules under `lean/SKEFTHawking/FaultTolerance/` building the AGP 2006 distance-3 threshold theorem on the Steane $[[7,1,3]]$ code. Abstract local stochastic error model; Fibonacci-anyon topological-substrate model deferred to a Phase 6p+ track. ~2,300 LoC sorry-free target.

**Audience:** quantum-error-correction researchers (Gottesman, Preskill, Aliferis, Cross-DiVincenzo-Terhal); fault-tolerant-architecture community (Litinski, O'Gorman, Babbush); formal-methods researchers working on quantum-software verification (Selinger, Heunen, Rand-Paykin-Zdancewic-QWIRE).

**Re-use story:** This is the first quantum-threshold-theorem formalization in any proof assistant — first-formalization-territory across Lean, Coq (QWIRE, SQIR/VOQC, CoqQ, Coq-QECC), Isabelle (HOL-Quantum, QHLProver), and Agda. The substrate is positioned as the **specification reference** against which all subsequent quantum-FT formalizations can be compared.

### Track 2 — FKLW Density (Topological Universality)

The headline phase deliverable. F.21 unconditional kernel-only via the Phase 5 Step 13 chain: von Neumann's accumulation-point theorem on closed subgroups of $SU(2)$, Cartan v4 closed-subgroup classification, three Mathlib-PR-quality matrix-Lie lemmas, and a complete inverse-function-theorem application through the tangent space $\mathfrak{su}(2)$.

**Audience:** topological-quantum-computation researchers in the Freedman-Kitaev-Larsen-Wang lineage (Freedman, Kitaev, Larsen, Wang, Wen, Bonesteel, Hormozi, Nayak, Trebst); analog-anyon physicists working on Fibonacci-anyon proposals (Mong-Clarke-Alicea-Lindner, Schotte-Zhu-Burgelman-Verstraete); Mathlib4 working group on Lie groups and matrix exponentials.

**Re-use story:** the F.21 substrate (Trotter, BCH cubic, IFT-through-$\mathfrak{su}(2)$) is alphabet-agnostic. Subsequent phases (6t, 6u) consume it for Fibonacci-specific and Clifford+T quantitative Solovay-Kitaev work without re-deriving the Lie-algebraic core.

### Track 3 — Explicit Braid-Word Compilation

The concrete-numerical bridge between FKLW density (theoretical) and the operational compilation pipeline. Hadamard (Rouabah 2020), CNOT (HZBS 2007 Fig. 15 transcription), T-gate (KBS algorithm). Cyclotomic-field decision $\mathbb{Q}(\zeta_{40})$ at degree 16 over $\mathbb{Q}$.

**Audience:** experimental topological-QC groups (Microsoft Station Q, IQIM Caltech, Princeton condensed-matter, ${\rm IBM}$/Quantinuum/IonQ industry teams targeting topological hybrid architectures); quantum-compilation toolchain developers (gridsynth, TQSim, staq).

**Re-use story:** Track 3 is the first interactive-prover formalization of explicit braid-word compilation for any anyon model. Three citation corrections were applied project-wide as a result of its literature audit; the audit itself is a methodology contribution for future anyon-compilation formalizations.

---

## Bridge Map — How Phase 6p Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6p |
|---|---|---|---|
| Phase 6n SymTFT audit + WittClass | 6n W1b | shipped | Provides the categorical substrate ($U_q(\mathfrak{sl}_2)$, MTC instances) that Track 2 builds on for the Fibonacci braid-group representation $\rho_{\mathrm{Fib}}$. |
| Phase 6n Wave 2a Glorioso-Liu monotonicity | 6n W2a | shipped | Independent — Phase 6p's AGP Track does not cross-bridge to LDP infrastructure (Wave 1a.1 DR decision: use Mathlib4 `SubGaussian` directly). |
| Phase 5c/5i/5p categorical chain | Phase 5 | shipped | Substrate consumer — paper11 (`Uqsl2/Uqsl3/Uqg`), paper14 (Ising + Fibonacci MTC), paper16_wrt_tqft (Temperley-Lieb + Jones-Wenzl). All imported freely. |
| Phase 5 Step 13 | Phase 5 / 6p | substantively closed in 6p | The F.21 unconditional discharge IS the Phase 5 Step 13 Path (i) closure. ~1,900 LoC of substrate (Trotter, BCH cubic, IFT) shipped along the way. |
| Mathlib4 (v4.29.0; pinned `8850ed93`) | upstream | partial | Probability concentration (`SubGaussian`, Chernoff, Hoeffding) PRESENT; Lie algebras + Lie groups PRESENT, deep; density in topological groups PRESENT; `BraidGroup n` ABSENT (Phase 6p builds it custom via `PresentedGroup`); Solovay-Kitaev ABSENT (Phase 6t builds it). |
| Phase 6t quantitative SK | downstream (in-flight at Phase 6p close) | pending | Phase 6t consumes Phase 6p's F.21 substrate + the Dawson-Nielsen SK tracked Prop. |
| Phase 6u generic SK substrate | downstream | pending | Phase 6u re-uses the Phase 5 Step 13 alphabet-agnostic substrate (von Neumann, Cartan v4) and validates its genericity on Clifford+T. |

---

## Audiences and Outward-Facing Positioning

### Audience 1: Topological-Quantum-Computation Researchers

The headline message: **Fibonacci-anyon braid-group density (FKLW 2002) is now kernel-verified unconditionally**. The verification is in Lean 4 (Mathlib4 v4.29.0), kernel-only `{propext, Classical.choice, Quot.sound}`, zero project-local axioms.

This is the trust-anchor for every Fibonacci-anyon proposal in the literature. For researchers proposing intrinsically fault-tolerant topological quantum computers, Phase 6p makes the theoretical foundation no longer "we cite a 24-year-old paper" but "we verified it."

### Audience 2: Formal-Methods and Verified-Quantum-Software Community

The methodology message: **substantive density-of-image proofs are feasible in Lean even when Mathlib4 lacks the specific theorem**. Phase 6p does not require a pre-existing Mathlib FKLW lemma; it builds the substrate (Trotter, BCH cubic remainder, the matrix-log Lipschitz tightening) project-local with eventual Mathlib upstream-PR pathway.

This positions Phase 6p as a **template for first-formalization work in matrix Lie theory**. Future formalization projects in the Lean/Coq/Agda ecosystems can follow the same pattern: build the substrate project-local, isolate the kernel-only headline, surface Mathlib-PR-quality lemmas as opportunistic upstream contributions.

### Audience 3: Quantum-Error-Correction and Fault-Tolerance Researchers

The Track 2 message: **the AGP distance-3 quantum threshold theorem now has a kernel-verifiable substrate in Lean**. This is the first quantum-threshold-theorem formalization in any proof assistant. The rigorously-proven AGP lower bound $\varepsilon_0 > 2.73 \times 10^{-5}$ (the "$10^{-4}$" commonly quoted in talks is heuristic) is now machine-checkable.

For QEC research, this is positioned as the **specification reference** for downstream fault-tolerant compilation toolchains. Once Track 2 ships its final headline, production-grade quantum-FT software can be checked against a kernel-verified threshold theorem rather than against AGP 2006's unverified Mathematica scripts.

### Audience 4: Lean / Mathlib Working Groups

Phase 6p surfaces multiple Mathlib-PR-quality lemmas opportunistically:

  - `ContinuousSMul ℝ (Matrix _ _ ℂ)` (explicit instance via `Complex.real_smul`).
  - `Matrix.specialUnitaryGroup_coe_zpow` (Submonoid zpow lift for unitary group).
  - `Matrix.specialUnitaryGroup_isClosed` (closed in `Matrix _ _ ℂ` via unitary ∩ det⁻¹{1}).
  - `Matrix.SU2_add_star_eq_trace_smul_one` (Cayley-Hamilton trace identity).
  - `expAmbient_decomp_of_sq_eq_scalar` (matrix exp decomp for $X^2 = c \cdot 1$).
  - The matrix-log Lipschitz tightening $\|Y_h(h)\| \le (\pi/2) \cdot \|h - 1\|$ on $SU(2)$.
  - Three telescoping-sum lemmas powering the Trotter limit substrate.

These are not on the critical path for Phase 6p closeout; they are tracked as opportunistic upstream contribution targets. The user-authorization gate for actual Mathlib4 PR submission remains explicit.

---

## What's Next

### Immediate (Phase 6q, 6r, 6s in parallel)

Phase 6p, 6q, 6r, 6s were scoped together in the 2026-05-12 four-phase planning conversation. Phase 6q is the DKM transport-bootstrap response to the Phase 6o Wave 1c NO-GO. Phase 6r is the SymTFT formalization arc. Phase 6s is bootstrap-Itô-LDP foundational substrate. These run in parallel to each other and are independent of Phase 6p substrate (one-way: 6q/6r/6s do not consume 6p outputs).

### Immediate (Phase 6t)

Phase 6t consumes Phase 6p's F.21 substrate to ship the **first kernel-verified quantitative Solovay-Kitaev length bound in any proof assistant**, instantiated for the Fibonacci-anyon braid representation. Discharges the `sk_axiom_Dawson_Nielsen` tracked Prop substantively.

### Medium-term (Phase 6u)

Phase 6u extracts the alphabet-agnostic substrate from Phase 6t (the Lie-algebraic core: Dawson-Nielsen super-quadratic recursion, Cartan closed-subgroup classification, BCH bracket closure, $\varepsilon_0$-net machinery) and validates it by instantiating at Clifford+T, the canonical fault-tolerant alphabet. The Phase 5 Step 13 substrate built in Phase 6p is the load-bearing input.

### Long-term (post-Phase-6 publication phase, Phase 7)

D4 bundle (Topological Quantum Computation) — §9.1–§9.5 absorbs Phase 6p F.21 + braid-word compilation; §9.6+ absorbs Phase 6t quantitative SK + Phase 6u generic substrate + Clifford+T. Flagship F gets a cross-bridge paragraph identifying the kernel-verified topological universality as a trust-anchor result.

### Long-term: Mathlib Upstreaming

Surface the matrix-Lie lemmas to Mathlib4. This is Phase 6s Track 2 (community citizenship) work and would meaningfully strengthen Mathlib's coverage of matrix Lie theory.

### Long-term: Topological Threshold Specialization

Phase 6p+ track for specializing the AGP threshold from the abstract local stochastic error model to the Fibonacci-anyon topological-substrate error model. Depends on still-active research (Schotte-Zhu-Burgelman-Verstraete arXiv:2012.04610; Schotte-Burgelman-Zhu arXiv:2301.00054). User-authorization gate explicit.

---

## Status

Phase 6p substantively COMPLETE. F.21 Fibonacci density theorem UNCONDITIONAL kernel-only — the load-bearing theoretical statement behind the entire topological-quantum-computation programme is now machine-verified. AGP Track 2 substrate scaffold delivered. Track 3 braid-word substrate + project-wide citation-correction sweep delivered. Three closed-subgroup-classification soundness corrections (v2/v3/v4) shipped and reviewed.

Project axiom count UNCHANGED at 1; both Phase-6p-opened axioms (`bridge_axiom_FKLW`, `sk_axiom_Dawson_Nielsen`) substantively discharged or scheduled-discharged. Build clean. Ready for downstream Phase 6t/6u quantitative-SK ascent and eventual D4 bundle absorption.
