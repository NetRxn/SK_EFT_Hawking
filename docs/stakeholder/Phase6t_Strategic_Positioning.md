# Strategic Positioning: Phase 6t — The First-Ascent Quantitative Solovay-Kitaev Phase

## How the Program Delivers the First Kernel-Verified Quantitative SK Theorem

**Date:** 2026-05-23
**Context:** This memo positions Phase 6t within the broader research program. Phase 6t substantively COMPLETE.

---

## Phase 6t's Strategic Value

The Solovay-Kitaev theorem is the trust anchor of practical quantum compilation. It has been in every textbook for nearly three decades — Nielsen-Chuang Appendix 3, Kitaev-Shen-Vyalyi Chapter 8, the Dawson-Nielsen 2006 review — yet it has *never been machine-verified* in any proof assistant. Production-grade quantum-compiler toolchains (Microsoft Q#, IBM Qiskit, Google Cirq, gridsynth, staq) implement variations of it, often with refinements (Ross-Selinger, Kliuchnikov-Maslov-Mosca exact synthesis); all of them trust the Dawson-Nielsen 2006 unverified Mathematica scripts as the underlying calibration.

Phase 6t closes that trust gap. The first kernel-verified quantitative Solovay-Kitaev length bound in any proof assistant — Lean, Coq/Rocq, Isabelle/HOL, Agda, HOL4, Metamath, or Mizar — ships in Phase 6t, instantiated for the Fibonacci-anyon braid representation in $SU(2)$. The pre-ship literature scan (`Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md`, May 2026) confirmed no precedent existed: no proof assistant has a kernel-verified quantitative SK theorem of any form, neither for $\{H, T\}$, Fibonacci anyons, nor abstract universal gate sets.

The strategic point: **the project's quantum-compilation contribution moves from "we cite Solovay-Kitaev" to "we verified Solovay-Kitaev."** All downstream Phase 6u/6v/6w work building alphabet-independent substrate or instantiating new gate sets (Clifford+T, Read-Rezayi, trapped-ion native) builds on Phase 6t's first ascent.

For external positioning, the headline shift is:

  - **Before Phase 6t:** "Solovay-Kitaev 1995/Dawson-Nielsen 2006 give $O(\log(1/\varepsilon)^{3.97})$ — trusted but not machine-verified."
  - **After Phase 6t:** "First kernel-verified quantitative Solovay-Kitaev length bound in any proof assistant, instantiated for the Fibonacci-anyon braid representation. UNCONDITIONAL. Bundled-strict (error AND length at the same compile level)."

Like recent phases, Phase 6t produces no new standalone papers. All content absorbs additively into bundle D4 (Topological Quantum Computation) §9.3–§9.5 via Late-Phase-6 Absorption Protocol Branch D.4 (sourceless lift). Wave 8 closeout shipped the §9 prose (~3,500 words), two new figures, two new notebooks (Technical + Stakeholder), and Python smoke tests.

---

## Three Strategic Pillars

### Pillar 1 — The Substantive Recursion (Waves 1-7)

Seven modules formalizing the *entire* Dawson-Nielsen 2006 super-quadratic recursion, not just its asymptotic statement. Group-commutator quadratic-shrinkage and cubic-linearization-remainder bounds (Wave 1); near-identity-sharpened stability (Wave 1+); $SU(2)$ balanced-commutator general-axis discharge via Bloch decomposition (Wave 2); $\varepsilon_0$-net `findNearest` correctness (Wave 3); level-0 base case + recursion-step bounds (Wave 4); polylog length asymptotic (Wave 5); bundled-strict generic headline (Wave 6); worked examples (Wave 7). Total ~1,890 LoC.

**Audience:** theoretical computer scientists working on quantum-compiler verification (Selinger, Ross, Heunen, Kliuchnikov); formal-methods researchers in the Lean/Coq/Agda communities working on quantum software; Mathlib4 working group on Lie groups and matrix exponentials.

**Re-use story:** Phase 6u extracts the alphabet-agnostic substrate from this layer and validates its genericity by instantiating at Clifford+T. The Phase 6t recursion modules are the load-bearing engineering deliverable that makes Phase 6u feasible without re-derivation.

### Pillar 2 — The Path A Option C Unconditional Discharge (~2,500 LoC)

Nineteen commits' worth of Y_h Lipschitz tightening ($c = 4 \to c = \pi/2$, a factor-2.55 sharpening of the matrix-log Lipschitz constant), $\rho_{\mathrm{Fib}\,SU(2)}$ matrix-level helpers, load-bearing identities $[F, G] = -Y_h \Delta$ and $\exp(-[F,G]) = \Delta$, the substantive `dnStepFG_gC_minus_Delta_norm_le_cubic` Dawson-Nielsen cubic composition, and the numerical chain helper `valid_branch_K_chain_le_K_compose_numeric` calibrating $K_{\mathrm{proof}} \le 788 \le K_{\mathrm{compose}} = 1024$.

**Audience:** quantum-information theorists working with matrix-Lie-group structure (Dawson, Nielsen, Aharonov, Arad); analog-anyon physicists (Bonesteel, Hormozi, Trebst, Bonderson); Mathlib4 working group (Y_h Lipschitz tightening is Mathlib-PR-quality).

**Why Path A Option C specifically:** Earlier discharge attempts (`SkApproxCSuperQuadraticBound K_compose` at smaller $K_{\mathrm{compose}}$ values) overshot the convergence condition $K \cdot \sqrt{2 \varepsilon_0} \le 1/2$. The principled path closes the calibration gap via sharper BCH cubic constants (320 → effective 200 via tighter $(\pi/4) \cdot \sqrt{2} \le 6/5$ bound), arriving at machine-verified constants $K_{\mathrm{compose}} = 1024$, $\varepsilon_0 = 1/8{,}388{,}608$, $K_{\mathrm{proof}} \le 788$ (margin ~236).

### Pillar 3 — The Wave 8 Closeout (D4 §9 + Figures + Notebooks + Tests)

The presentation-ready stack that transforms Phase 6t from "kernel-verified Lean substrate" to "fully publication-ready bundle absorption." D4 §9 unified prose (~3,500 words LaTeX, 5 subsections), two new figures (`fig_sk_length_bound_curve` and `fig_fibonacci_braid_word_t_gate_example`), two new notebooks (Technical + Stakeholder), 15 Python smoke tests, three new bibitems (`AharonovArad2017`, `DawsonNielsen2006`, `KitaevShenVyalyi2002`).

**Audience:** D4 bundle readership (topological quantum computing community); flagship F readership (broader research-program audience); reviewers consuming the unified Lean+LaTeX+notebook artifact stack.

**Why Wave 8 matters strategically:** The multi-modal artifact stack is what downstream researchers actually consume. The kernel-verified Lean proof is the trust anchor; the LaTeX prose is the academic-publication channel; the figures are the pedagogical anchor for talks and reviews; the notebooks are the executable demonstration for sceptical readers.

---

## Bridge Map — How Phase 6t Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6t |
|---|---|---|---|
| Phase 6p F.21 Fibonacci density | 6p | shipped UNCONDITIONAL | Substrate dependency — Phase 6t builds the quantitative compiler on top of Phase 6p's kernel-verified theoretical universality. Without Phase 6p's `fibonacci_density_F21_unconditional`, the Phase 6t result would be conditional on FKLW. |
| Phase 5 Step 13 (von Neumann + Cartan v4 + IFT-through-$\mathfrak{su}(2)$) | Phase 5/6p | shipped | Substrate dependency — Phase 6t uses the matrix-Lie infrastructure (Trotter limits, BCH cubic remainder, IFT chain). |
| Dawson-Nielsen 2006 arXiv:quant-ph/0505030 | upstream | published | Primary source — the textbook quantitative SK paper. Phase 6t formalizes the entire recursion, not just the asymptotic statement. |
| Aharonov-Arad arXiv:quant-ph/0605181 | upstream | published | Reichardt-style simpler reproof of FKLW (consumed by Phase 6p; new bibitem in D4 §9 via Phase 6t Wave 8). |
| Kitaev-Shen-Vyalyi 2002 | upstream | textbook | Classical Solovay-Kitaev textbook — new bibitem in D4 §9 via Phase 6t Wave 8. |
| Mathlib4 (v4.29.0; pinned `8850ed93`) | upstream | partial | Solovay-Kitaev ABSENT in any Mathlib (pre-Phase-6t); Stone-Weierstrass exists (`Mathlib/Topology/DenseRange.lean`) but not specialized. Phase 6t is the first formalization. |
| Phase 6u alphabet-agnostic substrate | downstream | shipped 2026-05-25 | Phase 6u extracts the alphabet-agnostic substrate from Phase 6t's Fibonacci-specific ascent. The seven Wave-1-6 modules become Phase 6u's generic substrate via abstraction over `GeneratingSet`. |
| D4 bundle §9 | Phase 7 absorption | pending (skeleton + 3,500-word prose in Wave 8) | D4 §9.3–§9.5 absorbs Phase 6t content. §9.6–§9.8 will additionally absorb Phase 6u's multi-alphabet showcase. |
| Mathlib upstream-PR pipeline | Phase 6s Track 2 / community citizenship | 9 PR-quality lemmas surfaced | Opportunistic upstream contribution targets; user-authorization gate for actual submission remains explicit. |

---

## Audiences and Outward-Facing Positioning

### Audience 1: Quantum-Compiler Researchers and Toolchain Developers

The practical message: **kernel-verified quantitative Solovay-Kitaev compiler exists**, instantiated for the Fibonacci-anyon braid representation, with explicit constants ($K_{\mathrm{compose}} = 1024$, $\varepsilon_0 = 1/8{,}388{,}608$, $K_{\mathrm{proof}} \le 788$, length constant $\approx 1000$, exponent $\log 5 / \log(3/2) \approx 3.97$). The verification is in Lean 4 (Mathlib4 v4.29.0), kernel-only `{propext, Classical.choice, Quot.sound}`, zero new project-local axioms.

This is positioned as a **specification reference** for industry compilation toolchains. Q#, Qiskit, Cirq, gridsynth — each implements a variation of Solovay-Kitaev with various refinements. Phase 6t's Lean formalization is the verifiable baseline against which those production compilers can be checked.

### Audience 2: Topological-Quantum-Computation Researchers

The Fibonacci-specific message: **the canonical Dawson-Nielsen quantitative SK length bound $O(\log(1/\varepsilon)^{3.97})$ is now kernel-verified for the Fibonacci braid representation $\rho_{\mathrm{Fib}}$ on $B_3$**. Combined with Phase 6p's F.21 unconditional density theorem, the project's two trust-anchor theorems for Fibonacci topological universal computation are both machine-verified.

For researchers in the Freedman-Kitaev-Larsen-Wang lineage and the Bonesteel-Hormozi-Trebst experimental-anyon community: Phase 6t completes the formal-verification stack from "Fibonacci anyons are dense" (Phase 6p F.21) to "Fibonacci anyons compile efficiently" (Phase 6t quantitative SK).

### Audience 3: Formal-Methods and Verified-Quantum-Software Community

The methodology message: **the substantive Dawson-Nielsen quantitative SK content is formalizable to kernel-only completeness in current Mathlib4** — no new Mathlib substrate was required for the Fibonacci-specific ascent. The Lie-algebraic core (group commutators, balanced commutators, BCH cubic remainder, IFT through tangent space) is project-local but kernel-clean.

This positions Phase 6t as a **template for first-ascent formalization work in quantum-compiler verification**. Future formalization projects in the Lean/Coq/Agda ecosystems can follow the same pattern: build the substrate project-local, isolate the kernel-only headline, surface Mathlib-PR-quality lemmas as opportunistic upstream contributions.

### Audience 4: Lean / Mathlib Working Groups

Phase 6t demonstrates Mathlib4 v4.29.0 is **sufficient** to formalize quantitative Solovay-Kitaev for a specific alphabet. No new Mathlib substrate was required.

Nine Mathlib-PR-quality lemmas surfaced during Phase 6t (listed in detail in `Phase6t_Implications.md`). These are natural upstream contributions:

  1. Generic `groupCommutator_stability` (Wave 1).
  2. Generic `matrix_inv_diff_norm_le` (Wave 1 strengthening).
  3. Generic 2×2 matrix entrywise→opNorm bridge (Wave 3).
  4. Generic geometric recurrence $x_{n+1} = a \cdot x_n + b$ closed form (Wave 5).
  5. `groupCommutator_stability_nearIdentity` (Iteration 2 substrate).
  6. `SU2_norm_sub_aI_le_norm_sub_one` ($SU(2)$ row-sum identity).
  7. `Y_h_norm_le_half_pi_norm_sub_one` (tightest matrix-log Lipschitz bound).
  8. `SU2_subtype_inv_val_eq_matrix_inv` (subtype-inverse bridge).
  9. `valid_branch_K_chain_le_K_compose_numeric` (numerical calibration template).

Future Phase 6s Track 2 (community citizenship) work could shepherd these to Mathlib upstream. The user-authorization gate for actual Mathlib4 PR submission remains explicit.

---

## Comparison: Phase 6p vs Phase 6t

| Dimension | Phase 6p | Phase 6t |
|---|---|---|
| Theorem class | Theoretical density (FKLW) | Quantitative compilation (Dawson-Nielsen) |
| First-of-kind claim | First kernel-verified UNCONDITIONAL FKLW density on Fibonacci | First kernel-verified quantitative SK length bound in any proof assistant |
| Substantive piece | F.21 unconditional via Phase 5 Step 13 closure (~1,900 LoC across 18+ commits) | Path A Option C super-quadratic discharge (~2,500 LoC across 19 commits) |
| Substrate produced | Lie-algebraic substrate (Trotter, BCH cubic, IFT-through-$\mathfrak{su}(2)$) | Recursion substrate (group commutators, balanced commutators, $\varepsilon_0$-net, length bound) + Y_h Lipschitz tightening |
| Practical resonance | Topological QC researchers (FKLW lineage) | Quantum-compiler toolchain developers (Q#, Qiskit, gridsynth) |
| Methodology contribution | Demonstrating substantive density-of-image proofs are feasible without pre-existing Mathlib theorems | Demonstrating the entire Dawson-Nielsen recursion is formalizable, with explicit kernel-verified calibrated constants |
| Bundle absorption | D4 §9.1–§9.2 (Fibonacci density section) | D4 §9.3–§9.5 (quantitative SK section) — Wave 8 ships unified §9 prose |
| Sessions | Multi-session arc culminating 2026-05-22 PM | Multi-wave arc culminating 2026-05-23 PM Path A Option C |

The Phase 6p → 6t progression is the canonical "theoretical → quantitative" formalization arc. Phase 6p answers "is it possible in principle?" (yes, unconditionally); Phase 6t answers "can the compilation be done efficiently with explicit constants?" (yes, with $K_{\mathrm{compose}} = 1024$ and exponent $3.97$).

---

## What's Next

### Immediate (Phase 6u, complete 2026-05-25)

Phase 6u extracts the alphabet-agnostic substrate from Phase 6t (the Lie-algebraic core: Dawson-Nielsen super-quadratic recursion, Cartan closed-subgroup classification, BCH bracket closure, $\varepsilon_0$-net machinery) and validates it by instantiating at Clifford+T, the canonical fault-tolerant alphabet. Phase 6u ships the **first kernel-verified UNCONDITIONAL Clifford+T quantitative SK compiler**, the substantive ⟨H, T⟩ density proof (via Niven's theorem), and the alphabet-independent generic substrate (`GenericSU2GeneratingSet`, `GenericClosureDenseWitness`, `GenericEpsilonNet`, `GenericSolovayKitaevRecursion`, etc.). The 800-LoC Wave 4b port of the Phase 6t Path A Option C super-quadratic discharge to the generic substrate is the load-bearing engineering deliverable that validates Phase 6t's alphabet-genericity.

### Medium-term (Phase 6x+)

Per-alphabet instantiations:

  - **Track T-A1** trapped-ion native gates (Mølmer-Sørensen + 1Q rotations) — requires a discretization step + likely a Klein-style $SU(2)$ classification fragment.
  - **Track T-A2** Clifford+CCZ at 3-qubit primitives — target group becomes $SU(8)$, so the Phase 6t/6u substrate needs extension to higher-rank $SU(d)$.
  - **Track T-B** Read-Rezayi $SU(2)_k$ for $k \in \{5, 7\}$ — highest substrate-reuse, target group remains $SU(2)$, only generators change.

These are scoped in Phase 6u's roadmap (and the explicit re-slotting to Phase 6x+, not Phase 6v/6w which are committed to other strategic content) is documented in ADR 008.

### Medium-term: Mathlib Upstreaming

Surface the nine Mathlib-PR-quality lemmas (listed under Audience 4) to Mathlib4. This is Phase 6s Track 2 (community citizenship) work and would meaningfully strengthen Mathlib's coverage of matrix Lie theory + normed-ring perturbation theory.

### Long-term: D4 Bundle Lift

When D4 (Topological Quantum Computation) is finalized in Phase 7 absorption, §9.3–§9.5 will be lifted from the Phase 6t Wave 8 prose; §9.6–§9.8 will additionally include Phase 6u's multi-alphabet showcase (Fibonacci + Clifford+T as two demonstrating instances of the universal statement).

### Long-term: Industry Partnerships

The kernel-verified Fibonacci-specific quantitative Solovay-Kitaev compiler is positioned as a candidate for direct industry engagement once the D4 bundle is publication-ready. The Lean specification could serve as a verifiable baseline for production-grade quantum-compiler toolchains targeting topological hybrid architectures.

---

## Status

Phase 6t substantively COMPLETE. Path A Option C UNCONDITIONAL DISCHARGE shipped at $K_{\mathrm{compose}} = 1024$ via Y_h Lipschitz tightening ($c = 4 \to c = \pi/2$) and substantive Dawson-Nielsen cubic composition. Bundled-strict UNCONDITIONAL headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` ships both error AND length bounds at the same algorithmic compile level for tight $\varepsilon \in (0, \varepsilon_0]$.

**First kernel-verified quantitative Solovay-Kitaev length bound in any proof assistant**, per the May 2026 Lit-Search landscape scan.

Wave 8 closeout shipped autonomously: D4 §9 unified prose (~3,500 words), two figures, two notebooks (Technical + Stakeholder), Python smoke tests, three new bibitems. LaTeX compile clean (27pp). Build clean at 8627 jobs. Project axiom count UNCHANGED at 1; zero new project-local axioms across Phase 6t. Ready for Phase 6u alphabet-agnostic abstraction + Clifford+T instantiation, and eventual D4 bundle absorption.
