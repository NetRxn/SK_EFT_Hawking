# Strategic Positioning: Phase 6g — Global / Nonperturbative GR

## How the Singularity / Area / No-Hair Layer Lands in Lean

**Date:** 2026-05-07
**Context:** This memo positions Phase 6g (W1–W6 algebraic-relation + W9 curve-theoretic finish-up + W10 1D PDE distillation) within the broader research program. Phase 6g is CLOSED.

---

## Phase 6g's Strategic Value

Phase 6g formalizes the *global / nonperturbative* content of classical general relativity that emerges in the singular-physics regime: causal structure, the Penrose and Hawking–Penrose singularity theorems, Hawking 1971's area theorem, the Cauchy problem well-posedness, and the Israel / Mazur / Bunting no-hair theorem.

The strategic point is twofold:

1. **Two parallel scopes.** Algebraic-relation scope (Wave 1–6 algebraic) ships the structural content cheaply. Curve-theoretic scope (W9 four sessions + W10 PDE distillation) ships the substantive content at machine-checked Riccati / focal-point / wave-equation level.

2. **The Mathlib-dependency-fallback discipline as a methodology contribution.** Wave 5 ships the Cauchy problem at structural-Prop predicate scope; W10 ships the 1D wave-equation Fourès-Bruhat distillation. Neither claims to do the full Mathlib-PDE-dependent Fourès-Bruhat existence; together they capture the substantive content within Mathlib's current capability and defer the rest cleanly. I1 picks this up as a worked case for "what to do when the formal infrastructure isn't yet available."

---

## Six Strategic Pillars

### Pillar 1: Causal Structure as the Prerequisite Layer (Wave 1)

Wald §8.1 axioms: $J^+$, $I^+$, global hyperbolicity, Cauchy surfaces, strong / stable causality, time-function arguments. The `realLineSpacetime` witness confirms non-vacuity. Audience: mathematical-relativity / cosmic-censorship community.

### Pillar 2: Penrose Singularity Theorem with Riccati Focusing (Wave 2 + W9-S1)

Riccati comparison via `Convex.mul_sub_le_image_sub_of_le_deriv` is the substantive kernel. Penrose hypothesis bundle (NEC + trapped surface + global hyperbolicity) → geodesic incompleteness, encoded as a correctness-push biconditional under applicability. Audience: singularity-theorems community (Senovilla, Garfinkle); cosmic-censorship-conjecture researchers.

### Pillar 3: Hawking–Penrose with Cosmological-Λ Counterexample (Wave 3 + W9-S3)

SEC-variant cosmological singularity theorem with explicit cosmological-$\Lambda$-violates-SEC counterexample. The de Sitter universe sits in the structurally-non-singular branch. Audience: cosmology / inflation theorists; quantum-gravity researchers concerned with Big-Bang resolution.

### Pillar 4: Hawking 1971 Area Theorem (Wave 4 + W9-S4)

Schwarzschild monotone-mass area theorem with cross-bridge to Phase 6a Wave 3 BH entropy. Area-evolution-ODE monotone-rigidity at null-generator scope. Audience: BH-thermodynamics / entropy community; Hawking 1971 readers.

### Pillar 5: Cauchy Problem under Structural-Prop Scoping (Wave 5 + W10)

The load-bearing methodology case study. W5 ships the predicate framework; W10 ships the 1D wave-equation Fourès-Bruhat distillation as a fully-proved sanity check. Audience: PDE-formalization community (LMPP project); the I1 methodology paper's readership.

### Pillar 6: No-Hair Theorem with Mazur 1D Distillation (Wave 6 + W9-S2)

Kerr family + sub-extremality $J^2 \leq M^4$ + Mazur 1D distillation + Ernst-potential coincidence corollary. Audience: no-hair-theorem researchers (Israel, Mazur, Bunting); BH-uniqueness community.

---

## Bridge Map — How Phase 6g Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6g |
|---|---|---|---|
| Algebraic Riemann + Einstein tensor + Λ-vacuum biconditional | 6f W1+W2 | shipped | All 6 Phase 6g waves consume directly |
| Energy conditions (NEC/SEC) + counterexample witnesses | 6f W3 | shipped | Penrose (NEC) + Hawking–Penrose (SEC) + cosmological-Λ counterexample directly call this |
| Exact solutions catalog (Schwarzschild, dS) | 6f W4 | shipped | Wave 4 (area) + Wave 6 (Kerr specialization) |
| ADM constraints (Hamiltonian + momentum) | 6f W5 | shipped | Wave 5 Cauchy problem references |
| Bonn `CovariantDerivative` + W8 Levi-Civita uniqueness | 6f W7+W8 | shipped | W9 curve-theoretic finish-up unblocked |
| Phase 6e emergent stress-energy $T_{\mu\nu}^{\rm emerg}$ | 6e W4 | shipped | Penrose-NEC-on-emergent correctness-push |
| BH entropy $S = A/(4 G_N) - (3/2) \log(A/(4 G_N))$ | 6a W3 | shipped | Wave 4 area-theorem cross-bridge |

---

## Publication Strategy

Phase 6g lifts as **D3 §23–§27** (D3 supplement) per `PAPER_DRAFT_MAPPING.md`:

- §23 — causal structure axioms + Wald §8.1 + `realLineSpacetime` witness.
- §24 — Penrose hypothesis bundle + Riccati-focusing core + correctness-push-under-applicability biconditional.
- §25 — Hawking–Penrose SEC variant + cosmological-Λ-violates-SEC counterexample.
- §26 — classical area theorem: Schwarzschild monotone-mass + BH-entropy bridge.
- §27 — no-hair: Kerr family + sub-extremality + Schwarzschild specialization.
- §28 (W10 addition) — 1D wave-equation Cauchy distillation.

The Cauchy-problem structural-Prop scoping pattern lifts as an **I1 sidebar** — a methodology case study of the Mathlib-dependency-fallback discipline.

No standalone Phase 6g PRL splash. The chain is interlocking and benefits from being read as a single deep section in D3 rather than fragmented.

---

## What Phase 6g Unblocks

- **D3 §23–§27 + §28** consumption: D3 is currently 🟢 GREEN through Phase 7 absorption.
- **I1 methodology paper sidebar** on Mathlib-dependency-fallback discipline: I1 is 🟢 GREEN.
- **Phase 6m Track A Sakharov-criterion cross-bridge** uses the curve-theoretic Penrose substrate.
- **Future Mathlib upstream PR cycle** has additional candidates from W9 (Riccati comparison) and W10 (1D wave-equation distillation).

---

## Phase 6g Closure Summary

**Phase 6g is CLOSED.** Six algebraic-relation waves + W9 four-session curve-theoretic finish-up + W10 1D PDE distillation all shipped end-to-end at substantive level.

**Total Phase 6g numbers:**
- ~62+ substantive Lean theorems / 0 sorry / 0 new axioms across ~10–11 modules.
- 5+ first-formalization-in-any-proof-assistant claims.
- All content lifts as D3 §23–§28 plus I1 sidebar (W5 + W10 PDE distillation).
- Strengthening-discipline retroactive cuts: 6 across the wave; pattern-class flagged.

---

## Program Maturity Assessment after Phase 6g

The project's emergent-gravity machinery now has formal access to:

- **Microscopic side (Phase 1–4):** SK-EFT, ADW gap equation, fermion bag, vestigial gravity.
- **Linearized GR (Phase 6a):** linearized EFE, FLRW, GW170817 falsification, BH entropy, BCH four laws.
- **Nonlinear effective action (Phase 6e):** heat-kernel through $a_4$, Stelle higher-curvature, diff invariance, variational EFE, CC-reproduced, Einstein–Cartan torsion.
- **Algebraic-GR backbone (Phase 6f):** Riemann, Einstein tensor, energy conditions, exact solutions, ADM, tetrad, Lorentzian metric, Levi-Civita uniqueness.
- **Global / nonperturbative GR (Phase 6g):** causal structure, Penrose, Hawking–Penrose, area theorem, Cauchy problem, no-hair.

The substrate-to-singularity-resolution chain is now formally complete. The Penrose-NEC-on-emergent-stress-energy correctness-push is the pivot: condensate UV-completion vs classical singularity formation depends on which branch the emergent stress-energy lands in, and both branches are now machine-checked alternatives rather than ad-hoc claims.
