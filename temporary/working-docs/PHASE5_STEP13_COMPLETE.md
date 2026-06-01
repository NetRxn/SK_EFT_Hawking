# Phase 5 Step 13 — F.21 Fibonacci Density Unconditional Discharge

**Ship date:** 2026-05-22 PM
**Lake build:** clean, 8617 jobs (full project)
**Substrate counts at ship:** 7,106 theorems / 369 modules / 13,275 declarations / 0 sorry / 0 effective project-local axioms
**Pipeline invariants:** #10 (no `maxHeartbeats` in proofs) and #15 (no new project-local axioms) RESPECTED throughout.

---

## Headline

The Freedman–Kitaev–Larsen–Wang **F.21 density theorem** for the Fibonacci anyon braid representation is now **fully unconditional** in the SK_EFT_Hawking Lean formalization. The terminal theorem

```
SKEFTHawking.FKLW.fibonacci_density_F21_unconditional :
  AharonovAradBridge.DenseInSpecialUnitary 3 2 (fun b => ↑(ρ_Fib_SU2 b))
```

has axiom closure `[propext, Classical.choice, Quot.sound]` (Lean standard kernel only) and **zero tracked propositional hypotheses**. The proof of `CartanFinalStep_SU2_v4_holds` — the last remaining gravity well in the Phase 6p Wave 2c.4a-R4.2.d.R5.4 arc — was discharged kernel-only on 2026-05-22 PM via a Cartan v4 Inverse Function Theorem (IFT) 3-direction composition through `↥𝔰𝔲(2)` (≈370 LoC), much lighter than the originally scoped closed-subgroup classification route (~1,500–2,500 LoC).

Phase 5 Step 13 Path (i) FINAL closed the substrate's longest-running open gap (≈30 sessions over multiple months).

---

## Mathematical content

### What F.21 says

F.21 is the density half of the Freedman–Kitaev–Larsen–Wang theorem for Fibonacci anyons (Freedman, Larsen, Wang, *Comm. Math. Phys.* 227 (2002) 605–622; Freedman, Kitaev, Larsen, Wang, *Bull. AMS* 40 (2003) 31–38). It states that the two-strand braid representation of the Fibonacci anyon model — the pair `(ρ_Fib(σ_1), ρ_Fib(σ_2))` of `SU(3)_2`-level Jones-Wenzl projector unitaries restricted to the Fibonacci subsector and embedded as elements of `SU(2)` — generates a dense subgroup of `SU(2)`.

Combined with the Solovay–Kitaev theorem (Dawson and Nielsen, *Quantum Inf. Comput.* 6 (2006) 81–95), density gives **efficient universal approximation**: any target unitary `U ∈ SU(2)` admits a length-`O(log^c (1/ε))` Fibonacci braid word `w` with `‖ρ_Fib(w) − U‖ < ε`. This is the formal foundation of topological quantum computation via Fibonacci anyons.

In Lean the density target is the standardized predicate

```
AharonovAradBridge.DenseInSpecialUnitary 3 2
  (fun b => ↑(ρ_Fib_SU2 b)) : Prop
```

unfolding to: the image of the Fibonacci 2-strand braid representation `ρ_Fib_SU2 : B_2 → SU(2)` is topologically dense in `specialUnitaryGroup (Fin 2) ℂ` under the `linftyOpNorm` topology.

### What `CartanFinalStep_SU2_v4_holds` proves

`CartanFinalStep_SU2_v4` is the SU(2) closed-subgroup classification predicate in its v4 form (revised 2026-05-21 after the v1/v2 predicates were shown soundness-flawed and v3 was conditional on a Trotter limit gap). The statement: for a closed subgroup `H ≤ SU(2)` and any two **ℝ-linearly-independent** `X_1, X_2 ∈ 𝔰𝔲(2) := tracelessSkewHermitian (Fin 2)` with `exp(ℝ • X_1) ⊆ H` and `exp(ℝ • X_2) ⊆ H` (pointwise), one has `H = ⊤ = SU(2)`.

The 2026-05-22 PM proof composes four steps:

1. **BCH bracket closure (Trotter limit).** From the two 1-parameter subgroups in `H`, derive `exp(ℝ • [X_1, X_2]) ⊆ H`, where `[X_1, X_2] := X_1 · X_2 − X_2 · X_1` is the matrix Lie bracket. The argument is the standard Trotter formula
   ```
   exp(t · [X_1, X_2]) = lim_{n→∞} (P_n)^n,
   P_n := exp(−s_n · X_1) · exp(−s_n · X_2) · exp(s_n · X_1) · exp(s_n · X_2),
   s_n := √(t/n).
   ```
   Each `P_n ∈ H` by group-multiplicative closure; each `(P_n)^n ∈ H` by power closure; `H` is topologically closed, so the limit lies in `H`. The per-step bound `‖P_n − exp(s_n^2 · [X_1, X_2])‖ ≤ 320 · δ^3` is supplied by `SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm` (already shipped).
2. **Spanning.** `{X_1, X_2, [X_1, X_2]}` is a basis of `𝔰𝔲(2)` whenever `X_1, X_2` are ℝ-linearly independent — supplied by `SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_spans`.
3. **Local diffeomorphism `𝔰𝔲(2) → SU(2)` near 1.** Supplied by `OneParameterSubgroupSU2.SU2_nhd_one_covered_by_exp_ts`: a neighborhood `W` of `1` in `Matrix (Fin 2) (Fin 2) ℂ` such that every `h ∈ W ∩ SU(2)` admits `Y ∈ 𝔰𝔲(2)` (in the IFT source) with `expAmbient Y = h`.
4. **Open subgroup containing 1 in interior ⟹ ⊤.** Supplied by `OneParameterSubgroupSU2.SU2_subgroup_eq_top_of_one_mem_interior`.

The IFT 3-direction discharge — the substantive 2026-05-22 PM ship — synthesizes a continuous linear equivalence `↥𝔰𝔲(2) ≃L[ℝ] (ℝ × ℝ × ℝ)` from the three independent directions `X_1, X_2, [X_1, X_2]`, composes it with the `expAmbient`-IFT instance shipped earlier, and threads through `tsProj` (the continuous linear projection of the ambient matrix space onto `↥𝔰𝔲(2)` via the orthogonal complement) to land in the spanning-locus open neighborhood of `1`.

---

## New / extended modules

All three modules live under `lean/SKEFTHawking/FKLW/` and were either created or substantially extended in the 2026-05-22 ship. The pre-existing top-level module `lean/SKEFTHawking/MatrixBCHCubic.lean` is consumed unchanged.

### `SU2BCHBracketClosure.lean` (1,523 LoC total; +370 LoC in 2026-05-22 PM, plus +660 LoC in 2026-05-22 AM)

The substantive discharge module for the v4 Cartan final step. Ships, in order:

- **Generic substrate.** `grpComm a b := a · b · a⁻¹ · b⁻¹` (group commutator); `bracketMatrix X Y := X · Y − Y · X` (matrix Lie bracket).
- **Bracket-closure substrate (Step 1).** `fourfoldComm s X Y := expAmbient (−s • X) · expAmbient (−s • Y) · expAmbient (s • X) · expAmbient (s • Y)`; `fourfoldComm_mem_H` (membership in `H` when both 1-parameter subgroups are); `fourfoldComm_norm_le` (cubic remainder bound, kernel-only); `trotter_sequence_tendsto` (n-th power of `fourfoldComm √(t/n)` converges to `expAmbient (t · [X,Y])`, kernel-only); `exp_bracket_mem_H` (Step 1 main theorem, kernel-only).
- **IFT 3-direction substrate (Step 3 composition).** `tsProj` (continuous linear projection onto `↥𝔰𝔲(2)` via complement); `tsProj_apply_of_mem` (`tsProj X = X` for `X ∈ 𝔰𝔲(2)`); `threeDirProduct` and `threeDirDerivCLE` (basis-change continuous linear equivalence `(ℝ × ℝ × ℝ) ≃L[ℝ] ↥𝔰𝔲(2)`); `threeDirProduct_hasStrictFDerivAt_zero` (the strict-derivative-at-zero composition, kernel-only).
- **Mathlib-PR-quality sub-lemmas.** `pow_sub_pow_telescoping_eq` (non-commutative telescoping identity `A^n − B^n = Σ_{k<n} A^k · (A − B) · B^{n−1−k}`); `pow_sub_pow_norm_le_of_pow_bounds` (operator norm bound on the telescoped sum); `expAmbient_smul_real_hasStrictDerivAt_zero` (strict derivative of `t ↦ expAmbient (t • X)` at zero).
- **Final composition.** `CartanFinalStep_SU2_v4_holds : CartanFinalStep_SU2_v4` (the headline discharge, kernel-only); `fibonacci_density_F21_unconditional` (the terminal F.21 culmination, kernel-only).

The module's top-of-file docstring documents the four-step proof structure, pipeline-invariant compliance, the ADR-006 retrospective (the prior "NOT Trotter" rule was an invented constraint — Trotter via the shipped cubic-remainder bound is the canonical path), and the full export ledger.

### `OneParameterSubgroupSU2.lean` (5,456 LoC total)

Discharges the strengthened gap-#2 predicate `OneParamSubgroupFromAccPt_SU2` via the von Neumann 1-parameter subgroup theorem for SU(2): any closed subgroup `H ≤ SU(2)` with the identity as an accumulation point contains a continuous nontrivial 1-parameter subgroup with image in `H`.

The module is structured as:

- **§1. `su2Log`** — the local IFT inverse of `expAmbient` near identity, extracted from the shipped `SU2LocalDiffeo` IFT instance, and (new on 2026-05-22) the named module-level lemma `su2Log_hasStrictFDerivAt_one` (Mathlib-PR-quality form of "matrix log has strict Fréchet derivative the identity at 1").
- **§2. `su2Log h ∈ tracelessSkewHermitian (Fin 2)`** — matrix log of an SU(2) element near 1 lies in 𝔰𝔲(2).
- **§3. von Neumann construction** — from a sequence `h_n → 1` in `H \ {1}`, extract a unit `X ∈ 𝔰𝔲(2)` with `exp(t · X) ∈ H` for all `t` via Bolzano–Weierstrass on the unit sphere of `𝔰𝔲(2)` and integer-rounding convergence.
- **§§ later sections** — local-diffeomorphism corollaries `SU2_nhd_one_covered_by_exp_ts` and the open-subgroup-implies-top result `SU2_subgroup_eq_top_of_one_mem_interior`, plus the H_Fib unconditional witness `H_Fib_v4_witness_unconditional` shipped 2026-05-21 (session 80).

This module is also the canonical home for the IFT corollaries consumed by `SU2BCHBracketClosure.lean` (specifically the nbhd-of-1 covering result and the subgroup-eq-top promotion).

### `SU2LieAlgebra.lean` (2,145 LoC total)

Foundational substrate: the (real) Lie algebra `𝔰𝔲(n) := tracelessSkewHermitian (Fin n) ℂ`, equipped with its standard generators and bracket structure.

- `Matrix.IsSkewHermitian` predicate (matrix-level skew-Hermitian; mirrors Mathlib's `Matrix.IsHermitian`).
- `tracelessSkewHermitian (n : Type*) [Fintype n] (α : Type*)` — the ℝ-submodule of `Matrix n n ℂ` of traceless skew-Hermitian matrices. The (real) Lie algebra `𝔰𝔲(n)`.
- Pauli anti-Hermitian generators `paulI_x, paulI_y, paulI_z` (= `i · σ_x`, `i · σ_y`, `i · σ_z`); membership lemmas.
- Lie-bracket closure (`tracelessSkewHermitian_bracket_mem`); spanning lemma `tracelessSkewHermitian_X_Y_bracket_spans` used by `SU2BCHBracketClosure.lean` Step 2.
- Cramer-rule spanning / linear-independence substrate, continuity helpers for the canonical projections, and the `pauliDet` machinery consumed downstream by `FibSU2LieBundle.lean`.

Architectural note: this module is the foundation for the Cartan-A → Cartan-D layer ramp:
- Cartan-B: matrix exponential `𝔰𝔲(2) → SU(2)` (smooth, derivative at 0 = identity).
- Cartan-C: normed-space IFT for local diffeomorphism.
- Cartan-D: composition closing `1 ∈ interior(closure H_Fib)`.
- Layer E: trivial composition into `DenseInSpecialUnitary`.

### `MatrixBCHCubic.lean` (1,755 LoC; pre-2026-05-22, consumed unchanged)

Ships the per-step cubic-remainder bound consumed by Step 1 of the v4 discharge:

```
SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm :
  ‖fourfoldComm s X Y − expAmbient (s² · bracketMatrix X Y)‖ ≤ 320 · δ³
```

for `δ ≤ s · max ‖X‖ ‖Y‖` and `δ ≤ 1`. The `K = 320` constant is structural (cleanest closed-form proof architecture); a `K ≤ 4` tightening was scoped as ~300–500 LoC MVT-style refactor and explicitly deferred — the looser constant is sufficient for all downstream applications.

---

## Headline theorems

All eight headline theorems verify kernel-only (axiom closure `[propext, Classical.choice, Quot.sound]`) via `#print axioms` / `lean_verify`.

| Fully-qualified Lean name | One-line statement |
| --- | --- |
| `SKEFTHawking.FKLW.fibonacci_density_F21_unconditional` | `DenseInSpecialUnitary 3 2 (fun b => ↑(ρ_Fib_SU2 b))` — the terminal F.21 density culmination (zero tracked Props). |
| `SKEFTHawking.FKLW.CartanFinalStep_SU2_v4_holds` | For any closed `H ≤ SU(2)` and ℝ-linearly-independent `X_1, X_2 ∈ 𝔰𝔲(2)` with `exp(ℝ • X_i) ⊆ H`, `H = ⊤`. |
| `SKEFTHawking.FKLW.OneParameterSubgroupSU2.H_Fib_v4_witness_unconditional` | Existence of two ℝ-LI `X_1, X_2 ∈ 𝔰𝔲(2)` with `exp(ℝ • X_i) ⊆ H_Fib` (the v4 witness feeding `CartanFinalStep_SU2_v4_holds`). |
| `SKEFTHawking.FKLW.trotter_sequence_tendsto` | `(P_n)^n → expAmbient (t · [X_1, X_2])` as `n → ∞`, with `P_n` the fourfold commutator at scale `√(t/n)`. |
| `SKEFTHawking.FKLW.exp_bracket_mem_H` | For closed `H ≤ SU(2)` and `X_1, X_2 ∈ 𝔰𝔲(2)` with `exp(ℝ • X_i) ⊆ H`, `exp(ℝ • [X_1, X_2]) ⊆ H`. |
| `SKEFTHawking.FKLW.threeDirProduct_hasStrictFDerivAt_zero` | The three-direction product map has strict Fréchet derivative `threeDirDerivCLM` at 0. |
| `SKEFTHawking.FKLW.tsProj` | Continuous linear projection `Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ↥𝔰𝔲(2)` via the orthogonal complement of `↥𝔰𝔲(2)`. |
| `SKEFTHawking.FKLW.OneParameterSubgroupSU2.su2Log_hasStrictFDerivAt_one` | `su2Log` has strict Fréchet derivative the identity at `1` (named module-level form of the IFT instance). |

---

## Substrate counts at ship (2026-05-22 PM regen)

| Metric | Value |
| --- | --- |
| Total declarations | 13,275 |
| Total theorems | 7,106 |
| Substantive theorems | 7,081 |
| Placeholder theorems | 25 |
| Project-local axioms | 0 |
| `sorry` declarations | 0 |
| Modules | 369 |

**Axiom posture.** The previously-shipped `gapped_interface_axiom` was retired on 2026-05-19 (session 29) via the Phase 5h Wave 2 conversion to a `TPFConjecture : Prop` tracked hypothesis (commit `d282677`). At ship, the project has **zero** project-local axioms in the effective sense: all surviving content is either kernel-only or routed through tracked propositional hypotheses that are explicit hypotheses on the theorems consuming them. Both prior surviving axioms were discharged in the autonomous-loop arc that built out the Phase 6p Wave 2c substrate.

**Strengthening discipline.** Pipeline invariants #10 (no `maxHeartbeats` in proof bodies) and #15 (no new project-local axioms) were respected throughout the 30-session arc. Sub-lemmas were decomposed to `have`-blocks of ≤ 12 terms each.

---

## Reproducibility

```bash
cd SK_EFT_Hawking/lean

# Full project build
lake build

# Standalone-target builds (each should report clean)
lake build SKEFTHawking.FKLW.SU2BCHBracketClosure   # ~8270 jobs
lake build SKEFTHawking.FKLW.OneParameterSubgroupSU2 # ~8269 jobs
lake build SKEFTHawking.FKLW.SU2LieAlgebra          # ~8249 jobs

# Kernel-only axiom verification
echo '#print axioms SKEFTHawking.FKLW.fibonacci_density_F21_unconditional' \
  | lake env lean --stdin
# Expected: 'propext, Classical.choice, Quot.sound'

echo '#print axioms SKEFTHawking.FKLW.CartanFinalStep_SU2_v4_holds' \
  | lake env lean --stdin
# Expected: 'propext, Classical.choice, Quot.sound'

echo '#print axioms SKEFTHawking.FKLW.OneParameterSubgroupSU2.H_Fib_v4_witness_unconditional' \
  | lake env lean --stdin
# Expected: 'propext, Classical.choice, Quot.sound'

# Or via the project's validation suite
cd ..
uv run python scripts/validate.py --check lean_build
uv run python scripts/validate.py --check graph_integrity
```

Standalone-target builds report ~8,250–8,270 jobs because they trace the full transitive dependency closure (Mathlib + the SK_EFT_Hawking substrate consumed by each module). A full-project `lake build` reports 8,617 jobs.

---

## Mathlib upstream-PR candidates

The 2026-05-22 PM ship contained four sub-lemmas of upstream Mathlib4 quality. None depend on SK_EFT_Hawking-specific definitions; each is a clean specialization of standard normed-algebra / Lie-group / matrix-analysis material that is currently absent from Mathlib at v4.29.0.

1. **`pow_sub_pow_telescoping_eq`** (`SU2BCHBracketClosure.lean`). Non-commutative telescoping identity: for a non-commutative ring and `A, B` with `n : ℕ`, `A^n − B^n = Σ_{k=0}^{n−1} A^k · (A − B) · B^{n−1−k}`. The commutative case is in Mathlib (`Commute.sub_pow`); the non-commutative version is a standard analysis prerequisite missing upstream.
2. **`pow_sub_pow_norm_le_of_pow_bounds`** (`SU2BCHBracketClosure.lean`). Operator-norm bound on the above telescoping sum: under uniform bounds on `‖A^k‖` and `‖B^k‖`, the right-hand side is bounded by `n · M^{n−1} · ‖A − B‖`. Useful far beyond SU(2).
3. **`expAmbient_smul_real_hasStrictDerivAt_zero`** (`SU2BCHBracketClosure.lean`). For a Banach algebra over ℝ and `X` in the algebra, `t ↦ NormedSpace.exp ℝ (t • X)` has strict derivative `X` at `0`. The non-strict version exists in Mathlib via `NormedSpace.hasDerivAt_exp_smul_const`; the strict version is the natural strengthening for IFT applications.
4. **`OneParameterSubgroupSU2.su2Log_hasStrictFDerivAt_one`** (`OneParameterSubgroupSU2.lean`). The local-IFT inverse of `expAmbient` near identity has strict Fréchet derivative the identity at `1`. The right Mathlib home would pair this with the existing `NormedSpace.exp` API to give a generic "matrix log near identity" instance for general dimension `n`; the SU(2) case here is the natural specialization.

A future Mathlib upstreaming pass on this ship would naturally also bring `tracelessSkewHermitian` to mathlib (as a specialization of `skewAdjoint R` from `Mathlib.Algebra.Star.SelfAdjoint`) and the Pauli anti-Hermitian generator file. These have been internally namespaced for project safety; the upstream form would drop the `SKEFTHawking` namespace prefix.

---

## What's next

The F.21 discharge closes the Phase 5 Step 13 / Phase 6p Wave 2c.4a-R4.2.d.R5.4 substrate arc. Several substrate directions naturally extend from it.

**1. Dawson–Nielsen length bound for Fibonacci anyons.** F.21 gives density; composing with the Solovay–Kitaev theorem gives length-`O(log^c (1/ε))` approximation. The constants are unfavorable in general but become explicit for the Fibonacci generators via the Rouabah split-braid substrate already shipped in `RouabahSplitBraid.lean`. A Phase 6p follow-up could formalize the explicit `c = log_φ(2 · 5 · 7)` / `c ≈ 3.97` constant for the Fibonacci-anyon Solovay–Kitaev variant (Kliuchnikov–Maslov–Mosca-style refinement).

**2. Mathlib upstream PRs.** The four sub-lemmas above, plus the `tracelessSkewHermitian` / Pauli substrate, plus the IFT-on-submanifold infrastructure used by `SU2_nhd_one_covered_by_exp_ts` are natural upstream candidates. The non-commutative telescoping lemma is the most reusable; the strict-derivative-at-zero lemma is the most immediately useful for downstream Lie-group work.

**3. Analog-Hawking applications.** The Fibonacci-anyon braid universality result connects to the project's broader analog-gravity programme via the `BHEntropyMicroscopic` and `APSEta.*` substrate: a universal topological-quantum-computation gate set realized inside a quantized 2+1-dimensional condensed-matter platform gives an explicit "topological microstate counting" route to the Bekenstein–Hawking entropy on the analog-Hawking side. This is a longer-term Phase 8 direction and currently scoped only at the references / Lit-Search level.

**4. Per-bundle absorption.** Per `BUNDLE_LIFT_PROCEDURE.md`, the Phase 5 Step 13 ship is candidate content for the Tier-1 D-series bundle that hosts the FKLW / topological-QC material (track this via `docs/PAPER_DRAFT_MAPPING.md` and the bundle-freshness check in `scripts/validate.py`). The absorption protocol in `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` is the canonical route once the bundle's freshness flag flips to `freshness-stale=true`.

---

## See also

- `docs/WAVE_EXECUTION_PIPELINE.md` — the 14-stage substrate-development pipeline that produced this ship.
- `SK_EFT_Hawking_Inventory_Index.md` — module map, counts, pipeline invariants; the 2026-05-22 PM entry is the canonical lifecycle record for this ship.
- `SK_EFT_Hawking_Inventory.md` — full per-module inventory, theorem-by-theorem.
- `docs/PERMANENT_TRACKED_HYPOTHESES.md` — registry of tracked propositional hypotheses (the F.21 chain has none).
- `docs/PAPER_STRATEGY.md` — bundle-architecture canon (1 flagship F + 5 Tier-1 D1–D5 + 3 Tier-2 L1–L3 + 2 Tier-3 I1–I2 + 1 Tier-3 I3 + 2 Tier-4 E1–E2).
- `lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean` — the substantive 2026-05-22 PM module, top-of-file docstring covers the four-step proof structure in detail.
