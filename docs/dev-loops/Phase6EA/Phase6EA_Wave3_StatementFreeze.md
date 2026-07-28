# Phase 6EA — Wave 3 Statement Freeze (shot noise & the quantum seam)

**Status: FROZEN (2026-07-28).** Completes the Stage-2 layer that
[`Phase6EA_Stage2_StatementFreeze.md`](Phase6EA_Stage2_StatementFreeze.md) left open: that
document froze Waves 1–2 and scoped Wave 3 as *recommended, not frozen* (its §4 resolved
UNKNOWN-3 at the level of "which shape", deferring the exact statements). This document freezes
the exact Wave-3 Lean statement layer.

**File:** `lean/SKEFTHawking/Detection/ShotNoise.lean` · **Namespace:** `SKEFTHawking.Detection`
**Root import:** add `import SKEFTHawking.Detection.ShotNoise` to `lean/SKEFTHawking.lean`
**in the same commit** (F8 — the `lean_lib` declares no `globs`).

**Publication target:** bundle **D12**. Bundle-aware from inception; no on-disk scaffolding here.

> **⚠️ GUARDRAIL (inherited).** Floors and screens over abstract count means and noise
> parameters. No device claim. Physical identification of an abstract parameter with a measured
> quantity is the consuming phase's declared hypothesis.

> **⚠️ This document is Stage 2 only** — frozen statement text + proof recipes, no proofs. The
> executing slot still runs the MCP-first loop and the Stage-3a strengthening checklist per
> theorem.

---

## 0. Substrate verified 2026-07-28 (read directly at main `d8d6473f`)

The prior freeze's §4.1 recipe named `psdSqrt`/`FidelityBounds` for the seam without pinning
locations. Six facts, verified by reading the sources:

| # | Finding | Impact |
|---|---|---|
| G1 | `sqrtFidelity hρ hσ := traceNorm (psdSqrt hσ * psdSqrt hρ)` (`MixedState.lean:548`) — it is **defined through `traceNorm`**, not through an abstract fidelity axiom. | (S1) reduces to a `traceNorm`-of-diagonal computation. Route is concrete; see §2.2. |
| G2 | `psdSqrt` is defined at `MixedState.lean:528` with `psdSqrt_posSemidef` / `_isHermitian` / `_mul_self` (`:532/536/540`). Additional API in `FidelityForwardBoundPSD.lean` (`psdSqrt_eq_conj_diag`) and `FidelityDataProcessing.lean` (`psdSqrt_unitary_conj`). | Present, but **spread across four files** — not the single "FidelityBounds substrate" the prior freeze implied. |
| G3 | **No `psdSqrt`-of-diagonal lemma exists** (grep: zero hits). | **One net-new lemma to build** (`psdSqrt_diagonal`, §2.1). This is the only genuinely new mathematical content in the seam. |
| G4 | `traceNorm_posSemidef : A.PosSemidef → traceNorm A = A.trace.re` — **PROVEN**, `MixedState.lean:142` (the 6AE linchpin). | Turns `traceNorm (diagonal r)` for `r ≥ 0` into `∑ r i` in one rewrite. |
| G5 | `traceDist_le_sqrt_one_sub_sqrtFidelity_sq` — **PROVEN**, `FidelityUpperBound.lean:126`. ⚠ `Phase6AE_Roadmap.md` still lists FvdG as *deferred frontier*; a note at `FidelityUpperBound.lean:23` records it was closed 2026-06-02. **The 6AE roadmap is stale on this point** — do not infer from it that FvdG is unavailable. | (S2) has its quantum half already proven. Logged as an out-of-scope doc-drift finding (§6). |
| G6 | Mathlib has `Matrix.PosSemidef.diagonal` (`LinearAlgebra/Matrix/PosDef.lean:61`, needs `0 ≤ d`) and `Matrix.diagonal_mul_diagonal` (`Data/Matrix/Mul.lean:381`). | Both §2.1 side-goals are one-lemma discharges. |

**Import cost, stated explicitly.** Wave 1 deliberately avoided importing `FidelityUpperBound`
(it drags the trace-norm/polar tower into `Detection/`). Wave 3 **pays that import** — the seam
*is* the tower's consumption. This is the prior freeze's own §5.7 judgement ("this is the place
where importing `FidelityUpperBound` would earn its keep"), now discharged. `ShotNoise.lean`
therefore has a heavier import chain than its two siblings **by design**, and Waves 1–2 remain
tower-free.

---

## 1. PSD convention — declared once, threaded everywhere

`GrapheneNoiseFormula` fixes the repo convention and Wave 3 matches it exactly:

* `johnsonNyquistPSD kB_T sigma_Q := 4 * kB_T * sigma_Q` — the **one-sided** Johnson–Nyquist form
  (two-sided would carry `2`).
* `hawkingNoisePSD hbar_omega sigma_Q greybody n_H := 2 * hbar_omega * sigma_Q * greybody * n_H`
  — the leading `2` is likewise the one-sided convention.

⟹ **Wave 3 is one-sided throughout**, and 6EB inherits it (its `shot_nep_formula :
NEP_shot,abs = √(2·E_ph·P_abs)` carries the same `2`, confirming consistency across the seam).
The convention is carried **in the statements**, not only in docstrings.

---

## 2. FROZEN — the quantum seam (UNKNOWN-3 discharged)

Per the prior freeze §4: ship **(S1) + (S2)**; **(S3)** (`OptimalHypothesisRate` consumption) is
**type-level impossible for Poisson** and is not attempted. Consequently **Wave 3 must NOT be
described as "the first project consumption of `HypothesisTesting`"** in any D12-facing text.

### 2.1 The one net-new lemma

```lean
/-- **`psdSqrt` of a PSD diagonal matrix is the entrywise `√`.** The only net-new mathematical
content of the seam: everything else composes existing lemmas. Proof: `psdSqrt` is characterised
by `psdSqrt_posSemidef` + `psdSqrt_mul_self`; `diagonal (√ ∘ d)` satisfies both
(`Matrix.PosSemidef.diagonal` with `Real.sqrt_nonneg`, and `Matrix.diagonal_mul_diagonal` plus
`Real.mul_self_sqrt (hd i)`), and the PSD square root is unique. -/
theorem psdSqrt_diagonal {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) :
    psdSqrt ((Matrix.PosSemidef.diagonal (fun i => Complex.ofReal_nonneg.mpr (hd i)))) =
      Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ))
```

*Executing slot: the exact binder shape of the PSD witness is elaboration-sensitive — settle it
with `lean_goal` before committing to the signature. The mathematical content is fixed; only the
witness plumbing is open.*

**Route grounded 2026-07-28 (G7, G8) — do not re-derive.** Uniqueness of the PSD square root is
the load-bearing step, and it does **not** need to be built:

* **G7.** `psdSqrt hM := hM.isHermitian.cfc Real.sqrt` (`MixedState.lean:528`) — the project's own
  *eigenvalue-based* functional calculus, **not** Mathlib's `CFC.sqrt`. Do **not** try to compute
  it on a diagonal matrix by unfolding `cfc`: `hM.isHermitian`'s eigendecomposition **sorts the
  eigenvalues**, so for `diagonal d` the eigenvector matrix is a permutation, not `1`, and the
  unfold route drags in sorting bookkeeping for no reason.
* **G8.** Mathlib **has PSD-square-root uniqueness** as
  `Matrix.PosSemidef.sq_eq_sq_iff` (`Mathlib.Analysis.Matrix.Order`):
  `A.PosSemidef → B.PosSemidef → (A ^ 2 = B ^ 2 ↔ A = B)`. Its siblings `sqrt_eq_iff_eq_sq`,
  `posSemidef_sqrt`, `sq_sqrt` are in the same module.

**Therefore the frozen proof is the uniqueness route, ~10 lines and fully cited:**
1. Both sides are PSD — `psdSqrt_posSemidef` (`MixedState.lean:532`) and
   `Matrix.PosSemidef.diagonal` (Mathlib `PosDef.lean:61`, entries `√(d i) ≥ 0`).
2. Both square to `diagonal d`: LHS by `psdSqrt_mul_self` (`MixedState.lean:540`), RHS by
   `Matrix.diagonal_mul_diagonal` + `Real.mul_self_sqrt (hd i)`.
3. Conclude by `Matrix.PosSemidef.sq_eq_sq_iff` (G8). Bridge `mul_self` ↔ `^2` with `sq` / `pow_two`.

`psdSqrt_eq_conj_diag` (`FidelityForwardBoundPSD.lean:40`) is **not needed** — an earlier draft of
this freeze suggested deriving uniqueness from it, which would have been re-deriving a Mathlib
lemma. Ignore that suggestion.

### 2.2 (S1) — the classical affinity IS the diagonal quantum fidelity

```lean
/-- **(S1) The commutative shadow.** For classical distributions `p q` on a finite alphabet, the
Uhlmann root-fidelity of their diagonal embeddings equals the classical Bhattacharyya affinity
`∑ᵢ √(pᵢqᵢ)`. This is the literal content of "the classical floors are the commutative shadow of
the quantum bounds", and it is a genuine cross-module bridge: the body *calls* `sqrtFidelity`,
`psdSqrt_diagonal`, and `traceNorm_posSemidef`. -/
theorem diagonalState_sqrtFidelity_eq_affinity {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    sqrtFidelity (diagonalPSD hp) (diagonalPSD hq) = ∑ i, Real.sqrt (p i * q i)
```

Proof recipe (all four steps are one-lemma rewrites once §2.1 lands):
1. `sqrtFidelity` unfolds to `traceNorm (psdSqrt _ * psdSqrt _)` (G1).
2. `psdSqrt_diagonal` twice, then `Matrix.diagonal_mul_diagonal` (G6) collapses the product to
   `diagonal (fun i => √(q i) * √(p i))`.
3. That matrix is PSD (`PosSemidef.diagonal`, entries `≥ 0`), so `traceNorm_posSemidef` (G4)
   rewrites `traceNorm` to `.trace.re`, and `Matrix.trace_diagonal` gives `∑ᵢ √(qᵢ)·√(pᵢ)`.
4. `Real.sqrt_mul_self`-family / `← Real.sqrt_mul (hq i)` turns `√qᵢ·√pᵢ` into `√(pᵢqᵢ)`
   (commute with `mul_comm`).

### 2.3 (S2) — the Wave-1 floor is the diagonal restriction of the quantum bound

```lean
/-- **(S2) The seam.** For any count rule `δ`, the two-outcome pushforward experiment
`P₀ = (1−e₀, e₀)`, `P₁ = (e₁, 1−e₁)` lives on `Fin 2` — finite, hence inside the quantum
substrate's reach. Chaining (S1) on that pushforward with the project's proven
`traceDist_le_sqrt_one_sub_sqrtFidelity_sq` (G5) and Wave 1's `affinity_le_binaryAffinity`
exhibits the Wave-1 Poisson floor as the diagonal restriction of the quantum two-state
discrimination bound. This is `classical_floor_le_quantum_optimum` in the only shape that is
true (an `OptimalHypothesisRate` specialization is type-level impossible — Poisson lives on ℕ,
which is not a `Fintype`). -/
theorem poissonFloor_le_diagonalQuantumBound {Nb Na : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2)
      ≤ avgAssignmentError (falseAlarm Nb δ) (missProb Na δ)
    ∧ sqrtFidelity (pushforwardPSD₀ hδ) (pushforwardPSD₁ hδ)
      = √(falseAlarm Nb δ * (1 - missProb Na δ)) + √((1 - falseAlarm Nb δ) * missProb Na δ)
```

> **Strengthening note (checklist #1 — flagged so the slot does not ship a weak form).** The
> conjunction above is **NOT** a redundant bundle: the left conjunct is the classical floor and
> the right is its quantum identification, and neither implies the other. But if the executing
> slot finds the two conjuncts drifting apart in use, **split them** — a two-conjunct bundle is
> only justified while both are cited together. Prefer the split if in doubt.

---

## 3. FROZEN — shot-noise algebra

```lean
/-- One-sided shot-noise PSD at a reference plane: `S = 2·E_ph·P` (the `2` is the one-sided
convention, matching `GrapheneNoiseFormula`). -/
noncomputable def shotPSD (E_ph P : ℝ) : ℝ := 2 * E_ph * P

/-- **Reference-plane transfer.** Referring an incident power to the absorbed plane through
quantum efficiency `η` scales the one-sided shot PSD by exactly `η`. The efficiency is an
explicit hypothesis, never absorbed into the definition. -/
theorem shotPSD_plane_transfer {E_ph P η : ℝ} (hη : 0 ≤ η) :
    shotPSD E_ph (η * P) = η * shotPSD E_ph P

theorem shotPSD_pos {E_ph P : ℝ} (hE : 0 < E_ph) (hP : 0 < P) : 0 < shotPSD E_ph P

/-- **Poisson thinning.** Independently retaining each count with probability `η` maps
`Poisson N` to `Poisson (η·N)`, at the level of the pmf.

**No `η ≤ 1` hypothesis** — see the strengthening note below. -/
theorem poisson_thinning {N η : ℝ≥0} (n : ℕ) :
    ∑' m, poissonPMFReal N m * (m.choose n : ℝ) * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (m - n)
      = poissonPMFReal (η * N) n

/-- **Mean = variance for the filtered count**, in the `N_eff` normalization — the scaling every
downstream dominance argument uses. -/
theorem shot_variance_eq_mean {N : ℝ≥0} : poissonVariance N = poissonMean N
```

**Strengthening note on `poisson_thinning` — the `η ≤ 1` hypothesis is DROPPED (checklist #4).**
My own first draft of this statement carried `(hη : η ≤ 1)`. Working the proof recipe shows it is
**not load-bearing**: reindexing `m = n + k` gives
`e^{−N}·(ηN)ⁿ/n! · ∑ₖ (N(1−η))ᵏ/k! = e^{−N}·(ηN)ⁿ/n!·e^{N(1−η)} = e^{−ηN}(ηN)ⁿ/n!`, and the
exponential series converges absolutely for **every** real argument — so neither the algebra nor
the summability ever consults `η ≤ 1`. Shipping it would be an unused hypothesis, which the
pipeline's theorem-quality rule forbids ("hypotheses must be load-bearing, not vacuously
satisfied"). Dropping it yields a **strictly stronger** theorem. `η ≤ 1` is what makes the
kernel a *probability* (i.e. what licenses reading the identity as physical thinning); that is a
consumer-side interpretive condition and belongs in 6EB's declared hypotheses, not here. Note
also that `m - n` is truncated ℕ subtraction, which is harmless: every `m < n` term is killed by
`m.choose n = 0`.

**Honest cost note on `poisson_thinning`.** This is the heaviest item in Wave 3 and the only one
that is not one-lemma algebra: it needs the reindexing `m = n + k` and the series identity
`∑ₖ Nᵏ(1−η)ᵏ/k! = exp(N(1−η))`, then `e^{−N}·e^{N(1−η)} = e^{−ηN}` by `← Real.exp_add`. It is
the same `NormedSpace.expSeries_div_hasSum_exp` template Wave 1 uses for the Bhattacharyya
identity, so the machinery is already familiar to the file. **It is not to be weakened to a
mean-only statement**: the roadmap AC says "pmf-level identity", and the consumer (6EB's plane
transfer) is only *honest* if the thinning is proved at the distribution level rather than
asserted for the mean. If it genuinely resists, report it — do not silently narrow.

---

## 4. FROZEN — the non-vacuity witness

The roadmap AC requires "at least one consuming falsifier-style witness: a concrete parameter
point where the shot-inclusive Gaussian model's average error strictly exceeds the Wave-1 floor".

```lean
/-- **The Wave-1 floor is not tight for a shot-limited Gaussian readout.** At the stated
operating point the Gaussian threshold model's average error strictly exceeds the Le Cam floor,
so the floor is a genuine *lower* bound with slack — not an equality dressed as an inequality
(which is what would make the whole floor family vacuous as a screen). -/
theorem shotGaussian_avgError_gt_leCam_floor : ...  -- `norm_num`, operating point fixed at Stage 3
```

*The operating point is deliberately NOT frozen here:* it must be chosen so both sides evaluate
by `norm_num` without a large-rational blowup, and that is cheapest to settle with the actual
Wave-1 and Wave-2 declarations in hand. Constraint for the slot: pick it so the **strict**
inequality holds with margin, and state the numerical gap in the theorem (checklist #2).

---

## 5. Preemptive-strengthening checklist, applied per frozen theorem

`Q1` bundle redundancy · `Q2` numerical connection · `Q3` bridge integrity · `Q4` trivial
discharge · `Q5` defining-the-conclusion.

| Declaration | Q1 | Q2 | Q3 | Q4 | Q5 | Note |
|---|---|---|---|---|---|---|
| `psdSqrt_diagonal` | ✓ | n/a | **calls** `psdSqrt_mul_self` + `PosSemidef.diagonal` | ✓ | ✓ | Net-new; uniqueness of the PSD root is the real content. |
| `diagonalState_sqrtFidelity_eq_affinity` | ✓ | n/a | **calls** `sqrtFidelity` + `traceNorm_posSemidef` — a real cross-module bridge, not a docstring reference | ✓ | ✓ | The literal "commutative shadow" statement. |
| `poissonFloor_le_diagonalQuantumBound` | ⚠ 2 conjuncts, **independent** — split if they drift | ✓ | **calls** Wave-1 floor + `sqrtFidelity` | ✓ | ✓ | See §2.3 note. |
| `shotPSD_plane_transfer` | ✓ | ✓ (the `η` factor is in the statement) | — | ⚠ cheap by `ring` — **but the content is the convention**, and the one-sided `2` is carried in `shotPSD` | ✓ | Documented: cheap proof, load-bearing convention. |
| `poisson_thinning` | ✓ | ✓ | **calls** `poissonPMFReal` | ✓ | ✓ | Distribution-level, not mean-level. The wave's hardest item. |
| `shot_variance_eq_mean` | ✓ | ✓ | — | ⚠ near-definitional once `poissonVariance` is defined — **push the content into a non-trivial definition or drop to a `simp` lemma**; do not present as physics | ✓ | Flagged: the Poisson mean=variance fact is only substantive if `poissonVariance` is defined independently (as a second moment), not as `:= N`. |
| `shotGaussian_avgError_gt_leCam_floor` | ✓ | ✓ | **calls** Wave-1 + Wave-2 | ✓ | ✓ | Strict inequality = the floor has slack. |

**Two flags carried forward to the post-wave audit.** `shotPSD_plane_transfer` and
`shot_variance_eq_mean` are the wave's tautology risks. `shot_variance_eq_mean` in particular is
**vacuous if `poissonVariance N := N`** — the definition must compute the second moment
independently, or the theorem states nothing. Decide at Stage 3 with `lean_goal`; if an
independent variance definition is disproportionate, ship it as a `simp` lemma with the
triviality disclosed rather than as a headline.

---

## 6. Out-of-scope finding logged (not this goal's to fix)

`docs/roadmaps/Phase6AE_Roadmap.md` describes the trace-norm triangle inequality, `traceDist ≤ 1`,
and Uhlmann fidelity / Fuchs–van de Graaf as an open "deferred frontier … multi-week from-scratch
build". At least FvdG is **closed**: `traceDist_le_sqrt_one_sub_sqrtFidelity_sq` is proven at
`FidelityUpperBound.lean:126`, with an in-file note dating it 2026-06-02 and explicitly
superseding the "needs trace-norm-dual / multi-week" assessment. The 6AE roadmap was not updated.
Recorded here so a future 6AE session does not re-derive a closed result; correcting that roadmap
is outside the Phase 6EA goal.

---

## 7. Execution notes

1. **Order.** `psdSqrt_diagonal` → (S1) → (S2); independently `shotPSD` defs → plane transfer →
   `poisson_thinning` → witness. The seam and the shot-noise algebra are independent within the
   file and can be interleaved freely.
2. **Wave 3 consumes Wave 1** — do not start (S2) before `affinity_le_binaryAffinity` and
   `poisson_avgError_floor` are merged to main.
3. **Root import in the same commit** (F8).
4. **Invariants.** Kernel-pure; `lean_verify` every headline; zero `sorry` / `native_decide` /
   `maxHeartbeats`; no new project-local `axiom` (none is needed).
5. **Do not attempt (S3).** `OptimalHypothesisRate` is `[Fintype d]`-bound and asymmetric
   (Neyman–Pearson), whereas Wave 1 bounds the symmetric Bayes/Le Cam average error. Settled-dead
   for this phase.

---

*Wave-3 freeze authored 2026-07-28 by the lead, concurrently with the Wave-1/Wave-2 slot builds.
Every substrate claim above (G1–G6) was verified by reading the cited source at main `d8d6473f`;
none is inherited from the prior freeze or from a worker report.*
