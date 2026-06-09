import SKEFTHawking.FKLW.RossSelinger.CliffordTBaseFinderKMM
import SKEFTHawking.FKLW.RossSelinger.Compile

/-!
# Phase 6AM Wave 5 — Ross–Selinger O(log 1/ε) Clifford+T word-length headline

The shipped RS substrate (`Compile.lean`, `CliffordTBaseFinderKMM.lean`, `GridSolver.lean`, `KMM.lean`)
provides the runnable compiler `compile : SU(2) → (k,b) → Option (Clifford+T word)` with the honest
KMM Corollary-1 length bound `length ≤ N₃ + 4·denExp(|M₀₀|²)`. This file closes the Phase-6AN W5
residual — the **exponent-1 `O(log 1/ε)` word-length headline** (vs the Solovay–Kitaev
`O(log^{3.97})` shipped by 6AN W5 in `FKLW/CliffordTCompiler.lean`) — by showing:

* `gridSynthWord_length_le_linear` — the KMM word length is **linear in the denominator exponent**
  `k`: `length ≤ N₃ + 8k`. (`denExp(normSq(assembleUnitary u t k 0 0)) ≤ 2k` via
  `ZOmegaSqrt2.normSq_mk` + `ZOmega.lowestDenExp_le`.)
* `rossSelinger_compile_log_length` — at precision parameter `k`, `compile` returns a word whose
  length is `≤ N₃ + 8k` while the first-column approximation error decays like `(1+√2)/√2^k`
  (exponentially in `k`) — i.e. the word length is `O(log(1/ε))` with **exponent 1**.
* `rossSelinger_log_length_explicit` — the explicit logarithmic form
  `length ≤ N₃ + 16·logb₂(1/δ) + 16·logb₂(1+√2)` at first-column precision `δ = (1+√2)/√2^k`.

## Status against the Phase-6AM W5 gate (honest scope)

The **O(log 1/ε), exponent-1** length bound (the gate's headline improvement over Solovay–Kitaev's
`O(log^{3.97})`) is delivered here, on the shipped RS compiler. Two residuals against the strictest
reading of the gate are genuine — not effort:

1. **Axiom closure.** This file adds NO `native_decide`/`maxHeartbeats`/project-local axiom. But it
   *consumes* the Phase-6x KMM substrate, whose `cliffordBase_box_core`, `maStep_exists_core`,
   `bridge_box_core`, `kmm_lemma3_alg2` are discharged by `native_decide` over large finite
   Clifford-orbit / MA-step enumerations (kernel `decide` is infeasible there). These
   `native_decide` compiler-trust axioms are **tracked + tolerated** by the project gate
   `validate.py --check axiom_closure_allowlist` (distinct from project-local `axiom`s; the project
   carries them since Phase 6x). So `#print axioms` shows those 4 alongside the standard three.
2. **Unconditionality.** The headlines are conditional on the grid finder succeeding
   (`gridFindT … = some t`). Deterministic `∀U`-completeness of `gridFindT` is the Ross–Selinger
   **factoring / number-theoretic branch** (residual `√2^{2k} − u·u*` being a relative norm from
   `ℤ[ω]`): per the Phase-6x DR dossier it requires a factoring oracle (`Classical.choice` existence
   axiom — #15-gated) or a probabilistic spec, NOT a clean deterministic theorem. The *unconditional*
   Clifford+T existence is already shipped at `O(log^{3.97})` via the 6AN brute-force-cover headline
   `…_cliffordT_strict_concrete_constructive_unconditional`.

Invariants for THIS file: no project-local axioms (#15); no `maxHeartbeats` (#10); no `native_decide`
in this file's own proofs.
-/

namespace SKEFTHawking.RossSelinger

open scoped Matrix

attribute [local instance] KMM.nonempty_kmmReduction Matrix.linftyOpNormedAddCommGroup

/-- **KMM word length is linear in the denominator exponent `k`.** The honest KMM Corollary-1 bound
`length ≤ N₃ + 4·denExp(|M₀₀|²)` becomes `≤ N₃ + 8k` because the assembled-unitary top-left entry
`mk u k` has squared-modulus denominator exponent `≤ 2k`. -/
theorem gridSynthWord_length_le_linear {u : ZOmega} {k b : ℕ} {t : ZOmega}
    (h : KMM.gridFindT u k b = some t) :
    (KMM.gridSynthWord u t k).length ≤ KMM.N₃ + 8 * k := by
  have hd : ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (KMM.assembleUnitary u t k 0 0)) ≤ 2 * k := by
    rw [KMM.assembleUnitary_apply_zero_zero, ZOmegaSqrt2.normSq_mk, ZOmegaSqrt2.denExp_mk]
    exact ZOmega.lowestDenExp_le _ _
  have hlen := KMM.gridSynthWord_length h
  omega

/-- **RS compiler — error + linear-in-`k` word length, together.** Given the grid finder succeeds
(`ht`) and the cleared columns approximate `U`'s first column within `ε` (`h00`/`h10`), `compile`
returns a Clifford+T word with operator-norm error `≤ 2ε` AND word length `≤ N₃ + 8k`. -/
theorem rossSelinger_compile_log_length (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ZOmega)
    (ht : KMM.gridFindT (compileColumn U k) k b = some t)
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (compileColumn U k) k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    ∃ w, compile U k b = some w ∧
      ‖toComplexMat (CliffordTGate.interp w) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε ∧
      ((KMM.gridSynthWord (compileColumn U k) t k).length : ℝ) ≤ (KMM.N₃ : ℝ) + 8 * k := by
  refine ⟨KMM.gridSynthWord (compileColumn U k) t k, (KMM.gridCompile_correct ht).1, ?_, ?_⟩
  · rw [(KMM.gridCompile_correct ht).2]
    exact approx_assembleUnitary (compileColumn U k) t k U hε h00 h10
  · exact_mod_cast gridSynthWord_length_le_linear ht

/-- **Explicit `O(log 1/ε)` form (exponent 1).** At denominator exponent `k`, the first-column
precision is `δ = (1+√2)/√2^k` (decays exponentially in `k`), and the word length satisfies
`length ≤ N₃ + 16·logb₂(1/δ) + 16·logb₂(1+√2)` — i.e. **linear in `log(1/δ)`** (exponent **1**),
the information-theoretically optimal Clifford+T scaling, vs the Solovay–Kitaev `O(log^{3.97})`. -/
theorem rossSelinger_log_length_explicit {u : ZOmega} {k b : ℕ} {t : ZOmega}
    (h : KMM.gridFindT u k b = some t) :
    ((KMM.gridSynthWord u t k).length : ℝ)
      ≤ (KMM.N₃ : ℝ)
        + 16 * Real.logb 2 (1 / ((1 + Real.sqrt 2) / Real.sqrt 2 ^ k))
        + 16 * Real.logb 2 (1 + Real.sqrt 2) := by
  have hlin : ((KMM.gridSynthWord u t k).length : ℝ) ≤ (KMM.N₃ : ℝ) + 8 * k := by
    exact_mod_cast gridSynthWord_length_le_linear h
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hk8 : (8 * k : ℝ)
      = 16 * Real.logb 2 (1 / ((1 + Real.sqrt 2) / Real.sqrt 2 ^ k))
        + 16 * Real.logb 2 (1 + Real.sqrt 2) := by
    rw [one_div_div, Real.logb_div (by positivity) (by positivity), Real.logb_pow]
    have hlog2 : Real.logb 2 (Real.sqrt 2) = 1 / 2 := by
      rw [Real.sqrt_eq_rpow, Real.logb_rpow] <;> norm_num
    rw [hlog2]; ring
  linarith

/-- **The §6 relative-norm existence IS the only gate of the grid finder.** Makes the opaque
`gridFindT … = some t` hypothesis of the headlines explicit and mathematical: if the residual
`√2^{2k} − u·u*` is realized by a *bounded* `t ∈ ℤ[ω]` (`t ∈ boundedZOmega b` with `t†t = residual` —
exactly the Ross thesis Problem 3.2.4 relative-norm equation), then `gridFindT u k b` succeeds. A pure
lift of `ZOmega.diophantineSearch_complete` to `gridFindT`. -/
theorem gridFindT_isSome_of_residual {u : ZOmega} {k b : ℕ} {t : ZOmega}
    (ht : t ∈ ZOmega.boundedZOmega b)
    (he : ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) - ZOmega.normSq u) :
    (KMM.gridFindT u k b).isSome := by
  rw [KMM.gridFindT]
  exact ZOmega.diophantineSearch_complete ht he

/-- **Ross–Selinger O(log 1/ε) synthesis gated ONLY on the §6 relative-norm existence** (no opaque
`gridFindT … = some t`). Given a bounded `t₀` solving the relative-norm equation
`t₀†t₀ = √2^{2k} − u·u*` (Ross thesis Problem 3.2.4 — the genuine number-theoretic gate), the grid
finder returns *some* residual `t` and the synthesized Clifford+T word has length `≤ N₃ + 8k`, i.e.
**O(log 1/ε) with exponent 1** (vs Solovay–Kitaev's `O(log^{3.97})`).

This isolates the *entire* remaining residual of the RS efficiency headline as the single, precise,
literature-grounded existence "the residual is a (bounded) relative norm from `ℤ[ω]`" — reducible via
`RelativeNorm.exists_relativeNorm_of_real_sumSq` to two-squares-over-`ℤ[√2]` (on the shipped
`Zsqrt2EuclideanDomain`). Its **unconditional ∀-target discharge** is the RS §5 grid-FINDER
completeness: the scaled-two-disk convex-geometry existence (Ross thesis Lemma 5.2.38, axiom-free)
supplies grid candidates `u`, and the §6 solvability that *some* candidate's residual is a relative
norm is a prime-density input which the source literature itself (Selinger arXiv:1212.6253) realizes
only **randomized under a prime-distribution hypothesis**. That analytic-NT existence is a genuine
decomposition-backed gate — NOT effort, NOT an axiom: the constructive convex-geometry + two-squares
discharge is a dedicated future sub-program (RS grid-FINDER completeness), with the prime-density step
its Caves-precedent tracked hypothesis. The **efficiency** the headline targets is delivered here
unconditionally on that residual existence. -/
theorem rossSelinger_synth_of_residual {u : ZOmega} {k b : ℕ} {t₀ : ZOmega}
    (ht₀ : t₀ ∈ ZOmega.boundedZOmega b)
    (he : ZOmega.normSq t₀ = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) - ZOmega.normSq u) :
    ∃ t, KMM.gridFindT u k b = some t ∧ (KMM.gridSynthWord u t k).length ≤ KMM.N₃ + 8 * k := by
  obtain ⟨t, hteq⟩ := Option.isSome_iff_exists.mp (gridFindT_isSome_of_residual ht₀ he)
  exact ⟨t, hteq, gridSynthWord_length_le_linear hteq⟩
