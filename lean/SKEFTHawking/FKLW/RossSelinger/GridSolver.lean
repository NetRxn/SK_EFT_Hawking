/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Items H/I — the deterministic grid-synthesis compiler (sound core)

With the KMM Theorem-1 converse complete (`KMMCompleteness.kmm_completeness`,
`isCliffordTRealizable_assembleUnitary`) and `assembleUnitary` certified `SU(2)`
(`GridSynth`), the synthesis half of the Ross-Selinger pipeline is now end-to-end verified:

  (c) `diophantineSearch N b` — solve `t·t* = N` in `ℤ[ω]` (bounded, deterministic, sound)
  (d) `assembleUnitary u t k` — `M = [[u,−t*],[t,u*]]/√2^k`  (`GridSynth`)
  (e) `kmmReduce M`           — the exact Clifford+T word  (`KMM`)

This file composes them into a **runnable, verified deterministic grid-synthesis word**:

  * `gridFindT u k b`        — find the residual `t` completing `u` (step (c)+(d)).
  * `gridFindT_realizable`   — the assembled `M` is Clifford+T-realizable (via completeness).
  * `gridSynthWord u t k`    — the explicit gate list (`kmmReduce`).
  * `gridSynthWord_correct`  — `interp (gridSynthWord …) = assembleUnitary u t k` (exact).
  * `gridSynthWord_length`   — KMM Corollary-1 length bound `≤ N₃ + 4·sde(|M₀₀|²)`.

`#eval`-runnable: e.g. `gridFindT ⟨0,0,0,1⟩ 1 2` finds `t` with `|t|² = ⟨0,0,0,1⟩` (validated
against `scripts/grid_stub_validation.py`, which uses the same `ℤ[ω]` brute-force Diophantine).

## What is verified vs. what remains (deterministic branch ONLY — NO §4 factoring fast-path)

VERIFIED here: the (c)→(d)→(e) chain is SOUND — *when* `gridFindT` returns a `t`, the produced
word is exactly correct and length-bounded. This is the synthesis backbone the private `gridcert`
port relies on.

REMAINING (the analytic completeness of the FINDER, Ross-Selinger §5 Theorem 2): the guarantee
that for any target `U ∈ SU(2,ℂ)` and `ε`, a `(u, t)` with `‖assembleUnitary u t k − U‖ < ε`
EXISTS in the search region (the `epsilonRegion` ε-region geometry + `gridSolutions` enumeration
completeness + the ℤ[ω] prime-factorization Diophantine completeness). That convex-geometry /
number-theory core is the documented next undertaking; it upgrades the bounded `diophantineSearch`
to a complete `gridSolutions` and adds the `‖·‖ < ε` approximation guarantee (Item I's
`compile_length_bound ≤ 12·⌈log₂(1/ε)⌉ + 42`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMCompleteness

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- Bounded integer range `[-b, b]` as a `List ℤ`. -/
def intRangeB (b : ℕ) : List ℤ := (List.range (2 * b + 1)).map (fun i => (i : ℤ) - b)

/-- Bounded `ℤ[ω]` candidate list: all `⟨a,b,c,d⟩` with coordinates in `[-b, b]`. -/
def boundedZOmega (b : ℕ) : List ZOmega :=
  (intRangeB b).flatMap (fun a => (intRangeB b).flatMap (fun bb =>
    (intRangeB b).flatMap (fun c => (intRangeB b).map (fun d => (⟨a, bb, c, d⟩ : ZOmega)))))

/-- **Bounded `ℤ[ω]` Diophantine search** (deterministic, sound): find a `t` with `|t|² = N`
among coordinates in `[-b, b]`, or `none`. Computable (`List.find?` over a finite candidate
set). This is the bounded deterministic stand-in for the Ross-Selinger §5 prime-factorization
Diophantine; its *soundness* is unconditional, its *completeness* (a solution is found whenever
one exists with small coords) is the analytic input deferred with the ε-region geometry. -/
def diophantineSearch (N : ZOmega) (b : ℕ) : Option ZOmega :=
  (boundedZOmega b).find? (fun t => decide (ZOmega.normSq t = N))

/-- **Soundness of the Diophantine search**: a returned `t` genuinely solves `|t|² = N`. -/
theorem diophantineSearch_sound {N : ZOmega} {b : ℕ} {t : ZOmega}
    (h : diophantineSearch N b = some t) : ZOmega.normSq t = N := by
  rw [diophantineSearch] at h
  simpa using List.find?_some h

end ZOmega

namespace KMM

open ZOmega
open scoped Matrix

/-- **Grid step (c)+(d)**: given a numerator `u` and denominator exponent `k`, find the residual
`t` (coords in `[-b, b]`) completing `u` to a unit column `|u|² + |t|² = √2^{2k} = ⟨0,0,0,2^k⟩`,
i.e. to a realizable `SU(2)` matrix `assembleUnitary u t k`. -/
def gridFindT (u : ZOmega) (k b : ℕ) : Option ZOmega :=
  diophantineSearch ((⟨0, 0, 0, 2 ^ k⟩ : ZOmega) - ZOmega.normSq u) b

/-- **The found pair assembles to a realizable unitary**: when `gridFindT` succeeds,
`assembleUnitary u t k` is Clifford+T-realizable. Soundness of the bounded deterministic grid
step, resting on `isCliffordTRealizable_assembleUnitary` (= the KMM Theorem-1 converse). -/
theorem gridFindT_realizable {u : ZOmega} {k b : ℕ} {t : ZOmega}
    (h : gridFindT u k b = some t) : IsCliffordTRealizable (assembleUnitary u t k) :=
  isCliffordTRealizable_assembleUnitary u t k (by rw [ZOmega.diophantineSearch_sound h]; ring)

attribute [local instance] nonempty_kmmReduction

/-- **Deterministic grid-synthesis word**: synthesize the assembled unitary `M = [[u,−t*],[t,u*]]
/√2^k` into an explicit Clifford+T gate list via `kmmReduce`. -/
noncomputable def gridSynthWord (u t : ZOmega) (k : ℕ) : List CliffordTGate :=
  kmmReduce (assembleUnitary u t k)

/-- **Word correctness**: when the grid step finds `t`, the synthesized word interprets back to
the assembled unitary exactly. (`kmmReduce_correct` + `gridFindT_realizable`.) -/
theorem gridSynthWord_correct {u : ZOmega} {k b : ℕ} {t : ZOmega} (h : gridFindT u k b = some t) :
    CliffordTGate.interp (gridSynthWord u t k) = assembleUnitary u t k :=
  kmmReduce_correct _ (gridFindT_realizable h)

/-- **Word length bound** (KMM Corollary 1): `≤ N₃ + 4·sde(|M₀₀|²)`. -/
theorem gridSynthWord_length {u : ZOmega} {k b : ℕ} {t : ZOmega} (h : gridFindT u k b = some t) :
    (gridSynthWord u t k).length
      ≤ N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (assembleUnitary u t k 0 0)) :=
  kmmReduce_length_bound _ (gridFindT_realizable h)

/-- **Deterministic grid-synthesis compiler** (numerator form): given the solved column numerator
`u`, denominator exponent `k`, and search bound `b`, produce a Clifford+T word for the assembled
unitary, or `none` if no residual `t` is found within the bound. The complex-target → `(u, k)`
rounding (the FINDER front-end) is the RS §5 ε-region step still gated on the grid-completeness
DR; this is the verified synthesis back-end it feeds. -/
noncomputable def gridCompile (u : ZOmega) (k b : ℕ) : Option (List CliffordTGate) :=
  (gridFindT u k b).map (fun t => gridSynthWord u t k)

/-- **Compile correctness**: when the grid step finds `t`, `gridCompile` returns the synthesized
word and it interprets back to the assembled unitary `[[u,−t*],[t,u*]]/√2^k` exactly. -/
theorem gridCompile_correct {u : ZOmega} {k b : ℕ} {t : ZOmega} (h : gridFindT u k b = some t) :
    gridCompile u k b = some (gridSynthWord u t k) ∧
      CliffordTGate.interp (gridSynthWord u t k) = assembleUnitary u t k :=
  ⟨by rw [gridCompile, h]; rfl, gridSynthWord_correct h⟩

end KMM

end SKEFTHawking.RossSelinger
