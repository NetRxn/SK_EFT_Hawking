/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the KMM-derived Clifford+T base finder (ρ_CliffT picture)

Item I shipped the runnable Ross-Selinger `compile : SU(2) → (k,b) → Option (List CliffordTGate)`
and its SOUNDNESS `compile_correct` in the `toComplexMat` picture (`‖toComplexMat (interp w) − U‖`).
The Solovay-Kitaev headline, however, lives in the `ρ_CliffT` / `FreeGroup (Fin 2)` picture
(`‖(ρ_CliffT w : ℂ-mat) − U‖`, `BaseFinder_approximates_within`). This file lifts the Item-I
synthesis into that picture via the phase bridge (`RossSelinger/PhaseBridge.lean`), composing the
shipped UNCONDITIONAL KMM exact synthesis (`nonempty_kmmReduction` → `kmmReduce`) with the bridge.

**The U(2)↔SU(2) phase obstruction, resolved.** KMM gate words are `U(2)` (det a 16th root of
unity); `ρ_CliffT` lands in `SU(2)`. The bridge `ρ_CliffT_freeword_eq` is clean only for `det`-1
words, where `phaseProd gs = ±1`. Ross-Selinger's `assembleUnitary` IS `det`-1 (`det_assembleUnitary`),
so the bridge applies — but it leaves a residual `±1` global sign. `signCorrect` below kills it:
appending `H·H` (with `ρ_CliffT (H·H) = H_SU² = −I`) flips the `−1` case, so the corrected word's
`ρ_CliffT` image equals `toComplexMat (interp gs)` on the nose for every `det`-1 word.

**What is UNCONDITIONAL here** (uses only `nonempty_kmmReduction` + the phase bridge, no completeness):
  - `coe_ρ_CliffT_signCorrect` — for any `det`-1 word, the sign-corrected `ρ_CliffT` image equals
    `toComplexMat (interp gs)` exactly (the ±1 sign killed).
  - `signCorrect_kmmReduce_resynth` — KMM re-synthesizes any `det`-1 realizable `M` to a word whose
    sign-corrected `ρ_CliffT` image is `toComplexMat M`, at the honest KMM length `N₃ + 4·sde(|M₀₀|²)`.
  - `cliffordTBaseFinder_kmm_approx` — the `ρ_CliffT`-picture counterpart of `compile_correct`: when
    the grid finder returns `t` and the cleared columns approximate `U`'s first column within `ε`,
    the KMM word's sign-corrected `ρ_CliffT` image is within `2ε` of `U` in `linftyOpNorm`.

**Scope (honest).** The fully UNCONDITIONAL 3-conjunct Clifford+T Solovay-Kitaev headline already
ships via the lightweight density base finder
(`solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_constructive_unconditional`,
`RossSelingerLightweight.lean`). A KMM-*algorithmic* base finder whose *unconditional* approximation
holds for every `U` requires the grid-completeness `t`-coupling (the documented, parked optional
follow-on — the same piece Item I's full unconditional compile needs; deterministic-branch soundness
is what ships). This file delivers that KMM finder's SOUNDNESS in the headline's `ρ_CliffT` picture
(the genuine Item-G content), composing the named substrate end-to-end.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.PhaseBridge
import SKEFTHawking.FKLW.RossSelinger.GridSolver
import SKEFTHawking.FKLW.RossSelinger.Compile

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open CliffordTGate
open scoped Matrix
open SKEFTHawking.FKLW.GenericSU2

attribute [local instance] KMM.nonempty_kmmReduction Matrix.linftyOpNormedAddCommGroup

/-- `H_SU_mat² = −1` (the `det`-1 Hadamard squares to `−I`): `(i/√2)² · [[1,1],[1,−1]]² =
(−1/2)·(2·I) = −I`. The sign corrector `ρ_CliffT (fgH·fgH)` uses this. -/
theorem H_SU_mat_sq : H_SU_mat * H_SU_mat = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsqrt : (Complex.I / (↑(Real.sqrt 2) : ℂ)) * (Complex.I / (↑(Real.sqrt 2) : ℂ)) = -(1/2) := by
    rw [div_mul_div_comm, Complex.I_mul_I,
      show ((↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2)) = 2 from by
        rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]; norm_num]
    ring
  rw [H_SU_mat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqrt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.neg_apply, Matrix.one_apply, smul_eq_mul,
      Fin.isValue] <;>
    norm_num

/-- `ρ_CliffT (fgH · fgH)` coerces to `−I` (the sign corrector). -/
theorem coe_ρ_CliffT_fgH_sq :
    ((ρ_CliffT (fgH * fgH) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [map_mul, Submonoid.coe_mul, fgH, ρ_CliffT_of_0]
  show H_SU_mat * H_SU_mat = _
  exact H_SU_mat_sq

/-- **The ±1-sign-corrected `FreeGroup` word of a KMM gate list.** `freeword gs` if the global
phase `phaseProd gs = 1`, else `freeword gs · (fgH · fgH)` (which multiplies the `ρ_CliffT` image by
`−I`, flipping the `−1` case). Noncomputable (the `phaseProd = 1` test is over `ℂ`). -/
noncomputable def signCorrect (gs : List CliffordTGate) : FreeGroup (Fin 2) :=
  open Classical in
  if phaseProd gs = 1 then freeword gs else freeword gs * (fgH * fgH)

/-- **Keystone (UNCONDITIONAL for `det`-1 words).** The sign-corrected word's `ρ_CliffT` image
equals `toComplexMat (interp gs)` exactly — the residual `±1` global phase of the bridge is killed
by the `H·H` correction. Uses `phaseProd_eq_one_or_neg_one` + `ρ_CliffT_freeword_eq` +
`coe_ρ_CliffT_fgH_sq`; no completeness needed. -/
theorem coe_ρ_CliffT_signCorrect (gs : List CliffordTGate) (hdet : (interp gs).det = 1) :
    ((ρ_CliffT (signCorrect gs) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = toComplexMat (interp gs) := by
  have hbridge := ρ_CliffT_freeword_eq gs hdet
  rcases phaseProd_eq_one_or_neg_one gs hdet with h1 | hn1
  · rw [signCorrect, if_pos h1, hbridge, h1, one_smul]
  · have hne : phaseProd gs ≠ 1 := by rw [hn1]; norm_num
    rw [signCorrect, if_neg hne, map_mul, Submonoid.coe_mul, hbridge, coe_ρ_CliffT_fgH_sq, hn1,
      neg_one_smul, neg_mul_neg, Matrix.mul_one]

/-- **KMM re-synthesis at honest length (UNCONDITIONAL).** Any `det`-1 Clifford+T-realizable `M` is
re-synthesized by `kmmReduce` into a word whose sign-corrected `ρ_CliffT` image is `toComplexMat M`,
with the honest KMM Corollary-1 length `≤ N₃ + 4·sde(|M₀₀|²)`. This composes the shipped
UNCONDITIONAL exact synthesis (`kmmReduce_correct`/`kmmReduce_length_bound`) with the keystone. -/
theorem signCorrect_kmmReduce_resynth (M : Mat2) (hreal : KMM.IsCliffordTRealizable M)
    (hdet : M.det = 1) :
    ((ρ_CliffT (signCorrect (KMM.kmmReduce M)) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = toComplexMat M ∧
    (KMM.kmmReduce M).length
      ≤ KMM.N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (M 0 0)) := by
  have hc : CliffordTGate.interp (KMM.kmmReduce M) = M := KMM.kmmReduce_correct M hreal
  refine ⟨?_, KMM.kmmReduce_length_bound M hreal⟩
  rw [coe_ρ_CliffT_signCorrect (KMM.kmmReduce M) (by rw [hc]; exact hdet), hc]

/-- **The KMM-derived Clifford+T base finder** (`ρ_CliffT` picture): round `U`'s first column to
`(compileColumn U k)`, KMM-synthesize the assembled `det`-1 unitary, and sign-correct into a
`FreeGroup (Fin 2)` word. `none` when no residual `t` is found within the bound `b`. -/
noncomputable def cliffordTBaseFinder_kmm (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ) :
    Option (FreeGroup (Fin 2)) :=
  (compile U k b).map signCorrect

/-- **`cliffordTBaseFinder_kmm` SOUNDNESS in the headline `ρ_CliffT` picture** — the counterpart of
`compile_correct`. When the grid finder returns a residual `t` and the cleared columns approximate
`U`'s first column entries `U₀₀` (via `compileColumn U k`) and `U₁₀` (via `t`) within `ε`, the
finder returns a `FreeGroup (Fin 2)` word whose `ρ_CliffT` image is within `2ε` of `U` in
`linftyOpNorm`. Composes `gridCompile_correct` + `det_assembleUnitary` + the keystone
`coe_ρ_CliffT_signCorrect` + `approx_assembleUnitary`. -/
theorem cliffordTBaseFinder_kmm_approx (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ZOmega)
    (ht : KMM.gridFindT (compileColumn U k) k b = some t)
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (compileColumn U k) k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    ∃ w, cliffordTBaseFinder_kmm U k b = some w ∧
      ‖((ρ_CliffT w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε := by
  -- the det-1 constraint from the bounded Diophantine search
  have hconstr : ZOmega.normSq (compileColumn U k) + ZOmega.normSq t
      = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) := by
    have := ZOmega.diophantineSearch_sound ht; rw [this]; ring
  set u := compileColumn U k with hu
  have hword := (KMM.gridCompile_correct ht)
  -- the synthesized word and its assembled matrix
  refine ⟨signCorrect (KMM.gridSynthWord u t k), ?_, ?_⟩
  · rw [cliffordTBaseFinder_kmm, compile, hword.1, Option.map_some]
  · have hinterp : CliffordTGate.interp (KMM.gridSynthWord u t k) = KMM.assembleUnitary u t k :=
      hword.2
    have hdet : (CliffordTGate.interp (KMM.gridSynthWord u t k)).det = 1 := by
      rw [hinterp]; exact KMM.det_assembleUnitary u t k hconstr
    rw [coe_ρ_CliffT_signCorrect (KMM.gridSynthWord u t k) hdet, hinterp]
    exact approx_assembleUnitary u t k U hε h00 h10

/-- **The KMM-derived Clifford+T base-finder headline** (`ρ_CliffT` picture): error + honest KMM
length. Under the same grid-finder-success + first-column-approximation hypotheses as
`compile_correct`, the KMM-derived word `w = cliffordTBaseFinder_kmm U k b` satisfies BOTH
Solovay-Kitaev headline conjuncts in the strict `linftyOpNorm` of the SK headline:

  - **Error**: `‖(ρ_CliffT w : ℂ-mat) − U‖ ≤ 2ε` (the `ρ_CliffT`-picture lift of `compile_correct`).
  - **Honest KMM length**: the underlying KMM gate word has length `≤ N₃ + 4·sde(|M₀₀|²)` — the KMM
    Corollary-1 bound (NOT the unsound `L ≤ 90`, which is incompatible with the proven SK `ε₀`).

This re-derives the headline on the KMM-algorithmic base finder. Its UNCONDITIONALITY (over all `U`)
is gated on the grid-completeness `t`-coupling (the documented parked optional follow-on); the fully
unconditional 3-conjunct headline ships via the lightweight density finder
(`solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_constructive_unconditional`). -/
theorem cliffordTBaseFinder_kmm_headline (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ZOmega)
    (ht : KMM.gridFindT (compileColumn U k) k b = some t)
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (compileColumn U k) k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    (∃ w, cliffordTBaseFinder_kmm U k b = some w ∧
        ‖((ρ_CliffT w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε) ∧
    (KMM.gridSynthWord (compileColumn U k) t k).length
      ≤ KMM.N₃ + 4 * ZOmegaSqrt2.denExp
          (ZOmegaSqrt2.normSq (KMM.assembleUnitary (compileColumn U k) t k 0 0)) :=
  ⟨cliffordTBaseFinder_kmm_approx U k b hε t ht h00 h10, KMM.gridSynthWord_length ht⟩

end SKEFTHawking.RossSelinger
