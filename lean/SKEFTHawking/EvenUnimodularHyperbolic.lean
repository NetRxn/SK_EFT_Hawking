/-
# Phase 5q.H (E1 lattice — the KT injective-direction core): the signature-0 hyperbolic normal form

An even unimodular integer form `M` of signature `0` is congruent to the `n`-fold hyperbolic form `n·H`.
This is the **lattice core of the injective direction of `Ω₄^{Spin}≅ℤ`** — the re-anchored 5q.H keystone (KT
geometric route, `Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md`): a `σ=0` spin
4-manifold's intersection form is `n·H`, hence (manifold realization — the carried surgery step) it is
`n(S²×S²)`, hence spin-null-bordant.

**UNCONDITIONAL** — the `[HM]` Hasse–Minkowski input is now a THEOREM
(`RokhlinHMRankFour.hasIsotropicVector`), so the split-off-H induction (`SplitHyperbolic`,
`VanDerBlijReduction`) closes with no carried hypothesis. Mirrors the van der Blij rank-induction but tracks
the hyperbolic normal form (`VanDerBlij` produces only the `8∣σ` divisibility).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.SplitHyperbolic
import SKEFTHawking.RokhlinHMRankFour
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.LatticeSigBlock
import SKEFTHawking.BlockSignature

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-- **A nonzero-rank even unimodular form of signature `0` is indefinite.** Since `M` is unimodular it is
nondegenerate (`radical = ⊥`), so `sigPos + sigNeg = rank = n`; and `latticeSig M = sigPos − sigNeg = 0`
forces `sigPos = sigNeg`, hence both are `n/2 > 0`. This is the enabling step of the `σ=0 ⟹ n·H` induction:
it certifies the `[HM]` hypothesis (`sigPos > 0 ∧ sigNeg > 0`) so a primitive isotropic vector exists and a
hyperbolic plane can be split off. -/
theorem even_unimodular_sig_zero_indefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M) (hsig : latticeSig M = 0) (hn : 0 < n) :
    0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ∧
    0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  have hsymm : Mᵀ = M := heu.1
  have hsymmR : (M.map (Int.cast : ℤ → ℝ))ᵀ = M.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, hsymm]
  have hdet : M.det ≠ 0 := by rcases heu.2.1 with h | h <;> rw [h] <;> norm_num
  have hrad : (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ :=
    nondeg_radical_eq_bot (M.map (Int.cast : ℤ → ℝ)) hsymmR (cast_nondegenerate M hdet)
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [hrad] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  unfold latticeSig at hsig
  -- `latticeSig` is stated in the current `toQuadraticForm'` API while this statement uses the
  -- deprecated-alias `toQuadraticMap'`; they are definitionally equal, so re-`show` the goal and
  -- re-ascribe `hsum` in the new name to give `omega` a single atom per signature component.
  show 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticForm' ∧
      0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticForm'
  have hsum' : sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticForm' +
      sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticForm' = n := hsum
  omega

/-- **The split-off-H inductive step for `σ=0` (unconditional).** A `σ=0` even unimodular form of rank
`≥ 2` is indefinite (`even_unimodular_sig_zero_indefinite`), so `[HM]` (`hasIsotropicVector`, now a theorem)
supplies a primitive isotropic vector; extending to a hyperbolic pair and splitting off `H`
(`SplitHyperbolic`) leaves an even unimodular form `M'` of rank `n − 2` that is again `σ=0`
(`latticeSig_split` preserves the signature, which is `0`). This is the lattice shadow of one surgery step
peeling an `S²×S²` off a `σ=0` spin 4-manifold — the engine of the `σ=0 ⟹ n·H` normal form. -/
theorem even_unimodular_sig_zero_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M) (hsig : latticeSig M = 0) (hn2 : 2 ≤ n) :
    ∃ M' : Matrix (Fin (n - 2)) (Fin (n - 2)) ℤ, IsEvenUnimodular M' ∧ latticeSig M' = 0 := by
  obtain ⟨hsp, hsn⟩ := even_unimodular_sig_zero_indefinite M heu hsig (by omega)
  obtain ⟨v, hvprim, hviso⟩ := hasIsotropicVector M heu hsp hsn
  obtain ⟨w', hv0, hvw, hw0⟩ := exists_hyperbolic_pair M heu.1 heu.2.2 v hvprim hviso heu.2.1
  have hindep := hyperbolic_linearIndependent M heu.1 v w' hv0 hvw hw0
  have hic := hyperbolic_isCompl M v w' heu.1 hv0 hvw hw0
  have hfr := hypPerp_finrank M v w' hindep hic
  refine ⟨residGram M v w' hfr, residGram_evenUnimodular hn2 M heu v w' hv0 hvw hw0 hfr, ?_⟩
  have hsplit := latticeSig_split hn2 M heu.1 heu.2.1 v w' hv0 hvw hw0 hfr
  rw [latticeSigOf_fin] at hsplit
  omega

end SKEFTHawking
