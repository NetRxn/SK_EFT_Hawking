/-
Phase 5q.B: van der Blij `8 ∣ σ` reduced to its two classical inputs.

This is the capstone of the classification route to van der Blij's theorem. It assembles the entire
signature calculus and the hyperbolic-plane split-off recursion into a single reduction:

  **`eight_dvd_latticeSig_of_HM_of_Theta`** — for *every* even unimodular integer form `M`,
  `8 ∣ latticeSig M`, GIVEN only the two precisely-isolated classical inputs:
   • **[HM]**  an indefinite (`sigPos > 0 ∧ sigNeg > 0`) even unimodular form has a *primitive isotropic
     vector* (Hasse–Minkowski / Meyer), and
   • **[Θ]**  a definite (`sigPos = 0 ∨ sigNeg = 0`) even unimodular form has `8 ∣ σ` (theta-modularity:
     `8 ∣ rank`).

Everything between these two inputs and the conclusion is now machine-checked kernel-pure: the generator
signatures (`σ(E₈)=8`, `σ(H)=0`), Sylvester congruence-invariance, block additivity, the primitive-vector /
hyperbolic-pair construction, the split-off-H step `latticeSig M = latticeSigOf (residGram)`
(`SplitHyperbolic.latticeSig_split`), and the fact that the residual is again even unimodular of rank `n−2`
(`residGram_evenUnimodular`). The proof is strong induction on the rank: definite forms hit [Θ]; indefinite
forms peel a hyperbolic plane via [HM] and recurse.

This isolates the *only* remaining content of van der Blij to two named classical theorems (neither yet in
Mathlib): the local-global Hasse–Minkowski input and the theta-modularity input. The dependency graph is
clean and anti-circular: it routes `even-unimodular ⇒ 8∣σ` through [HM]+[Θ], never through ABP / Rokhlin.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom (the two classical inputs are explicit *hypotheses*, not axioms).
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.LatticeSignature
import SKEFTHawking.LatticeSigBlock
import SKEFTHawking.SplitHyperbolic
import SKEFTHawking.RokhlinClassification

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-- **van der Blij, reduced to [HM] + [Θ].** Given that every *indefinite* even unimodular form has a
primitive isotropic vector ([HM]) and every *definite* even unimodular form has `8 ∣ σ` ([Θ]), every even
unimodular integer form has `8 ∣ latticeSig`. Proof: strong induction on rank — definite forms use [Θ]
directly; indefinite forms produce a hyperbolic pair ([HM] + `exists_hyperbolic_pair`), split off a
hyperbolic plane (`latticeSig_split`: `latticeSig M = latticeSigOf (residGram)`) leaving an even unimodular
residual of rank `n−2` (`residGram_evenUnimodular`), and recurse. -/
theorem eight_dvd_latticeSig_of_HM_of_Theta
    (hHM : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      ∃ v : Fin m → ℤ, IsPrimitiveVec v ∧ v ⬝ᵥ A *ᵥ v = 0)
    (hΘ : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∨
       sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0) → 8 ∣ latticeSig A) :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ), IsEvenUnimodular M → 8 ∣ latticeSig M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro M hM
    by_cases hdef : sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∨
        sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0
    · exact hΘ M hM hdef
    · rw [not_or] at hdef
      obtain ⟨hsp, hsn⟩ := hdef
      obtain ⟨v, hvprim, hviso⟩ := hHM M hM (Nat.pos_of_ne_zero hsp) (Nat.pos_of_ne_zero hsn)
      obtain ⟨w', hv0, hvw, hw0⟩ :=
        exists_hyperbolic_pair M hM.1 hM.2.2 v hvprim hviso hM.2.1
      have hindep := hyperbolic_linearIndependent M hM.1 v w' hv0 hvw hw0
      have hic := hyperbolic_isCompl M v w' hM.1 hv0 hvw hw0
      have hfr := hypPerp_finrank M v w' hindep hic
      have hsum : sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
          + sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ≤ n := by
        have h := QuadraticForm.sigPos_add_sigNeg_add_radical
          (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
        have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by simp
        rw [hfin] at h
        omega
      have hn2 : 2 ≤ n := by
        have h1 := Nat.pos_of_ne_zero hsp
        have h2 := Nat.pos_of_ne_zero hsn
        omega
      have hsplit := latticeSig_split hn2 M hM.1 hM.2.1 v w' hv0 hvw hw0 hfr
      have hRGeu := residGram_evenUnimodular hn2 M hM v w' hv0 hvw hw0 hfr
      have hIH := IH (n - 2) (by omega) (residGram M v w' hfr) hRGeu
      rw [hsplit, latticeSigOf_fin]
      exact hIH

/-- **Rokhlin `16 ∣ σ` from geometric + classical inputs (no assumed algebraic hypothesis).** For an even
unimodular form `M` with the topological factor `2 ∣ σ/8`, given the two classical inputs [HM] and [Θ],
`16 ∣ latticeSig M`. This composes the van der Blij reduction (`eight_dvd_latticeSig_of_HM_of_Theta`) with
the Rokhlin bridge (`sixteen_dvd_latticeSig_of_eight_dvd_of_topo`): the `8 ∣ σ` is now *derived* from
even-unimodularity + [HM] + [Θ] rather than assumed, so the only inputs are the geometric ones
(even-unimodular [Wu], `2 ∣ σ/8` [Â-genus even]) and the two named classical theorems. -/
theorem sixteen_dvd_latticeSig_of_HM_of_Theta_of_topo {n : ℕ}
    (hHM : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      ∃ v : Fin m → ℤ, IsPrimitiveVec v ∧ v ⬝ᵥ A *ᵥ v = 0)
    (hΘ : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∨
       sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0) → 8 ∣ latticeSig A)
    (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M)
    (htopo : (2 : ℤ) ∣ latticeSig M / 8) :
    (16 : ℤ) ∣ latticeSig M :=
  sixteen_dvd_latticeSig_of_eight_dvd_of_topo M
    (eight_dvd_latticeSig_of_HM_of_Theta hHM hΘ n M heu) htopo

end SKEFTHawking
