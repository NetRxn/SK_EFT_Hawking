/-
# `8 ∣ σ` and `16 ∣ σ` for even unimodular forms, with [Θ] discharged

`VanDerBlijReduction.eight_dvd_latticeSig_of_HM_of_Theta` reduces `8 ∣ latticeSig` for every even
unimodular form to two classical inputs: [HM] (indefinite ⟹ primitive isotropic vector) and [Θ]
(definite ⟹ `8 ∣ σ`). The [Θ] input is now a **theorem**
(`ThetaDefiniteDischarge.eight_dvd_latticeSig_of_definite`, via theta-modularity), so this file composes it
in: the even-unimodular `8 ∣ σ` and `16 ∣ σ` results now depend on **only [HM]** (and the topological
factor `2 ∣ σ/8` for the `16` version).

This isolates the *single* remaining mathematical gap to [HM] = the Hasse–Minkowski local–global statement
for even unimodular forms (under construction: `HilbertSymbolReal`, `PadicUnitResidue`, `HilbertSymbolPadic`).
Dependency graph (anti-circularity): `eight_dvd_rank` (theta-modularity, no Rokhlin/ABP input) → [Θ]; [HM]
(Hilbert-symbol Hasse–Minkowski, no Rokhlin/ABP input) → here. Kernel-pure, no new axioms.
-/

import Mathlib
import SKEFTHawking.VanDerBlijReduction
import SKEFTHawking.ThetaDefiniteDischarge

namespace SKEFTHawking

open Matrix QuadraticForm

/-- Abbreviation for the [HM] hypothesis: every *indefinite* even unimodular form has a primitive
isotropic vector. -/
abbrev HasIsotropicVectorHyp : Prop :=
  ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
    0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    ∃ v : Fin m → ℤ, IsPrimitiveVec v ∧ v ⬝ᵥ A *ᵥ v = 0

/-- **`8 ∣ σ` for even unimodular forms, with [Θ] discharged.** Given only the [HM] input, every even
unimodular integer form has `8 ∣ latticeSig`. The definite branch is supplied unconditionally by
theta-modularity (`eight_dvd_latticeSig_of_definite`). -/
theorem eight_dvd_latticeSig_of_HM (hHM : HasIsotropicVectorHyp)
    (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M) : 8 ∣ latticeSig M :=
  eight_dvd_latticeSig_of_HM_of_Theta hHM (fun A => eight_dvd_latticeSig_of_definite A) n M heu

/-- **`16 ∣ σ` for even unimodular forms, with [Θ] discharged.** Given the [HM] input and the topological
factor `2 ∣ σ/8`, every even unimodular form has `16 ∣ latticeSig`. -/
theorem sixteen_dvd_latticeSig_of_HM_of_topo {n : ℕ} (hHM : HasIsotropicVectorHyp)
    (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M) (htopo : (2 : ℤ) ∣ latticeSig M / 8) :
    (16 : ℤ) ∣ latticeSig M :=
  sixteen_dvd_latticeSig_of_HM_of_Theta_of_topo hHM (fun A => eight_dvd_latticeSig_of_definite A) M heu htopo

end SKEFTHawking
