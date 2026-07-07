/-
# Phase 5q.H (E1 CSC-PD tower) — the empty-open vanishings `Hᵏ_c(∅;ℤ) = 0`, `Hₙ(sub ∅;ℤ) = 0` (integral)

Integral mirror of `SingularPDWindow.cscOpen_empty_eq_zero` / `homology_sub_empty_eq_zero` — the trivial
`W = ∅` branch that seeds the finite-union induction (`pdWindowPInt_empty`). Over ℤ the relative cochains
of the pair `(X, X)` are subsingleton (`relCochainsInt (∅ᶜ) n` — a cochain pairing to `0` with every chain,
since `subspaceChainsInt (∅ᶜ) = ⊤`, is `0`), so `Hⁿ(X, X; ℤ) = 0` directly — no UCT needed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCVanishAboveInt
import SKEFTHawking.SingularGoodCompactEuclideanInt
import SKEFTHawking.SingularRelativeEmptyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCVanishAboveInt
open SKEFTHawking.SingularGoodCompactEuclideanInt (subspaceChainsInt_compl_empty_eq_top)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularCSCEmptyInt

variable {X : TopCat}

/-- The relative cochains of the pair `(X, X)` are subsingleton (a cochain pairing to `0` with every
chain — `subspaceChainsInt (∅ᶜ) = ⊤` — is `0`). -/
theorem relCochainsInt_compl_empty_subsingletonInt (n : ℕ) :
    Subsingleton (relCochainsInt (∅ᶜ : Set ↑X) n) := by
  refine ⟨fun a b => Subtype.ext (funext fun σ => ?_)⟩
  have hmem : ∀ c : SingularChainInt X n, c ∈ subspaceChainsInt (∅ᶜ : Set ↑X) n := by
    rw [subspaceChainsInt_compl_empty_eq_top]; exact fun _ => Submodule.mem_top
  have ha : kronecker (a : SingularCochainInt X n) (Finsupp.single σ 1) = 0 := a.2 _ (hmem _)
  have hb : kronecker (b : SingularCochainInt X n) (Finsupp.single σ 1) = 0 := b.2 _ (hmem _)
  rw [kronecker_single, one_mul] at ha hb
  rw [ha, hb]

/-- **`Hⁿ(X, X; ℤ) = Hⁿ(X | ∅; ℤ) = 0`** (integral). -/
theorem relCohomology_compl_empty_eq_zeroInt (n : ℕ)
    (x : RelativeCohomologyInt (∅ᶜ : Set ↑X) n) : x = 0 := by
  haveI := relCochainsInt_compl_empty_subsingletonInt (X := X) n
  haveI : Subsingleton (LinearMap.ker (relCoboundaryIntₗ (∅ᶜ : Set ↑X) n)) := inferInstance
  haveI : Subsingleton (RelativeCohomologyInt (∅ᶜ : Set ↑X) n) :=
    inferInstanceAs (Subsingleton (_ ⧸ _))
  exact Subsingleton.elim x 0

/-- **`Hᵏ⁺¹_c(∅; ℤ) = 0`** (integral): every stage of the empty open's directed system is
`Hᵏ⁺¹(X, X; ℤ) = 0`. -/
theorem cscOpen_empty_eq_zeroInt {N : ℕ}
    (α : CompactlySupportedCohomologyOpenInt (∅ : Set ↑X) (N + 1)) : α = 0 := by
  refine cscOpen_eq_zero_of_cofinal_vanishInt (fun K => ⟨K, le_refl K, fun x => ?_⟩) α
  have hKe : (↑K.1 : Set ↑X) = ∅ := Set.subset_empty_iff.mp K.2
  have hvan : ∀ y : RelativeCohomologyInt ((↑K.1 : Set ↑X)ᶜ) (N + 1), y = 0 := by
    rw [hKe]
    exact relCohomology_compl_empty_eq_zeroInt (N + 1)
  exact hvan x

/-- **`Hₙ(sub ∅; ℤ) = 0`** (integral): the empty subspace has subsingleton chain modules. -/
theorem homology_sub_empty_eq_zeroInt (n : ℕ)
    (b : Homology (sub (∅ : Set ↑X)) n) : b = 0 := by
  haveI := SKEFTHawking.SingularRelativeEmptyInt.singularChainInt_empty_subsingleton (X := X) n
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show z = 0 from Subsingleton.elim z 0]
  exact Submodule.Quotient.mk_zero _

end SKEFTHawking.SingularCSCEmptyInt
