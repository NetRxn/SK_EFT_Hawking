/-
# Phase 5q.H (E1 integral topology) — coordinate quotients of the free chains are PROJECTIVE

A **general** enabler for the field-UC-free relative-cohomology Mayer–Vietoris over ℤ: any quotient of
the free `SingularChainInt X n = (simplices →₀ ℤ)` by a **`Finsupp.supported`** (coordinate) submodule is
projective — the submodule is a direct summand via the `Finsupp.restrictDom` retraction. This covers
both `RelativeChainInt S n` (`subspaceChainsInt S = supported(range simplexIncl)`) and the MV third-term
`QChainInt U V n = C / (C(U)+C(V))` (`mvUnionChainsInt = supported(range simplexInclU ∪ range
simplexInclV)`), whose projectivity splits the chain MV SES so that `Hom(−, ℤ)` dualizes it exactly.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVInt

open Opposite
open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularChainQuotientProjectiveInt

variable {R : Type*} [Ring R]

/-- **A quotient of a projective module by a retraction-split submodule is projective.** If `N ≤ M`
(`M` projective) admits a linear retraction `ρ : M → N` (`ρ ∘ incl = id`), then `M ⧸ N` is projective:
`i := id − incl∘ρ` kills `N`, descending to a section of `mkQ`. Generalizes the `Module.Projective.of_split`
argument used for `RelativeChainInt`. -/
theorem projective_quotient_of_retraction {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Projective R M] (N : Submodule R M) (ρ : M →ₗ[R] N)
    (hρ : ∀ x : N, ρ (x : M) = x) : Module.Projective R (M ⧸ N) := by
  have hle : N ≤ LinearMap.ker (LinearMap.id - N.subtype ∘ₗ ρ) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [show ρ x = (⟨x, hx⟩ : N) from hρ ⟨x, hx⟩]
    simp
  refine Module.Projective.of_split (Submodule.liftQ N (LinearMap.id - N.subtype ∘ₗ ρ) hle)
    N.mkQ ?_
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show (Submodule.Quotient.mk (x - N.subtype (ρ x)) : M ⧸ N) = Submodule.Quotient.mk x
  rw [Submodule.Quotient.mk_sub,
    show (Submodule.Quotient.mk (N.subtype (ρ x)) : M ⧸ N) = 0 from
      (Submodule.Quotient.mk_eq_zero _).2 (ρ x).2, sub_zero]

variable {X : TopCat}

/-- A `Finsupp.supported` submodule of the free `SingularChainInt X n` is retraction-split (via
`Finsupp.restrictDom`); hence the quotient is projective. -/
theorem supported_quotient_projective (n : ℕ)
    (s : Set ((TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))))
    (N : Submodule ℤ (SingularChainInt X n)) (hN : N = Finsupp.supported ℤ ℤ s) :
    Module.Projective ℤ (SingularChainInt X n ⧸ N) := by
  classical
  subst hN
  refine projective_quotient_of_retraction (Finsupp.supported ℤ ℤ s) (Finsupp.restrictDom ℤ ℤ s) ?_
  intro x
  apply Subtype.ext
  rw [Finsupp.restrictDom_apply, Finsupp.filter_eq_self_iff]
  intro a ha
  exact (Finsupp.mem_supported ℤ _).1 x.2 (Finsupp.mem_support_iff.2 ha)

end SKEFTHawking.SingularChainQuotientProjectiveInt
