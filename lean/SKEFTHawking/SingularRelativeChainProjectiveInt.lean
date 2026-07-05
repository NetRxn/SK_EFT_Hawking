/-
# Phase 5q.H (E1 integral topology) — the relative integral chains are PROJECTIVE

`RelativeChainInt S n = Cₙ(X;ℤ) / Cₙ(S;ℤ)` is a **projective** ℤ-module. This is the enabling brick for
the relative-cohomology Mayer–Vietoris exactness over ℤ (the CSC-PD tower's crux node): the relative-
homology MV chain SES `0 → RC(U∩V) → RC(U)⊕RC(V) → RC(U∪V) → 0` (on main, `relMvChain_exactInt`)
Hom-dualizes to the relative-cohomology MV **iff** `RC(U∪V)` is projective (`Ext¹(RC, ℤ) = 0`), avoiding
the field-only universal-coefficient route the mod-2 tower uses.

**Why projective:** `chainIncl S = Finsupp.lmapDomain (simplexIncl S)` with `simplexIncl` INJECTIVE, so it
is a **split** injection — a left inverse `g` of `simplexIncl` gives the retraction `Finsupp.lmapDomain g`
(`lmapDomain g ∘ lmapDomain simplexIncl = lmapDomain id = id`). Hence `subspaceChainsInt S =
range(chainIncl S)` is a direct summand of the free `SingularChainInt X n`, so the quotient
`RelativeChainInt S n` is projective (`Module.Projective.of_split`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelHomologyInt

open Opposite
open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl simplexIncl_injective)

namespace SKEFTHawking.SingularRelativeChainProjectiveInt

variable {X : TopCat}

/-- **The relative integral chains are projective.** -/
theorem relativeChainInt_projective (S : Set ↑X) (n : ℕ) :
    Module.Projective ℤ (RelativeChainInt S n) := by
  by_cases hne : Nonempty ((TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n)))
  · haveI := hne
    have hci : chainIncl S n = Finsupp.lmapDomain ℤ ℤ (simplexIncl S n) := rfl
    -- The retraction `r` of the split injection `chainIncl S n` (via a left inverse of `simplexIncl`).
    set r : SingularChainInt X n →ₗ[ℤ] SingularChainInt (sub S) n :=
      Finsupp.lmapDomain ℤ ℤ (Function.invFun (simplexIncl S n)) with hrdef
    have hr : r ∘ₗ chainIncl S n = LinearMap.id := by
      rw [hrdef, hci, ← Finsupp.lmapDomain_comp,
        show (Function.invFun (simplexIncl S n)) ∘ (simplexIncl S n) = id from
          funext (Function.leftInverse_invFun (simplexIncl_injective S n)),
        Finsupp.lmapDomain_id]
    -- `φ = id - chainIncl ∘ r` kills `subspaceChainsInt`, descending to a section of `mkQ`.
    set φ : SingularChainInt X n →ₗ[ℤ] SingularChainInt X n :=
      LinearMap.id - (chainIncl S n) ∘ₗ r with hφdef
    have hle : subspaceChainsInt S n ≤ LinearMap.ker φ := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [LinearMap.mem_ker, hφdef]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      rw [show r (chainIncl S n y) = y from by
        rw [← LinearMap.comp_apply, hr, LinearMap.id_apply], sub_self]
    refine Module.Projective.of_split (Submodule.liftQ (subspaceChainsInt S n) φ hle)
      (subspaceChainsInt S n).mkQ ?_
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (Submodule.Quotient.mk (x - (chainIncl S n) (r x)) : RelativeChainInt S n)
      = Submodule.Quotient.mk x
    rw [Submodule.Quotient.mk_sub,
      show (Submodule.Quotient.mk ((chainIncl S n) (r x)) : RelativeChainInt S n) = 0 from
        (Submodule.Quotient.mk_eq_zero _).2 ⟨r x, rfl⟩, sub_zero]
  · -- Empty: no `(sub S)`-simplices ⟹ `subspaceChainsInt S n = ⊥` ⟹ `RelativeChainInt ≅ SingularChainInt`.
    have hbot : subspaceChainsInt S n = ⊥ := by
      rw [subspaceChainsInt, LinearMap.range_eq_bot]
      apply LinearMap.ext
      intro c
      rw [not_nonempty_iff] at hne
      have hc0 : c = 0 := Finsupp.ext fun a => (hne.false a).elim
      rw [hc0, map_zero, LinearMap.zero_apply]
    exact Module.Projective.of_equiv (Submodule.quotEquivOfEqBot _ hbot).symm

end SKEFTHawking.SingularRelativeChainProjectiveInt
