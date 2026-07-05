/-
# Phase 5q.H (E1 integral topology) — the split of the relative-homology MV chain SES as an EQUIVALENCE

From the section `relMvChainSumInt_split` (the chain MV SES splits, `QChainInt` projective) plus the
on-main exactness (`relMvChain_exactInt`) and injectivity (`relMvChainDiagInt_injective`),
`Function.Exact.splitSurjectiveEquiv` packages the split as a linear equivalence
  `RC(U)⊕RC(V) ≃ₗ RC(U∩V) × QChainInt`
with `Diag = e.symm ∘ inl` and `Sum = snd ∘ e`. Dualizing this equivalence (`Hom(A×C)=Hom A × Hom C`)
yields the exact cochain MV SES — the field-UC-free relative-cohomology MV.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVSplitInt

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt SKEFTHawking.SingularRelativeMVSplitInt

namespace SKEFTHawking.SingularRelativeMVSplitEquivInt

variable {M : TopCat}

/-- **The relative-homology MV chain SES split, as a linear equivalence**
`RC(U)⊕RC(V) ≃ₗ RC(U∩V) × QChainInt`. -/
noncomputable def mvChainSplitEquiv (U V : Set ↑M) (n : ℕ) :
    (RelativeChainInt U n × RelativeChainInt V n) ≃ₗ[ℤ]
      (RelativeChainInt (U ∩ V) n × QChainInt U V n) :=
  ((relMvChain_exactInt U V n).splitSurjectiveEquiv (relMvChainDiagInt_injective U V n)
    ⟨(relMvChainSumInt_split U V n).choose, (relMvChainSumInt_split U V n).choose_spec⟩ : {_e // _}).1

end SKEFTHawking.SingularRelativeMVSplitEquivInt
