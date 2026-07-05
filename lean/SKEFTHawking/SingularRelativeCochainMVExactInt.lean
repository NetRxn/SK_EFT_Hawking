/-
# Phase 5q.H (E1 integral topology) — the DUAL cochain MV sequence is exact

Applying `exact_dualMap_of_split` (Hom of a split-exact SES is exact) to the SPLIT relative-homology MV
chain SES (`SingularRelativeMVSplitInt`), the dualized sequence of `Module.Dual ℤ`s
  `(QChainInt)* →^{Sum*} (RC(U)⊕RC(V))* →^{Diag*} (RC(U∩V))*`
is **exact**. Under the pairing iso `relKroneckerIntEquiv : relCochainsInt ≅ Hom(RC,ℤ)`, this is the
degreewise exactness of the relative-COchain MV sequence — the field-UC-free input to the relative-
cohomology Mayer–Vietoris (the remaining pieces: the cohomology middle-exactness chase + the dual small-
chains iso `Hⁿ(Hom Q) ≅ RelativeCohomologyInt(U∪V)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVSplitInt
import SKEFTHawking.LinearAlgebraDualExactInt

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt SKEFTHawking.SingularRelativeMVSplitInt
open SKEFTHawking.LinearAlgebraDualExactInt

namespace SKEFTHawking.SingularRelativeCochainMVExactInt

variable {M : TopCat}

/-- **The dual cochain MV sequence is exact**: `(QChainInt)* →^{Sum*} (RC(U)⊕RC(V))* →^{Diag*}
(RC(U∩V))*`. Immediate from `exact_dualMap_of_split` on the split chain MV SES. -/
theorem mvCochain_dual_exact (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvChainSumInt U V n).dualMap (relMvChainDiagInt U V n).dualMap :=
  exact_dualMap_of_split (relMvChain_exactInt U V n)
    (relMvChainSumInt_split U V n).choose (relMvChainSumInt_split U V n).choose_spec

end SKEFTHawking.SingularRelativeCochainMVExactInt
