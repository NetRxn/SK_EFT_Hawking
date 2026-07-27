/-
# Phase 5q.H — the welded `K3`'s E1 atom triple rests on the K10 GRAM CONGRUENCE ALONE

The end of the E1 residual ledger for the welded Kummer `K3`. `KummerK3E1Package.KummerK3E1Residuals`
opened with three homological inputs; they have now all gone:

| residual | status |
|---|---|
| `h1Free` (`Module.Free ℤ H₁(K3;ℤ)`) | discharged — `KummerK3SeamWindingParity.free_h1K3_uncond` (`H₁(K3;ℤ) = 0`) |
| `pdInput` (integral Poincaré duality) | **not independent** — `KummerK3PoincareDuality.kummerK3_pdInput_of_gram`: the Gram congruence already contains it (`k3Form` is unimodular and congruence preserves determinants) |
| `orientInput` (`H₃(K3;ℤ)` 2-torsion-free) | **no longer needed** — `KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond` produces the `orient` field unconditionally by the degree-4 seam-kernel route |

So the only thing between the tree and `Nonempty KummerK3E1Atoms` is the K10 span's own geometric
obligation, the K3-lattice Gram congruence

    ∀ o, ∃ (C : IntH2Basis K3top) (hC : C.rank = 22),
      IntCongr (reindex (interMatrix [K3]_o C)) k3Form.

`nonempty_kummerK3E1Atoms_of_gram` records exactly that, and nothing more.

## ⚠ Precisely what is and is not claimed about `orientInput`

`orientInput = KummerK3E1Package.KummerK3H3TwoTorsionFree` is a statement about `H₃(K3;ℤ)`. It is
**neither proved nor disproved** here: by
`KummerK3H3SeamWindow.kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated` it is equivalent to
2-*saturation* of `im qSeamCoord3`, which does not follow from the nontriviality of
`ker qSeamCoord3` that the seam transport supplies. What changed is that **nothing consumes it any
more**: the orientation atom it existed to produce now comes from the degree-4 route
(`KummerK3OrientFromSeamKernel`), which never mentions `H₃`. The ledger entry is retired as a *gate*,
not settled as a *proposition*.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3SeamTransport
import SKEFTHawking.KummerK3PoincareDuality

namespace SKEFTHawking.KummerK3E1FromGram

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (k3Form)

noncomputable section

/-- **THE E1 ATOM TRIPLE OF THE WELDED `K3`, FROM THE GRAM CONGRUENCE ALONE.**

Every homological residual of `KummerK3E1Package.KummerK3E1Residuals` is gone: `h1Free` is
unconditional, `pdInput` is contained in the Gram statement, and `orientInput` has been retired as a
gate by the seam transport (`KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond`). What is
left is exactly the K10 span's geometric obligation — that some rank-22 `IntH2Basis` of the welded
carrier has intersection form `IntCongr` to the K3 lattice `2·(−E8) ⊕ 3·H`.

Compare `KummerK3PoincareDuality.nonempty_kummerK3E1Atoms_of_orient_gram`, which still took
`orientInput` alongside. -/
theorem nonempty_kummerK3E1Atoms_of_gram
    (hgram : ∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
      IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :
    Nonempty KummerK3E1Atoms :=
  SKEFTHawking.KummerK3SeamTransport.nonempty_kummerK3E1Atoms_of_pd
    (SKEFTHawking.KummerK3PoincareDuality.kummerK3_pdInput_of_gram hgram)

/-- **The same, on the packaged basis** — the shape `KummerK3E1Package.kummerK3_hk3_of_geometric_basis`
produces: a single `IntCongr` on the canonical rank-22 basis `kummerK3IntH2Basis`, for every integral
orientation, suffices. -/
theorem nonempty_kummerK3E1Atoms_of_hk3
    (hk3 : ∀ o : IntOrientation KummerK3,
      IntCongr (Matrix.reindex (finCongr kummerK3IntH2Basis_rank)
        (finCongr kummerK3IntH2Basis_rank)
        (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis)) k3Form) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_gram fun o =>
    ⟨kummerK3IntH2Basis, kummerK3IntH2Basis_rank, hk3 o⟩

end

end SKEFTHawking.KummerK3E1FromGram
