/-
# Phase 5q.H (E1→E2 seam) — the σ÷16 leg with the spin-Wu binder ELIMINATED

Pure-glue composition of two leaf modules that landed in consecutive commits but were never
wired to each other:

* `SixteenDvdOfOrientation.sixteen_dvd_latticeSig_of_orientationData` (commit `a461fb3a`) — the
  class-level σ÷16 leg fed by the orientation datum, which still consumed the spin-Wu datum `D`
  as a BINDER;
* `SpinWuDatumClosed.spinWuDatum_of_closed` (commit `4c087774`) — `SpinWuDatum` as a THEOREM at
  any closed oriented spin 4-manifold (honest inputs: the orientation + spin in `v₂`-form).

The two carriers agree definitionally — `intFundamentalClassOfIntOrientation (intOrientationOfData d)
= intFundamentalClassOfHomology d.fundClass` (both sides unfold to the same
`intFundamentalClassOfHomology` application) — so the composition is `rfl`-transport-free.

After this brick the σ÷16 leg's contract at a plus-oriented closed charted spin 4-manifold is:
`d : IntOrientationData M` (+ `orient ≡ 1`) + `kron`/`hkron` (H₂ Kronecker duality, OPEN —
`intPoincareDuality`-grade input) + `B : IntH2Basis` (OPEN — `intH2_basis_datum`) + `hv2` (spin as
`wuClass2 (poincareDual4Mid_of_closed) = 0`, the honest mod-2 statement) + `htopo` (E2's `2 ∣ σ/8`)
⟹ `16 ∣ σ`. The `SpinWuDatum` binder is GONE.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SixteenDvdOfOrientation
import SKEFTHawking.SpinWuDatumClosed

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)

namespace SKEFTHawking.SixteenDvdOfOrientationSpin

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **`16 ∣ σ` at a plus-oriented closed charted SPIN 4-manifold — spin-Wu binder eliminated.**
The σ÷16 leg (`sixteen_dvd_latticeSig_of_orientationData`) with its `D : SpinWuDatum …` input
DISCHARGED by `SpinWuDatumClosed.spinWuDatum_of_closed` at the orientation
`intOrientationOfData d` (the two fundamental-class carriers agree definitionally). Remaining
open inputs: the H₂ Kronecker duality `kron`/`hkron`, the basis `B`, and E2's topological factor
`htopo : 2 ∣ σ/8`; the spin input is the honest mod-2 statement `hv2 : v₂ = 0`. -/
theorem sixteen_dvd_latticeSig_of_orientation_spin (d : IntOrientationData M)
    (h1 : ∀ x, d.orient x = 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0)
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  SKEFTHawking.SixteenDvdOfOrientation.sixteen_dvd_latticeSig_of_orientationData d h1 kron hkron B
    (SKEFTHawking.SpinWuDatumClosed.spinWuDatum_of_closed (intOrientationOfData d) hv2) htopo

end SKEFTHawking.SixteenDvdOfOrientationSpin
