/-
# Phase 5q.H (E1) — `SpinWuDatum` DISCHARGED at a general closed oriented spin 4-manifold

The glue module ending the `spinWu_even_datum` chain (E1 shard, arm-2 turns 3–6): for any closed
charted 4-manifold with an integral orientation `o : IntOrientation M` and the spin condition in
`v₂`-form (`wuClass2 (poincareDual4Mid_of_closed) = 0` — for oriented `M`, `v₂ = w₂`, so this IS spin),
the full `SpinWuDatum (intFundamentalClassOfIntOrientation o)` is CONSTRUCTED:

* `mu₂` and the PD frame — `poincareDual4Mid_of_closed` (5q.G X6, hypothesis-free);
* `eval_compat` — `kroneckerHInt_redCompat` (the ℤ→ℤ/2 Kronecker naturality, brick 8) chained with
  `o.redCompat` (the integral `[M]` reduces to `[M]₂`);
* `wu_vanish` — DERIVED via the Wu relation (`spinWuDatum_of_pd4Mid`, brick 3).

So the σ÷16 leg's `D` input is a THEOREM given the two honest inputs (orientation + spin), and
`interMatrix_even_of_spinWu` applies at any such manifold. Consumed by the general-M Rokhlin leg
(`sixteen_dvd_latticeSigInt`) and E2's evenness conjunct.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinWuFromPD
import SKEFTHawking.SingularPD4Instances
import SKEFTHawking.KroneckerRedCompat

namespace SKEFTHawking.SpinWuDatumClosed

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt (SpinWuDatum IntFundamentalClass redH)
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.SpinWuFromPD

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The ℤ→ℤ/2 evaluation compatibility at an oriented closed 4-manifold**: the integral
fundamental-class evaluation reduces to the mod-2 fundamental functional. `kroneckerHInt_redCompat`
(brick 8) chained with the orientation's `redCompat` field. -/
theorem eval_redCompat_of_intOrientation (o : IntOrientation M)
    (ω : SKEFTHawking.SingularCohomologyInt.Cohomology (TopCat.of M) 4) :
    (((intFundamentalClassOfIntOrientation o).eval ω : ℤ) : ZMod 2)
      = fundamentalFunctional (m := 2) (redH (TopCat.of M) 4 ω) := by
  show ((kroneckerHInt 4 ω o.fundClass : ℤ) : ZMod 2) = fundamentalFunctional (m := 2) (redH _ 4 ω)
  rw [kroneckerHInt_redCompat, intOrientation_redHomology_fundClass]
  rfl

/-- **`SpinWuDatum` is a THEOREM at a closed oriented spin 4-manifold.** The two honest inputs are the
integral orientation `o` and the spin condition in `v₂`-form (`wuClass2 P = 0`; on an oriented manifold
`v₂ = w₂`, so this is exactly `w₂ = 0`). Everything else — the mod-2 PD frame, the ℤ→ℤ/2 evaluation
compatibility, and the Wu-relation derivation of `wu_vanish` — is proven machinery (5q.G X6 + bricks
3/8). Discharges the `spinWu_even_datum` chain at general `M`. -/
noncomputable def spinWuDatum_of_closed (o : IntOrientation M)
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0) :
    SpinWuDatum (intFundamentalClassOfIntOrientation o) :=
  spinWuDatum_of_pd4Mid (intFundamentalClassOfIntOrientation o)
    (poincareDual4Mid_of_closed (M := M))
    (fun ω => eval_redCompat_of_intOrientation o ω)
    hv2

/-- **The intersection matrix of a closed oriented spin 4-manifold is EVEN** — the evenness conjunct of
`IsEvenUnimodular` discharged at general `M` from the two honest inputs (orientation + spin-as-`v₂=0`),
via the constructed `SpinWuDatum`. -/
theorem interMatrix_even_of_closed (o : IntOrientation M)
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0)
    (B : SKEFTHawking.SingularCohomologyInt.IntH2Basis (TopCat.of M)) :
    SKEFTHawking.IsEven
      (SKEFTHawking.SingularCohomologyInt.interMatrix (intFundamentalClassOfIntOrientation o) B) :=
  SKEFTHawking.SingularCohomologyInt.interMatrix_even_of_spinWu
    (intFundamentalClassOfIntOrientation o) B (spinWuDatum_of_closed o hv2)

end SKEFTHawking.SpinWuDatumClosed
