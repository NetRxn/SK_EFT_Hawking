/-
# Phase 5q.H W-A arm 4 — the ADMISSIBILITY PIN (spec item 3): the gate-citing DISCRIMINATION half

The FIX for the round-5 vacuity finding **F3** (`PinPlusCharPairGeoRealizationGate` §5, fork
`wadm-sqop-gauge-w2-filter-vacuous`): `LefschetzWuDatum.sqOp` is a FREE field — it appears in NEITHER
of the datum's constraints (`nondeg`, `dimeq`) — so `LefschetzWuDatum.zeroSq` replaces it with `0`,
after which both Wu classes vanish (`wuClass_zeroSq`), `wuW2 = 0` holds DEFINITIONALLY for every `W`
whatever its honest `w₂` (`wuW2_zeroSq`), and a full `CharPairWProvider` is dischargeable from bare
Lefschetz-duality data with ZERO Steenrod input (`charPairWProviderOfDuality`). W-admissibility, as
shaped, is not a `w₂(W) = 0` filter. The pin layer MAKES it one.

## The DAG split (arm-4 round 5 sever)

The pin layer's STRUCTURES and non-vacuity witnesses live in **`PinPlusWAdmPinnedCore`** (same
namespace `SKEFTHawking.PinPlusWAdmPinned` — every FQN unchanged), which is gate-free so the
realized-carrier chain can import it without cycling through the KT/instance-consumer chain. THIS
file keeps only the four theorems that cite the round-5 gate module (`LefschetzWuDatum.zeroSq`,
`WAdm.ofLefschetzNoWu`): the discrimination that the F3 exploit route is EXCLUDED wherever the
honest Steenrod square is nonzero.

## The pin design + the `mu`/`cup` audit (recorded verdicts — full detail in the git history)

Per-field CERTIFICATE over the frozen `LefschetzWuDatum` (never a re-defined structure): `sqOp`
pinned to `relSq1`/`relSq2` (the sharp F3 exploit — the only field in `wuFunctional` but no
constraint), and `cup`/`μ` ALSO pinned (`relCupH14/23` / a genuine `RelFundClassDatum.mu`) because
`nondeg` only forces the pairing perfect, not ACTUAL — a perfect-but-wrong pairing decouples
`wuClass` from the manifold's `w₂` (the faithfulness hole). Non-vacuity: every `ofRelFund`-
assembled datum is pinned by construction (`ofRelFund14/23_pinned`, `cylinderP14/23_pinned` —
in the Core).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusWAdmPinnedCore
import SKEFTHawking.PinPlusCharPairGeoRealizationGate

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularRelativeBockstein SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairGeoRealizationGate

namespace SKEFTHawking.PinPlusWAdmPinned

/-! ## §1. Discrimination (a): the F3 `zeroSq` route is EXCLUDED wherever the honest Steenrod
square is nonzero. -/

section Discrimination

variable {X : TopCat} {S : Set X}

/-- **The `zeroSq` route satisfies the `(2,3)` Steenrod pin IFF the honest `relSq² = 0`.** Since
`(zeroSq P).sqOp = 0` definitionally, the pin `0 = relSq²` holds exactly when the substrate Steenrod
square itself vanishes — i.e. the F3 shortcut becomes pin-satisfying precisely in the *honestly*-
vanishing case, and NOWHERE else. -/
theorem sqOpPinned23_zeroSq_iff (P : LefschetzWuDatum X S 2 3 5) :
    SqOpPinned23 (LefschetzWuDatum.zeroSq P) ↔ (relSq2 : RelativeCohomology S 3 →ₗ[ZMod 2]
      RelativeCohomology S 5) = 0 :=
  eq_comm

/-- **The `zeroSq` route satisfies the `(1,4)` Steenrod pin IFF the honest `relSq¹ = 0`.** -/
theorem sqOpPinned14_zeroSq_iff (P : LefschetzWuDatum X S 1 4 5) :
    SqOpPinned14 (LefschetzWuDatum.zeroSq P) ↔ (relSq1 (n := 3) : RelativeCohomology S 4 →ₗ[ZMod 2]
      RelativeCohomology S 5) = 0 :=
  eq_comm

/-- Wherever the honest relative `Sq² ≠ 0`, a `zeroSq`-ed datum is NOT Steenrod-pinned. -/
theorem not_sqOpPinned23_zeroSq (P : LefschetzWuDatum X S 2 3 5)
    (h : (relSq2 : RelativeCohomology S 3 →ₗ[ZMod 2] RelativeCohomology S 5) ≠ 0) :
    ¬ SqOpPinned23 (LefschetzWuDatum.zeroSq P) :=
  fun hp => h ((sqOpPinned23_zeroSq_iff P).mp hp)

end Discrimination

/-! ## §2. Discrimination (b): the provider-route exploit is un-pinnable. -/

section Provider

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

omit [I.Boundaryless] in
/-- **The F3 exploit route is UN-pinnable on genuine-Steenrod bordisms.** `WAdm.ofLefschetzNoWu`
(the engine behind `charPairWProviderOfDuality`) hands each bordism a `zeroSq`-ed `P23`, so it is
Steenrod-pinned only where the honest `relSq² = 0`. Hence no `WAdmPinned` — and no
`CharPairWProviderPinned` — can be assembled from bare Lefschetz-duality data on a bordism whose
`W` carries genuine `Sq²`. -/
theorem not_sqOpPinned23_ofLefschetzNoWu {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t}
    (P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5)
    (P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (h : relSq2 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W) ≠ 0) :
    ¬ SqOpPinned23 ((WAdm.ofLefschetzNoWu P14 P23).P23) :=
  fun hp => h ((sqOpPinned23_zeroSq_iff P23).mp hp)

end Provider

end SKEFTHawking.PinPlusWAdmPinned
