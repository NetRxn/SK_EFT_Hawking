/-
# Phase 5q.H close-out — THE CAPSTONE COHOMOLOGY MV DATUM: the four finite-dimensionality atoms
# reduced to the two-piece MV cover row.

The `CapstoneAmbientSupply` row (`PinPlusTraceCapstoneInhabit.lean`) carries four cohomology
finite-dimensionality atoms on the CONSTRUCTED capstone `W = (ktHandleAttachment …).carrier`:
`findimAbs14`/`findimAbs23` (`H¹(W)`, `H²(W)` finite-dim) and `findimRel14`/`findimRel23`
(`H⁴(W,∂W)`, `H³(W,∂W)` finite-dim). This module reduces all four to ONE transparent geometric row —
the two-piece Mayer–Vietoris cover `W = A ∪ B` (`A` the cyl side `≃ M`, `B` the handle side `≃ D⁵`)
together with the all-degree homology finiteness of the two pieces, their overlap, and the boundary —
by firing the carrier-agnostic openers of `SingularMVCohomologyFinite.lean`.

**The reduction (§2).** `CapstoneCohomologyMVDatum` bundles the interior cover `A`/`B`/`hcov` and the
four all-degree finiteness facts `hA` (`H_*(A) < ∞`), `hB` (`H_*(B) < ∞`), `hAB` (`H_*(A∩B) < ∞`),
`hBd` (`H_*(∂W) < ∞`) — each a genuinely-geometric input (the pieces are compact,
finite-Betti-type: `A ≃ M` a closed 4-manifold, `B ≃ D⁵` contractible, `A∩B ≃` the seam, `∂W = M ⊔ M′`
two closed 4-manifolds). The four `.toFindim…` projections then chain the openers:

* `findimAbs14/23` = `finiteDimensional_cohomology_of_homology` ∘ `finiteDimensional_homology_of_mv_cover`
  — `Hᵏ(W)` ← `Hₖ(W)` (absolute UC) ← MV-cover at `k = 1, 2`;
* `findimRel14/23` = `finiteDimensional_relativeCohomology_of_relativeHomology` ∘
  `finiteDimensional_relativeHomology_of_pair` ∘ `finiteDimensional_homology_of_mv_cover` — `Hᵏ(W,∂W)`
  ← `Hₖ(W,∂W)` (relative UC) ← pair-LES sandwich (`Hₖ(W)` + `H_{k-1}(∂W)`) ← MV-cover at `k = 4, 3`.

So the four capstone cohomology-finiteness atoms shrink to the single MV-cover row — none a
completeness Prop; each `hA`/`hB`/`hAB`/`hBd` is an honest per-piece homology finiteness on the
constructed carrier, the genuine geometric content of the numerics' finite-dimensionality obligation.

**Fences.** THE COLLAR FORK is respected: the cover `A`/`B` is the constructed handle-attachment's own
`range fromCyl`/`range fromHandle` two-piece structure (carried as datum, per the provider pattern),
never a general collar theorem. The sealed heavy carrier term appears only in field TYPES (via
`TopCat.of (capstoneB …).W`), never re-elaborated inside a constructed term — the whnf discipline the
predecessor's `CapstoneRelFundPartitionDatum` follows.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularMVCohomologyFinite
import SKEFTHawking.PinPlusTraceCapstoneInhabit

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularMVCohomologyFinite
open SKEFTHawking.PinPlusTraceCapstoneInhabit

namespace SKEFTHawking.PinPlusTraceCapstoneCohomologyMV

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The capstone cohomology MV datum — the two-piece cover + all-degree piece finiteness. -/

/-- **The capstone cohomology MV datum** — the honest named row reducing the four finite-dimensionality
atoms of `CapstoneAmbientSupply` to the two-piece Mayer–Vietoris cover `W = A ∪ B`. Carries the
interior cover `A`/`B`/`hcov` and the four all-degree homology-finiteness facts on the constructed
carrier: `hA` (`H_*(A)`, the cyl side `≃ M`), `hB` (`H_*(B)`, the handle side `≃ D⁵`), `hAB`
(`H_*(A∩B)`, the seam), and `hBd` (`H_*(∂W)`, the two closed 4-manifold ends). Each is a genuine
per-piece homology finiteness, none a completeness Prop. -/
structure CapstoneCohomologyMVDatum where
  /-- the cyl-side piece of the MV cover (intended: `range fromCyl`, thickened; `≃ M`). -/
  A : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  /-- the handle-side piece of the MV cover (intended: `range fromHandle`, thickened; `≃ D⁵`). -/
  B : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  /-- the interiors of `A`, `B` cover `W` (the Mayer–Vietoris cover hypothesis). -/
  hcov : (⋃ U ∈ ({A, B} : Set (Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))),
      interior U) = Set.univ
  /-- `H_*(A) < ∞` in every degree (the cyl side `≃ M`, a closed 4-manifold). -/
  hA : ∀ n, FiniteDimensional (ZMod 2) (Homology (sub A) n)
  /-- `H_*(B) < ∞` in every degree (the handle side `≃ D⁵`, contractible). -/
  hB : ∀ n, FiniteDimensional (ZMod 2) (Homology (sub B) n)
  /-- `H_*(A∩B) < ∞` in every degree (the seam overlap). -/
  hAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (sub (A ∩ B)) n)
  /-- `H_*(∂W) < ∞` in every degree (the boundary `∂W = M ⊔ M′`, two closed 4-manifolds). -/
  hBd : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) n)

/-! ## §2. The four finite-dimensionality projections — the atoms discharged from the MV row. -/

/-- **`findimAbs14` from the MV row**: `H¹(W)` finite-dim via absolute UC (`Hᵏ ← Hₖ`) composed with
the MV cover at `k = 1` (`H₁(W)` ← `H₁(A)`, `H₁(B)`, `H₀(A∩B)`). -/
theorem CapstoneCohomologyMVDatum.toFindimAbs14
    (D : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d) :
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 1) :=
  finiteDimensional_cohomology_of_homology 0
    (finiteDimensional_homology_of_mv_cover D.A D.B 0 D.hcov (D.hA 1) (D.hB 1) (D.hAB 0))

/-- **`findimAbs23` from the MV row**: `H²(W)` finite-dim via absolute UC composed with the MV cover
at `k = 2` (`H₂(W)` ← `H₂(A)`, `H₂(B)`, `H₁(A∩B)`). -/
theorem CapstoneCohomologyMVDatum.toFindimAbs23
    (D : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d) :
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 2) :=
  finiteDimensional_cohomology_of_homology 1
    (finiteDimensional_homology_of_mv_cover D.A D.B 1 D.hcov (D.hA 2) (D.hB 2) (D.hAB 1))

/-- **`findimRel14` from the MV row**: `H⁴(W,∂W)` finite-dim via relative UC (`Hᵏ(W,∂W) ← Hₖ(W,∂W)`)
composed with the pair-LES sandwich (`H₄(W,∂W)` ← `H₄(W)` + `H₃(∂W)`), whose `H₄(W)` end comes from
the MV cover at `k = 4` (`H₄(A)`, `H₄(B)`, `H₃(A∩B)`) and whose boundary end is `hBd 3`. -/
theorem CapstoneCohomologyMVDatum.toFindimRel14
    (D : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 4) :=
  finiteDimensional_relativeCohomology_of_relativeHomology 3
    (finiteDimensional_relativeHomology_of_pair _ 3
      (finiteDimensional_homology_of_mv_cover D.A D.B 3 D.hcov (D.hA 4) (D.hB 4) (D.hAB 3))
      (D.hBd 3))

/-- **`findimRel23` from the MV row**: `H³(W,∂W)` finite-dim via relative UC composed with the pair-LES
sandwich (`H₃(W,∂W)` ← `H₃(W)` + `H₂(∂W)`), whose `H₃(W)` end comes from the MV cover at `k = 3`
(`H₃(A)`, `H₃(B)`, `H₂(A∩B)`) and whose boundary end is `hBd 2`. -/
theorem CapstoneCohomologyMVDatum.toFindimRel23
    (D : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3) :=
  finiteDimensional_relativeCohomology_of_relativeHomology 2
    (finiteDimensional_relativeHomology_of_pair _ 2
      (finiteDimensional_homology_of_mv_cover D.A D.B 2 D.hcov (D.hA 3) (D.hB 3) (D.hAB 2))
      (D.hBd 2))

end

end SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
