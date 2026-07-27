/-
# Phase 5q.H — K10: the welded Kummer `K3`'s `pdInput` is NOT an independent residual

`KummerK3E1Package.KummerK3E1Residuals` listed three open homological inputs of the `K3` E1 atom
package; `KummerK3SeamWindingParity.free_h1K3_uncond` closed `h1Free` unconditionally
(`H₁(K3;ℤ) = 0`), leaving `orientInput` (`H₃(K3;ℤ)` 2-torsion-free) and

  `pdInput : ∀ o : IntOrientation KummerK3,`
  `  Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))`.

This module does two things.

## §1–§2 — the `H₁`-freeness binder is discharged, so the whole `H²` side goes UNCONDITIONAL

`KummerK3E1Package` §3 (the UCT flip `H²(K3;ℤ) ≅ Hom(H₂(K3;ℤ),ℤ)`, the rank-22 cohomology basis, the
`IntH2Basis` atom, the Kronecker binder `kronH2KummerK3`) sat under
`variable [Module.Free ℤ (Homology KummerK3top 1)]`. Registering `free_h1K3_uncond` as an instance
(`kummerK3H1Free`) discharges that binder once and for all, so §2 re-exports the whole `H²` side with
**zero binders**: `H²(K3;ℤ) ≅ ℤ²²` (`kummerK3CohomTwoEquivInt_uncond`), `H²(K3;ℤ)` finite free, and
the abstract identification `H₂(K3;ℤ) ≃ₗ H²(K3;ℤ)` (`kummerK3HomologyCohomologyEquiv`) that the cap
route needs. The `Module.Projective ℤ (boundaries KummerK3top 1)` side-condition of the cap route is
universal (`SphereWitnessTowerInt.boundariesProjective`) and is re-confirmed here as
`kummerK3BoundariesOneProjective`.

## §3 — THE STRUCTURAL RESULT: `pdInput` follows from the Gram span's own target

`IntPDDetCriterion` proves `Nonempty (IntPoincareDuality fc) ↔ IsUnit (interMatrix fc B).det` for any
`IntH2Basis` datum `B`. The welded `K3` now *has* such a datum unconditionally (§2), and the K10 Gram
span's obligation is exactly `IntCongr (reindex (interMatrix …)) SpinSigmaRoute.k3Form` with `k3Form`
even unimodular. Congruence preserves determinants, so:

> **`hk3` (on ANY rank-22 basis) ⟹ `pdInput`** — `nonempty_intPD_of_geometric_gram`.

So the E1 residual ledger drops to **one** open homological input (`orientInput`) plus the Gram
statement the K10 span already owes: `kummerK3E1Residuals_of_orient_gram`,
`nonempty_kummerK3E1Atoms_of_orient_gram`.

Non-vacuity: none of these is an implication with an unsatisfiable hypothesis. `hk3` is the genuine
(still open) geometric Gram congruence — true for the real `K3` — and the conclusion `pdInput` is not
otherwise known, so the implication carries content in both directions of use. §4 keeps the two cap
routes available for a discharge that goes through geometry rather than through the Gram matrix.

## ⚠ What this does NOT do

It does not prove `hk3`. The Gram span still owes the geometric computation, and per `SETTLED_FORKS`
(`kummer-16-plus-6-geometric-block-is-not-a-basis`) the 16 exceptional + 6 descended-torus classes
span only a proper finite-index sublattice of `H₂(K3;ℤ)` — the Kummer half-sums are required. Nothing
here shortcuts that.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntPoincareDualityDetCriterion
import SKEFTHawking.KummerK3SeamWindingParity

namespace SKEFTHawking.KummerK3PoincareDuality

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (k3Form k3Form_isEvenUnimodular)

noncomputable section

/-! ## §1. The `H₁`-freeness binder of the E1 package is now an INSTANCE -/

/-- **`H₁(K3;ℤ)` is a free ℤ-module, as an instance.** `KummerK3SeamWindingParity.free_h1K3_uncond` is
unconditional (it rests on `h1K3_eq_zero_uncond`: `H₁(K3;ℤ) = 0`), so the
`variable [Module.Free ℤ (Homology KummerK3top 1)]` binder that `KummerK3E1Package` §3/§6 carry is
discharged from here on. Every `H²`-side definition of that module becomes binder-free below. -/
instance kummerK3H1Free : Module.Free ℤ (Homology KummerK3top 1) :=
  SKEFTHawking.KummerK3SeamWindingParity.free_h1K3_uncond

/-! ## §2. The `H²(K3;ℤ)` side, UNCONDITIONALLY -/

/-- **`H²(K3;ℤ) ≅ ℤ²²`, with no binders** — the UCT flip of the K7 arc's unconditional
`H₂(K3;ℤ) ≅ ℤ²²`, now that `Ext(H₁(K3;ℤ), ℤ) = 0` is a theorem rather than a hypothesis. This is the
cohomological form of `b₂(K3) = 22`. -/
def kummerK3CohomTwoEquivInt_uncond : Cohomology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ) :=
  kummerK3CohomTwoEquivInt

/-- **`H²(K3;ℤ)` is a free ℤ-module**, unconditionally. -/
instance kummerK3CohomTwoFree : Module.Free ℤ (Cohomology KummerK3top 2) :=
  Module.Free.of_equiv kummerK3CohomTwoEquivInt_uncond.symm

/-- **`H²(K3;ℤ)` is a finitely generated ℤ-module**, unconditionally — one of the two instance
side-conditions of `IntPDCapOnly`'s cap route, and the Noetherian input of
`IntPDDetCriterion.capBijective_of_capSurjective`. -/
instance kummerK3CohomTwoFinite : Module.Finite ℤ (Cohomology KummerK3top 2) :=
  Module.Finite.equiv kummerK3CohomTwoEquivInt_uncond.symm

/-- **The abstract identification `H₂(K3;ℤ) ≃ₗ H²(K3;ℤ)`** — both are `ℤ²²` (homology by the K7 arc's
`kummerK3_b2_target_unconditional`, cohomology by §2's UCT flip). NOT the Poincaré-duality map: it is
an arbitrary basis-matching iso, and is used only where the *existence* of some isomorphism is what
matters (the Orzech/Vasconcelos surjective-endomorphism step of
`IntPDDetCriterion.capBijective_of_capSurjective`). -/
def kummerK3HomologyCohomologyEquiv : Homology KummerK3top 2 ≃ₗ[ℤ] Cohomology KummerK3top 2 :=
  kummerK3H2EquivInt.trans kummerK3CohomTwoEquivInt_uncond.symm

/-- **The last instance side-condition of the cap route holds at `K3`** — `boundaries K3 1` is a
projective ℤ-module. Universal over the PID ℤ (`SphereWitnessTowerInt.boundariesProjective`);
recorded here so the `K3` instance set of `IntPDCapOnly` is visibly complete. -/
theorem kummerK3BoundariesOneProjective : Module.Projective ℤ (boundaries KummerK3top 1) :=
  inferInstance

/-! ## §3. `pdInput` from the Gram span's own congruence target -/

/-- **Integral PD at the welded `K3` ⟺ the integer Gram determinant is a unit.** The `K3` instance of
`IntPDDetCriterion.nonempty_intPoincareDuality_iff_isUnit_det`, available now only because §2 supplies
the `IntH2Basis KummerK3top` datum with no binders. Read right-to-left it is the discharge route;
read left-to-right it is the banked `interMatrix_isUnit_det_of_intPD`. -/
theorem nonempty_intPD_iff_isUnit_det (o : IntOrientation KummerK3) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))
      ↔ IsUnit (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis).det :=
  IntPDDetCriterion.nonempty_intPoincareDuality_iff_isUnit_det _ _

/-- **THE HEADLINE — `hk3` ⟹ `pdInput`, on ANY rank-22 basis.** If for the orientation `o` some
rank-22 `IntH2Basis` of `H²(K3;ℤ)` has its (reindexed) Gram matrix `IntCongr` to `SpinSigmaRoute.k3Form`
— which is *exactly* the K10 Gram span's obligation, and is deliberately a congruence rather than a
matrix equality — then the `IntPoincareDuality` datum for that same orientation is inhabited.

`k3Form` is even unimodular (`k3Form_isEvenUnimodular`), reindexing preserves the determinant, and
congruence preserves the determinant (`IntCongr.det_eq`), so the Gram matrix is unimodular and
`IntPDDetCriterion.intPoincareDualityOfIntCongr` produces the duality equivalence. -/
theorem nonempty_intPD_of_geometric_gram (o : IntOrientation KummerK3)
    (C : IntH2Basis KummerK3top) (hC : C.rank = 22)
    (hgeo : IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) :=
  ⟨IntPDDetCriterion.intPoincareDualityOfIntCongr _ C hC k3Form_isEvenUnimodular.2.1 hgeo⟩

/-- **The same, phrased on the packaged (anonymous) basis** — the exact shape
`KummerK3E1Package.kummerK3_hk3_of_geometric_basis` produces, so its output feeds this directly. -/
theorem nonempty_intPD_of_hk3 (o : IntOrientation KummerK3)
    (hk3 : IntCongr (Matrix.reindex (finCongr kummerK3IntH2Basis_rank)
        (finCongr kummerK3IntH2Basis_rank)
        (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis)) k3Form) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) :=
  nonempty_intPD_of_geometric_gram o kummerK3IntH2Basis kummerK3IntH2Basis_rank hk3

/-- **`pdInput`, the whole `∀ o` field, from the Gram statement.** The K10 span's Gram obligation, once
proved for every integral orientation of the welded carrier, *is* the `pdInput` field of
`KummerK3E1Residuals`. -/
theorem kummerK3_pdInput_of_gram
    (hgram : ∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
      IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :
    ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) := by
  intro o
  obtain ⟨C, hC, hgeo⟩ := hgram o
  exact nonempty_intPD_of_geometric_gram o C hC hgeo

/-- **THE LEDGER DROPS TO ONE HOMOLOGICAL INPUT.** `KummerK3E1Residuals` is assembled from
`orientInput` (`H₃(K3;ℤ)` 2-torsion-free) alone, plus the Gram congruence the K10 span already owes:
`h1Free` is `free_h1K3_uncond` and `pdInput` is §3. Compare
`KummerK3SeamWindingParity.kummerK3E1Residuals_of_orient_pd`, which still took `pdInput` as an
independent input. -/
theorem kummerK3E1Residuals_of_orient_gram (orientInput : KummerK3H3TwoTorsionFree)
    (hgram : ∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
      IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :
    KummerK3E1Residuals :=
  ⟨orientInput, kummerK3H1Free, kummerK3_pdInput_of_gram hgram⟩

/-- **The E1 atom triple `orient`/`B`/`pd` + `rank22` from the orientation input and the Gram
statement.** The end-to-end consequence: everything `PinPlusKTSpinSigmaAtomReduce.SpinSigmaAtomPkg`
wants at the welded `K3` follows from `H₃(K3;ℤ)` 2-torsion-freeness together with the K3-lattice
congruence — no separate Poincaré-duality disclosure. -/
theorem nonempty_kummerK3E1Atoms_of_orient_gram (orientInput : KummerK3H3TwoTorsionFree)
    (hgram : ∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
      IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :
    Nonempty KummerK3E1Atoms :=
  kummerK3E1Atoms_of_residuals (kummerK3E1Residuals_of_orient_gram orientInput hgram)

/-! ## §4. The two CAP routes at `K3`, with every instance side-condition discharged

Kept available because a discharge of `pdInput` through geometry (exhibited homology classes and their
cohomological cap-duals) is independent of the Gram route of §3 — either one closes the field. All
three instance side-conditions of `IntPDCapOnly` (`Module.Free`/`Module.Finite` for `H₂(K3;ℤ)`,
`Module.Projective ℤ (boundaries K3 1)`) are in scope at `K3` (§2 and `KummerK3E1Package` §2). -/

/-- **`pdInput` from a cap-DUAL BASIS on the welded `K3`** — the packaged form of
`IntPDCapOnly.intPoincareDualityOfCapDualBasis`: a basis of `H²(K3;ℤ)` whose cap-images against `[K3]`
form a basis of `H₂(K3;ℤ)` delivers the duality datum. -/
theorem nonempty_intPD_of_capDualBasis (o : IntOrientation KummerK3) {ι : Type}
    (B : Module.Basis ι ℤ (Cohomology KummerK3top 2))
    (c : Module.Basis ι ℤ (Homology KummerK3top 2))
    (hdual : ∀ i, capHInt 2 1 (B i) o.fundClass = c i) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) :=
  ⟨IntPDCapOnly.intPoincareDualityOfCapDualBasis B c hdual⟩

/-- **`pdInput` from a cap-SPANNING family on the welded `K3`** — the weakened cap route of
`IntPDDetCriterion.capBijective_of_capSurjective`: it is enough that the cap-images of *some* family
of cohomology classes GENERATE `H₂(K3;ℤ)`; they need not be a basis and the family need not be finite.
The abstract `H₂ ≃ₗ H²` this needs is §2's `kummerK3HomologyCohomologyEquiv`, available because both
sides are unconditionally `ℤ²²`. -/
theorem nonempty_intPD_of_capSpan (o : IntOrientation KummerK3) {ι : Type*}
    (a : ι → Cohomology KummerK3top 2)
    (hspan : Submodule.span ℤ (Set.range fun i => capHInt 2 1 (a i) o.fundClass) = ⊤) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) :=
  ⟨IntPDDetCriterion.intPoincareDualityOfCapSpan kummerK3HomologyCohomologyEquiv a hspan⟩

end

end SKEFTHawking.KummerK3PoincareDuality
