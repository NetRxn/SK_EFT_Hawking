/-
# Phase 5q.H — K10 span 2: the welded Kummer `K3`'s **E1 package atoms** (orientation + rank-22 basis)

The K7 arc closed `H₂(K3;ℤ) ≅ ℤ²²` **unconditionally** on the actual welded carrier
(`KummerChart1NbhdAcyclicInt.kummerK3_b2_target_unconditional`, zero binders). The row side wants a
`PinPlusKTSpinSigmaAtomReduce.SpinSigmaAtomPkg` — `orient : IntOrientation`, `B : IntH2Basis`,
`pd : IntPoincareDuality` — none of which the `H₂` statement is. This module builds the first two
atoms' worth of bridge and states precisely what is still missing.

## What lands here (all on the real welded carrier `KummerWeld.KummerK3`)

* **§1 — the charted-space transport, as a usable instance.** `KummerK3Manifold.isManifold_R4_kummerK3`
  carries its `ChartedSpace (𝓔⁴) KummerK3` in a `letI`; every `IntOrientation` / `fundamentalClass`
  statement needs it in scope. `kummerK3ChartedR4` re-exports it as a scoped instance, and
  `isManifold_R4_kummerK3'` re-states the smooth-manifold theorem against it (so the instance used
  downstream is provably the one the manifold theorem was proved for).
* **§2 — `H₂(K3;ℤ)` is finite free of rank 22, as instances.** Transported from the unconditional
  equivalence. UNCONDITIONAL.
* **§3 — the `H²(K3;ℤ)` side and the `IntH2Basis` datum.** The `B` field of `SpinSigmaAtomPkg` is a
  basis of **co**homology; the K7 computation is **homology**. The bridge is the in-tree absolute
  integral UCT (`SingularAbsoluteUCInt.ucIntEquivOfFree`), whose one open input at degree 2 is
  `Module.Free ℤ (H₁(K3;ℤ))` — carried here as an honest instance binder (`kummerK3IntH2Basis`), NOT
  silently assumed. Under it: `H²(K3;ℤ) ≅ ℤ²²`, a rank-22 `IntH2Basis KummerK3top`, and the σ÷16
  leg's Kronecker binder `kronH2OfFree` closing at `K3` (`kronH2KummerK3`).
* **§4 — the orientation atom**, from `IntOrientationMod2Lift`: `Nonempty (IntOrientation KummerK3)`
  from the single homological input `H₃(K3;ℤ)` 2-torsion-free (`KummerK3H3TwoTorsionFree`).

## What is HONESTLY still missing (do not read this module as more than it is)

1. **The basis is not canonical and not geometric.** `kummerK3_b2_target` is a `Nonempty`; the
   equivalence extracted from it is an arbitrary `Classical.choice`. So `kummerK3IntH2Basis` is *a*
   rank-22 basis, not *the* basis of 3 hyperbolic planes + 2(−E₈) on which
   `SpinSigmaRoute.k3Form` is the Gram matrix. `hrank` (rank = 22) is discharged; `hk3`
   (`IntCongr (interMatrix …) k3Form`) is NOT, and is not weakened by anything here — the Gram
   computation still needs the exceptional/Q-side classes' cup products, which no statement in this
   module touches. **§6 shows the anonymity is nevertheless free**: `hk3` proved on ANY rank-22
   basis transfers to this one (`kummerK3_hk3_of_geometric_basis`), because the row asks for a
   congruence rather than a Gram equality.
2. **Three named open inputs**, each a single homological fact on the welded carrier, listed in
   §5 (`KummerK3E1Residuals`): `H₁` free (§3's binder), `H₃` 2-torsion-free (§4), and the
   `IntPoincareDuality` unimodularity atom (untouched here).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerChart1NbhdAcyclicInt
import SKEFTHawking.KummerK3Manifold
import SKEFTHawking.IntOrientationMod2Lift
import SKEFTHawking.IntersectionMatrixBasisChange

namespace SKEFTHawking.KummerK3E1Package

open scoped Manifold
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularAbsoluteUCInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)

noncomputable section

/-! ## §1. The `𝓡 4` charted structure of the welded `K3`, as a scoped instance -/

/-- **The welded `K3`'s charted structure on `𝓔⁴`.** `KummerK3Manifold` proves the weld atlas is a
`C^k` atlas on the flat model `𝓔³ × ℝ` and transports it along `prodRealEquivEuclidean 3`; that
transport is stated with a `letI`, so the instance is not in scope for consumers. Here it is a
scoped instance, which is what `IntOrientation KummerK3` and
`SingularFundamentalClass.fundamentalClass` require. -/
scoped instance kummerK3ChartedR4 : ChartedSpace (EuclideanSpace ℝ (Fin 4)) KummerK3 :=
  SKEFTHawking.ManifoldModelTransport.transportedChartedSpace
    (SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 3) KummerK3

/-- **The smooth-manifold theorem holds for the §1 instance.** Re-states
`KummerK3Manifold.isManifold_R4_kummerK3` against `kummerK3ChartedR4` — so the charted structure
carrying the orientation/fundamental-class statements below is provably the one on which
`KummerK3` is a `C^k` 4-manifold, for every regularity `k` (in particular `k = ⊤`). Without this the
scoped instance would be an unmoored second charted structure. -/
theorem isManifold_R4_kummerK3' {k : WithTop ℕ∞} : IsManifold (𝓡 4) k KummerK3 :=
  SKEFTHawking.KummerK3Manifold.isManifold_R4_kummerK3

/-! ## §2. `H₂(K3;ℤ)` is finite free of rank 22 — UNCONDITIONAL -/

/-- **A rank-22 trivialisation of `H₂(K3;ℤ)` — an ARBITRARY CHOICE.** `kummerK3_b2_target` is a
`Nonempty`, so this extracts one of its inhabitants; it is *a* trivialisation, never a pinned
generator system. Everything downstream that only needs freeness/rank is choice-robust; anything
naming specific classes (the Gram computation) is NOT and must not route through it. -/
def kummerK3H2EquivInt : Homology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ) :=
  Classical.choice SKEFTHawking.KummerChart1NbhdAcyclicInt.kummerK3_b2_target_unconditional

/-- **`H₂(K3;ℤ)` is a free ℤ-module** — transported from §2's trivialisation. One of the two
reflexivity inputs of the σ÷16 leg's Kronecker binder. UNCONDITIONAL. -/
instance kummerK3H2Free : Module.Free ℤ (Homology KummerK3top 2) :=
  Module.Free.of_equiv kummerK3H2EquivInt.symm

/-- **`H₂(K3;ℤ)` is a finitely generated ℤ-module** — the other reflexivity input. UNCONDITIONAL. -/
instance kummerK3H2Finite : Module.Finite ℤ (Homology KummerK3top 2) :=
  Module.Finite.equiv kummerK3H2EquivInt.symm

/-- **A rank-22 ℤ-basis of `H₂(K3;ℤ)`** — the §2 trivialisation read as a basis (again: arbitrary,
not the geometric 3H ⊕ 2(−E₈) system). -/
def kummerK3H2Basis : Module.Basis (Fin 22) ℤ (Homology KummerK3top 2) :=
  (Pi.basisFun ℤ (Fin 22)).map kummerK3H2EquivInt.symm

/-! ## §3. The `H²` side: the UCT flip and the `IntH2Basis` atom

The single open input is `Module.Free ℤ (Homology KummerK3top 1)` — `H₁(K3;ℤ)` torsion-free. The K7
arc reduced it to a `Q`-side fact (`KummerK7H1Window.h1K3_surjective_from_Q`: `H₁(K3;ℤ)` is a
quotient of `H₁(Q;ℤ)`) but did not close it, so it is carried as an instance binder here. The
boundary-projectivity inputs of the UCT are universal (`SphereWitnessTowerInt.boundariesProjective`).
-/

section CohomologySide

variable [Module.Free ℤ (Homology KummerK3top 1)]

/-- **`H²(K3;ℤ) ≅ Hom(H₂(K3;ℤ), ℤ)`** — the absolute integral UCT at degree 2 on the welded carrier
(`ucIntEquivOfFree` at `M = 0`), whose `Ext`-vanishing input is the `H₁` freeness binder and whose
boundary projectivities are universal. -/
def kummerK3UCT : Cohomology KummerK3top 2 ≃ₗ[ℤ] Module.Dual ℤ (Homology KummerK3top 2) :=
  haveI : Module.Free ℤ (Homology KummerK3top (0 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology KummerK3top 1))
  ucIntEquivOfFree KummerK3top 0

/-- **A rank-22 ℤ-basis of `H²(K3;ℤ)`** — the dual of §2's homology basis, pulled back across the
UCT. This is the shape `IntH2Basis` (hence `SpinSigmaAtomPkg.B`) demands: a basis of
**co**homology, which the K7 homology computation is not. -/
def kummerK3CohomTwoBasis : Module.Basis (Fin 22) ℤ (Cohomology KummerK3top 2) :=
  kummerK3H2Basis.dualBasis.map kummerK3UCT.symm

/-- **`H²(K3;ℤ) ≅ ℤ²²`** — the cohomological form of `b₂(K3) = 22`, from §3's basis. -/
def kummerK3CohomTwoEquivInt : Cohomology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ) :=
  kummerK3CohomTwoBasis.equivFun

/-- **The `B` atom of `SpinSigmaAtomPkg` at the welded `K3`** — the `IntH2Basis KummerK3top` datum,
rank 22. Together with §4's orientation this is two of the package's three fields; the third (`pd`)
and the Gram congruence `hk3` are untouched (see the module header). -/
def kummerK3IntH2Basis : IntH2Basis KummerK3top :=
  ⟨22, kummerK3CohomTwoBasis⟩

/-- **`b₂(K3) = 22` in the exact shape `K3RealizingElement.hrank` consumes** (`rfl` on the datum's
rank field). The substance is upstream — `kummerK3_b2_target_unconditional`, an actual Mayer–Vietoris
computation on the welded carrier — not in this equation. -/
@[simp] theorem kummerK3IntH2Basis_rank : kummerK3IntH2Basis.rank = 22 := rfl

/-- **The σ÷16 leg's Kronecker binder closes at the welded `K3`** — `H₂(K3;ℤ) ≃ₗ (H²(K3;ℤ))*` — with
no leftover obligations beyond the `H₁` freeness binder: `H₂` finite free is §2 (unconditional),
boundary projectivity is universal. The `K3` analogue of `SphereWitnessTowerInt.kronH2Sphere4` /
`kronH2SphereProd`; this is the instance set `SixteenDvdKronFree`'s σ÷16 legs consume. -/
def kronH2KummerK3 : Homology KummerK3top 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology KummerK3top 2) :=
  kronH2OfFree KummerK3top

end CohomologySide

/-! ## §4. The orientation atom -/

open scoped SKEFTHawking.KummerK3E1Package in
/-- **The one homological input of the `K3` orientation atom**: `H₃(K3;ℤ)` has no 2-torsion.

Mayer–Vietoris on the weld (`qThick ∪ eImage`, intersection `≃ 16 × ∂E ≃ 16 × ℝP³`) reduces this to
the `Q`-side: `H₂(ℝP³;ℤ) = 0` makes `H₃(K3;ℤ)` the cokernel of `H₃(16×ℝP³;ℤ) → H₃(qThick;ℤ)`
(`H₃(ResE) = 0`, the piece deformation-retracting to `S²`). Named as a `Prop` rather than assumed
silently, per the tracked-hypothesis discipline. -/
def KummerK3H3TwoTorsionFree : Prop :=
  ∀ x : Homology KummerK3top 3, (2 : ℤ) • x = 0 → x = 0

/-- **The `orient` atom of `SpinSigmaAtomPkg` at the welded `K3`**, from the single §4 input.

`IntOrientationMod2Lift.intOrientation_of_h3_twoTorsionFree` replaced the `IntOrientation`
docstring's "integral local-homology tower / coherent generator choice" residual by 2-torsion-freeness
of `H₃`; this fires it on the welded carrier, whose closed-charted-4-manifold instances
(`T2Space`/`CompactSpace`/`Nonempty` from `KummerWeld`, charts from §1) are all in tree. -/
theorem nonempty_intOrientation_kummerK3 (h3 : KummerK3H3TwoTorsionFree) :
    Nonempty (IntOrientation KummerK3) :=
  SKEFTHawking.IntOrientationMod2Lift.intOrientation_of_h3_twoTorsionFree h3

/-! ## §5. The residual ledger -/

/-- **The three open homological inputs of the `K3` E1 package**, as one named conjunction — the
honest statement of what §1–§4 did NOT close. `orientInput` and `h1Free` are the binders of §4 and
§3; `pdInput` is the `IntPoincareDuality` (unimodularity) atom, untouched here. Deliberately NOT
including the Gram congruence `hk3`: that is not a homological input but the intersection-form
computation, a separate span. -/
structure KummerK3E1Residuals : Prop where
  /-- `H₃(K3;ℤ)` 2-torsion-free — the orientation input (§4). -/
  orientInput : KummerK3H3TwoTorsionFree
  /-- `H₁(K3;ℤ)` torsion-free — the UCT input that turns the K7 homology computation into the
  cohomological `B` atom (§3). -/
  h1Free : Module.Free ℤ (Homology KummerK3top 1)
  /-- Integral Poincaré duality on the welded carrier — the `pd` field, i.e. the unimodularity of the
  intersection form. -/
  pdInput : ∀ o : IntOrientation KummerK3,
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))

/-- **The E1 atom triple at the welded `K3`, un-indexed by the K9 `StrMfd` packaging.** Exactly the
`orient`/`B`/`pd` fields of `PinPlusKTSpinSigmaAtomReduce.SpinSigmaAtomPkg` plus the `hrank` value
`K3RealizingElement` demands, stated on the welded carrier alone. Splitting it off from
`SpinSigmaAtomPkg` is what lets this span land BEFORE K9 (the `SingularManifold`/spin-structure
packaging): the E1 content is carrier-local, the indexing is not. -/
structure KummerK3E1Atoms where
  /-- The integral orientation `[K3] ∈ H₄(K3;ℤ)` with its mod-2 compatibility (§4). -/
  orient : IntOrientation KummerK3
  /-- The rank-22 basis of `H²(K3;ℤ)` (§3). -/
  B : IntH2Basis KummerK3top
  /-- Integral Poincaré duality against that orientation — the unimodularity input. -/
  pd : IntPoincareDuality (intFundamentalClassOfIntOrientation orient)
  /-- `b₂(K3) = 22` — the `K3RealizingElement.hrank` value. -/
  rank22 : B.rank = 22

/-- **The ledger delivers the E1 atom triple — and needs all three residuals to do it.** `orientInput`
supplies §4's orientation, `h1Free` turns §2's homology computation into §3's cohomological basis
(with `rank22` then `rfl`), and `pdInput` supplies the duality field. Makes the ledger load-bearing
rather than decorative: it is exactly the input set §1–§4 consume, and its output is exactly the
`SpinSigmaAtomPkg` payload that the K9 packaging will index. -/
theorem kummerK3E1Atoms_of_residuals (r : KummerK3E1Residuals) : Nonempty KummerK3E1Atoms := by
  haveI := r.h1Free
  obtain ⟨o⟩ := nonempty_intOrientation_kummerK3 r.orientInput
  obtain ⟨pd⟩ := r.pdInput o
  exact ⟨⟨o, kummerK3IntH2Basis, pd, rfl⟩⟩

/-! ## §6. The anonymity of §3's basis costs the Gram span NOTHING -/

section GramTransfer

variable [Module.Free ℤ (Homology KummerK3top 1)]

/-- **The `hk3` obligation on the packaged (anonymous) basis, from the K3-lattice congruence on ANY
rank-22 basis.** §3's `kummerK3IntH2Basis` is a `Classical.choice` extraction and names no geometry;
this shows that is not a defect of the packaging. Because the row's `hk3` field asks for an
`IntCongr` — not a Gram equality — and Gram matrices of two bases of the same free module differ by a
unimodular congruence (`IntersectionMatrixBasisChange.interMatrix_intCongr_of_rank_eq`), the Gram
span may be executed in whatever coordinates make the cup products computable (the 16 exceptional
`(−2)`-sphere classes plus the six descended `T⁴` classes, the latter's block already congruent to
`3H` by `KummerT4GramCross.interMatrix_t4_intCongr_torusFourForm`) and transferred here for free.

So the outstanding Gram work is exactly the *geometric* statement `hgeo`, with no basis-normalisation
tax on top — the K10 counterpart of the `SphereProdGramPin` retirement. -/
theorem kummerK3_hk3_of_geometric_basis (o : IntOrientation KummerK3) (C : IntH2Basis KummerK3top)
    (hC : C.rank = 22)
    (hgeo : IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C))
      SKEFTHawking.SpinSigmaRoute.k3Form) :
    IntCongr (Matrix.reindex (finCongr kummerK3IntH2Basis_rank) (finCongr kummerK3IntH2Basis_rank)
        (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis))
      SKEFTHawking.SpinSigmaRoute.k3Form :=
  SKEFTHawking.IntersectionMatrixBasisChange.hk3_of_other_basis _ _ C
    kummerK3IntH2Basis_rank hC hgeo

end GramTransfer

end

end SKEFTHawking.KummerK3E1Package
