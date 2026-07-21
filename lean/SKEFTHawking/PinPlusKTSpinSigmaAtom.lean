/-
# Phase 5q.H · The R-atom opener — the σ-presentation of the empty-Σ spin carrier from disclosed E1 data

`SpinPresentationRow.R : SpinSigmaPresentation (spinEmptyData prov)` is the last substrate atom
between the KT §5 presentation row and genuine dA/dC consumption (round-11 spec-3: the row's
consumers are live; `R` is the terminal σ-presentation atom, flagged in `PinPlusKTFreezeAssembly`
PRE-arm-4). This module gives the SHARPEST honest reduction of that atom.

The genuine full wiring does NOT reach in-tree: `SpinSigmaPresentation.sig`'s bordism-invariance is
Thom's signature theorem, and `interMatrix` consumes a per-manifold `IntFundamentalClass` +
`IntH2Basis` (Mathlib has no manifold cohomology — both are disclosed E1 data). So the deliverable is
the `#143`/`#151` typed-atom pattern: a bundle `SpinSigmaAtoms` of the disclosed per-manifold E1
geometry — integral fundamental class, `H²(M;ℤ)` basis, Spin/Wu (`w₂ = 0`), integral Poincaré
duality — plus the Thom signature-descent and the distinguished `S²×S²` witness, from which
`spinSigmaPresentation_of_atoms` BUILDS the full σ-presentation.

The build DISCHARGES real E1 content, so the reduction is non-vacuous, not a repackaging: the abstract
`even_unimod` field (an `IsEvenUnimodular` property per manifold) is produced from the two clean
geometric data via `isEvenUnimodular_of_intPD` — spin ⟹ even (Wu criterion through the ℤ→ℤ/2 bridge)
and Poincaré duality ⟹ unimodular (the perfect-pairing iso). Drop the `SpinWuDatum` field and evenness
breaks; drop the `IntPoincareDuality` field and unimodularity breaks. What remains as atoms is exactly
the disclosed literature residual (four per-manifold E1 data + σ-descent + the `S²×S²` realization).

`spinPresentationRow_of_atoms` is the capstone: with the atom bundle plus the Rokhlin `16 ∣ σ` and the
`σ(K3) = −16` K3-generator data (`hrank`/`hk3`), the WHOLE `SpinPresentationRow` — hence dA
(`DualSpinForwardDatum`) and dC (`KTSpinPresentationDatum`) consumption — assembles. The R-atom is no
longer the terminal blocker between the row and consumption; it is reduced to the E1 disclosed data.

Dimension discipline: this lives entirely on `spinEmptyData prov` — the CLOSED SPIN 4-manifold,
empty-Σ carrier (Σ = ∅). It shares no wires with the Pin⁺-side `pinPlusCharPairData` ℝP⁴-witness
machinery (4-dim carrier with a 2-dim characteristic surface); the only bridge remains the honest
`spinForgetPhi`, untouched here.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinPresentationRow
import SKEFTHawking.IntersectionFormUnimodularInt

namespace SKEFTHawking.PinPlusKTSpinSigmaAtom

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTExtension SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTLemma53Wave SKEFTHawking.PinPlusKTKernelSpinRoute

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The disclosed per-manifold E1 atom bundle -/

/-- **The disclosed E1 geometry of the empty-Σ spin carrier, bundled.** For each structured manifold
`p` of `spinEmptyData prov` (whose underlying closed spin 4-manifold is `p.1.M`), the four disclosed
integral-cohomology data the `interMatrix` intersection-form substrate consumes, together with the
Thom signature-descent and the distinguished `S²×S²`. Each field is a named theorem of the literature
(discharge tier `discharge_future`); none is an axiom.

* `fc`/`B` — the integral fundamental class `[M] ∈ H₄(M;ℤ)` and a finite free `H²(M;ℤ)` basis;
* `wu` — the Spin/Wu datum (`w₂ = 0`), giving EVENNESS of `interMatrix`;
* `pd` — integral Poincaré duality (the perfect-pairing iso), giving UNIMODULARITY of `interMatrix`;
* `sig`/`sig_eq` — the bordism-invariant signature hom (Thom) and its computation via the lattice
  signature of the intersection matrix;
* `s2s2`/`s2s2_rank`/`s2s2_hyp` — the distinguished `S²×S²` structured manifold (rank-2 hyperbolic
  intersection form), the falsifiable identity pin of the σ-presentation. -/
structure SpinSigmaAtoms where
  /-- integral fundamental class of each carrier manifold. -/
  fc : (p : StrMfd (spinEmptyData prov)) → IntFundamentalClass (TopCat.of p.1.M)
  /-- a finite free `H²(M;ℤ)` basis of each carrier manifold. -/
  B : (p : StrMfd (spinEmptyData prov)) → IntH2Basis (TopCat.of p.1.M)
  /-- Spin/Wu datum (`w₂ = 0`) — the EVEN conjunct's disclosed input. -/
  wu : (p : StrMfd (spinEmptyData prov)) → SpinWuDatum (fc p)
  /-- integral Poincaré duality — the UNIMODULAR conjunct's disclosed input. -/
  pd : (p : StrMfd (spinEmptyData prov)) → IntPoincareDuality (fc p)
  /-- the bordism-invariant signature homomorphism (Thom). -/
  sig : DataBordismGrp (spinEmptyData prov) →+ ℤ
  /-- the signature computes as the lattice signature of the intersection matrix. -/
  sig_eq : ∀ p, sig (DataBordismGrp.mk (spinEmptyData prov) p)
    = latticeSig (interMatrix (fc p) (B p))
  /-- the distinguished `S²×S²` structured manifold. -/
  s2s2 : StrMfd (spinEmptyData prov)
  /-- `S²×S²` has `b₂ = 2`. -/
  s2s2_rank : (B s2s2).rank = 2
  /-- `II(S²×S²)` is the rank-2 hyperbolic form. -/
  s2s2_hyp : ∃ N, IsHyperbolicForm N ∧ IntCongr (interMatrix (fc s2s2) (B s2s2)) N

variable {prov}

/-! ## §2. The builder — the σ-presentation from the atom bundle -/

/-- **The R-atom opener.** From the disclosed E1 atom bundle, BUILD the σ-presentation of the empty-Σ
spin carrier. The `even_unimod` field is DISCHARGED via `isEvenUnimodular_of_intPD` (spin ⟹ even, PD ⟹
unimodular) — the genuine E1 content of the reduction; `form`/`rank` are wired from `interMatrix`; the
rest is the disclosed data verbatim. This inhabits `SpinPresentationRow.R`. -/
noncomputable def spinSigmaPresentation_of_atoms (a : SpinSigmaAtoms prov) :
    SpinSigmaPresentation (spinEmptyData prov) where
  sig := a.sig
  rank p := (a.B p).rank
  form p := interMatrix (a.fc p) (a.B p)
  even_unimod p := isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p)
  sig_eq := a.sig_eq
  s2s2 := a.s2s2
  s2s2_rank := a.s2s2_rank
  s2s2_hyp := a.s2s2_hyp

/-- The built presentation's `sig` is the disclosed Thom hom (documents the wiring; `rfl`). -/
@[simp] theorem spinSigmaPresentation_of_atoms_sig (a : SpinSigmaAtoms prov) :
    (spinSigmaPresentation_of_atoms a).sig = a.sig := rfl

/-- The built presentation's `form` is the `interMatrix` of the disclosed E1 data (`rfl`). -/
theorem spinSigmaPresentation_of_atoms_form (a : SpinSigmaAtoms prov)
    (p : StrMfd (spinEmptyData prov)) :
    (spinSigmaPresentation_of_atoms a).form p = interMatrix (a.fc p) (a.B p) := rfl

/-! ## §3. The capstone — the full presentation row from the atom bundle -/

/-- **The full `SpinPresentationRow` from disclosed atoms.** With the E1 atom bundle plus the Rokhlin
`16 ∣ σ` residual and the K3-generator data (`b₂ = 22`, form `IntCongr` to `k3Form`), the WHOLE
KT §5 presentation row assembles — the R-atom is reduced to the disclosed E1 geometry. `σ(K3) = −16`
is DERIVED (`SpinPresentationRow.hg`, from `hk3` + the banked K3 lattice signature), not assumed.
Firing dA (`nonempty_dualSpinForwardDatum_of_row`) / dC (`nonempty_ktSpinPresentationDatum_of_row…`)
now needs only this bundle + their own disclosed gate inputs. -/
noncomputable def spinPresentationRow_of_atoms (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form) :
    PinPlusKTSpinPresentationRow.SpinPresentationRow prov where
  R := spinSigmaPresentation_of_atoms a
  hdvd := hdvd
  g := g
  hrank := hrank
  hk3 := hk3

/-- **`Ω₄^{Spin} ≅ ℤ` from the atom bundle (the N1a headline).** The atom bundle + Rokhlin + K3
generator, together with the two terminal Freeze-A atoms (`HandleTradeCobordism`, `HyperbolicBase`)
and Freeze B (`SphereProductBounds`), deliver the normalized-signature iso `σ = −16·e`, `e[g] = 1`.
The R-atom's E1 data reaches all the way to the spin-bordism iso, modulo exactly the frozen
manifold-topology statements (carried, not discharged). -/
theorem dataBordismGrp_equiv_int_of_atoms (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hCob : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism)
    (hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds) :
    ∃ e : DataBordismGrp (spinEmptyData prov) ≃+ ℤ,
      (∀ x, a.sig x = -16 * e x) ∧ e (DataBordismGrp.mk (spinEmptyData prov) g) = 1 :=
  dataBordismGrp_equiv_int_of_row (spinPresentationRow_of_atoms a hdvd g hrank hk3) hCob hBase hB

/-! ## §4. End-to-end — the atom bundle drives the KT §5 consumers -/

/-- **dC from atoms, overhang-free (G9-4 `KTKernelCard` route).** The E1 atom bundle plus the row's
own disclosed gate inputs — Rokhlin `hdvd`, K3-generator data (`hrank`/`hk3`), sphere-product freezes
(`hA`/`hB`), the generator image `hΦg`, and the kernel-cardinality binder `KTKernelCard` — yield the
dC datum, AVOIDING the `SectorIsGeometric` overhang (round-9 G8-5: the overhang bites only the
geometric-Φ routes). This is the terminal dC consumption reduced to the R-atom's E1 data plus the
kernel-card binder (still open, per sub-block-1: gated by `KernelReducesToSpin`, the KT §5 surgery). -/
theorem nonempty_ktSpinPresentationDatum_of_atoms_of_kernelCard (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (hcard : KTKernelCard prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  nonempty_ktSpinPresentationDatum_of_row_of_kernelCard
    (spinPresentationRow_of_atoms a hdvd g hrank hk3) hA hB hΦg hcard

/-- **dC from atoms, overhang route (G8-5 `SectorIsGeometric`).** The alternative dC leaf: the same
atom bundle + row inputs, with the G8-5 overhang `SectorIsGeometric` CONSUMED AS A HYPOTHESIS (round-9
gate), NOT discharged. -/
theorem nonempty_ktSpinPresentationDatum_of_atoms (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (hsec : SectorIsGeometric prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  nonempty_ktSpinPresentationDatum_of_row
    (spinPresentationRow_of_atoms a hdvd g hrank hk3) hA hB hΦg hsec

/-- **dA from atoms (`DualSpinForwardDatum`).** The Direction-A leaf from the atom bundle. `hfwd` (the
KT "only if", each instance a `Div32BoundingDatum` — the separate `KTSharpnessSupply` lane) and
`SpinImageCyclic` stay GATED inputs, threaded as hypotheses and NEVER discharged here (fence
`geometric-phi-does-not-close-hfwd-fakeability`); the atom bundle supplies only the σ-presentation
`R`, `g`, and the derived `σ(K3) = −16`. -/
theorem nonempty_dualSpinForwardDatum_of_atoms (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ a.sig x)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (DualSpinForwardDatum prov (spinEmptyData prov)) :=
  nonempty_dualSpinForwardDatum_of_row
    (spinPresentationRow_of_atoms a hdvd g hrank hk3) hfwd hcyc h2

end SKEFTHawking.PinPlusKTSpinSigmaAtom
