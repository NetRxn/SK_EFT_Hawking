/-
# Phase 5q.H close-out — the σ-descent's Thom atoms sharpened, and the stock-element residuals

This module continues `PinPlusKTSpinSigmaAtomReduce`. Two honest jobs:

## §1–§2. The σ-descent additivity input REDUCED to a single geometric atom

`sigDescend` (reduce §5) descends a per-manifold local signature to a bordism-invariant hom given the
two classical Thom inputs `hbord` (bordism-invariance — the deep half) and `hadd` (additivity under
`⊔`). This module DISCHARGES the additivity plumbing of `hadd` down to exactly ONE geometric atom:
the disjoint-union intersection form is integer-CONGRUENT to the block sum of the summand forms
(`interMatrix (p ⊔ q) ≅ interMatrix p ⊕ interMatrix q`). The lattice half — `latticeSig` is additive
under a block-congruent sum of even-unimodular blocks — is PROVEN here from
`latticeSig_blockDiag` + `IntCongr.latticeSig` + reindex-invariance. So after this module the σ-descent's
`sig`/`sig_eq` pair reduces to just `hbord` (deep Thom) + `hblock` (elementary block geometry), with all
the `latticeSig` bookkeeping discharged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
import SKEFTHawking.SpinSigmaGenerator
import SKEFTHawking.SphereWitnessFiringUncondInt
import SKEFTHawking.SphereProdCrossInt

namespace SKEFTHawking.PinPlusKTSpinSigmaStock

open scoped Manifold
open SKEFTHawking SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.SphereWitnessTowerInt (SphereFour sphere4IntH2Basis)
open SKEFTHawking.SphereFourOrientationDataInt (sphere4IntOrientationDataUncond)

/-! ## §1. The lattice half of Thom additivity — `latticeSig` is additive under a block-congruent sum -/

/-- **`latticeSig` is additive across a block-congruent decomposition.** If a rank-`n` integer form
`Mpq` is integer-congruent (after the rank relabelling `n = np + nq`) to the block-diagonal sum of two
even-unimodular forms `Mp`, `Mq`, then `σ(Mpq) = σ(Mp) + σ(Mq)`. Pure lattice content: reindex-invariance
of `latticeSig` (`latticeSigOf_reindex`), Sylvester congruence-invariance (`IntCongr.latticeSig`), and
block additivity (`latticeSig_blockDiag`). This is the lattice half of the Thom signature's disjoint-union
additivity — the geometric half (that the intersection form of `M ⊔ N` IS the block sum up to congruence)
stays a disclosed atom. -/
theorem latticeSig_of_blockCongr {n np nq : ℕ} (hn : n = np + nq)
    (Mpq : Matrix (Fin n) (Fin n) ℤ) (Mp : Matrix (Fin np) (Fin np) ℤ)
    (Mq : Matrix (Fin nq) (Fin nq) ℤ)
    (heuP : IsEvenUnimodular Mp) (heuQ : IsEvenUnimodular Mq)
    (hcong : IntCongr (Matrix.reindex (finCongr hn) (finCongr hn) Mpq) (blockDiag Mp Mq)) :
    latticeSig Mpq = latticeSig Mp + latticeSig Mq := by
  have hre : latticeSig (Matrix.reindex (finCongr hn) (finCongr hn) Mpq) = latticeSig Mpq := by
    rw [← latticeSigOf_fin, ← latticeSigOf_fin Mpq, latticeSigOf_reindex]
  have hcg : latticeSig (blockDiag Mp Mq)
      = latticeSig (Matrix.reindex (finCongr hn) (finCongr hn) Mpq) := IntCongr.latticeSig hcong
  rw [← hre, ← hcg, latticeSig_blockDiag Mp Mq heuP heuQ]

/-! ## §2. The σ-descent additivity input, discharged for the atom bundle -/

variable (prov : CharPairWProviderPerOp (𝓡 4) 0)

/-- **The geometric block-sum atom of the atom bundle** — the ONLY residual of Thom additivity after the
lattice bookkeeping (§1) is discharged. For the disclosed atom bundle `a`, the intersection matrix of a
disjoint union `p ⊔ q` is integer-CONGRUENT (after the rank relabelling
`b₂(p ⊔ q) = b₂(p) + b₂(q)`) to the block sum of the summands' intersection matrices. This is elementary
manifold geometry (`II(M ⊔ N) = II(M) ⊕ II(N)`), the counterpart of the deep bordism-invariance half;
it is NOT discharged in-tree (no manifold cohomology in Mathlib) but is named here explicitly as the
single geometric input `hadd` reduces to. -/
def InterMatrixBlockAtom (a : SpinSigmaAtoms prov) : Prop :=
  ∀ p q : StrMfd (spinEmptyData prov),
    ∃ hn : (a.B ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩).rank
        = (a.B p).rank + (a.B q).rank,
      IntCongr (Matrix.reindex (finCongr hn) (finCongr hn)
          (interMatrix (a.fc ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩)
            (a.B ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩)))
        (blockDiag (interMatrix (a.fc p) (a.B p)) (interMatrix (a.fc q) (a.B q)))

variable {prov}

/-- **Thom additivity for the atom bundle, discharged from the block atom.** For the atom bundle `a`, the
per-manifold lattice signature `p ↦ σ(II p)` is additive under `⊔` — the `hadd` input of `sigDescend` —
given ONLY the geometric block-sum atom `hblock`. The even-unimodularity of each summand form (needed by
the lattice half §1) is FREE from the bundle's own `wu`/`pd` fields
(`isEvenUnimodular_of_intPD`). So the σ-descent's additivity plumbing is completely discharged; only the
block atom survives as an input. -/
theorem sigAdditivity_atoms_of_blockCongr (a : SpinSigmaAtoms prov)
    (hblock : InterMatrixBlockAtom prov a) (p q : StrMfd (spinEmptyData prov)) :
    latticeSig (interMatrix (a.fc ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩)
        (a.B ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩))
      = latticeSig (interMatrix (a.fc p) (a.B p)) + latticeSig (interMatrix (a.fc q) (a.B q)) := by
  obtain ⟨hn, hcong⟩ := hblock p q
  exact latticeSig_of_blockCongr hn _ _ _
    (isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p))
    (isEvenUnimodular_of_intPD (a.fc q) (a.B q) (a.wu q) (a.pd q)) hcong

/-- **The σ-presentation's `sig`/`sig_eq` pair, rebuilt from its two irreducible Thom atoms.** Given the
atom bundle `a`, the deep bordism-invariance atom `hbord` (Novikov additivity / signature-vanishes-on-
boundaries — the genuinely hard half of Thom), and the elementary geometric block atom `hblock`, the
bordism-invariant signature homomorphism `Ω → ℤ` is BUILT (via `sigDescend`), with all `latticeSig`
plumbing discharged. This is the sharpest honest reduction of the σ-descent: its `sig` field is exactly
`hbord + hblock`, nothing else. -/
noncomputable def sigThomOfAtoms (a : SpinSigmaAtoms prov)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (a.fc p) (a.B p)) = latticeSig (interMatrix (a.fc q) (a.B q)))
    (hblock : InterMatrixBlockAtom prov a) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  sigDescend prov (fun p => latticeSig (interMatrix (a.fc p) (a.B p))) hbord
    (sigAdditivity_atoms_of_blockCongr a hblock)

/-- **The rebuilt Thom hom computes the lattice signature on classes** (`rfl`) — this IS the `sig_eq`
obligation of `SpinSigmaPresentation`, so the `sigThomOfAtoms` hom is a drop-in for the disclosed
`a.sig`, exhibiting the σ-descent's `sig`/`sig_eq` reduced to `hbord + hblock`. -/
@[simp] theorem sigThomOfAtoms_mk (a : SpinSigmaAtoms prov)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (a.fc p) (a.B p)) = latticeSig (interMatrix (a.fc q) (a.B q)))
    (hblock : InterMatrixBlockAtom prov a) (p : StrMfd (spinEmptyData prov)) :
    sigThomOfAtoms a hbord hblock (DataBordismGrp.mk (spinEmptyData prov) p)
      = latticeSig (interMatrix (a.fc p) (a.B p)) :=
  rfl

/-! ## §3. The S⁴ stock element's integral-topology residual (the natural spin sphere) -/

/-- **The integral orientation of `S⁴`.** The unconditional S⁴ orientation datum
(`sphere4IntOrientationDataUncond`, the choice-absorbing global section from `H₄(S⁴;ℤ) ≅ ℤ`) already
carries exactly the two `IntOrientation` fields — the integral fundamental class `[S⁴] ∈ H₄(S⁴;ℤ)` and
the mod-2 reduction compatibility — so it repackages directly to `IntOrientation S⁴`. This is the
`orient` atom of the S⁴ spin-sphere package, discharged from theorem-backed geometry (no freeze). -/
noncomputable def sphere4IntOrientation : IntOrientation SphereFour :=
  ⟨sphere4IntOrientationDataUncond.fundClass, sphere4IntOrientationDataUncond.redCompat⟩

/-- **`H²(S⁴;ℤ)` is trivial** — the second integral cohomology of `S⁴` is a subsingleton (`b₂(S⁴) = 0`),
the fact behind the rank-0 basis `sphere4IntH2Basis`. Extracted here for the S⁴ Poincaré-duality
construction. -/
instance sphere4_cohomology2_subsingleton :
    Subsingleton (Cohomology (TopCat.of SphereFour) 2) :=
  ⟨fun _ _ => sphere4IntH2Basis.basis.ext_elem (fun i => i.elim0)⟩

/-- **The integral Poincaré duality of `S⁴`.** Since `H²(S⁴;ℤ) = 0`, the perfect-pairing isomorphism
`H²(S⁴;ℤ) ≃ₗ[ℤ] Dual ℤ (H²(S⁴;ℤ))` is the (unique) equivalence of trivial modules, and its pairing
condition `PD a b = ⟨a ∪ b, [S⁴]⟩` holds because every `a` is `0`. This is the degenerate-but-honest
`pd` atom of the S⁴ package — the UNIMODULAR input, realized at rank 0. -/
noncomputable def sphere4IntPoincareDuality :
    IntPoincareDuality (intFundamentalClassOfIntOrientation sphere4IntOrientation) where
  toDualEquiv :=
    { toFun := fun _ => 0
      map_add' := fun _ _ => Subsingleton.elim _ _
      map_smul' := fun _ _ => Subsingleton.elim _ _
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  toDualEquiv_apply := fun a b => by
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    show (0 : Module.Dual ℤ _) b = interFormInt _ 0 b
    rw [map_zero, LinearMap.zero_apply]

/-- **The S⁴ package data feeds the PROVEN unconditional Rokhlin leg `16 ∣ σ(S⁴)`.** The integral
intersection form of `S⁴` on the package's orientation (`sphere4IntOrientation`) and basis
(`sphere4IntH2Basis`) is `16`-divisible — the zero-binder firing
`sixteen_dvd_latticeSig_sphere4_unconditional`, applied verbatim (the package's fundamental class is
definitionally the unconditional witness's). Ties the S⁴ spin-sphere package's `orient`/`B` atoms to the
`Ω₄^{Spin}` Rokhlin `hdvd` input at the S⁴ class — the value is `16 ∣ 0` (`b₂(S⁴) = 0`), but the WHOLE
orientation → intersection form → even-unimodular → σ÷16 pipeline fires on the package's own data. -/
theorem sphere4_pkg_sixteen_dvd_latticeSig :
    (16 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfIntOrientation sphere4IntOrientation) sphere4IntH2Basis) :=
  SKEFTHawking.SphereWitnessFiringUncondInt.sixteen_dvd_latticeSig_sphere4_unconditional

/-! ## §4. The S²×S² stock element's s2s2 witness (functional level) + the orientation gap

The distinguished `S²×S²` is the presentation's `s2s2` normalization witness (rank-2 hyperbolic form
`II(S²×S²) = H`). Its integral-homology arc is COMPUTED in-tree: `H₁ = 0`, `H₂ ≅ ℤ²` with a computed
rank-2 basis (`sphereProdIntH2Basis`), the honest fundamental class `sphereProdIntFundClassHonest`
(`H₄ ≅ ℤ`). The `s2s2_hyp` field shape is discharged from the **Gram pin** `interMatrix fc B = H`
below — but **the pin is no longer the residual**: the S²×S² intersection form is now known
UNCONDITIONALLY to be integrally congruent to `Hyp` itself (`SphereProdBasisIdInt`, downstream of
this module), and the hypothesis-free replacements for every `*_of_gram` consumer below live in
`SphereProdGramPinRetire` (§2 there). See the `SphereProdGramPin` docstring for what remains.

**The orientation gap (an honest per-element-vs-total-function boundary instance).** Unlike `S⁴` (which
carries the unconditional orientation datum `sphere4IntOrientationDataUncond` — §3), the S²×S² arc
supplies its `[M]` at the *functional* level (`IntFundamentalClass SphereProdT`, from the MV homology
computation) but NOT as an `IntOrientation SphereProdT` (its `redCompat` mod-2 comparison is not
in-tree). So the S²×S² data populates the TOTAL bundle `SpinSigmaAtoms`' `fc`/`s2s2` slots (functional,
no `Nonempty`/orientation needed) — NOT the per-element `SpinSigmaAtomPkg` (whose `orient` field would
require an `IntOrientation`). This is exactly the vacuity-boundary asymmetry the reduce module's dissolve
identifies: the s2s2 witness lives at the `SpinSigmaAtoms` functional level, not the `IntOrientation`-
carrying package level. -/

open SKEFTHawking.SphereWitnessTowerInt
  (SphereProdT SphereProdHData sphereProdHDataComputed sphereProdIntH2Basis
   sphereProd_interMatrix_evenUnimodular_of_gram sphereProd_interMatrix_latticeSig_of_gram)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)

/-- **The S²×S² Gram-pin slot — RETIRED, not a geometric residual.** The literal matrix equality
`II(S²×S²) = H` (`= sphereProdFormDatum`) on the computed rank-2 basis, kept as the hypothesis shape
of the `*_of_gram` consumers below.

**This is no longer a disclosed geometric atom.** The Künneth/EZ content it stood in for IS in tree
and unconditional: `SphereProdBasisIdInt.sphereProd_interMatrix_intCongr_hyp` (the MV cup–Stokes peel
`SphereProdHemiUnitInt.hcross_pm` + the basis-ID `crossFamily_basis_intCongr`) proves the intersection
matrix integrally CONGRUENT to `Hyp` itself, with no hypotheses. Every consumer of this pin concludes
something congruence-invariant, so the congruence supersedes it; the hypothesis-free forms are
`SphereProdGramPinRetire.sphereProd_s2s2_{hyp,evenUnimodular,latticeSig,htopo}'`.

What the literal equality asks for BEYOND the congruence is a basis normalization, not geometry, and
is provably NOT available in tree: `SphereProdGramPinRetire.sphereProdGramPin_iff` computes the exact
computed-basis Gram (`!![-(2sυε), υε; υε, 0]`) and shows this Prop holds iff `s = 0` and `υ·ε = 1` —
where `s` is the α-coordinate of the `Exists.choose` split generator `deltaGen` (choice-dependent
modulo `sumInto`) and `υ`, `ε` are pinned only as units. So the pin is retired at the consumer level
rather than proved. -/
abbrev SphereProdGramPin : Prop :=
  interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis = sphereProdFormDatum

/-- **The S²×S² `s2s2_hyp` witness, assembled from the Gram pin.** Given the Gram-pin atom, the honest
fundamental class + computed rank-2 basis deliver the `∃ N, IsHyperbolicForm N ∧ IntCongr (II) N` shape
— exactly the `s2s2_hyp` field of `SpinSigmaAtoms` / `SpinSigmaPresentation`, now stated for the CONCRETE
product intersection matrix (`interMatrix (honest fc) (computed B)`), not the abstract
`sphereProdFormDatum`. **Superseded**: `SphereProdGramPinRetire.sphereProd_s2s2_hyp'` proves the same
conclusion with NO hypothesis. -/
theorem sphereProd_s2s2_hyp_of_gram (hgram : SphereProdGramPin) :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis) N := by
  obtain ⟨N, hN, hcong⟩ := sphereProdFormDatum_hyp_pin
  exact ⟨N, hN, by rw [hgram]; exact hcong⟩

/-- **The S²×S² intersection matrix is even unimodular under the Gram pin** — the concrete
`even_unimod` obligation at the distinguished `s2s2`, from `sphereProd_interMatrix_evenUnimodular_of_gram`.
Confirms the s2s2 sector's even-unimodularity is realized by the computed product data (modulo the pin),
consistent with the S⁴ pipeline. **Superseded**:
`SphereProdGramPinRetire.sphereProd_s2s2_evenUnimodular'` proves it with NO hypothesis. -/
theorem sphereProd_s2s2_evenUnimodular_of_gram (hgram : SphereProdGramPin) :
    IsEvenUnimodular (interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis) :=
  sphereProd_interMatrix_evenUnimodular_of_gram sphereProdHDataComputed sphereProdIntFundClassHonest hgram

/-- **`b₂(S²×S²) = 2`** — the `s2s2_rank` obligation at the distinguished witness (`rfl`, the computed
rank-2 basis). -/
theorem sphereProd_s2s2_rank : sphereProdIntH2Basis.rank = 2 := rfl

/-! ## §5. The per-element package realizes the presentation, and the K3 row fires

The row builder `spinPresentationRow_of_atoms` consumes the TOTAL-function `SpinSigmaAtoms` bundle (the
disclosed E1 object, which stays non-vacuous precisely because its fields are functional-level —
`IntFundamentalClass`, not `IntOrientation`). The per-element `SpinSigmaAtomPkg` (which carries the
`Nonempty`-requiring `IntOrientation`) cannot assemble the total bundle (the empty element obstructs
`orient` — the vacuity boundary). What the package DOES do is REALIZE, by genuine per-manifold disclosed
geometry, the bundle's even-unimodular obligation at its element — the honest per-element↔total bridge. -/

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **The per-element package realizes the presentation's even-unimodular obligation at its element.**
If the disclosed total bundle `a`'s fundamental class at `p` is the package's (from its orientation),
then the presentation's `even_unimod p` — an `IsEvenUnimodular` on the `interMatrix` — is discharged by
the package's own `orient` + `pd` via the reduce module's dissolve
(`isEvenUnimodular_of_orientation_pd_emptySigma`: the EVEN conjunct from the orientation + the empty
membrane's Wu certificate, the UNIMODULAR conjunct from `pd`, which works for the bundle's basis `a.B p`
directly). This is the honest content of "the package inhabits the presentation at its sector": the
abstract bundle's obligation at `p` is discharged by concrete disclosed geometry, not assumed. -/
theorem pkg_realizes_even_unimod (a : SpinSigmaAtoms prov)
    {p : StrMfd (spinEmptyData prov)} [T2Space p.1.M] [Nonempty p.1.M]
    (pkg : SpinSigmaAtomPkg prov p)
    (hfc : a.fc p = intFundamentalClassOfIntOrientation pkg.orient) :
    IsEvenUnimodular ((spinSigmaPresentation_of_atoms a).form p) := by
  rw [spinSigmaPresentation_of_atoms_form, hfc]
  exact isEvenUnimodular_of_orientation_pd_emptySigma prov p pkg.orient (a.B p) pkg.pd

/-- **A K3-realizing spin element — a HYPOTHESIS, conditional-on-existence (NOT fabricated).** There is
no in-tree K3 manifold (Mathlib has no algebraic-surface / complex-geometry machinery), so the σ = −16
generator of `Ω₄^{Spin}` is carried as disclosed data, exactly as `SpinPresentationRow` already carries
its `g`. This bundles, relative to the disclosed total bundle `a`, a generator element `g` together with
its per-element E1 package `pkg` (the concrete `orient`/`B`/`pd`), the agreement of `a` with `pkg` at `g`,
and the two K3-generator data: `b₂(g) = 22` and its intersection form integer-congruent to `k3Form`
(`II(K3) = 2(−E₈) ⊕ 3H`, σ = −16). ANY future K3-realizing element (supplying its orientation/basis/PD)
instantiates this and plugs into the row. -/
structure K3RealizingElement (a : SpinSigmaAtoms prov) where
  /-- The K3-class generator element (disclosed — no in-tree K3 manifold). -/
  g : StrMfd (spinEmptyData prov)
  /-- The generator manifold is Hausdorff. -/
  [t2 : T2Space g.1.M]
  /-- The generator manifold is nonempty (a genuine closed spin 4-manifold). -/
  [ne : Nonempty g.1.M]
  /-- The generator's per-element E1 package (concrete orientation/basis/PD). -/
  pkg : SpinSigmaAtomPkg prov g
  /-- The total bundle's fundamental class at `g` is the package's (from its orientation). -/
  hfc : a.fc g = intFundamentalClassOfIntOrientation pkg.orient
  /-- The total bundle's `H²` basis at `g` is the package's. -/
  hB : a.B g = pkg.B
  /-- `b₂(K3) = 22`. -/
  hrank : (a.B g).rank = 22
  /-- The intersection form is integer-congruent to `k3Form` (σ(K3) = −16). -/
  hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
    (interMatrix (a.fc g) (a.B g))) k3Form

/-- **The presentation row FIRES from a K3-realizing element** (given the disclosed bundle + Rokhlin
`16 ∣ σ`). The K3 element's rank/congruence data are stated directly against the bundle's `g`-slot
(`a.fc g`/`a.B g`), so they ARE the `spinPresentationRow_of_atoms` inputs — no transport needed. Its
`pkg`/`hfc`/`hB` fields witness that this generator slot is realized by concrete disclosed geometry
(orientation/basis/PD), NOT merely assumed. -/
noncomputable def K3RealizingElement.presentationRow (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x) (k : K3RealizingElement a) :
    SpinPresentationRow prov :=
  spinPresentationRow_of_atoms a hdvd k.g k.hrank k.hk3

/-- **`Ω₄^{Spin} ≅ ℤ` from a K3-realizing element** (the N1a headline, modulo the two terminal Freeze-A
manifold-topology atoms + Freeze B). The disclosed bundle + Rokhlin + the K3-realizing element deliver
the normalized-signature iso `σ = −16·e`, `e[g] = 1`, with the generator slot realized by the element's
concrete package. This is the row-fires corollary on the inhabited (K3) sector. -/
theorem K3RealizingElement.dataBordismGrp_equiv_int (a : SpinSigmaAtoms prov)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x) (k : K3RealizingElement a)
    (hCob : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism)
    (hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase)
    (hSB : (spinSigmaPresentation_of_atoms a).SphereProductBounds) :
    ∃ e : DataBordismGrp (spinEmptyData prov) ≃+ ℤ,
      (∀ x, a.sig x = -16 * e x) ∧ e (DataBordismGrp.mk (spinEmptyData prov) k.g) = 1 :=
  dataBordismGrp_equiv_int_of_atoms a hdvd k.g k.hrank k.hk3 hCob hBase hSB

end SKEFTHawking.PinPlusKTSpinSigmaStock
