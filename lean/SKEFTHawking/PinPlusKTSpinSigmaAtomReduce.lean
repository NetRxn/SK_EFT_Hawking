/-
# Phase 5q.H close-out (R-atom SUPPLY) — the E1 atom DISSOLVE for the empty-Σ spin carrier

`PinPlusKTSpinSigmaAtom.SpinSigmaAtoms` bundles, per structured manifold of `spinEmptyData prov`,
FOUR disclosed E1 data — `fc` (integral fundamental class), `B` (`H²(M;ℤ)` free basis), `wu`
(`SpinWuDatum`, the EVEN input) and `pd` (`IntPoincareDuality`, the UNIMODULAR input) — plus the Thom
signature descent and the `S²×S²` witness. This module gives the HONEST re-triage of that bundle: how
much of it the in-tree integral-topology stack reaches GENERICALLY vs what is irreducibly per-manifold.

## The dissolve (verified here, kernel-pure)

* **`wu` and `fc` are NOT independent atoms.** For a closed *connected nonempty* spin 4-manifold the
  `SpinWuDatum` is a THEOREM: `SpinWuDatumClosed.spinWuDatum_of_closed` builds it from an integral
  orientation `o` (which also yields `fc = intFundamentalClassOfIntOrientation o`) plus the mod-2 spin
  certificate `wuClass2 (poincareDual4Mid_of_closed) = 0`; the PD-mid frame `poincareDual4Mid_of_closed`
  is hypothesis-free (5q.G X6). So `wu`/`fc` reduce to `IntOrientation` + the spin certificate.

* **On the empty-Σ carrier the spin certificate is CARRIED BY CONSTRUCTION** (`spinCert_of_emptySigma`).
  The carrier's own bundle field `CharPairStrBundled.hchar` states `⟨a, emb₊[Σ]⟩ = μ(a ∪ a)`. Because
  the spin sector is the *strictly geometric* empty-characteristic-surface form (`IsEmpty σ.surf.M`),
  the surface class pushes forward to `0` (`emptySigma_surfClass_eq_zero`: `H₂(∅) = 0`), so `hchar`
  collapses to `μ(a ∪ a) = 0` for all `a` — exactly the vanishing of the Wu functional, i.e.
  `wuClass2 (poincareDual4Mid_of_closed) = 0`. The empty membrane IS the spin condition `w₂ = 0`; the
  disclosed `wu` atom's spin content costs nothing beyond the carrier it already lives on.

So the GENUINE per-manifold residual of the four E1 atoms is only THREE, and it is per *nonempty*
element: `IntOrientation p.1.M` (⟹ `fc`), the `H²(M;ℤ)` free basis `IntH2Basis`, and the integral
Poincaré-duality perfect pairing `IntPoincareDuality`. The `SpinWuDatum` (evenness/Wu) is derived from
the orientation + the carrier's free spin bit (`isEvenUnimodular_of_orientation_pd_emptySigma`).

## Why this dissolve does NOT collapse the TOTAL-FUNCTION `SpinSigmaAtoms` bundle (the vacuity boundary)

The generic Wu/PD producers require `[T2Space M] [Nonempty M]`. `T2Space p.1.M` is available per element
(the bundle's own `CharPairStr.t2` field), but `Nonempty p.1.M` genuinely FAILS on the empty manifold,
which is an element of the carrier (`DataBordismGrp.zero`). A total-function reduced bundle that carried
an `IntOrientation p.1.M` — or any datum whose very *type* mentions `Nonempty p.1.M` — for EVERY
`p : StrMfd` would therefore be VACUOUS (uninhabitable on the empty element). `SpinSigmaAtoms` stays
non-vacuous precisely because its fields live at the `TopCat`/functional level (`IntFundamentalClass X`,
`SpinWuDatum fc`) which needs no `Nonempty`. Hence the dissolve is intrinsically **per-nonempty-element**
and the correct architecture for consuming it is the PROVIDER pattern — atoms attached to the elements
that are genuine nonempty closed spin 4-manifolds (`SpinSigmaAtomPkg`), NOT a total-function reduction.
The per-element package's inhabitation on the stock manifolds (S⁴, S²×S², K3) is stated as the residual
(§4). This distinction is data-carrying, NOT grade-fabricating (fence `synthetic-grade-ker-bot-nogo`):
the package carries genuine disclosed E1 geometry per manifold, it does not manufacture a free grade.

Dimension discipline: this lives entirely on `spinEmptyData prov` — CLOSED SPIN 4-manifolds `M`
(`ChartedSpace (EuclideanSpace ℝ (Fin (2+2))) M`, `CompactSpace`) with empty characteristic surface
(Σ = ∅); integral (co)homology in degrees 0–4; the intersection form on `H²(M;ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaAtom
import SKEFTHawking.SpinWuDatumClosed
import SKEFTHawking.SingularPD4Instances
import SKEFTHawking.PinPlusCharPairSurfaceTie

namespace SKEFTHawking.PinPlusKTSpinSigmaAtomReduce

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairBorTethered SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SpinWuDatumClosed
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.SingularCohomologyMod2

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The empty-Σ carrier carries the spin (Wu) certificate BY CONSTRUCTION -/

/-- **The empty-Σ surface class vanishes.** For a spin-side structured manifold `p` (whose bundle
carries `IsEmpty p.2.val.surf.M`), the mod-2 surface fundamental class `[Σ] ∈ H₂(Σ;ℤ/2)` is `0` —
`H₂` of an empty space is a subsingleton (`PinPlusCharPairSurfaceTie.subsingleton_homology`). This is
the seed of the spin condition: an empty characteristic surface has no Poincaré-dual cup-square. -/
theorem emptySigma_surfClass_eq_zero (p : StrMfd (spinEmptyData prov)) :
    p.2.val.surfClass = 0 := by
  haveI : IsEmpty p.2.val.surf.M := p.2.property
  exact Subsingleton.elim _ _

/-- **The spin (Wu) certificate is carried by the empty-Σ structure** — for a *nonempty* (`T2`) spin-side
carrier `p`, `wuClass2 (poincareDual4Mid_of_closed) = 0` (equivalently `w₂ = 0` on the oriented
4-manifold, i.e. `M` is Spin). Proof: the bundle's `hchar` field reads `⟨a, emb₊[Σ]⟩ = μ(a ∪ a)`, and
`emb₊[Σ] = 0` since `[Σ] = 0` (`emptySigma_surfClass_eq_zero`); hence the Wu functional
`a ↦ μ(a ∪ a)` vanishes, so its Poincaré-dual representative `v₂ = wuClass2` is `0`. The `[Nonempty]`
hypothesis is essential (the empty manifold has no fundamental class and no spin structure to certify);
`[T2Space]` is supplied at call sites from the bundle's own `CharPairStr.t2` field. -/
theorem spinCert_of_emptySigma (p : StrMfd (spinEmptyData prov))
    [T2Space p.1.M] [Nonempty p.1.M] :
    wuClass2 (poincareDual4Mid_of_closed (M := p.1.M)) = 0 := by
  have hchar := p.2.val.hchar
  have hzero : ∀ a : SingularCohomologyMod2.Cohomology (TopCat.of p.1.M) 2,
      (poincareDual4Mid_of_closed (M := p.1.M)).mu (cupH24 a a) = 0 := by
    intro a
    have h := hchar a
    rw [emptySigma_surfClass_eq_zero prov p, map_zero, map_zero] at h
    exact h.symm
  have hwf : wuFunctional (poincareDual4Mid_of_closed (M := p.1.M)) = 0 := by
    ext a
    show (poincareDual4Mid_of_closed (M := p.1.M)).mu (cupSquare2ₗ a) = 0
    rw [show cupSquare2ₗ a = cupH24 a a from rfl]
    exact hzero a
  rw [wuClass2, hwf, Equiv.symm_apply_eq]
  exact (map_zero (pairing (poincareDual4Mid_of_closed (M := p.1.M)))).symm

/-! ## §2. The `wu`/`fc` atoms DISSOLVE — `SpinWuDatum` from an orientation alone -/

/-- **The `SpinWuDatum` (EVEN) atom is a THEOREM from an orientation alone, on the empty-Σ carrier.**
Given a *nonempty* (`T2`) spin-side carrier `p` and an integral orientation `o : IntOrientation p.1.M`,
the full `SpinWuDatum (intFundamentalClassOfIntOrientation o)` is built — the orientation supplies `fc`
and the ℤ→ℤ/2 evaluation compatibility, and the spin certificate is the carrier's own
(`spinCert_of_emptySigma`). So the disclosed `wu` atom of `SpinSigmaAtoms` reduces to just the
orientation; its spin content is free on this carrier. This is DATA-carrying (the orientation is genuine
disclosed geometry), NOT grade-fabrication (fence `synthetic-grade-ker-bot-nogo`). -/
noncomputable def spinWuDatum_of_emptySigma (p : StrMfd (spinEmptyData prov))
    [T2Space p.1.M] [Nonempty p.1.M] (o : IntOrientation p.1.M) :
    SpinWuDatum (intFundamentalClassOfIntOrientation o) :=
  spinWuDatum_of_closed o (spinCert_of_emptySigma prov p)

/-! ## §3. Reduced even-unimodular — the `wu`-input eliminated (orientation + PD only) -/

/-- **`IsEvenUnimodular (interMatrix)` on the empty-Σ carrier from JUST an orientation + integral PD.**
The even-unimodular hypothesis the DONE lattice `σ÷16` leg consumes, reduced on the spin carrier to
exactly TWO disclosed geometric data — the integral orientation `o` (⟹ `fc` and, with the carrier's
free spin bit, the EVEN conjunct via `spinWuDatum_of_emptySigma`) and the integral Poincaré-duality
perfect pairing `PD` (⟹ the UNIMODULAR conjunct). The `SpinWuDatum` input of
`SingularCohomologyInt.isEvenUnimodular_of_intPD` is now DERIVED, not disclosed: three of the four E1
atoms (`fc`, `wu`, and the symmetric conjunct) collapse onto the orientation + the empty membrane. -/
theorem isEvenUnimodular_of_orientation_pd_emptySigma (p : StrMfd (spinEmptyData prov))
    [T2Space p.1.M] [Nonempty p.1.M] (o : IntOrientation p.1.M)
    (B : IntH2Basis (TopCat.of p.1.M))
    (PD : IntPoincareDuality (intFundamentalClassOfIntOrientation o)) :
    IsEvenUnimodular (interMatrix (intFundamentalClassOfIntOrientation o) B) :=
  isEvenUnimodular_of_intPD _ B (spinWuDatum_of_emptySigma prov p o) PD

/-! ## §4. The provider pattern — the per-element atom package (the enriched sector shape) -/

/-- **The reduced per-element E1 atom package for the empty-Σ spin carrier** — the enriched-sector shape
(cf. `CharPairStrBundled` carrying its `basis`/`hpolar`, and the collar-fork provider carrying `[W,∂W]`
data). Attaches to ONE *nonempty* (`T2`) structured manifold `p` its genuine per-manifold E1 residual —
and ONLY that residual:

* `orient` — an integral orientation `IntOrientation p.1.M` (the `fc = [M]`/orientation datum);
* `B` — the finite free `H²(M;ℤ)` basis;
* `pd` — the integral Poincaré-duality perfect-pairing iso.

The `wu`/`SpinWuDatum` (EVEN) atom is DELIBERATELY ABSENT — it is derived from `orient` + the carrier's
own empty-membrane spin bit (`spinWuDatum_of_emptySigma`), the dissolve of §1–§3. So the package carries
three disclosed data where the flat `SpinSigmaAtoms` carried four.

The substantive load sits in the atoms' inhabitation, NOT in the package's mere shape (preemptive-
strengthening: no defining-the-conclusion). The package's *type* mentions `IntOrientation p.1.M`, which
requires `[Nonempty p.1.M]`; that is exactly why it must be a per-*nonempty*-element provider and canNOT
be a total function over `StrMfd` (the empty carrier obstructs — the vacuity boundary, module docstring). -/
structure SpinSigmaAtomPkg (p : StrMfd (spinEmptyData prov))
    [T2Space p.1.M] [Nonempty p.1.M] where
  /-- The integral orientation of the carrier manifold (yields `fc = [M]`). -/
  orient : IntOrientation p.1.M
  /-- The finite free `H²(M;ℤ)` basis. -/
  B : IntH2Basis (TopCat.of p.1.M)
  /-- The integral Poincaré-duality perfect-pairing iso (the UNIMODULAR input). -/
  pd : IntPoincareDuality (intFundamentalClassOfIntOrientation orient)

/-- **The package delivers the even-unimodular intersection matrix** — `SpinSigmaAtomPkg`'s three
disclosed atoms build `IsEvenUnimodular (interMatrix)` with the `SpinWuDatum` derived (§3). This is the
even-unimodular presentation the σ-route (`SpinSigmaPresentation.even_unimod`) needs on the class `p`,
supplied from the reduced package. -/
theorem SpinSigmaAtomPkg.isEvenUnimodular {p : StrMfd (spinEmptyData prov)}
    [T2Space p.1.M] [Nonempty p.1.M] (a : SpinSigmaAtomPkg prov p) :
    IsEvenUnimodular (interMatrix (intFundamentalClassOfIntOrientation a.orient) a.B) :=
  isEvenUnimodular_of_orientation_pd_emptySigma prov p a.orient a.B a.pd

/-! ## §5. The Thom σ-descent opener — `sig`/`sig_eq` from the two bordism-invariance atoms

The σ-presentation's `sig : DataBordismGrp ξ →+ ℤ` and `sig_eq` fields are disclosed as the Thom
signature theorem. This section OPENS that atom: it descends any per-manifold *local* signature
`sigLocal : StrMfd ξ → ℤ` to the bordism group, isolating the exact two classical inputs. -/

/-- **The Thom σ-descent** (on the empty-Σ spin carrier `spinEmptyData prov`). A per-manifold *local*
signature `sigLocal : StrMfd (spinEmptyData prov) → ℤ` descends to a bordism-invariant additive
homomorphism `DataBordismGrp (spinEmptyData prov) →+ ℤ` given EXACTLY the two classical Thom inputs:

* `hbord` — **bordism-invariance** of the signature (`IsDataBordant p q → σ(p) = σ(q)`): the Novikov-
  additivity / signature-vanishes-on-boundaries content, the genuinely deep half of Thom's theorem;
* `hadd` — **additivity of the signature under disjoint union** (`σ(p ⊔ q) = σ(p) + σ(q)`): elementary
  (the intersection form of `M ⊔ N` is the block sum `II(M) ⊕ II(N)`).

Everything else — the descent through the `Quot`, the `AddMonoidHom` structure — is kernel-pure plumbing
(`Quot.lift` + `AddMonoidHom.mk'`, with `map_zero` free from the group structure). This names the σ-atom's
two irreducible pieces and reduces the disclosed `SpinSigmaPresentation.sig` field to them. -/
noncomputable def sigDescend (sigLocal : StrMfd (spinEmptyData prov) → ℤ)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q → sigLocal p = sigLocal q)
    (hadd : ∀ p q : StrMfd (spinEmptyData prov),
      sigLocal ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩ = sigLocal p + sigLocal q) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  AddMonoidHom.mk' (Quot.lift sigLocal hbord) (by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    show sigLocal ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩ = sigLocal p + sigLocal q
    exact hadd p q)

/-- **The descended signature computes on classes** — `sigDescend sigLocal … [p] = sigLocal p` (`rfl`).
When `sigLocal p := latticeSig (form p)`, this IS the σ-presentation's `sig_eq` field: the descended
`sig` evaluated on `[p]` returns the lattice signature of `p`'s intersection matrix, automatically. -/
@[simp] theorem sigDescend_mk (sigLocal : StrMfd (spinEmptyData prov) → ℤ)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q → sigLocal p = sigLocal q)
    (hadd : ∀ p q : StrMfd (spinEmptyData prov),
      sigLocal ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩ = sigLocal p + sigLocal q)
    (p : StrMfd (spinEmptyData prov)) :
    sigDescend prov sigLocal hbord hadd (DataBordismGrp.mk (spinEmptyData prov) p) = sigLocal p :=
  rfl

/-- **`sig_eq` is automatic from the σ-descent.** For the intersection-form local signature
`sigLocal p := latticeSig (form p).2`, the descended hom satisfies the σ-presentation `sig_eq` obligation
`sig [p] = latticeSig (form p)` for every `p` — with no further input. This is the exact shape the
`SpinSigmaPresentation.sig`/`sig_eq` pair reduces to, once the two Thom Props (`hbord`, `hadd`) hold. -/
theorem sigDescend_latticeSig_eq
    (form : StrMfd (spinEmptyData prov) → Σ n : ℕ, Matrix (Fin n) (Fin n) ℤ)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (form p).2 = latticeSig (form q).2)
    (hadd : ∀ p q : StrMfd (spinEmptyData prov),
      latticeSig (form ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩).2
        = latticeSig (form p).2 + latticeSig (form q).2)
    (p : StrMfd (spinEmptyData prov)) :
    sigDescend prov (fun p => latticeSig (form p).2) hbord hadd (DataBordismGrp.mk (spinEmptyData prov) p)
      = latticeSig (form p).2 :=
  rfl

end SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
