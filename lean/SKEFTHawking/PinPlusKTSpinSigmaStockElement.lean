/-
# Phase 5q.H close-out — THE S⁴ STOCK ELEMENT: the first fully-live presentation-row element

`PinPlusKTSpinSigmaStock` §3 discharged the S⁴ spin-sphere package's integral-topology residuals
(`sphere4IntOrientation`, `sphere4IntPoincareDuality`, `sphere4_pkg_sixteen_dvd_latticeSig`) MODULO the
element itself — the actual `StrMfd (spinEmptyData prov)` member on S⁴. This module BUILDS that element
and instantiates the per-element E1 package on it.

## What is built

* **`sphere4SM`** — the 4-sphere `S⁴ = Metric.sphere (0 : ℝ⁵) 1` as a `SingularManifold PUnit 0 (𝓡 4)`
  (`ChartedSpace`/`IsManifold`/`CompactSpace`/`BoundarylessManifold` all from Mathlib's sphere stack; the
  `k = 0` C⁰ collapse makes `IsManifold` trivial).
* **`sphere4CharPairBundled`** — the `CharPairStrBundled (𝓡 4) sphere4SM` with **empty characteristic
  surface** (Σ = ∅). Its algebraic core (`n = 0`, `q = stdQuadratic 0`) and its surface/`basis`/`hpolar`
  fields are the `charPairBundledEmpty` precedent verbatim (rank-0 empty surface); the two S⁴-specific
  fields are `cert` (the Pin⁺/`w₂ = 0` certificate — FREE because `H²(S⁴;ℤ/2) = 0`, so `wuW2` lives in a
  subsingleton) and the NONEMPTY-carrier `hchar` (`⟨a, emb₊[Σ]⟩ = μ(a∪a)`, both sides `0`: LHS since
  `[Σ] = 0`, RHS since `H²(S⁴;ℤ/2) = 0` forces `a = 0`).
* **`sphere4Element`** — the `StrMfd (spinEmptyData prov)` member: `⟨sphere4SM, ⟨sphere4CharPairBundled,
  IsEmpty …⟩⟩`. This is the first fully-live element of the empty-Σ spin carrier.
* **`sphere4AtomPkg`** — the `SpinSigmaAtomPkg prov sphere4Element` inhabited from the Stock module's three
  disclosed S⁴ atoms (`sphere4IntOrientation` / `sphere4IntH2Basis` / `sphere4IntPoincareDuality`).
* **The visible corollary** — the per-element package REALIZES both presentation obligations at the S⁴
  sector: the intersection matrix is even-unimodular (`SpinSigmaAtomPkg.isEvenUnimodular`, with the
  `SpinWuDatum` derived from the carrier's own empty membrane) AND `16 ∣ σ` (the Rokhlin leg,
  `sphere4_pkg_sixteen_dvd_latticeSig`). So the whole orientation → intersection form → even-unimodular →
  σ÷16 pipeline fires on the element's own data.

**Dimension discipline**: S⁴ = the closed spin 4-manifold; Σ = ∅ (the empty 2-surface); H¹(S⁴;ℤ/2) = 0,
H²(S⁴;ℤ/2) = 0 (rank-0 form); the value is `16 ∣ 0` (`b₂(S⁴) = 0`), but the entire pipeline fires
end-to-end on the S⁴ element's disclosed geometry.

**Fence** `synthetic-grade-ker-bot-nogo`: the element is DATA-carrying by construction (genuine S⁴
orientation/PD/basis geometry), not a fabricated grade. `no_empty_surface_bundle_on_rp4` (ℝP⁴ is not
spin-side) is not contradicted — S⁴ IS spin (`wuW2(S⁴) = 0` because the group vanishes).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaStock

namespace SKEFTHawking.PinPlusKTSpinSigmaStockElement

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking
open SKEFTHawking.BordismTheory
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusTiedData
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
open SKEFTHawking.PinPlusKTSpinSigmaStock
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SphereWitnessTowerInt (SphereFour sphere4IntH2Basis)

/-! ## §1. S⁴ as a `SingularManifold PUnit 0 (𝓡 4)` -/

/-- **The 4-sphere as a `SingularManifold PUnit 0 (𝓡 4)`.** All structural instances come from Mathlib's
sphere stack (`ChartedSpace (EuclideanSpace ℝ (Fin 4))`, `CompactSpace`, `BoundarylessManifold`); at
regularity `k = 0` the `IsManifold` obligation is the trivial C⁰ groupoid. The base map to `PUnit` is
constant. -/
noncomputable def sphere4SM : SingularManifold PUnit k (𝓡 4) where
  M := SphereFour
  f := fun _ => PUnit.unit
  hf := continuous_const

/-! ## §2. The Pin⁺/`w₂ = 0` certificate on S⁴ — FREE from `H²(S⁴;ℤ/2) = 0` -/

/-- **S⁴ is `w₂`-admissible** — `wuW2(S⁴) = 0` because the group it lives in, `H²(S⁴;ℤ/2)`, is trivial
(`SphereWitnessFiringInt`'s subsingleton instance). Unlike the `ℝP⁴` certificate (which needs the whole
Wu-square `v₂ = v₁²` computation), the sphere's certificate is a one-line subsingleton collapse. -/
theorem sphere4_hcert : PinPlusCertK (𝓡 4) (sphere4SM (k := k)) := by
  intro _ _
  haveI : Subsingleton (SingularCohomologyMod2.Cohomology (TopCat.of (sphere4SM (k := k)).M) 2) :=
    inferInstanceAs (Subsingleton (SingularCohomologyMod2.Cohomology (Sph 4) 2))
  exact Subsingleton.elim _ _

/-! ## §3. The empty-Σ char-pair structure and bundle on S⁴ -/

/-- **The char-pair (algebraic) structure on S⁴** — rank-0 enhancement (`n = 0`, `q = stdQuadratic 0`,
the empty-characteristic-surface shadow), the S⁴ Hausdorff witness, and the `w₂ = 0` certificate. -/
noncomputable def sphere4CharPairStr : CharPairStr (𝓡 4) (sphere4SM (k := k)) where
  t2 := inferInstanceAs (T2Space SphereFour)
  cert := sphere4_hcert
  n := 0
  q := stdQuadratic 0

/-- **The empty-Σ `CharPairStrBundled` on S⁴.** The surface is the EMPTY singular manifold (Σ = ∅), the
`basis`/`hpolar`/`surfClass` fields are the rank-0 `charPairBundledEmpty` construction verbatim, and the
NONEMPTY-carrier `hchar` holds with both sides `0`. -/
noncomputable def sphere4CharPairBundled : CharPairStrBundled (𝓡 4) (sphere4SM (k := k)) where
  toCharPairStr := sphere4CharPairStr
  surf := (emptySM : SingularManifold.{0} PUnit.{1} k (𝓡 2))
  surfT2 := ⟨fun x => x.elim⟩
  emb := fun x => x.elim
  embSmooth := fun x => x.elim
  embInj := fun x => x.elim
  surfClass := 0
  basis := by
    show _ ≃ₗ[ZMod 2] (Fin 0 → ZMod 2)
    exact LinearEquiv.ofSubsingleton _ _
  hpolar := fun a b => by
    have hz : ∀ x y : Fin 0 → ZMod 2, (stdQuadratic 0).B x y = 0 :=
      fun x y => by rw [Subsingleton.elim x 0]; exact (stdQuadratic 0).B_zero_left y
    show (stdQuadratic 0).B _ _ = _
    rw [hz, map_zero]
  hchar := by
    intro _ _ a
    haveI : Subsingleton (SingularCohomologyMod2.Cohomology (TopCat.of (sphere4SM (k := k)).M) 2) :=
      inferInstanceAs (Subsingleton (SingularCohomologyMod2.Cohomology (Sph 4) 2))
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    simp

/-! ## §4. The S⁴ stock element -/

/-- **THE S⁴ STOCK ELEMENT** — the `StrMfd (spinEmptyData prov)` member on the 4-sphere with empty
characteristic surface. The first fully-live element of the empty-Σ spin carrier `spinEmptyData prov`. -/
noncomputable def sphere4Element (prov : CharPairWProviderPerOp (𝓡 4) k) :
    StrMfd (spinEmptyData prov) :=
  ⟨sphere4SM, sphere4CharPairBundled, inferInstanceAs (IsEmpty PEmpty)⟩

/-! ## §5. The per-element E1 package on S⁴, and the visible corollary -/

/-- S⁴'s ambient `T2Space` re-registered on the element carrier type (defeq to `SphereFour`), so the
per-nonempty-element package's `[T2Space p.1.M]` binder resolves (the regular def `sphere4Element` is not
unfolded during instance search, so the instance is keyed on the projected carrier directly). -/
instance sphere4Element_t2 (prov : CharPairWProviderPerOp (𝓡 4) k) :
    T2Space (sphere4Element prov).1.M := inferInstanceAs (T2Space SphereFour)

/-- S⁴'s ambient `Nonempty` re-registered on the element carrier type, so the package's `[Nonempty p.1.M]`
binder resolves. -/
instance sphere4Element_nonempty (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Nonempty (sphere4Element prov).1.M := inferInstanceAs (Nonempty SphereFour)

/-- **The per-element E1 atom package instantiated on the S⁴ element.** The three disclosed S⁴ atoms of
`PinPlusKTSpinSigmaStock` §3 — the integral orientation, the `H²(S⁴;ℤ)` basis, and the integral
Poincaré-duality perfect pairing — populate the `SpinSigmaAtomPkg` at `sphere4Element`. -/
noncomputable def sphere4AtomPkg (prov : CharPairWProviderPerOp (𝓡 4) k) :
    SpinSigmaAtomPkg prov (sphere4Element prov) where
  orient := sphere4IntOrientation
  B := sphere4IntH2Basis
  pd := sphere4IntPoincareDuality

/-- **The S⁴ package realizes the presentation's even-unimodular obligation at its element.** The three
disclosed atoms build `IsEvenUnimodular (interMatrix)` with the `SpinWuDatum` (EVEN conjunct) DERIVED from
the S⁴ carrier's own empty membrane (`spinWuDatum_of_emptySigma`), and the UNIMODULAR conjunct from the
integral PD. This is the presentation-row machinery firing on the concrete S⁴ sector. -/
theorem sphere4Element_isEvenUnimodular (prov : CharPairWProviderPerOp (𝓡 4) k) :
    IsEvenUnimodular (interMatrix (intFundamentalClassOfIntOrientation sphere4IntOrientation)
      sphere4IntH2Basis) :=
  (sphere4AtomPkg prov).isEvenUnimodular

/-- **The whole σ÷16 pipeline fires on the S⁴ element's own data.** The per-element package delivers BOTH
presentation obligations at the S⁴ sector: the intersection matrix is even-unimodular AND its
signature is `16`-divisible (the Rokhlin leg, `sphere4_pkg_sixteen_dvd_latticeSig`). The value is `16 ∣ 0`
(`b₂(S⁴) = 0`), but the entire orientation → intersection form → even-unimodular → σ÷16 pipeline fires
end-to-end on the disclosed S⁴ geometry the element carries. -/
theorem sphere4Element_realizes_even_unimod_and_rokhlin (prov : CharPairWProviderPerOp (𝓡 4) k) :
    IsEvenUnimodular (interMatrix (intFundamentalClassOfIntOrientation sphere4IntOrientation)
        sphere4IntH2Basis)
      ∧ (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfIntOrientation sphere4IntOrientation)
        sphere4IntH2Basis) :=
  ⟨sphere4Element_isEvenUnimodular prov, sphere4_pkg_sixteen_dvd_latticeSig⟩

end SKEFTHawking.PinPlusKTSpinSigmaStockElement
