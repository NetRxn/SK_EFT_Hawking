import Mathlib
import SKEFTHawking.CharSurfaceNormalShadow
import SKEFTHawking.PinPlusCharPairEmptySourceRealization

/-!
# The rank-zero surface bounding datum (hcolD brick B1 — interface)

The per-`τ` honest freeze of the Kirby–Taylor terminal move's geometric input: the carried
characteristic surface `Σ_τ` **bounds** a compact 3-manifold-with-boundary `Q`, pin-compatibly.
Per the design adjudication (option (c)): the datum SPLITS into

* **B1a `RankZeroSurfaceBoundingDatum`** — the pre-weld geometric core, riding the frozen
  `PinCharSurface.Bounding` package (`CharSurfaceBounding`): a compact `MembraneModel`-charted
  `Q = bound.V` with a smooth injection `e : Σ_τ → V` whose range is EXACTLY `∂V`
  (`he_boundary : Set.range e = J.boundary V` — the anti-fake heart), the Hausdorff certificate,
  the pin⁻ spin-bit compatibility (`KernelSpinVanishing` — the strongest honest in-tree
  formulation; NOT a literal principal Pin⁻ bundle, which is absent substrate), and the interior
  `H₁` coordinates. The `PinCharSurface` side is derived from the bundled carrier by
  `pinCharSurfaceOfBundled` (the `H₁`-basis transported from `τ.basis` through the Kronecker
  bridge `homologyBasisOfCohomologyBasis`).
* **B1b `RankZeroSurfaceWeldAnchor`** — the capstone-anchored weld plumbing: the dim-3 handle
  presentation `HAQ` of `Q`, its weld into the FIXED `ktHandleAttachment` capstone carrier, the
  presentation homeomorphism, and the τ-end boundary factorization — literally B4's remaining
  inputs, so `toLeaves` composes into `TraceMembraneLeaves.ofRankZeroTauMembrane` with NO
  transport gap.

Anti-vacuity: a point `Q` cannot chart over the 3-dim model with nonempty boundary range; `Q = Σ`
fails the model dimension; `Q = Σ × [0,1]` has TWO surface ends so one embedding cannot exhaust
`∂V`; an unrelated abstract cap is excluded by the weld anchor. No union-of-spheres classification
and no normal-Euler hypothesis is baked in (SETTLED FORKS: rank zero + `hchar` do NOT force
`e = 0`).

Inhabitation (the `WuNullCarrier` ⟹ embedded bounding `Q` construction) is the deep geometric
front and is NOT claimed here — this module is the consumption-shaped interface B2's endpoint
construction and the B5/B6 assembly build against.
-/

open scoped Manifold
open Topology
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.CharSurface
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusTraceMembranePresented
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

namespace SKEFTHawking.PinPlusKTRankZeroBounding

/-- **The bundled carrier's characteristic surface as a `PinCharSurface`** on the 4-manifold
carrier: the same closed 2-manifold `τ.surf.M`, mapped by `τ.emb` (injectivity = `τ.embInj`),
with the enhancement `τ.q` on the index `Fin τ.n` and the `H₁`-side basis transported from the
carrier's cohomology-side `τ.basis` through the perfect Kronecker pairing
(`homologyBasisOfCohomologyBasis`). This is the bridge the `PinCharSurface.Bounding`/Taylor
machinery consumes — no new tie is introduced: `q`, `basis`, `emb` are EXACTLY the carrier's. -/
noncomputable def pinCharSurfaceOfBundled
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]
    (τ : CharPairStrBundled (𝓡 4) t) : PinCharSurface t.M 0 where
  F :=
    { M := τ.surf.M
      topSpaceM := τ.surf.topSpaceM
      chartedSpace := τ.surf.chartedSpace
      isManifold := τ.surf.isManifold
      compactSpace := τ.surf.compactSpace
      boundaryless := τ.surf.boundaryless
      f := τ.emb
      hf := τ.embSmooth.continuous }
  emb := τ.embInj
  ι := Fin τ.n
  Q := τ.q
  H1Iso := homologyBasisOfCohomologyBasis (N := 0) τ.basis

/-- **B1a: the rank-zero surface bounding datum** — the pre-weld geometric core. `bound` carries
the compact `MembraneModel`-charted 3-manifold `V`, the smooth injective boundary identification
`e : Σ_τ → V` with `range e = ∂V` (the load-bearing exactness), plus the manifold instances; the
remaining fields are the Hausdorff certificate, the pin⁻ spin-bit compatibility on the bounding
kernel, and the interior `H₁(V;ℤ/2)` coordinates B4 consumes. Named `RankZero…` for its intended
hcolD consumption (the fields themselves are rank-agnostic; the rank-zero hypothesis enters at
`toLeaves`). -/
structure RankZeroSurfaceBoundingDatum
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]
    (τ : CharPairStrBundled (𝓡 4) t) where
  /-- The frozen exact-boundary bounding package: compact charted `V`, smooth injective
  `e : Σ_τ → V`, `Set.range e = ((𝓡 2).prod (𝓡∂ 1)).boundary V`. -/
  bound : (pinCharSurfaceOfBundled τ).Bounding ((𝓡 2).prod (𝓡∂ 1))
  /-- The membrane carrier is Hausdorff (needed for the closed-embedding upgrade and B4). -/
  QT2 : T2Space bound.V
  /-- **Pin⁻ compatibility** (the strongest honest in-tree formulation): the halving spin
  reduction `toZ2` of the carrier's enhancement vanishes on the bounding kernel
  `ker (H₁(Σ;ℤ/2) → H₁(V;ℤ/2))` — the class-level `Ω₁^{Spin} ≅ ℤ/2` pin⁻ atom
  (`membraneSpinKill_of_kernelSpinVanishing` upgrades it to `MembraneSpinKill`). NOT a literal
  principal Pin⁻ bundle restriction (absent substrate — a separate front if ever needed). -/
  pinCompat : bound.KernelSpinVanishing
  /-- `dim H₁(V;ℤ/2)` — the interior-basis coordinate count. -/
  mid : ℕ
  /-- The interior `H₁` basis (the free interior gauge — kernel-invariant). -/
  eQ : Homology (TopCat.of bound.V) 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2)

namespace RankZeroSurfaceBoundingDatum

variable {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]
  {τ : CharPairStrBundled (𝓡 4) t}

/-- The membrane space as a `TopCat` — B4's `QC`. -/
noncomputable def QC (B : RankZeroSurfaceBoundingDatum τ) : TopCat := TopCat.of B.bound.V

/-- Compactness of the membrane — B4's `QCompact`, read off the bounding package. -/
theorem QCompact (B : RankZeroSurfaceBoundingDatum τ) : CompactSpace (B.QC : Type) :=
  B.bound.compactV

/-- The Hausdorff certificate in B4's `↑QC`-coerced form. -/
theorem QT2' (B : RankZeroSurfaceBoundingDatum τ) : T2Space (B.QC : Type) := B.QT2

/-- The boundary identification as a continuous map `Σ_τ → Q` — B4's `ιY`. -/
def ιY (B : RankZeroSurfaceBoundingDatum τ) :
    C((τ.surf.M : Type), (B.QC : Type)) :=
  ⟨B.bound.e, B.bound.he_smooth.continuous⟩

/-- `ιY` is a closed embedding — continuous + injective from the compact surface into the
Hausdorff membrane. B4's `hιY`. -/
theorem hιY (B : RankZeroSurfaceBoundingDatum τ) :
    Topology.IsClosedEmbedding B.ιY := by
  letI := B.QT2
  exact B.bound.he_smooth.continuous.isClosedEmbedding B.bound.he_inj

end RankZeroSurfaceBoundingDatum

/-- **B1b: the capstone weld anchor** — the plumbing binding the free-standing bounding datum to
the FIXED KT capstone carrier: the dim-3 handle presentation of `Q`, its weld, the presentation
homeomorphism onto the welded membrane object, and the τ-end boundary factorization. These are
LITERALLY B4's remaining inputs (`HAQ`/`weld`/`hQ`/`glueτ`), so composition is definitional.
`chartQ` is deliberately NOT a field here — it is derived from B1a's package (storing it again
would permit incoherent duplicate atlas choices). -/
structure RankZeroSurfaceWeldAnchor
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M] [T2Space t.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]
    (B : RankZeroSurfaceBoundingDatum τ) where
  /-- The membrane's dim-3 handle presentation `Q = B ⊔_φ Ha`. -/
  HAQ : HandleAttachment.{0, 0}
  /-- The membrane weld `Q ↪ W` into the fixed capstone carrier. -/
  weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
  /-- `Q` presented as `HAQ.carrier` (presentation homeomorphism; no carrier retyping). -/
  hQ : letI := B.QT2'; letI := B.QCompact
    ((capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q : Type) ≃ₜ HAQ.carrier
  /-- The τ-end boundary factorization through the surgered-end packaging. -/
  glueτ : letI := B.QT2'; letI := B.QCompact
    ∀ x : ↑(sub (capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ),
      weld.carrierMap (hQ ((capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).ι
          (subInclCM (capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ x)))
        = (capstoneB s t S hS φ hφ hφinj cd hseam d).e
            (Sum.inr (τ.emb ((capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).homτ x)))

/-- The membrane discipline chart — B4's `chartQ`, derived (not stored): the welded membrane
object is definitionally `B.bound.V`, and `MembraneModel` is definitionally the model space of
`(𝓡 2).prod (𝓡∂ 1)`, so the bounding package's `chartV` applies by `change`. -/
@[reducible] noncomputable def RankZeroSurfaceBoundingDatum.chartQ
    {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]
    (σ : CharPairStrBundled (𝓡 4) s) [IsEmpty σ.surf.M]
    {τ : CharPairStrBundled (𝓡 4) t} (B : RankZeroSurfaceBoundingDatum τ) :
    letI := B.QT2'; letI := B.QCompact
    ChartedSpace MembraneModel
      ↑(capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q := by
  letI := B.QT2'; letI := B.QCompact
  change ChartedSpace MembraneModel B.bound.V
  exact B.bound.chartV

/-- **The B1 → B4 composition** (the hcolD collapse row's membrane leg, end to end): a bounding
datum + its weld anchor yield the `TraceMembraneLeaves` of the capstone bordism, through the
rank-zero constructor (`hq`/`hlagK` self-discharge honestly at rank zero). NO transport lemma
beyond the derived views — every B4 input is read off `B`/`A` verbatim. -/
noncomputable def RankZeroSurfaceWeldAnchor.toLeaves
    {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space s.M] [T2Space t.M]
    {S : Set D5} {hS : IsClosed S} {φ : ↥S → s.M × Set.Icc (0 : ℝ) 1}
    {hφ : Continuous φ} {hφinj : Function.Injective φ}
    {cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
    {hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd}
    {d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam}
    {σ : CharPairStrBundled (𝓡 4) s} {τ : CharPairStrBundled (𝓡 4) t}
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    {B : RankZeroSurfaceBoundingDatum τ}
    (A : RankZeroSurfaceWeldAnchor s t S hS φ hφ hφinj cd hseam d σ τ B) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  TraceMembraneLeaves.ofRankZeroTauMembrane s t S hS φ hφ hφinj cd hseam d σ τ
    B.QC B.QT2' B.QCompact B.ιY B.hιY B.mid B.eQ
    A.HAQ A.weld A.hQ A.glueτ (B.chartQ σ)

/-- **Pin⁻ spin-kill, delivered**: the datum's `pinCompat` field upgrades through the banked
`membraneSpinKill_of_kernelSpinVanishing` to the geometric `MembraneSpinKill` atom on the bounding
package — confirming the compatibility field is genuinely load-bearing (anti-vacuity: it is the
irreducible pin⁻ content the mod-2 intersection form cannot see). -/
theorem RankZeroSurfaceBoundingDatum.membraneSpinKill
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]
    {τ : CharPairStrBundled (𝓡 4) t} (B : RankZeroSurfaceBoundingDatum τ) :
    B.bound.MembraneSpinKill :=
  B.bound.membraneSpinKill_of_kernelSpinVanishing B.pinCompat

end SKEFTHawking.PinPlusKTRankZeroBounding
