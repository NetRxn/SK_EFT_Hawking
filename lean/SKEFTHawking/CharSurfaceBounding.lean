/-
# Phase 5q.H (E1 → E2) — the characteristic-surface geometric datum + the bounding statement freeze

The E1-checklist "characteristic-surface datum type" and the **statement freeze** for the Taylor/Klug
geometric inputs of the `[FK]`/Rokhlin discharge (blueprint route A; DAG A5/A6; normalization report
`GM_structure_ABK_invariant_normalizations_20260703.md` — its stated consumer is exactly this freeze):

* `PinCharSurface` — a closed 2-dim `SingularManifold` surface mapped injectively into the ambient
  space (embeddedness = DATA, per the checklist), carrying its `ZMod 4`-quadratic enhancement `Q` (the
  pin⁻ shadow, Taylor `0802.0111` §1 / Debray–Gunningham Thm 3.12) tied to the surface's REAL singular
  `H₁(F;ℤ/2)` by an explicit iso (falsifiable: the rank must be `b₁(F)`).
* `PinCharSurface.Bounding` — the surface bounds a compact 3-manifold `V` (Mathlib
  manifold-with-boundary, encoded by the same smooth-injection-onto-the-boundary collar pattern as
  `BordismGroup.Bordism`); `kernelL` = `ker(H₁(F;ℤ/2) → H₁(V;ℤ/2))` transported to the enhancement's
  space — the Taylor/Klug **metabolizer**.
* `TaylorKernelVanishing` (Taylor `0802.0111` **Theorem 1.1**: classes dying in `V` have `q = 0`) and
  `KernelHalfLivesHalfDies` (Poincaré–Lefschetz for the bounding 3-manifold: the kernel is maximal
  self-orthogonal) — the two NAMED geometric targets, frozen as Props.
* `gmrelation_null_of_bounding` — the composed end: a bounded characteristic surface satisfying the two
  frozen statements has vanishing GM residue (`GMrelation 0 0 Q`), via the metabolic theorem
  (`BrownMetabolic`; `β(F) = 0` is DERIVED). This is the null-bordant leg of `[FK]`-by-bordism-invariance
  with the geometry isolated to exactly the two named Props.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.GMRokhlinDischarge
import SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.CharSurface



open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality
open scoped Manifold

/-- **A pin⁻-enhanced characteristic surface datum** on a space `X`: a closed 2-dimensional
`C^k`-`SingularManifold` `F` mapped injectively into `X` (embeddedness = data, not demanded), with a
`ZMod 4`-quadratic enhancement `Q` of its mod-2 intersection form (the pin⁻ shadow) whose underlying
vector space is the surface's genuine singular `H₁(F;ℤ/2)` via the explicit iso `H1Iso`. The
characteristic (dual-to-`w₂+w₁²`) condition on the ambient class lives one level up (the consumer's
`GMrelation`/Wu data); this datum is the SURFACE side. -/
structure PinCharSurface (X : Type) [TopologicalSpace X] (k : WithTop ℕ∞) where
  /-- The closed 2-dimensional surface with its map to `X`. -/
  F : SingularManifold.{0} X k (𝓡 2)
  /-- Embeddedness as data: the map to `X` is injective. -/
  emb : Function.Injective F.f
  /-- Index type of the surface's `H₁(F;ℤ/2)` basis. -/
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  /-- The `ZMod 4`-quadratic enhancement (the pin⁻ structure's shadow — Taylor §1, DG Thm 3.12). -/
  Q : Z4Quadratic ι
  /-- The enhancement's space IS the surface's singular `H₁(F;ℤ/2)` (falsifiability: rank = `b₁`). -/
  H1Iso : Homology (TopCat.of F.M) 1 ≃ₗ[ZMod 2] (ι → ZMod 2)

attribute [instance] PinCharSurface.fι PinCharSurface.dι

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-- **A bounding 3-manifold for the surface**: a compact `C^k` manifold-with-boundary `V` (model `J`,
one dimension up) with a smooth injection `e : F → V` onto the boundary — the same collar encoding as
`BordismGroup.Bordism` (Mathlib's `ModelWithCorners.boundary` is a `Set V`, so the boundary
identification is an injection with range exactly `J.boundary V`). -/
structure PinCharSurface.Bounding
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    (C : PinCharSurface X k) where
  /-- The bounding compact 3-manifold-with-boundary. -/
  V : Type
  [topV : TopologicalSpace V]
  [chartV : ChartedSpace H' V]
  [mfdV : IsManifold J k V]
  [compactV : CompactSpace V]
  /-- The boundary identification: a smooth injection of `F` onto `∂V`. -/
  e : C.F.M → V
  he_smooth : ContMDiff (𝓡 2) J k e
  he_inj : Function.Injective e
  he_boundary : Set.range e = J.boundary V

namespace PinCharSurface.Bounding

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k}

instance (b : C.Bounding J) : TopologicalSpace b.V := b.topV
instance (b : C.Bounding J) : ChartedSpace H' b.V := b.chartV
instance (b : C.Bounding J) : IsManifold J k b.V := b.mfdV
instance (b : C.Bounding J) : CompactSpace b.V := b.compactV

/-- **The metabolizer candidate**: `ker(H₁(F;ℤ/2) → H₁(V;ℤ/2))` of the boundary inclusion, transported
to the enhancement's space through `H1Iso`. Taylor/Klug: this is the Lagrangian on which `q` vanishes. -/
noncomputable def kernelL (b : C.Bounding J) : Submodule (ZMod 2) (C.ι → ZMod 2) :=
  (LinearMap.ker (Homology.map (X := TopCat.of C.F.M) (Y := TopCat.of b.V)
    (ContinuousMap.mk b.e b.he_smooth.continuous) 1)).map C.H1Iso.toLinearMap

noncomputable instance (b : C.Bounding J) : Fintype b.kernelL := Fintype.ofFinite _

/-- **Statement freeze — Taylor `0802.0111` Theorem 1.1** (verbatim shape: *"Let M³ be a 3-manifold with
a fixed Pin⁻-structure and let F be the boundary … Let x ∈ H₁(F;ℤ/2) be a class which vanishes in
H₁(M;ℤ/2). Then q(x) = 0"*): the enhancement vanishes on the kernel of the bounding inclusion. The
geometric proof (handle decompositions, surgery on framed circles via Lemma 1.2, the two-ended-arc
count) is the E2-MEDIUM/HARD wave; this Prop is its frozen target. -/
def TaylorKernelVanishing (b : C.Bounding J) : Prop :=
  ∀ l ∈ b.kernelL, C.Q.q l = 0

/-- **Statement freeze — half-lives-half-dies** (Poincaré–Lefschetz duality of the bounding pair
`(V, ∂V = F)`): the kernel of the boundary inclusion is MAXIMAL self-orthogonal in `H₁(F;ℤ/2)` — its
`B`-orthogonal complement is itself. Self-orthogonality (`L ⊆ L^⊥`) is already forced by
`TaylorKernelVanishing` via polarization; this Prop freezes the maximality half (`L^⊥ ⊆ L`). -/
def KernelHalfLivesHalfDies (b : C.Bounding J) : Prop :=
  ∀ v, (∀ l ∈ b.kernelL, C.Q.B v l = 0) → v ∈ b.kernelL

/-- **A bounded characteristic surface has vanishing GM residue.** Given the two frozen geometric
statements — Taylor Thm 1.1 (`q` kills the kernel) and half-lives-half-dies (the kernel is Lagrangian)
— the metabolic theorem forces `β(F) = 0` and the null Guillou–Marin congruence `GMrelation 0 0 Q`
holds outright. The null-bordant leg of `[FK]`-by-bordism-invariance, with ALL geometry isolated in the
two named hypotheses. -/
theorem gmrelation_null (b : C.Bounding J)
    (hq : b.TaylorKernelVanishing) (hmax : b.KernelHalfLivesHalfDies) :
    GMrelation 0 0 C.Q :=
  SKEFTHawking.GMRokhlin.gmrelation_null_of_metabolic C.Q b.kernelL hq hmax

/-- **`β(F) = 0` for a bounded characteristic surface** — the Brown-invariant form of the same
conclusion (Taylor's Theorem 1.1 ⟹ the abstract bounding-vanishing, through `BrownMetabolic`). -/
theorem brown_eq_zero (b : C.Bounding J)
    (hq : b.TaylorKernelVanishing) (hmax : b.KernelHalfLivesHalfDies) :
    C.Q.brown = 0 :=
  C.Q.brown_eq_zero_of_metabolic b.kernelL hq hmax

end PinCharSurface.Bounding

end SKEFTHawking.CharSurface
