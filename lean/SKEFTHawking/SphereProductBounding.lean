/-
# Phase 5q.H (N1a) — Freeze-B instantiation: `S²×S² = ∂(S²×D³)` at the manifold level

Instantiation layer for `SpinSigmaRoute`'s **Freeze B** (`SphereProductBounds`: the distinguished
`S²×S²` class is zero — DR route sub-piece (1), `Lit-Search/Phase-5qH/
Omega4Spin_Z_formalization_route_20260706.md`: "TRIVIAL — `S²×S² = ∂(S²×D³)`, one-liner; reuses
manifold primitives"; Kirby–Taylor arXiv:math/9803101 pp.6–7, bordisms "built from 2- and
3-handles"). This module makes the "reuses manifold primitives" claim HONEST against today's
Mathlib, building everything genuinely available and freezing exactly what is absent:

**GENUINE (built here, no freeze):**
* `S²×S²` as a Mathlib-real smooth compact boundaryless manifold — the product of two unit spheres
  (`Mathlib.Geometry.Manifold.Instances.Sphere`) over the product model `I4 = (𝓡 2).prod (𝓡 2)` —
  packaged as the `SingularManifold` the `s2s2` slot of a `SpinSigmaPresentation` consumes
  (`sphereProdSM`), at every smoothness `k` (`IsManifold.of_le le_top`).
* The rank-2 hyperbolic pin, data-level: the form datum `sphereProdFormDatum := Hyp` with the
  `s2s2_hyp`/`even_unimod`/`sig_eq`-shaped discharge lemmas (in-tree lattice algebra; the
  cohomology of `S²×S²` is not computed in-tree, so the form is carried as the datum — exactly the
  presentation's disclosed-data design), plus the σ-consistency of Freeze B itself
  (`sig_s2s2_eq_zero`: the signature obstruction to `[S²×S²] = 0` vanishes for EVERY presentation).
* The full topological layer of the coboundary `S²×D³`: the space, its compactness, the boundary
  inclusion `S²×S² → S²×D³` with injectivity/continuity, and the identification of the candidate
  boundary set with the genuine topological frontier slice (`frontier_closedBall`).
* The composed conditional: a `SphereDiskSmoothData`-freeze + a structure-extension datum yield a
  genuine project `Bordism` (`sphereDiskBordism`) and discharge Freeze B
  (`sphereProductBounds_of_package`) — exercised end-to-end on the trivial tangential datum with
  the CONCRETE `S²×S²` in the slot (`trivialSpherePresentation_sphereProductBounds`: the §5 chain
  is jointly satisfiable modulo exactly the two named gaps).
* The atlas-free alternative route: reversal-fixed classes are 2-torsion
  (`mk_add_self_eq_zero_of_revStr_fixed`, the per-class refinement of the kernel-checked
  `dataBordism_two_torsion_of_revStr_trivial` mechanism), so Freeze B also follows from
  "the `S²×S²` structure is reversal-fixed + the carrier has no 2-torsion" — both inputs open for
  the genuine spin datum, recorded as the route-map alternative only.

**FROZEN (named Mathlib gaps, `SphereDiskSmoothData`):**
1. `Metric.closedBall` (the disk `D³`, and any `Dⁿ`, `n ≥ 2`) has NO `ChartedSpace`/`IsManifold`
   instance in Mathlib — `Mathlib.Geometry.Manifold.Instances.Real` provides only `Set.Icc`
   (`n = 1`); instance synthesis for the closed ball fails (checked at pin v4.29.1).
2. No change-of-model/atlas-transport machinery: the project `Bordism` encoding fixes the collar
   model `J5 = I4.prod (𝓡∂ 1)`, and even a future `D³`-instance on a `(𝓡∂ 3)`-style model would
   make `S²×D³` a `(𝓡 2).prod (𝓡∂ 3)`-manifold, not a `J5`-manifold.
   NOT a gap: `ModelWithCorners.boundary_of_boundaryless_left` (`∂(M×N) = univ ×ˢ ∂N`) EXISTS —
   but is inapplicable here because the product splitting `(S²)×(D³)` does not match `J5`'s model
   splitting `(4-dim)×(half-line)`, so the boundary identification stays inside the freeze.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaRoute

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory Metric
open scoped Manifold

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-! ### §1. The genuine `S²×S²` — fully Mathlib-real

The unit sphere `S² ⊆ ℝ³` is a smooth (indeed analytic) manifold in Mathlib
(`Mathlib.Geometry.Manifold.Instances.Sphere`); products of manifolds, compactness of spheres in
proper spaces and boundarylessness of products are all instances. Nothing in this section is
frozen. -/

/-- `S²` — the unit 2-sphere in `ℝ³`, with Mathlib's smooth-manifold structure
(stereographic charts into `EuclideanSpace ℝ (Fin 2)`). -/
abbrev TwoSphere : Type := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- `S²×S²` — the product of two unit 2-spheres, a smooth compact boundaryless 4-manifold over
the product model `I4`. -/
abbrev SphereProd : Type := TwoSphere × TwoSphere

/-- The 4-manifold model for `S²×S²`: the product `(𝓡 2).prod (𝓡 2)` (boundaryless). -/
noncomputable abbrev I4 := (𝓡 2).prod (𝓡 2)

/-- **`S²×S²` as a singular manifold** (general target): the genuine Mathlib product-of-spheres
manifold with a reference map `f : S²×S² → X`, at any smoothness `k` (the sphere is `C^ω`;
`IsManifold.of_le le_top` downgrades). This is the underlying-manifold datum of the
`SpinSigmaPresentation.s2s2` slot. -/
noncomputable def sphereProdSMOf {X : Type*} [TopologicalSpace X] (k : WithTop ℕ∞)
    (f : SphereProd → X) (hf : Continuous f) : SingularManifold X k I4 :=
  haveI : IsManifold I4 k SphereProd := .of_le le_top
  ⟨SphereProd, f, hf⟩

/-- **`S²×S²` as an absolute singular manifold** (`X = PUnit`, the absolute bordism group's
target — `Ω₄^{Spin} = Ω₄^{Spin}(pt)`). -/
noncomputable def sphereProdSM (k : WithTop ℕ∞) : SingularManifold PUnit k I4 :=
  sphereProdSMOf k (fun _ => PUnit.unit) continuous_const

/-! ### §2. The rank-2 hyperbolic pin — the data-level tie

`II(S²×S²) = H` (the hyperbolic plane) is the identity pin of the `s2s2` slot
(`s2s2_rank`/`s2s2_hyp`). The singular cohomology of `S²×S²` is not computed in-tree, so — exactly
as the presentation's disclosed-data design intends — the form is carried as a DATUM
(`sphereProdFormDatum := Hyp`), with the pin's discharge lemmas proven from the in-tree lattice
algebra. An instantiating presentation assigns `rank s2s2 := 2`, `form s2s2 := sphereProdFormDatum`
and discharges `s2s2_rank` by `rfl`, `s2s2_hyp` by `sphereProdFormDatum_hyp_pin`. -/

/-- The intersection-form datum carried for `S²×S²`: the hyperbolic plane `H = !![0,1;1,0]`
(`II(S²×S²) = H` — Benedetti arXiv:1907.10297 Ch. 20; carried as a datum, see section
docstring). -/
def sphereProdFormDatum : Matrix (Fin 2) (Fin 2) ℤ := Hyp

/-- The `S²×S²` form datum is even unimodular — the `even_unimod` field's discharge at the
`s2s2` slot. -/
theorem sphereProdFormDatum_even_unimod : IsEvenUnimodular sphereProdFormDatum :=
  ⟨hyp_symm, hyp_unimodular, hyp_even⟩

/-- The `S²×S²` form datum has signature zero — the `sig_eq` consistency at the `s2s2` slot
(`σ(S²×S²) = 0`). -/
theorem sphereProdFormDatum_latticeSig : latticeSig sphereProdFormDatum = 0 :=
  hyp_latticeSig

/-- The `S²×S²` form datum is hyperbolic-standard — the `s2s2_hyp` pin's discharge at
instantiation. -/
theorem sphereProdFormDatum_hyp_pin :
    ∃ N, IsHyperbolicForm N ∧ IntCongr sphereProdFormDatum N :=
  (isHyperbolicForm_congr_iff _).mpr
    ⟨sphereProdFormDatum_even_unimod, sphereProdFormDatum_latticeSig⟩

/-- **The σ-obstruction to Freeze B vanishes** — for EVERY σ-presentation, the signature of the
distinguished `S²×S²` class is zero (the hyperbolic pin `s2s2_hyp` + `sig_eq` force it). Freeze B
(`SphereProductBounds`: `[S²×S²] = 0`) is therefore CONSISTENT with the signature homomorphism —
the only bordism invariant the presentation carries cannot falsify it. -/
theorem SpinSigmaPresentation.sig_s2s2_eq_zero {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) : R.sig (DataBordismGrp.mk ξ R.s2s2) = 0 := by
  obtain ⟨N, hN, hcong⟩ := R.s2s2_hyp
  rw [R.sig_eq, ← hcong.latticeSig, hN.latticeSig_eq_zero]

/-! ### §3. The coboundary `S²×D³` — the genuine topological layer

Everything below the atlas is Mathlib-real: the space, compactness, the boundary inclusion and its
injectivity/continuity, and the identification of the candidate boundary set with the genuine
topological frontier slice `S² × ∂D³` (`frontier_closedBall`). -/

/-- `D³` — the closed unit 3-ball in `ℝ³` (NO manifold structure in Mathlib; see §4). -/
abbrev ThreeDisk : Type := closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- `S²×D³` — the coboundary underlying space of the 3-handle bounding `S²×S² = ∂(S²×D³)`. -/
abbrev SphereDisk : Type := TwoSphere × ThreeDisk

/-- The boundary inclusion `S²×S² → S²×D³`, `(x, y) ↦ (x, y)` via `S² = ∂D³ ⊆ D³`. -/
def sphereDiskIncl : SphereProd → SphereDisk := fun p =>
  (p.1, ⟨(p.2 : EuclideanSpace ℝ (Fin 3)), sphere_subset_closedBall p.2.2⟩)

theorem sphereDiskIncl_injective : Function.Injective sphereDiskIncl := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [sphereDiskIncl, Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Prod.ext h.1 (Subtype.ext h.2)

theorem sphereDiskIncl_continuous : Continuous sphereDiskIncl :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

/-- The candidate boundary set of `S²×D³`: the slice `S² × ∂D³` (points whose disk coordinate
lies on the unit sphere). -/
def sphereDiskBoundarySet : Set SphereDisk :=
  {p : SphereDisk | (p.2 : EuclideanSpace ℝ (Fin 3)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}

/-- The boundary inclusion maps `S²×S²` bijectively onto the candidate boundary set. -/
theorem range_sphereDiskIncl : Set.range sphereDiskIncl = sphereDiskBoundarySet := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    rw [← h]
    exact b.2
  · intro hy
    exact ⟨(x, ⟨(y : EuclideanSpace ℝ (Fin 3)), hy⟩), Prod.ext rfl (Subtype.ext rfl)⟩

/-- **The falsifiability pin of the freeze's boundary field**: the candidate boundary set IS the
genuine topological frontier slice `S² × frontier D³` (`frontier_closedBall`). A frozen
`boundary_eq` (§4) therefore asserts the manifold boundary of the frozen atlas agrees with the
genuine topology of `S²×D³` — it cannot be satisfied by a degenerate atlas. -/
theorem sphereDiskBoundarySet_eq_frontier :
    sphereDiskBoundarySet =
      {p : SphereDisk | (p.2 : EuclideanSpace ℝ (Fin 3)) ∈
        frontier (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)} := by
  rw [frontier_closedBall _ one_ne_zero]
  rfl

/-- The candidate boundary set is nonempty — a frozen `boundary_eq` (§4) cannot be satisfied by a
boundaryless atlas (`∂ = ∅`). -/
theorem sphereDiskBoundarySet_nonempty : sphereDiskBoundarySet.Nonempty := by
  obtain ⟨v, hv⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨(⟨v, hv⟩, ⟨v, sphere_subset_closedBall hv⟩), hv⟩

/-- The candidate boundary set is proper (the disk's center slice is interior) — a frozen
`boundary_eq` (§4) cannot be satisfied by an everywhere-boundary degenerate atlas either. -/
theorem sphereDiskBoundarySet_ne_univ : sphereDiskBoundarySet ≠ Set.univ := by
  intro hcontra
  obtain ⟨v, hv⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have h0 : ((⟨v, hv⟩, ⟨0, mem_closedBall_self zero_le_one⟩) : SphereDisk) ∈
      sphereDiskBoundarySet := hcontra ▸ Set.mem_univ _
  simp [sphereDiskBoundarySet] at h0

/-! ### §4. The freeze: the smooth atlas of `S²×D³` on the collar model

The ONE Mathlib-absent layer, carried as disclosed data (the `CharSurfaceBounding` pattern). -/

/-- The collar bordism model fixed by the project `Bordism` encoding: `J5 = I4.prod (𝓡∂ 1)`. -/
noncomputable abbrev J5 := I4.prod (𝓡∂ 1)

/-- **Statement freeze — the smooth collar atlas of `S²×D³`** (the 3-handle coboundary of DR
sub-piece (1)). The underlying TOPOLOGY is NOT frozen — it is the genuine product-subspace
topology of §3 (compactness is proven against it, and `boundary_eq` pins the frozen manifold
boundary to the genuine frontier slice via `sphereDiskBoundarySet_eq_frontier`). What is frozen is
exactly the atlas layer, whose two missing Mathlib items are:

1. **closed-ball `IsManifold` instance**: `Metric.closedBall` (`Dⁿ`, `n ≥ 2`) has no
   `ChartedSpace`/`IsManifold` instance (`Mathlib.Geometry.Manifold.Instances.Real` provides only
   `Set.Icc`); and
2. **change-of-model transport**: `Bordism` fixes the collar model `J5 = I4.prod (𝓡∂ 1)`, and no
   Mathlib machinery re-models a product atlas (e.g. a future `(𝓡 2).prod (𝓡∂ 3)`-structure on
   `S²×D³`) onto it. (`ModelWithCorners.boundary_of_boundaryless_left` EXISTS but is inapplicable:
   the product splitting `(S²)×(D³)` does not match `J5`'s `(4-dim)×(half-line)` splitting.)

Discharge plan: the standard collar atlas of `S²×D³` (interior charts from the smooth open ball,
boundary charts from polar collar coordinates `S²×S²×[0,1) → S²×(D³∖{0})`), or the Mathlib items
above once they land. -/
structure SphereDiskSmoothData (k : WithTop ℕ∞) where
  /-- Frozen: the collar-model charted structure on `S²×D³` (missing Mathlib item 1 + 2). -/
  [chartW : ChartedSpace
    (ModelProd (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (EuclideanHalfSpace 1)) SphereDisk]
  /-- Frozen: the atlas is `C^k` for the collar model `J5`. -/
  [mfdW : IsManifold J5 k SphereDisk]
  /-- Frozen: the boundary inclusion `S²×S² → S²×D³` is `C^k` for the frozen atlas. -/
  smooth_incl : ContMDiff I4 J5 k sphereDiskIncl
  /-- Frozen: the manifold boundary of the frozen atlas is the genuine frontier slice
  `S² × ∂D³` (falsifiability pin: `sphereDiskBoundarySet_eq_frontier`). -/
  boundary_eq : J5.boundary SphereDisk = sphereDiskBoundarySet

/-! ### §5. The composed bordism and the Freeze-B conditional discharge -/

/-- **The 3-handle bounding as a genuine project `Bordism`**: given the frozen atlas data, `S²×D³`
witnesses `S²×S² ~ ∅` in the `BordismGroup` encoding (compact `J5`-manifold-with-boundary + smooth
injection of `S²×S² ⊔ ∅` onto the boundary). Every field except the four frozen ones is the
genuine §3 topology. -/
noncomputable def sphereDiskBordism (d : SphereDiskSmoothData k) :
    Bordism J5 (sphereProdSM k) (emptySM (X := PUnit) (k := k) (I := I4)) :=
  letI := d.chartW
  letI := d.mfdW
  { W := SphereDisk
    e := Sum.elim sphereDiskIncl (fun z => isEmptyElim z)
    he_smooth := ContMDiff.sumElim d.smooth_incl (fun z => isEmptyElim z)
    he_inj := by
      rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (sphereDiskIncl_injective hab)
      · exact isEmptyElim b
      · exact isEmptyElim a
      · exact isEmptyElim a
    he_boundary := by
      rw [Set.Sum.elim_range]
      simp only [Set.range_eq_empty, Set.union_empty]
      exact range_sphereDiskIncl.trans d.boundary_eq.symm
    g := fun _ => PUnit.unit
    hg := continuous_const
    hg_restrict := by
      funext x
      rcases x with a | z
      · rfl
      · exact isEmptyElim z }

/-- **Freeze B from a bounding bordism** (generic, any carrier): if the distinguished `S²×S²` is
structured-bordant to the empty manifold, its class is zero — `SphereProductBounds` holds. The
generic consumer shape of the §5 construction. -/
theorem SpinSigmaPresentation.sphereProductBounds_of_bordant {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ)
    (h : IsDataBordant ξ R.s2s2 ⟨emptySM, ξ.emptyStr⟩) : R.SphereProductBounds :=
  DataBordismGrp.mk_eq_of_bordant ξ h

/-- **The full Freeze-B discharge package** over a tangential datum on the `S²×S²` model: the
frozen atlas (§4) + a chosen structure on `S²×S²` + the structure's extension over the 3-handle
coboundary (the spin-side packaging — for the genuine spin datum this is "the spin structure of
`S²×S²` extends over `S²×D³`", the structure-level half of DR sub-piece (1)). -/
structure SphereDiskBoundingPackage (ξ : TangentialData PUnit k I4) where
  /-- The frozen smooth-atlas data of `S²×D³` (§4). -/
  smoothData : SphereDiskSmoothData k
  /-- The chosen tangential structure on the concrete `S²×S²`. -/
  str : ξ.Mfd (sphereProdSM k)
  /-- The structure extends over the 3-handle coboundary. -/
  strBor : ξ.Bor (sphereDiskBordism smoothData) str ξ.emptyStr

/-- **Freeze B discharged modulo the named freezes** — the composed conditional: for any
σ-presentation over a tangential datum on the concrete `S²×S²` model whose distinguished `s2s2` IS
the concrete manifold, the §4 atlas freeze + the structure-extension datum yield
`SphereProductBounds`. This is the exact decomposition of Freeze B into (i) the two named
Mathlib-absent atlas items and (ii) the structure-extension geometry — nothing else. -/
theorem sphereProductBounds_of_package {ξ : TangentialData PUnit k I4}
    (R : SpinSigmaPresentation ξ) (P : SphereDiskBoundingPackage ξ)
    (hs : R.s2s2 = ⟨sphereProdSM k, P.str⟩) : R.SphereProductBounds :=
  R.sphereProductBounds_of_bordant
    (hs ▸ ⟨sphereDiskBordism P.smoothData, ⟨P.strBor⟩⟩)

/-- **Non-vacuity upgrade of `trivialPresentation`**: the σ-presentation shape is inhabitable with
the CONCRETE `S²×S²` manifold in the distinguished slot (trivial tangential datum over the `I4`
model) — all the slot's pins discharge on the genuine manifold: `s2s2_rank` by `rfl` on the
rank-2 datum, `s2s2_hyp` by `sphereProdFormDatum_hyp_pin`. Inhabitation witness only, as in
`trivialPresentation` (claims nothing about the freezes on the genuine spin instantiation). -/
noncomputable def trivialSpherePresentation (k : WithTop ℕ∞) :
    SpinSigmaPresentation (trivialData (X := PUnit) (k := k) (I := I4)) where
  sig := 0
  rank _ := 2
  form _ := sphereProdFormDatum
  even_unimod _ := sphereProdFormDatum_even_unimod
  sig_eq _ := by simp [sphereProdFormDatum, hyp_latticeSig]
  s2s2 := ⟨sphereProdSM k, ⟨⟩⟩
  s2s2_rank := rfl
  s2s2_hyp := sphereProdFormDatum_hyp_pin

/-- **The §5 chain is jointly satisfiable modulo exactly the atlas freeze** (consistency guard for
the composed conditional): on the trivial tangential datum the structure-extension data is trivial
(`Bor ≡ PUnit`), so ANY `SphereDiskSmoothData` discharges Freeze B for the concrete-`S²×S²`
presentation — `sphereProductBounds_of_package` exercised end-to-end, its only remaining input
being the two named Mathlib gaps of §4. -/
theorem trivialSpherePresentation_sphereProductBounds (k : WithTop ℕ∞)
    (d : SphereDiskSmoothData k) : (trivialSpherePresentation k).SphereProductBounds :=
  sphereProductBounds_of_package (trivialSpherePresentation k) ⟨d, ⟨⟩, ⟨⟩⟩ rfl

/-! ### §6. The atlas-free alternative: reversal-fixed classes are 2-torsion

The per-class refinement of the kernel-checked no-go mechanism
`dataBordism_two_torsion_of_revStr_trivial` (Phase 5q.F: a datum with globally trivial `revStr`
has a 2-torsion carrier, killing free-grade `ℤ/16` designs). Here the mechanism is used
POSITIVELY, at a single class: if the `S²×S²` structure is a fixed point of `revStr` (plausible
for the genuine spin datum — `H¹(S²×S²;ℤ/2) = 0` — but OPEN, depending on how the instantiation
treats orientation), then `[S²×S²]` is 2-torsion with NO manifold input, and Freeze B reduces to
the carrier having no 2-torsion. Both binders are open for the genuine spin datum (torsion-freeness
of `Ω₄^{Spin}` is downstream of the full iso); the §5 geometric route remains the discharge plan —
this is the route map's honest alternative, not a shortcut claim. -/

/-- **Reversal-fixed classes are 2-torsion**: if `revStr σ = σ` then `[M,σ] + [M,σ] = 0` (the
class is its own inverse, via `negBor`). Per-class refinement of
`dataBordism_two_torsion_of_revStr_trivial`. -/
theorem mk_add_self_eq_zero_of_revStr_fixed {ξ : TangentialData X k I} (p : StrMfd ξ)
    (hrev : ξ.revStr p.2 = p.2) :
    DataBordismGrp.mk ξ p + DataBordismGrp.mk ξ p = 0 := by
  have hneg : -DataBordismGrp.mk ξ p = DataBordismGrp.mk ξ p := by
    show DataBordismGrp.neg ξ (DataBordismGrp.mk ξ p) = DataBordismGrp.mk ξ p
    rw [DataBordismGrp.neg_mk]
    exact congrArg (fun σ => DataBordismGrp.mk ξ ⟨p.1, σ⟩) hrev
  calc DataBordismGrp.mk ξ p + DataBordismGrp.mk ξ p
      = -DataBordismGrp.mk ξ p + DataBordismGrp.mk ξ p := by rw [hneg]
    _ = 0 := neg_add_cancel _

/-- **Freeze B from reversal-fixedness + torsion-freeness** (atlas-free alternative; see section
docstring — both binders open for the genuine spin datum). -/
theorem SpinSigmaPresentation.sphereProductBounds_of_revStr_fixed {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (hrev : ξ.revStr R.s2s2.2 = R.s2s2.2)
    (htf : ∀ x : DataBordismGrp ξ, x + x = 0 → x = 0) : R.SphereProductBounds :=
  htf _ (mk_add_self_eq_zero_of_revStr_fixed R.s2s2 hrev)

end SKEFTHawking.SpinSigmaRoute
