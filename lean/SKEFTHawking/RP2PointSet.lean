import Mathlib

/-!
# W-A ℝP²-witness prerequisite (B4a analogue, one dimension down) — the point-set layer

The carrier for the closed-surface `SingularSurfaceIntersectionForm` machinery: real projective
2-space as the orbit space of the antipodal `ℤˣ`-action on the unit 2-sphere. Mirrors
`RP4PointSet.lean` (Phase 5q.G B4a) one dimension down — this brick supplies the point-set
layer — the action, its continuity and proper discontinuity, and the quotient's
`TopologicalSpace`/`T2Space`/`CompactSpace`/`Nonempty` instances — all from Mathlib's stock
machinery (`t2Space_of_properlyDiscontinuousSMul_of_t2Space`, `Quotient.compactSpace`).
The charted structure (descending the sphere's stereographic charts on hemispheres where the
quotient map is injective) is in `RP2Manifold.lean`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric

namespace SKEFTHawking.RP2PointSet

/-- The unit 2-sphere in `ℝ³`. -/
abbrev S2 : Type := sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1

/-- The antipodal `ℤˣ`-action on the sphere: `u • x = (±1) • x`. -/
instance : SMul ℤˣ S2 where
  smul u x := ⟨((u : ℤ) : ℝ) • x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp x.2, mul_one]
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> norm_num⟩

@[simp] theorem smul_coe (u : ℤˣ) (x : S2) :
    ((u • x : S2) : EuclideanSpace ℝ (Fin (2 + 1))) = ((u : ℤ) : ℝ) • x.1 := rfl

instance : MulAction ℤˣ S2 where
  one_smul x := Subtype.ext (by simp)
  mul_smul u v x := Subtype.ext (by
    simp only [smul_coe]
    rw [Units.val_mul, Int.cast_mul, mul_smul])

instance : ContinuousConstSMul ℤˣ S2 :=
  ⟨fun u => Continuous.subtype_mk (continuous_subtype_val.const_smul (((u : ℤ) : ℝ))) _⟩

/-- The antipodal action is properly discontinuous (`ℤˣ` is finite). -/
instance : ProperlyDiscontinuousSMul ℤˣ S2 :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- **`ℝP²` as the antipodal orbit space `S²/±`.** -/
def RP2 : Type := Quotient (MulAction.orbitRel ℤˣ S2)

instance : TopologicalSpace RP2 :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ S2)))

instance : CompactSpace RP2 :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel ℤˣ S2)))

/-- `ℝP²` is Hausdorff — the properly-discontinuous quotient theorem. -/
instance : T2Space RP2 :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel ℤˣ S2)))

/-- A basepoint: the class of the first coordinate vector. -/
noncomputable instance : Nonempty RP2 :=
  ⟨Quotient.mk _ ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩⟩

/-! ## §2. The hemisphere layer — where the quotient map is an open embedding

For each `x : S²`, the open hemisphere `hemi x = {y | ⟪x,y⟫ > 0}` meets every antipodal pair at
most once, so `Quotient.mk` restricted to it is injective; the orbit map is open
(`isOpenMap_quotient_mk'_mul`), so the restriction is an **open embedding** — the engine that
descends the sphere's charts to `RP2`. -/

open scoped RealInnerProductSpace

/-- The open hemisphere around `x`. -/
def hemi (x : S2) : Set S2 :=
  {y : S2 | 0 < ⟪(x : EuclideanSpace ℝ (Fin (2 + 1))), (y : EuclideanSpace ℝ (Fin (2 + 1)))⟫}

theorem hemi_isOpen (x : S2) : IsOpen (hemi x) :=
  isOpen_lt continuous_const (Continuous.inner continuous_const continuous_subtype_val)

theorem mem_hemi_self (x : S2) : x ∈ hemi x := by
  show 0 < ⟪(x : EuclideanSpace ℝ (Fin (2 + 1))), (x : EuclideanSpace ℝ (Fin (2 + 1)))⟫
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- The quotient map is open (the group-orbit map). -/
theorem isOpenMap_mk :
    IsOpenMap (Quotient.mk (MulAction.orbitRel ℤˣ S2)) :=
  isOpenMap_quotient_mk'_mul (Γ := ℤˣ) (T := S2)

/-- **`Quotient.mk` is injective on a hemisphere** — an antipodal pair never lies in one. -/
theorem mk_injOn_hemi (x : S2) :
    Set.InjOn (Quotient.mk (MulAction.orbitRel ℤˣ S2)) (hemi x) := by
  intro y hy y' hy' hmk
  obtain ⟨u, hu⟩ : y ∈ MulAction.orbit ℤˣ y' := Quotient.eq''.mp hmk
  have hu' : u • y' = y := hu
  rcases Int.units_eq_one_or u with h1 | h1
  · rw [h1, one_smul] at hu'
    exact hu'.symm
  · exfalso
    rw [h1] at hu'
    have hcoe : (y : EuclideanSpace ℝ (Fin (2 + 1)))
        = -(y' : EuclideanSpace ℝ (Fin (2 + 1))) := by
      rw [← hu', smul_coe]
      norm_num
    have h2 : (0 : ℝ) < ⟪(x : EuclideanSpace ℝ (Fin (2 + 1))),
        -(y' : EuclideanSpace ℝ (Fin (2 + 1)))⟫ := hcoe ▸ hy
    rw [inner_neg_right] at h2
    exact absurd hy' (not_lt.mpr (le_of_lt (neg_pos.mp h2)))

/-- **The hemisphere-restricted quotient map is an open embedding** — continuous + injective +
open (composite of the orbit map with the open-subtype inclusion). -/
theorem isOpenEmbedding_mk_hemi (x : S2) :
    Topology.IsOpenEmbedding
      (fun y : ↥(hemi x) => Quotient.mk (MulAction.orbitRel ℤˣ S2) y.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact Continuous.comp continuous_quotient_mk' continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (mk_injOn_hemi x a.2 b.2 hab)
  · exact IsOpenMap.comp isOpenMap_mk ((hemi_isOpen x).isOpenMap_subtype_val)

/-! ## §3. The charted structure — the sphere's charts descend to `RP2`

Per class `[x]`: restrict the sphere's chart at `x` to the hemisphere (`subtypeRestr`), then
lift along the open embedding `mk|_{hemi x}` (`lift_openEmbedding` — the `ChartedSpace.sum`
pattern). The chart source is `mk '' (hemisphere ∩ chart-source)`, which contains `[x]`. -/

/-- The hemisphere as an open set (for `subtypeRestr`). -/
def hemiOpens (x : S2) : TopologicalSpace.Opens S2 := ⟨hemi x, hemi_isOpen x⟩

instance (x : S2) : Nonempty (hemiOpens x) := ⟨⟨x, mem_hemi_self x⟩⟩

/-- **The `RP2` chart at (the class of) `x`**: the sphere chart at `x`, hemisphere-restricted,
lifted along the hemisphere open embedding. -/
noncomputable def rp2Chart (x : S2) :
    OpenPartialHomeomorph RP2 (EuclideanSpace ℝ (Fin 2)) :=
  ((chartAt (EuclideanSpace ℝ (Fin 2)) x).subtypeRestr
      (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).lift_openEmbedding
    (isOpenEmbedding_mk_hemi x)

/-- **`RP2` is a charted space over `ℝ²`** — the descended stereographic atlas. -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) RP2 where
  atlas := Set.range rp2Chart
  chartAt p := rp2Chart p.out
  mem_chart_source p := by
    show p ∈ (rp2Chart p.out).source
    rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨⟨p.out, mem_hemi_self p.out⟩, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact mem_chart_source (EuclideanSpace ℝ (Fin 2)) p.out
    · exact p.out_eq
  chart_mem_atlas p := Set.mem_range_self _

end SKEFTHawking.RP2PointSet
