import Mathlib

/-!
# Phase 5q.G (B-arc, B4a) — `ℝP⁴` as `S⁴/±`: the point-set layer

The carrier for the tied datum's odd witness (`w₁⁴[ℝP⁴] = 1`): real projective 4-space as the
orbit space of the antipodal `ℤˣ`-action on the unit 4-sphere. This brick supplies the
point-set layer — the action, its continuity and proper discontinuity, and the quotient's
`TopologicalSpace`/`T2Space`/`CompactSpace`/`Nonempty` instances — all from Mathlib's stock
machinery (`t2Space_of_properlyDiscontinuousSMul_of_t2Space`, `Quotient.compactSpace`).
The charted structure (descending the sphere's stereographic charts on hemispheres where the
quotient map is injective) is B4b.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric

namespace SKEFTHawking.RP4PointSet

/-- The unit 4-sphere in `ℝ⁵`. -/
abbrev S4 : Type := sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1

/-- The antipodal `ℤˣ`-action on the sphere: `u • x = (±1) • x`. -/
instance : SMul ℤˣ S4 where
  smul u x := ⟨((u : ℤ) : ℝ) • x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp x.2, mul_one]
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> norm_num⟩

@[simp] theorem smul_coe (u : ℤˣ) (x : S4) :
    ((u • x : S4) : EuclideanSpace ℝ (Fin (4 + 1))) = ((u : ℤ) : ℝ) • x.1 := rfl

instance : MulAction ℤˣ S4 where
  one_smul x := Subtype.ext (by simp)
  mul_smul u v x := Subtype.ext (by
    simp only [smul_coe]
    rw [Units.val_mul, Int.cast_mul, mul_smul])

instance : ContinuousConstSMul ℤˣ S4 :=
  ⟨fun u => Continuous.subtype_mk (continuous_subtype_val.const_smul (((u : ℤ) : ℝ))) _⟩

/-- The antipodal action is properly discontinuous (`ℤˣ` is finite). -/
instance : ProperlyDiscontinuousSMul ℤˣ S4 :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- **`ℝP⁴` as the antipodal orbit space `S⁴/±`.** -/
def RP4 : Type := Quotient (MulAction.orbitRel ℤˣ S4)

instance : TopologicalSpace RP4 :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ S4)))

instance : CompactSpace RP4 :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel ℤˣ S4)))

/-- `ℝP⁴` is Hausdorff — the properly-discontinuous quotient theorem. -/
instance : T2Space RP4 :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel ℤˣ S4)))

/-- A basepoint: the class of the first coordinate vector. -/
noncomputable instance : Nonempty RP4 :=
  ⟨Quotient.mk _ ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩⟩

/-! ## §2. The hemisphere layer — where the quotient map is an open embedding

For each `x : S⁴`, the open hemisphere `hemi x = {y | ⟪x,y⟫ > 0}` meets every antipodal pair at
most once, so `Quotient.mk` restricted to it is injective; the orbit map is open
(`isOpenMap_quotient_mk'_mul`), so the restriction is an **open embedding** — the engine that
descends the sphere's charts to `RP4` (B4b-2). -/

open scoped RealInnerProductSpace

/-- The open hemisphere around `x`. -/
def hemi (x : S4) : Set S4 :=
  {y : S4 | 0 < ⟪(x : EuclideanSpace ℝ (Fin (4 + 1))), (y : EuclideanSpace ℝ (Fin (4 + 1)))⟫}

theorem hemi_isOpen (x : S4) : IsOpen (hemi x) :=
  isOpen_lt continuous_const (Continuous.inner continuous_const continuous_subtype_val)

theorem mem_hemi_self (x : S4) : x ∈ hemi x := by
  show 0 < ⟪(x : EuclideanSpace ℝ (Fin (4 + 1))), (x : EuclideanSpace ℝ (Fin (4 + 1)))⟫
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- The quotient map is open (the group-orbit map). -/
theorem isOpenMap_mk :
    IsOpenMap (Quotient.mk (MulAction.orbitRel ℤˣ S4)) :=
  isOpenMap_quotient_mk'_mul (Γ := ℤˣ) (T := S4)

/-- **`Quotient.mk` is injective on a hemisphere** — an antipodal pair never lies in one. -/
theorem mk_injOn_hemi (x : S4) :
    Set.InjOn (Quotient.mk (MulAction.orbitRel ℤˣ S4)) (hemi x) := by
  intro y hy y' hy' hmk
  obtain ⟨u, hu⟩ : y ∈ MulAction.orbit ℤˣ y' := Quotient.eq''.mp hmk
  have hu' : u • y' = y := hu
  rcases Int.units_eq_one_or u with h1 | h1
  · rw [h1, one_smul] at hu'
    exact hu'.symm
  · exfalso
    rw [h1] at hu'
    have hcoe : (y : EuclideanSpace ℝ (Fin (4 + 1)))
        = -(y' : EuclideanSpace ℝ (Fin (4 + 1))) := by
      rw [← hu', smul_coe]
      norm_num
    have h2 : (0 : ℝ) < ⟪(x : EuclideanSpace ℝ (Fin (4 + 1))),
        -(y' : EuclideanSpace ℝ (Fin (4 + 1)))⟫ := hcoe ▸ hy
    rw [inner_neg_right] at h2
    exact absurd hy' (not_lt.mpr (le_of_lt (neg_pos.mp h2)))

/-- **The hemisphere-restricted quotient map is an open embedding** — continuous + injective +
open (composite of the orbit map with the open-subtype inclusion). -/
theorem isOpenEmbedding_mk_hemi (x : S4) :
    Topology.IsOpenEmbedding
      (fun y : ↥(hemi x) => Quotient.mk (MulAction.orbitRel ℤˣ S4) y.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact Continuous.comp continuous_quotient_mk' continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (mk_injOn_hemi x a.2 b.2 hab)
  · exact IsOpenMap.comp isOpenMap_mk ((hemi_isOpen x).isOpenMap_subtype_val)

/-! ## §3. The charted structure — the sphere's charts descend to `RP4`

Per class `[x]`: restrict the sphere's chart at `x` to the hemisphere (`subtypeRestr`), then
lift along the open embedding `mk|_{hemi x}` (`lift_openEmbedding` — the `ChartedSpace.sum`
pattern). The chart source is `mk '' (hemisphere ∩ chart-source)`, which contains `[x]`. -/

/-- The hemisphere as an open set (for `subtypeRestr`). -/
def hemiOpens (x : S4) : TopologicalSpace.Opens S4 := ⟨hemi x, hemi_isOpen x⟩

instance (x : S4) : Nonempty (hemiOpens x) := ⟨⟨x, mem_hemi_self x⟩⟩

/-- **The `RP4` chart at (the class of) `x`**: the sphere chart at `x`, hemisphere-restricted,
lifted along the hemisphere open embedding. -/
noncomputable def rp4Chart (x : S4) :
    OpenPartialHomeomorph RP4 (EuclideanSpace ℝ (Fin 4)) :=
  ((chartAt (EuclideanSpace ℝ (Fin 4)) x).subtypeRestr
      (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).lift_openEmbedding
    (isOpenEmbedding_mk_hemi x)

/-- **`RP4` is a charted space over `ℝ⁴`** — the descended stereographic atlas. -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 4)) RP4 where
  atlas := Set.range rp4Chart
  chartAt p := rp4Chart p.out
  mem_chart_source p := by
    show p ∈ (rp4Chart p.out).source
    rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨⟨p.out, mem_hemi_self p.out⟩, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact mem_chart_source (EuclideanSpace ℝ (Fin 4)) p.out
    · exact p.out_eq
  chart_mem_atlas p := Set.mem_range_self _

end SKEFTHawking.RP4PointSet
