/-
# The Euclidean-carrier `ℝP³ = S³_𝔼/±`: point-set layer + central-projection coordinate charts

The geometric substrate for the `H₄(ℝP³;ℤ) = H₅(ℝP³;ℤ) = 0` termination input (the 4-chart
good-cover Mayer–Vietoris telescope). Mirrors `RP4PointSet` one dimension down, on the sphere
`S3E := Metric.sphere (0 : 𝔼⁴) 1` — the exact domain of `KummerRP3SphereHomeo.sphHomeoS3`, so the
final vanishing transports to the pinned `ℂ²`-carrier `RP3top` along the descended homeomorphism.

Contents:
* the antipodal `ℤˣ`-action on `S3E`, its quotient `RP3E` with
  `TopologicalSpace`/`T2Space`/`CompactSpace` instances, and the fiber description `fiberE_pair`;
* the four **coordinate hemispheres** `hemiC i = {y | 0 < y i}` (`i : Fin 4`), on which the
  quotient map `mkE` is an open embedding (`isOpenEmbedding_mkE_hemiC`);
* the four **charts** `UE i = mkE '' hemiC i`, open, with the saturation membership law
  `mkE_mem_UE_iff : mkE y ∈ UE i ↔ y i ≠ 0` and the cover `UE_cover`;
* the **central-projection chart homeomorphism** `chartHomeo i : ↥(hemiC i) ≃ₜ 𝔼³`,
  `y ↦ (y (i.succAbove j) / y i)ⱼ` — under which coordinate-sign lune conditions on `S³`
  correspond to open half-space conditions on `𝔼³` (the convexity input for the acyclicity
  engine `SingularConvexSubAcyclicInt.homology_chartConvexSub_eq_zeroInt`);
* the composite chart `charted i : ↥(UE i) ≃ₜ ↥(Set.univ : Set 𝔼³)` with its evaluation law
  `charted_coe`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib

open Metric Topology

namespace SKEFTHawking.KummerRP3EuclCharts

/-! ## §1. The sphere, the antipodal action, and the quotient `RP3E` -/

/-- The unit 3-sphere in `𝔼⁴` — the exact domain of `KummerRP3SphereHomeo.sphHomeoS3`. -/
abbrev S3E : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The antipodal `ℤˣ`-action on the sphere: `u • x = (±1) • x`. -/
instance : SMul ℤˣ S3E where
  smul u x := ⟨((u : ℤ) : ℝ) • x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp x.2, mul_one]
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> norm_num⟩

@[simp] theorem smul_coe (u : ℤˣ) (x : S3E) :
    ((u • x : S3E) : EuclideanSpace ℝ (Fin 4)) = ((u : ℤ) : ℝ) • x.1 := rfl

instance : MulAction ℤˣ S3E where
  one_smul x := Subtype.ext (by simp)
  mul_smul u v x := Subtype.ext (by
    simp only [smul_coe]
    rw [Units.val_mul, Int.cast_mul, mul_smul])

instance : ContinuousConstSMul ℤˣ S3E :=
  ⟨fun u => Continuous.subtype_mk (continuous_subtype_val.const_smul (((u : ℤ) : ℝ))) _⟩

/-- The antipodal action is properly discontinuous (`ℤˣ` is finite). -/
instance : ProperlyDiscontinuousSMul ℤˣ S3E :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- **`ℝP³` on the Euclidean carrier** — the antipodal orbit space `S³_𝔼/±`. -/
def RP3E : Type := Quotient (MulAction.orbitRel ℤˣ S3E)

instance : TopologicalSpace RP3E :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ S3E)))

instance : CompactSpace RP3E :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel ℤˣ S3E)))

/-- `RP3E` is Hausdorff — the properly-discontinuous quotient theorem. -/
instance : T2Space RP3E :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel ℤˣ S3E)))

/-- The `TopCat` carrier of `RP3E`. -/
abbrev RP3Etop : TopCat := TopCat.of RP3E

/-- The quotient map `S³_𝔼 → ℝP³_𝔼`. -/
def mkE (y : S3E) : RP3E := Quotient.mk (MulAction.orbitRel ℤˣ S3E) y

theorem continuous_mkE : Continuous mkE := continuous_quotient_mk'

/-- The quotient map is open (the group-orbit map). -/
theorem isOpenMap_mkE : IsOpenMap mkE :=
  isOpenMap_quotient_mk'_mul (Γ := ℤˣ) (T := S3E)

theorem mkE_surjective : Function.Surjective mkE := Quotient.mk_surjective

/-- Antipodal descent: `mkE ((-1) • y) = mkE y`. -/
theorem mkE_neg_smul (y : S3E) : mkE ((-1 : ℤˣ) • y) = mkE y :=
  Quotient.sound ⟨-1, rfl⟩

/-- **The fiber description**: `mkE x = mkE y` forces `x = y` or `x = (-1) • y`. -/
theorem fiberE_pair {x y : S3E} (h : mkE x = mkE y) : x = y ∨ x = (-1 : ℤˣ) • y := by
  obtain ⟨u, hu⟩ : x ∈ MulAction.orbit ℤˣ y := Quotient.eq''.mp h
  have hu' : u • y = x := hu
  rcases Int.units_eq_one_or u with h1 | h1
  · left; rw [h1, one_smul] at hu'; exact hu'.symm
  · right; rw [h1] at hu'; exact hu'.symm

@[simp] theorem neg_one_smul_apply (y : S3E) (k : Fin 4) :
    (((-1 : ℤˣ) • y : S3E) : EuclideanSpace ℝ (Fin 4)) k = -(y : EuclideanSpace ℝ (Fin 4)) k := by
  rw [smul_coe]
  norm_num

/-! ## §2. Coordinate hemispheres and the open-embedding layer -/

/-- The open coordinate hemisphere `{y ∈ S³ | 0 < y i}`. -/
def hemiC (i : Fin 4) : Set S3E :=
  {y : S3E | 0 < (y : EuclideanSpace ℝ (Fin 4)) i}

theorem hemiC_isOpen (i : Fin 4) : IsOpen (hemiC i) :=
  isOpen_lt continuous_const (by fun_prop)

/-- `mkE` is injective on a coordinate hemisphere — an antipodal pair never lies in one. -/
theorem mkE_injOn_hemiC (i : Fin 4) : Set.InjOn mkE (hemiC i) := by
  intro y hy y' hy' hmk
  rcases fiberE_pair hmk with h | h
  · exact h
  · exfalso
    have hcoord : (y : EuclideanSpace ℝ (Fin 4)) i = -(y' : EuclideanSpace ℝ (Fin 4)) i := by
      rw [h]; exact neg_one_smul_apply y' i
    have h2 : (0 : ℝ) < -(y' : EuclideanSpace ℝ (Fin 4)) i := hcoord ▸ hy
    exact absurd hy' (not_lt.mpr (le_of_lt (neg_pos.mp h2)))

/-- **The hemisphere-restricted quotient map is an open embedding.** -/
theorem isOpenEmbedding_mkE_hemiC (i : Fin 4) :
    Topology.IsOpenEmbedding (fun y : ↥(hemiC i) => mkE y.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_mkE.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (mkE_injOn_hemiC i a.2 b.2 hab)
  · exact IsOpenMap.comp isOpenMap_mkE ((hemiC_isOpen i).isOpenMap_subtype_val)

/-! ## §3. The four charts `UE i` and their membership law -/

/-- **The `i`-th chart of `ℝP³_𝔼`** — the image of the `i`-th coordinate hemisphere. -/
def UE (i : Fin 4) : Set RP3E := mkE '' hemiC i

theorem UE_isOpen (i : Fin 4) : IsOpen (UE i) :=
  isOpenMap_mkE _ (hemiC_isOpen i)

/-- **The saturation membership law**: `mkE y ∈ UE i ↔ y i ≠ 0`. -/
theorem mkE_mem_UE_iff {y : S3E} {i : Fin 4} :
    mkE y ∈ UE i ↔ (y : EuclideanSpace ℝ (Fin 4)) i ≠ 0 := by
  constructor
  · rintro ⟨h, hh, hmk⟩
    rcases fiberE_pair hmk with heq | heq
    · rw [← heq]; exact ne_of_gt hh
    · have hh' : (0 : ℝ) < (((-1 : ℤˣ) • y : S3E) : EuclideanSpace ℝ (Fin 4)) i := by
        rw [← heq]; exact hh
      rw [neg_one_smul_apply] at hh'
      exact fun h0 => by rw [h0, neg_zero] at hh'; exact lt_irrefl 0 hh'
  · intro hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact ⟨(-1 : ℤˣ) • y, by simpa [hemiC] using hneg, mkE_neg_smul y⟩
    · exact ⟨y, hpos, rfl⟩

/-- Every class has a representative with some nonzero coordinate — the four charts cover. -/
theorem UE_cover : UE 0 ∪ UE 1 ∪ UE 2 ∪ UE 3 = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨y, rfl⟩ := mkE_surjective q
  by_cases h0 : (y : EuclideanSpace ℝ (Fin 4)) 0 ≠ 0
  · exact Or.inl (Or.inl (Or.inl (mkE_mem_UE_iff.mpr h0)))
  by_cases h1 : (y : EuclideanSpace ℝ (Fin 4)) 1 ≠ 0
  · exact Or.inl (Or.inl (Or.inr (mkE_mem_UE_iff.mpr h1)))
  by_cases h2 : (y : EuclideanSpace ℝ (Fin 4)) 2 ≠ 0
  · exact Or.inl (Or.inr (mkE_mem_UE_iff.mpr h2))
  by_cases h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 ≠ 0
  · exact Or.inr (mkE_mem_UE_iff.mpr h3)
  exfalso
  rw [not_ne_iff] at h0 h1 h2 h3
  have hzero : (y : EuclideanSpace ℝ (Fin 4)) = 0 := by
    apply WithLp.ofLp_injective
    funext k
    fin_cases k <;> assumption
  have hnorm := mem_sphere_zero_iff_norm.mp y.2
  rw [hzero] at hnorm
  simp at hnorm

/-! ## §4. The central-projection chart homeomorphism `↥(hemiC i) ≃ₜ 𝔼³` -/

noncomputable section

/-- The unnormalized inverse-chart vector: coordinate `i` set to `1`, the rest to `z`. -/
def wvec (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (Fin.insertNth (α := fun _ => ℝ) i 1 (WithLp.ofLp z))

@[simp] theorem wvec_apply_self (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) :
    wvec i z i = 1 := by
  show Fin.insertNth (α := fun _ => ℝ) i 1 (WithLp.ofLp z) i = 1
  simp

@[simp] theorem wvec_apply_succAbove (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    wvec i z (i.succAbove j) = z j := by
  show Fin.insertNth (α := fun _ => ℝ) i 1 (WithLp.ofLp z) (i.succAbove j) = z j
  simp

theorem wvec_ne_zero (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) : wvec i z ≠ 0 := by
  intro h0
  have h1 : wvec i z i = 1 := wvec_apply_self i z
  rw [h0] at h1
  simp at h1

theorem wvec_norm_pos (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) : 0 < ‖wvec i z‖ :=
  norm_pos_iff.mpr (wvec_ne_zero i z)

theorem continuous_wvec (i : Fin 4) : Continuous fun z => wvec i z := by
  refine continuous_induced_rng.mpr ?_
  show Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
    Fin.insertNth (α := fun _ => ℝ) i 1 (WithLp.ofLp z)
  have hof : Continuous fun z : EuclideanSpace ℝ (Fin 3) => (WithLp.ofLp z : Fin 3 → ℝ) := by
    fun_prop
  exact (continuous_const (y := (1 : ℝ))).finInsertNth i hof

/-- The forward central projection `y ↦ (y (i.succAbove j) / y i)ⱼ`. -/
def centralProj (i : Fin 4) (y : ↥(hemiC i)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j =>
    (y.1 : EuclideanSpace ℝ (Fin 4)) (i.succAbove j) / (y.1 : EuclideanSpace ℝ (Fin 4)) i

@[simp] theorem centralProj_apply (i : Fin 4) (y : ↥(hemiC i)) (j : Fin 3) :
    centralProj i y j
      = (y.1 : EuclideanSpace ℝ (Fin 4)) (i.succAbove j) / (y.1 : EuclideanSpace ℝ (Fin 4)) i :=
  rfl

theorem continuous_centralProj (i : Fin 4) : Continuous (centralProj i) := by
  refine continuous_induced_rng.mpr (continuous_pi fun j => Continuous.div ?_ ?_ ?_)
  · fun_prop
  · fun_prop
  · exact fun y => ne_of_gt y.2

/-- The inverse central projection `z ↦ wvec i z / ‖wvec i z‖`, landing in the hemisphere. -/
def centralInv (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) : ↥(hemiC i) :=
  ⟨⟨‖wvec i z‖⁻¹ • wvec i z, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (ne_of_gt (wvec_norm_pos i z))]⟩, by
    show (0 : ℝ) < (‖wvec i z‖⁻¹ • wvec i z) i
    have : (‖wvec i z‖⁻¹ • wvec i z) i = ‖wvec i z‖⁻¹ * wvec i z i := rfl
    rw [this, wvec_apply_self, mul_one]
    exact inv_pos.mpr (wvec_norm_pos i z)⟩

theorem continuous_centralInv (i : Fin 4) : Continuous (centralInv i) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact ((continuous_wvec i).norm.inv₀ fun z => ne_of_gt (wvec_norm_pos i z)).smul
    (continuous_wvec i)

theorem centralProj_centralInv (i : Fin 4) (z : EuclideanSpace ℝ (Fin 3)) :
    centralProj i (centralInv i z) = z := by
  apply WithLp.ofLp_injective
  funext j
  show centralProj i (centralInv i z) j = z j
  rw [centralProj_apply]
  show (‖wvec i z‖⁻¹ • wvec i z) (i.succAbove j) / (‖wvec i z‖⁻¹ • wvec i z) i = z j
  have h1 : (‖wvec i z‖⁻¹ • wvec i z) (i.succAbove j) = ‖wvec i z‖⁻¹ * wvec i z (i.succAbove j) :=
    rfl
  have h2 : (‖wvec i z‖⁻¹ • wvec i z) i = ‖wvec i z‖⁻¹ * wvec i z i := rfl
  rw [h1, h2, wvec_apply_self, wvec_apply_succAbove,
    mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt (wvec_norm_pos i z))), div_one]

theorem wvec_centralProj (i : Fin 4) (y : ↥(hemiC i)) :
    wvec i (centralProj i y)
      = ((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹ • (y.1 : EuclideanSpace ℝ (Fin 4)) := by
  apply WithLp.ofLp_injective
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · show wvec i (centralProj i y) i = (((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹
      • (y.1 : EuclideanSpace ℝ (Fin 4))) i
    rw [wvec_apply_self]
    show (1 : ℝ) = ((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹ * (y.1 : EuclideanSpace ℝ (Fin 4)) i
    rw [inv_mul_cancel₀ (ne_of_gt y.2)]
  · intro j
    show wvec i (centralProj i y) (i.succAbove j) = (((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹
      • (y.1 : EuclideanSpace ℝ (Fin 4))) (i.succAbove j)
    rw [wvec_apply_succAbove, centralProj_apply]
    show (y.1 : EuclideanSpace ℝ (Fin 4)) (i.succAbove j) / (y.1 : EuclideanSpace ℝ (Fin 4)) i
      = ((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹ * (y.1 : EuclideanSpace ℝ (Fin 4)) (i.succAbove j)
    rw [div_eq_inv_mul]

theorem centralInv_centralProj (i : Fin 4) (y : ↥(hemiC i)) :
    centralInv i (centralProj i y) = y := by
  have hipos : (0 : ℝ) < (y.1 : EuclideanSpace ℝ (Fin 4)) i := y.2
  have hnorm : ‖wvec i (centralProj i y)‖ = ((y.1 : EuclideanSpace ℝ (Fin 4)) i)⁻¹ := by
    rw [wvec_centralProj, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hipos, mem_sphere_zero_iff_norm.mp y.1.2, mul_one]
  apply Subtype.ext
  apply Subtype.ext
  show ‖wvec i (centralProj i y)‖⁻¹ • wvec i (centralProj i y) = _
  rw [hnorm, wvec_centralProj, inv_inv, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hipos), one_smul]

/-- **The central-projection chart homeomorphism** `↥(hemiC i) ≃ₜ 𝔼³`. -/
def chartHomeo (i : Fin 4) : ↥(hemiC i) ≃ₜ EuclideanSpace ℝ (Fin 3) where
  toFun := centralProj i
  invFun := centralInv i
  left_inv := centralInv_centralProj i
  right_inv := centralProj_centralInv i
  continuous_toFun := continuous_centralProj i
  continuous_invFun := continuous_centralInv i

/-! ## §5. The composite chart `↥(UE i) ≃ₜ ↥(univ : Set 𝔼³)` and its evaluation law -/

/-- The hemisphere ≃ chart homeomorphism from the open embedding (range = image). -/
def hemiEquivUE (i : Fin 4) : ↥(hemiC i) ≃ₜ ↥(UE i) :=
  ((isOpenEmbedding_mkE_hemiC i).toHomeomorph).trans
    (Homeomorph.setCongr (by rw [UE, Set.image_eq_range]))

@[simp] theorem hemiEquivUE_coe (i : Fin 4) (y : ↥(hemiC i)) :
    ((hemiEquivUE i y : ↥(UE i)) : RP3E) = mkE y.1 := rfl

/-- **The composite chart** `↥(UE i) ≃ₜ ↥(univ : Set 𝔼³)` — the shape consumed by
`homology_chartConvexSub_eq_zeroInt` (with `V = Set.univ`). -/
def charted (i : Fin 4) : ↥(UE i) ≃ₜ ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
  ((hemiEquivUE i).symm.trans (chartHomeo i)).trans (Homeomorph.Set.univ _).symm

/-- Evaluation of the composite chart: on the class of a hemisphere point `y`, the chart value is
the central projection of `y`. -/
theorem charted_coe (i : Fin 4) (y : ↥(hemiC i)) :
    ((charted i (hemiEquivUE i y) : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) :
        EuclideanSpace ℝ (Fin 3))
      = centralProj i y := by
  show ((Homeomorph.Set.univ _).symm (chartHomeo i ((hemiEquivUE i).symm (hemiEquivUE i y))) :
    EuclideanSpace ℝ (Fin 3)) = centralProj i y
  rw [Homeomorph.symm_apply_apply]
  rfl

end

end SKEFTHawking.KummerRP3EuclCharts
