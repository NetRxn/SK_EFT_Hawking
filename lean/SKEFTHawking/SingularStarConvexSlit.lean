/-
# Phase 5q.H (N5 witness tower) — star-convex contractions and the slit-plane polar cover of ℝ²∖{0}

Input layer for the product-homology arc's H₂ slice (`SphereProdHData` residue): the
`H_{≤2}(S²×S¹)`-grade Mayer–Vietoris runs over the doubly-punctured sphere `S²∖{v,−v} ≃ₜ ℝ²∖{0}`
(stereographic), and `ℝ²∖{0}` carries the classic SLIT-PLANE polar cover — two open slit planes
(each star-shaped, hence contractible) whose union is `ℝ²∖{0}` and whose intersection is the
two-component `{x₀ ≠ 0}` (each half convex; the S⁰-shape `SingularClopenSplitInt` splits).

* §1 — `starConvexContraction`: the straight-line contraction of a STAR-CONVEX subspace to its
  star center, with the two slice lemmas — the verbatim generalization of
  `SingularConvexSubAcyclic.convexContraction` (which is the `Convex.starConvex` special case;
  the segment only ever needs one endpoint fixed at the center). Coefficient-agnostic (pure
  topology), so BOTH towers consume it.
* §2 — the slit-plane cover data in `ℝ²`: the closed rays `rayUp`/`rayDown`, the open slit planes
  `slitUp = (rayDown)ᶜ` / `slitDown = (rayUp)ᶜ`, their star-convexity at `±e₁` (the poles
  `(0, ±1)`), the cover identity `slitUp ∪ slitDown = {0}ᶜ`, the intersection identity
  `slitUp ∩ slitDown = {x₀ ≠ 0}`, and the two convex open half-planes `posHalf`/`negHalf` with
  `posHalf ∪ negHalf = {x₀ ≠ 0}`, `posHalf ∩ negHalf = ∅` (the clopen-split input shape).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularRelativeHomologyMod2

open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)

namespace SKEFTHawking.SingularStarConvexSlit

/-! ## §1. The star-convex straight-line contraction -/

/-- Star-convexity membership for the straight-line contraction: the segment from a point of `C`
to the star center stays in `C`. -/
theorem starContraction_mem {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {p₀ : EuclideanSpace ℝ (Fin n)} (hC : StarConvex ℝ p₀ C)
    (x : ↥(sub (X := Eucl n) C)) (t : unitInterval) :
    (1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n)) + (t : ℝ) • p₀ ∈ C := by
  rw [add_comm]
  exact hC x.2 t.2.1 (by linarith [t.2.2]) (by ring)

/-- The **straight-line contraction of a star-convex subspace** to its star center `p₀` — the
`StarConvex` generalization of `convexContraction` (`Convex.starConvex` recovers that case). -/
noncomputable def starConvexContraction {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {p₀ : EuclideanSpace ℝ (Fin n)} (hC : StarConvex ℝ p₀ C) :
    C(↑(sub (X := Eucl n) C) × unitInterval, ↑(sub (X := Eucl n) C)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin n)) + (p.2 : ℝ) • p₀,
    starContraction_mem hC p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.add ?_ ?_) _
    · exact Continuous.smul
        (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
        (continuous_subtype_val.comp continuous_fst)
    · exact Continuous.smul (continuous_subtype_val.comp continuous_snd) continuous_const

theorem slice_starConvexContraction_zero {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {p₀ : EuclideanSpace ℝ (Fin n)} (hC : StarConvex ℝ p₀ C) :
    slice (starConvexContraction hC) 0 = ContinuousMap.id ↑(sub (X := Eucl n) C) := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((0 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n))
      + ((0 : unitInterval) : ℝ) • p₀ = (x : _)
  simp

theorem slice_starConvexContraction_one {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {p₀ : EuclideanSpace ℝ (Fin n)} (hC : StarConvex ℝ p₀ C) (hp₀ : p₀ ∈ C) :
    slice (starConvexContraction hC) 1
      = ContinuousMap.const ↑(sub (X := Eucl n) C) ⟨p₀, hp₀⟩ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((1 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n))
      + ((1 : unitInterval) : ℝ) • p₀ = p₀
  simp

/-! ## §2. The slit-plane polar cover of `ℝ²∖{0}` -/

/-- The closed upward ray `{x₀ = 0, x₁ ≥ 0}`. -/
def rayUp : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 = 0 ∧ 0 ≤ x 1}

/-- The closed downward ray `{x₀ = 0, x₁ ≤ 0}`. -/
def rayDown : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 = 0 ∧ x 1 ≤ 0}

/-- The slit plane cut along the DOWNWARD ray (contains the upper pole `(0,1)`). -/
def slitUp : Set (EuclideanSpace ℝ (Fin 2)) := rayDownᶜ

/-- The slit plane cut along the UPWARD ray (contains the lower pole `(0,−1)`). -/
def slitDown : Set (EuclideanSpace ℝ (Fin 2)) := rayUpᶜ

/-- The upper pole `(0, 1)`. -/
noncomputable def poleUp : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)

/-- The lower pole `(0, −1)`. -/
noncomputable def poleDown : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (-1 : ℝ)

theorem rayUp_isClosed : IsClosed rayUp := by
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous
  exact (isClosed_eq h0 continuous_const).inter (isClosed_le continuous_const h1)

theorem rayDown_isClosed : IsClosed rayDown := by
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous
  exact (isClosed_eq h0 continuous_const).inter (isClosed_le h1 continuous_const)

theorem slitUp_isOpen : IsOpen slitUp := rayDown_isClosed.isOpen_compl

theorem slitDown_isOpen : IsOpen slitDown := rayUp_isClosed.isOpen_compl

@[simp] theorem poleUp_apply_zero : poleUp 0 = 0 := by
  simp [poleUp]

@[simp] theorem poleUp_apply_one : poleUp 1 = 1 := by
  simp [poleUp]

@[simp] theorem poleDown_apply_zero : poleDown 0 = 0 := by
  simp [poleDown]

@[simp] theorem poleDown_apply_one : poleDown 1 = -1 := by
  simp [poleDown]

/-- The upper pole lies in the upper slit plane (off the downward ray). -/
theorem poleUp_mem_slitUp : poleUp ∈ slitUp := by
  intro h
  have h1 : poleUp 1 ≤ 0 := h.2
  rw [poleUp_apply_one] at h1
  linarith

/-- The lower pole lies in the lower slit plane (off the upward ray). -/
theorem poleDown_mem_slitDown : poleDown ∈ slitDown := by
  intro h
  have h1 : (0 : ℝ) ≤ poleDown 1 := h.2
  rw [poleDown_apply_one] at h1
  linarith

/-- **The upper slit plane is star-shaped at the upper pole**: a segment from `(0,1)` can only
re-enter the downward ray if its far endpoint already sits on the closed lower axis, which the
slit removed. -/
theorem starConvex_slitUp : StarConvex ℝ poleUp slitUp := by
  intro y hy a b ha hb hab hmem
  obtain ⟨h0, h1⟩ := hmem
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    poleUp_apply_zero, mul_zero, zero_add] at h0
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    poleUp_apply_one, mul_one] at h1
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- b = 0 ⟹ a = 1 ⟹ the point is the pole itself, off the ray
    rw [← hb0, zero_mul] at h1
    have ha1 : a = 1 := by linarith
    rw [ha1] at h1
    linarith
  · -- b > 0 ⟹ y₀ = 0, and y off the down-ray forces y₁ > 0 ⟹ x₁ > 0
    have hy0 : y 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (by positivity)
      · exact h
    have hy1 : 0 < y 1 := by
      by_contra hle
      exact hy ⟨hy0, le_of_not_gt hle⟩
    nlinarith

/-- **The lower slit plane is star-shaped at the lower pole** (mirror). -/
theorem starConvex_slitDown : StarConvex ℝ poleDown slitDown := by
  intro y hy a b ha hb hab hmem
  obtain ⟨h0, h1⟩ := hmem
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    poleDown_apply_zero, mul_zero, zero_add] at h0
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    poleDown_apply_one, mul_neg_one] at h1
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0, zero_mul] at h1
    have ha1 : a = 1 := by linarith
    rw [ha1] at h1
    linarith
  · have hy0 : y 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (by positivity)
      · exact h
    have hy1 : y 1 < 0 := by
      by_contra hle
      exact hy ⟨hy0, le_of_not_gt hle⟩
    nlinarith

/-- **The cover identity**: the two slit planes exhaust the punctured plane,
`slitUp ∪ slitDown = {0}ᶜ` (the rays meet exactly at the origin). -/
theorem slitUp_union_slitDown : slitUp ∪ slitDown = ({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
  rw [slitUp, slitDown, ← Set.compl_inter]
  refine congrArg _ (Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩)
  · exact ⟨⟨rfl, le_of_eq rfl⟩, rfl, le_of_eq rfl⟩
  · rintro x ⟨⟨h0, h1d⟩, -, h1u⟩
    refine PiLp.ext fun i => ?_
    fin_cases i
    · exact h0
    · exact le_antisymm h1d h1u

/-- **The intersection identity**: the slit planes meet in the axis complement,
`slitUp ∩ slitDown = {x₀ ≠ 0}` (the rays union to the whole vertical axis). -/
theorem slitUp_inter_slitDown :
    slitUp ∩ slitDown = {x : EuclideanSpace ℝ (Fin 2) | x 0 ≠ 0} := by
  rw [slitUp, slitDown, ← Set.compl_union]
  refine congrArg _ (Set.ext fun x => ?_)
  constructor
  · rintro (⟨h0, -⟩ | ⟨h0, -⟩) <;> exact h0
  · intro h0
    rcases le_or_gt (x 1) 0 with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1.le⟩

/-- The open right half-plane `{x₀ > 0}` — one component of the slit planes' intersection. -/
def posHalf : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 < x 0}

/-- The open left half-plane `{x₀ < 0}` — the other component. -/
def negHalf : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 < 0}

theorem posHalf_isOpen : IsOpen posHalf :=
  isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous

theorem negHalf_isOpen : IsOpen negHalf :=
  isOpen_lt (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const

/-- The coordinate evaluation `x ↦ x 0` is a linear map (the `EuclideanSpace.proj` CLM's
underlying linearity, repackaged for the half-space convexity lemmas). -/
theorem isLinearMap_coord_zero :
    IsLinearMap ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x 0) :=
  ⟨fun x y => (EuclideanSpace.proj (0 : Fin 2)).map_add x y,
    fun c x => (EuclideanSpace.proj (0 : Fin 2)).map_smul c x⟩

/-- The half-planes are convex (sublevel/superlevel sets of the linear coordinate). -/
theorem posHalf_convex : Convex ℝ posHalf := by
  have := convex_halfSpace_gt isLinearMap_coord_zero 0
  simpa [posHalf] using this

theorem negHalf_convex : Convex ℝ negHalf := by
  have := convex_halfSpace_lt isLinearMap_coord_zero 0
  simpa [negHalf] using this

/-- The half-planes partition the axis complement: `posHalf ∪ negHalf = {x₀ ≠ 0}`. -/
theorem posHalf_union_negHalf :
    posHalf ∪ negHalf = {x : EuclideanSpace ℝ (Fin 2) | x 0 ≠ 0} := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h
  · intro h
    rcases h.lt_or_gt with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The half-planes are disjoint: `posHalf ∩ negHalf = ∅` (the S⁰ shape — two components, the
`SingularClopenSplitInt` input at the intersection stage of the slit-plane MV). -/
theorem posHalf_inter_negHalf : posHalf ∩ negHalf = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have h1 : 0 < x 0 := hx.1
  have h2 : x 0 < 0 := hx.2
  linarith

/-- The half-plane poles witness nonemptiness: `(±1, 0)`-style points. -/
theorem posHalf_nonempty : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) ∈ posHalf := by
  simp [posHalf]

theorem negHalf_nonempty : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) ∈ negHalf := by
  simp [negHalf]

end SKEFTHawking.SingularStarConvexSlit
