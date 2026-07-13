import Mathlib
import SKEFTHawking.RP2PointSet
import SKEFTHawking.RP4PointSet

/-!
# W-A (n = 2 witness, stretch) — the equatorial inclusion `ℝP² ↪ ℝP⁴`

The standard equatorial embedding `ℝ³ ↪ ℝ⁵` (first three coordinates, last two zero) is a
norm-preserving `ℝ`-linear `ℤˣ`-equivariant map `S² → S⁴`, so it descends to a **continuous** map
`ℝP² → ℝP⁴` — the point-set carrier of the witness's `emb` (the `hchar` characteristic-surface
input, whose mod-2 fundamental-class pushforward is dual to `w₁²`; see the module footnote for
the remaining smooth/pushforward obligations).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric

namespace SKEFTHawking.RP2EquatorialInclusion

open SKEFTHawking.RP2PointSet SKEFTHawking.RP4PointSet

/-- **The coordinate zero-extension `ℝ³ → ℝ⁵`** (first three coordinates, last two zero). -/
noncomputable def euclIncl (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 5) :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm (fun i => if h : (i : ℕ) < 3 then v.ofLp ⟨i, h⟩ else 0)

@[simp] theorem euclIncl_ofLp (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 5) :
    (euclIncl v).ofLp i = if h : (i : ℕ) < 3 then v.ofLp ⟨i, h⟩ else 0 := rfl

/-- The zero-extension is norm-preserving: `‖euclIncl v‖ = ‖v‖`. -/
theorem euclIncl_norm (v : EuclideanSpace ℝ (Fin 3)) : ‖euclIncl v‖ = ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (euclIncl v)), ← Real.sqrt_sq (norm_nonneg v),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_five, Fin.sum_univ_three]
  simp only [euclIncl_ofLp, Real.norm_eq_abs]
  norm_num
  rfl

/-- The zero-extension is additive. -/
theorem euclIncl_add (u v : EuclideanSpace ℝ (Fin 3)) :
    euclIncl (u + v) = euclIncl u + euclIncl v := by
  apply (WithLp.equiv 2 (Fin 5 → ℝ)).injective
  funext i
  show (euclIncl (u + v)).ofLp i = ((euclIncl u) + (euclIncl v)).ofLp i
  rw [euclIncl_ofLp]
  by_cases h : (i : ℕ) < 3 <;> simp [euclIncl_ofLp, h]

/-- The zero-extension commutes with the scalar action (it is `ℝ`-linear). -/
theorem euclIncl_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    euclIncl (c • v) = c • euclIncl v := by
  apply (WithLp.equiv 2 (Fin 5 → ℝ)).injective
  funext i
  show (euclIncl (c • v)).ofLp i = (c • euclIncl v).ofLp i
  rw [euclIncl_ofLp]
  by_cases h : (i : ℕ) < 3 <;> simp [euclIncl_ofLp, h]

/-- **`euclIncl` bundled as an `ℝ`-linear map** — for continuity (finite-dimensional). -/
noncomputable def euclInclₗ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun := euclIncl
  map_add' := euclIncl_add
  map_smul' := euclIncl_smul

theorem continuous_euclIncl : Continuous euclIncl :=
  euclInclₗ.continuous_of_finiteDimensional

/-! ## §2. The sphere-level map and its descent -/

/-- **The equatorial inclusion `S² → S⁴`** — norm-preservation lands the image on the unit sphere. -/
noncomputable def embS2 (x : S2) : S4 :=
  ⟨euclIncl x.1, by
    rw [mem_sphere_zero_iff_norm, euclIncl_norm, ← mem_sphere_zero_iff_norm]; exact x.2⟩

@[simp] theorem embS2_coe (x : S2) : (embS2 x).1 = euclIncl x.1 := rfl

theorem continuous_embS2 : Continuous embS2 :=
  Continuous.subtype_mk (continuous_euclIncl.comp continuous_subtype_val) _

/-- **The inclusion is `ℤˣ`-equivariant** — the antipodal action commutes with `euclIncl`. -/
theorem embS2_smul (u : ℤˣ) (x : S2) : embS2 (u • x) = u • embS2 x := by
  apply Subtype.ext
  show euclIncl (((u : ℤ) : ℝ) • x.1) = ((u : ℤ) : ℝ) • euclIncl x.1
  exact euclIncl_smul _ _

/-- **The equatorial inclusion `ℝP² → ℝP⁴`** — the descent of `embS2` through the antipodal
quotients (well defined by `ℤˣ`-equivariance). -/
noncomputable def embRP2 : RP2 → RP4 :=
  Quotient.map' embS2 (by
    rintro x y ⟨u, rfl⟩
    exact ⟨u, (embS2_smul u y).symm⟩)

@[simp] theorem embRP2_mk (x : S2) :
    embRP2 (Quotient.mk'' x) = Quotient.mk'' (embS2 x) := rfl

/-- **`embRP2` is continuous** — the descent of the continuous equivariant `embS2` through the
antipodal quotient (universal property of the quotient topology). -/
theorem continuous_embRP2 : Continuous embRP2 :=
  continuous_quot_lift _ (continuous_quotient_mk'.comp continuous_embS2)

/-! ## Footnote — remaining obligations for the full `hchar` input

`embRP2` is the point-set carrier of the witness's `emb`. Two obligations remain beyond this
continuous map, both out of scope for the surface substrate piece:

* **Smoothness** (`ContMDiff`): `emb` is required smooth + injective for the geometric `Σ·Σ`.
  Injectivity is immediate (`euclInclₗ` is injective, antipodal-compatible); smoothness needs the
  chart-compatibility of the descended stereographic atlases (`RP2Manifold`/`RP4Manifold`) — the
  statement shape is `ContMDiff (𝓡²-model) (𝓡⁴-model) ⊤ embRP2`.
* **The mod-2 fundamental-class pushforward** (`hchar`): the load-bearing identity is
  `Homology.map ⟨embRP2, continuous_embRP2⟩ 2 [ℝP²] = PD(w₁²) ∈ H₂(ℝP⁴;ℤ/2)` — the
  characteristic-surface condition, paired against the RP4 cup ladder via
  `RP4WuAssembly.mu_xpow_four`. The pushforward-cap naturality it needs is the
  `RP4ProjectionFormula` engine one functor level up, not built here.
-/

end SKEFTHawking.RP2EquatorialInclusion
