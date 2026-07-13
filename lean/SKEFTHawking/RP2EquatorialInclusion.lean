import Mathlib
import SKEFTHawking.RP2PointSet
import SKEFTHawking.RP4PointSet
import SKEFTHawking.RP2Manifold
import SKEFTHawking.RP4Manifold

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

/-! ## §3. Injectivity of the equatorial inclusion -/

/-- The zero-extension `ℝ³ → ℝ⁵` is injective (it is norm-preserving and additive). -/
theorem euclIncl_injective : Function.Injective euclIncl := by
  intro u v huv
  have hnorm : ‖u - v‖ = 0 := by
    rw [← euclIncl_norm]
    have hsub : euclIncl (u - v) = euclInclₗ u - euclInclₗ v := map_sub euclInclₗ u v
    rw [hsub]
    show ‖euclIncl u - euclIncl v‖ = 0
    rw [huv, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- **`embS2 : S² → S⁴` is injective** — from `euclIncl` injectivity on the underlying vectors. -/
theorem embS2_injective : Function.Injective embS2 := by
  intro x y hxy
  exact Subtype.ext (euclIncl_injective (congrArg Subtype.val hxy))

/-- **`embRP2 : ℝP² → ℝP⁴` is injective** — `euclIncl` injectivity plus antipodal equivariance:
if the images agree mod `±`, the deck element transports back to `S²`. -/
theorem embRP2_injective : Function.Injective embRP2 := by
  refine Quotient.ind fun x => Quotient.ind fun y => ?_
  intro hxy
  rw [embRP2_mk, embRP2_mk] at hxy
  obtain ⟨u, hu⟩ : embS2 x ∈ MulAction.orbit ℤˣ (embS2 y) := Quotient.eq''.mp hxy
  have hu' : u • embS2 y = embS2 x := hu
  rw [← embS2_smul] at hu'
  have hxy' : x = u • y := embS2_injective hu'.symm
  exact Quotient.sound ⟨u, hxy'.symm⟩

/-! ## §4. Smoothness of the equatorial inclusion

`embRP2` is `C^k` (all `k`, hence `Cω`): in the descended stereographic charts of `RP2Manifold`
and `RP4Manifold` the map reads, on the two deck pieces (`±1`), as
`repr₄ ∘ stereoToFun ∘ (±euclIncl) ∘ (Φ_s).symm` — a composite of `C^k` sphere-chart primitives with
the `ℝ`-linear `euclIncl`. Mirrors the `contDiffOn_transition_A/B` machinery of `RP*Manifold`,
crossing dimensions with `euclIncl` inserted. -/

open scoped Manifold RealInnerProductSpace
open SKEFTHawking.RP2PointSet SKEFTHawking.RP4PointSet

/-- `euclIncl` is `C^k` (it is `ℝ`-linear on a finite-dimensional space). -/
theorem contDiff_euclIncl {k : WithTop ℕ∞} : ContDiff ℝ k euclIncl :=
  euclInclₗ.toContinuousLinearMap.contDiff

/-- `embRP2` on a class, in the `Quotient.mk`-of-orbitRel normal form (matches the manifold
primitives, which speak `Quotient.mk (orbitRel ℤˣ ·)` rather than `Quotient.mk''`). -/
theorem embRP2_mk' (s : S2) :
    embRP2 (Quotient.mk (MulAction.orbitRel ℤˣ S2) s)
      = Quotient.mk (MulAction.orbitRel ℤˣ S4) (embS2 s) := embRP2_mk s

/-- Piece A (deck `1`): where the lifted sphere point maps into `hemi w`, open in `ℝ²`. -/
theorem isOpen_embVA (s : S2) (w : S4) :
    IsOpen ((rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi w)) := by
  have h1 := (RP2Manifold.Φ s).symm.isOpen_inter_preimage
    ((hemi_isOpen w).preimage continuous_embS2)
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi w)
      = (rp2Chart s).target ∩
        ((RP2Manifold.Φ s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi w)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, RP2Manifold.rp2Chart_target_subset s ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp2Chart s).open_target.inter h1

/-- Piece B (deck `-1`): where the lifted sphere point maps into `hemi (-w)`, open in `ℝ²`. -/
theorem isOpen_embVB (s : S2) (w : S4) :
    IsOpen ((rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi (-w))) := by
  have h1 := (RP2Manifold.Φ s).symm.isOpen_inter_preimage
    ((hemi_isOpen (-w)).preimage continuous_embS2)
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi (-w))
      = (rp2Chart s).target ∩
        ((RP2Manifold.Φ s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi (-w))) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, RP2Manifold.rp2Chart_target_subset s ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp2Chart s).open_target.inter h1

/-- **Transition class A (deck element `1`)**: on the piece where `embS2 ((Φ_s).symm t) ∈ hemi w`,
`rp4Chart w ∘ embRP2 ∘ (rp2Chart s).symm` reads as `repr₄ ∘ stereoToFun(-w) ∘ euclIncl ∘ (Φ_s).symm`,
which is `C^k`. -/
theorem contDiffOn_embTransition_A {k : WithTop ℕ∞} (s : S2) (w : S4) :
    ContDiffOn ℝ k (fun t : EuclideanSpace ℝ (Fin 2) => rp4Chart w (embRP2 ((rp2Chart s).symm t)))
      ((rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi w)) := by
  apply ContDiffOn.congr (f := fun t : EuclideanSpace ℝ (Fin 2) =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
      (ne_zero_of_mem_unit_sphere (-w))).repr
      (stereoToFun ((-w : S4) : RP4Manifold.E5)
        (euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3))))
  · refine (RP4Manifold.contDiffOn_reprStereo w).comp
      (contDiff_euclIncl.comp (RP2Manifold.contDiff_chartSymm_coe_S2 s)).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪(w : RP4Manifold.E5), (embS2 ((RP2Manifold.Φ s).symm t) : RP4Manifold.E5)⟫ :=
      hhemi
    show innerSL ℝ ((-w : S4) : RP4Manifold.E5)
      (euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3)) ≠ 1
    rw [innerSL_apply_apply, show ((-w : S4) : RP4Manifold.E5) = -(w : RP4Manifold.E5) from rfl,
      inner_neg_left,
      show euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3)
          = ((embS2 ((RP2Manifold.Φ s).symm t)) : RP4Manifold.E5) from (embS2_coe _).symm]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp2Chart s).symm t
        = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((RP2Manifold.Φ s).symm t) :=
      RP2Manifold.rp2Chart_symm_apply s htgt
    have hhemi' : embS2 ((RP2Manifold.Φ s).symm t) ∈ hemi w := hhemi
    rw [hmk, embRP2_mk', RP4Manifold.rp4Chart_apply_mk w hhemi', RP4Manifold.chartAt_S4_apply,
      embS2_coe]

/-- **Transition class B (deck element `-1`)**: on the piece where `embS2 ((Φ_s).symm t) ∈ hemi (-w)`
(its antipode is in `hemi w`), the transition reads as
`repr₄ ∘ stereoToFun(-w) ∘ (·)⁻ ∘ euclIncl ∘ (Φ_s).symm` — with the ambient negation — which is
`C^k`. -/
theorem contDiffOn_embTransition_B {k : WithTop ℕ∞} (s : S2) (w : S4) :
    ContDiffOn ℝ k (fun t : EuclideanSpace ℝ (Fin 2) => rp4Chart w (embRP2 ((rp2Chart s).symm t)))
      ((rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi (-w))) := by
  apply ContDiffOn.congr (f := fun t : EuclideanSpace ℝ (Fin 2) =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
      (ne_zero_of_mem_unit_sphere (-w))).repr
      (stereoToFun ((-w : S4) : RP4Manifold.E5)
        (-(euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3)))))
  · refine (RP4Manifold.contDiffOn_reprStereo w).comp
      ((contDiff_euclIncl.comp (RP2Manifold.contDiff_chartSymm_coe_S2 s)).neg).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪((-w : S4) : RP4Manifold.E5),
        (embS2 ((RP2Manifold.Φ s).symm t) : RP4Manifold.E5)⟫ := hhemi
    show innerSL ℝ ((-w : S4) : RP4Manifold.E5)
      (-(euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3))) ≠ 1
    rw [innerSL_apply_apply, inner_neg_right,
      show euclIncl ((RP2Manifold.Φ s).symm t : RP2Manifold.E3)
          = ((embS2 ((RP2Manifold.Φ s).symm t)) : RP4Manifold.E5) from (embS2_coe _).symm]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp2Chart s).symm t
        = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((RP2Manifold.Φ s).symm t) :=
      RP2Manifold.rp2Chart_symm_apply s htgt
    have hhemiB : embS2 ((RP2Manifold.Φ s).symm t) ∈ hemi (-w) := hhemi
    have hneg : (-(embS2 ((RP2Manifold.Φ s).symm t))) ∈ hemi w :=
      (RP4Manifold.mem_hemi_neg w (embS2 ((RP2Manifold.Φ s).symm t))).mp hhemiB
    rw [hmk, embRP2_mk', ← RP4Manifold.mk_neg (embS2 ((RP2Manifold.Φ s).symm t)),
      RP4Manifold.rp4Chart_apply_mk w hneg, RP4Manifold.chartAt_S4_apply,
      RP4Manifold.coe_neg_S4 (embS2 ((RP2Manifold.Φ s).symm t)), embS2_coe]

/-- **The RP²↪RP⁴ chart transition is `C^k`** on the transition source: assembled from the two
disjoint open deck pieces (`±1`), each a `C^k` sphere-chart transition composed with `euclIncl`. -/
theorem contDiffOn_embTransition {k : WithTop ℕ∞} (s : S2) (w : S4) :
    ContDiffOn ℝ k (fun t : EuclideanSpace ℝ (Fin 2) => rp4Chart w (embRP2 ((rp2Chart s).symm t)))
      ((rp2Chart s).target ∩ ↑(rp2Chart s).symm ⁻¹' (embRP2 ⁻¹' (rp4Chart w).source)) := by
  intro t ht
  obtain ⟨htgt, hsrc⟩ := ht
  have hmk : (rp2Chart s).symm t
      = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((RP2Manifold.Φ s).symm t) :=
    RP2Manifold.rp2Chart_symm_apply s htgt
  rw [Set.mem_preimage, Set.mem_preimage, hmk, embRP2_mk'] at hsrc
  rcases (RP4Manifold.mk_mem_source_iff w).mp hsrc with hA | hB
  · have hVA : t ∈ (rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi w) :=
      ⟨htgt, hA⟩
    exact ((contDiffOn_embTransition_A s w).contDiffAt
      ((isOpen_embVA s w).mem_nhds hVA)).contDiffWithinAt
  · have hB' : embS2 ((RP2Manifold.Φ s).symm t) ∈ hemi (-w) :=
      (RP4Manifold.mem_hemi_neg w (embS2 ((RP2Manifold.Φ s).symm t))).mpr hB
    have hVB : t ∈ (rp2Chart s).target ∩ ↑(RP2Manifold.Φ s).symm ⁻¹' (embS2 ⁻¹' hemi (-w)) :=
      ⟨htgt, hB'⟩
    exact ((contDiffOn_embTransition_B s w).contDiffAt
      ((isOpen_embVB s w).mem_nhds hVB)).contDiffWithinAt

/-- **`embRP2 : ℝP² → ℝP⁴` is `C^k`** for every regularity `k : WithTop ℕ∞` (hence `Cω`) — the
descended equatorial inclusion is, in charts, a rational (stereographic) composite with the
`ℝ`-linear `euclIncl`. This is the witness's `emb`/`embSmooth` field. -/
theorem contMDiff_embRP2 {k : WithTop ℕ∞} : ContMDiff (𝓡 2) (𝓡 4) k embRP2 := by
  rw [contMDiff_iff]
  refine ⟨continuous_embRP2, fun x y => ?_⟩
  simp only [mfld_simps]
  show ContDiffOn ℝ k
    (fun t : EuclideanSpace ℝ (Fin 2) => rp4Chart y.out (embRP2 ((rp2Chart x.out).symm t)))
    ((rp2Chart x.out).target ∩
      ↑(rp2Chart x.out).symm ⁻¹' (embRP2 ⁻¹' (rp4Chart y.out).source))
  exact contDiffOn_embTransition x.out y.out

/-- **`embRP2` is real-analytic (`Cω`)** — the strongest regularity, matching the `Cω` structures on
`ℝP²`/`ℝP⁴`. -/
theorem contMDiff_embRP2_analytic : ContMDiff (𝓡 2) (𝓡 4) ⊤ embRP2 := contMDiff_embRP2

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
