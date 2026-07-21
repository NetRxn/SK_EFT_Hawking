import Mathlib
import SKEFTHawking.KummerRP3EuclCharts
import SKEFTHawking.KummerRP3SphereHomeo

/-!
# Phase 5q.H — K6′b Leg 1: the **smooth structure on the pinned `ℝP³`** (the weld seam's carrier)

The K6′b weld `K3 := (T⁴°/τ) ∪_{16 × ℝP³} 16 × E` glues along `∂E ≅ ℝP³` in the **pinned**
presentation of `KummerResolutionPiece` (`RP3 := S³/±1` with `S³ = {(a,b) : ℂ × ℂ | ‖a‖²+‖b‖² = 1}`).
Both side-certificates are complete — `KummerResolutionPieceManifold.isManifold_resE` (the E side)
and `KummerQuotientManifold.isManifold_freeQuotient` (the Q side) — and both `§Z` status blocks name
the same residual: *the smooth `∂E ≅ ℝP³` upgrade of `bdryHomeoRP3`*. That upgrade is meaningless
until `ℝP³` itself carries a smooth structure, which is what this module ships.

**The route (no fresh carriers — everything transports onto objects the weld already consumes):**

* **§1–§4.** The Euclidean carrier `RP3E = S³_𝔼/±` of `KummerRP3EuclCharts` (the *existing*
  `ℤˣ`-action carrier, already used by the `H₄ = H₅ = 0` telescope, which had **no** smooth data:
  its `chartHomeo`/`charted` are `Homeomorph`s only) is given the descended stereographic atlas and
  the `k`-generic `IsManifold (𝓡 3) k RP3E`. This is the `RP4Manifold` recipe one dimension down:
  the transition between two descended charts splits into the deck-`1` piece (`hemi y`) and the
  deck-`(-1)` piece (`hemi (-y)`), each a `C^k` sphere-chart transition.
* **§5.** The **descended homeomorphism** `rp3EHomeoRP3 : RP3E ≃ₜ RP3` — `KummerRP3SphereHomeo`'s
  coordinate homeomorphism `sphHomeoS3 : S³_𝔼 ≃ₜ S³_{ℂ²}` descended through both antipodal
  quotients (it is `ℝ`-linear, hence intertwines the two antipodal maps: `antipodal_sphToS3`).
  Built with an explicit two-sided inverse, so no `T2Space RP3` input is needed.
* **§6.** **Transport along an open embedding** (`OpenPartialHomeomorph.lift_openEmbedding`, the same
  Mathlib lever `rp4Chart` itself uses): a chart on the source lifts to a chart on the target, and
  the lifted transition is *pointwise* the original transition on the *same* coordinate set. Shipped
  as reusable model-space-generic infrastructure (`liftedTransition_eq`, `liftedTransition_source`)
  and instantiated to give the pinned `RP3` its charted space and

    **`isManifold_rp3 : IsManifold (𝓡 3) k RP3`** — the K6′b seam carrier is a `C^k` 3-manifold,

  for every `k : WithTop ℕ∞` (in particular `k = ⊤`, matching the smooth-category target).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/

open Metric Set
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.KummerRP3SphereHomeo (sphToS3 continuous_sphToS3 sphToS3_injective
  sphToS3_surjective sphHomeoS3)

namespace SKEFTHawking.KummerRP3Smooth

noncomputable section

/-- Ambient `ℝ⁴` (the sphere's ambient space). -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Model `ℝ³` (the chart model of `ℝP³`). -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## §1. Foundational: `S³_𝔼` is `C^k`-smooth, and the antipodal relation on classes -/

/-- Local dimension fact for `S³ ⊆ ℝ⁴`, needed by every `stereographic'` unfold. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Abbreviation for the sphere's stereographic chart at `x`. -/
noncomputable abbrev Φ (x : S3E) : OpenPartialHomeomorph S3E E3 := chartAt E3 x

/-- `S³_𝔼` is a `C^k` manifold for every regularity `k` (from Mathlib's `ω`-smooth instance). -/
instance isManifold_S3E {k : WithTop ℕ∞} : IsManifold (𝓡 3) k S3E := IsManifold.of_le le_top

/-- The sphere's `Neg` coercion agrees with ambient negation (`rfl`). -/
theorem coe_neg_S3E (s : S3E) : ((-s : S3E) : E4) = -(s : E4) := rfl

/-- The class of a sphere point equals the class of its antipode (deck element `-1`). -/
theorem mkE_neg (s : S3E) : mkE (-s) = mkE s := by
  apply Quotient.sound
  refine ⟨(-1 : ℤˣ), ?_⟩
  apply Subtype.ext
  rw [smul_coe]
  norm_num

/-! ## §2. The hemisphere layer — where the quotient map is an open embedding -/

/-- The open hemisphere around `x` (inner-product form — the chart-carrying hemisphere, distinct
from `KummerRP3EuclCharts.hemiC`, which is the coordinate hemisphere of the homology telescope). -/
def hemi (x : S3E) : Set S3E := {y : S3E | 0 < ⟪(x : E4), (y : E4)⟫}

theorem hemi_isOpen (x : S3E) : IsOpen (hemi x) :=
  isOpen_lt continuous_const (Continuous.inner continuous_const continuous_subtype_val)

theorem mem_hemi_self (x : S3E) : x ∈ hemi x := by
  show 0 < ⟪(x : E4), (x : E4)⟫
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- **`mkE` is injective on a hemisphere** — an antipodal pair never lies in one. -/
theorem mkE_injOn_hemi (x : S3E) : Set.InjOn mkE (hemi x) := by
  intro y hy y' hy' hmk
  rcases fiberE_pair hmk with h | h
  · exact h
  · exfalso
    have hcoe : (y : E4) = -(y' : E4) := by
      rw [h, smul_coe]; norm_num
    have h2 : (0 : ℝ) < ⟪(x : E4), -(y' : E4)⟫ := hcoe ▸ hy
    rw [inner_neg_right] at h2
    exact absurd hy' (not_lt.mpr (le_of_lt (neg_pos.mp h2)))

/-- **The hemisphere-restricted quotient map is an open embedding** — the engine that descends the
sphere's charts to `ℝP³`. -/
theorem isOpenEmbedding_mkE_hemi (x : S3E) :
    Topology.IsOpenEmbedding (fun y : ↥(hemi x) => mkE y.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_mkE.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (mkE_injOn_hemi x a.2 b.2 hab)
  · exact IsOpenMap.comp isOpenMap_mkE ((hemi_isOpen x).isOpenMap_subtype_val)

/-- The hemisphere as an open set (for `subtypeRestr`). -/
def hemiOpens (x : S3E) : TopologicalSpace.Opens S3E := ⟨hemi x, hemi_isOpen x⟩

instance (x : S3E) : Nonempty (hemiOpens x) := ⟨⟨x, mem_hemi_self x⟩⟩

/-- **The `ℝP³_𝔼` chart at (the class of) `x`**: the sphere chart at `x`, hemisphere-restricted,
lifted along the hemisphere open embedding. -/
noncomputable def rp3Chart (x : S3E) : OpenPartialHomeomorph RP3E E3 :=
  ((chartAt E3 x).subtypeRestr
      (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).lift_openEmbedding
    (isOpenEmbedding_mkE_hemi x)

/-- **`ℝP³_𝔼` is a charted space over `ℝ³`** — the descended stereographic atlas. -/
noncomputable instance instChartedSpaceRP3E : ChartedSpace E3 RP3E where
  atlas := Set.range rp3Chart
  chartAt p := rp3Chart p.out
  mem_chart_source p := by
    show p ∈ (rp3Chart p.out).source
    rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨⟨p.out, mem_hemi_self p.out⟩, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact mem_chart_source E3 p.out
    · exact p.out_eq
  chart_mem_atlas p := Set.mem_range_self _

/-! ## §3. Bridge: `rp3Chart` in terms of the sphere charts -/

/-- The sphere chart's source is the complement of the antipode of the base point. -/
theorem chartAt_S3E_source (x : S3E) : (Φ x).source = {-x}ᶜ := stereographic'_source (-x)

/-- Every hemisphere point lies in the base chart's source (the antipode is the excluded pole). -/
theorem hemi_subset_source (x : S3E) : hemi x ⊆ (Φ x).source := by
  intro s hs
  rw [chartAt_S3E_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcontra
  have hpos : 0 < ⟪(x : E4), (s : E4)⟫ := hs
  rw [hcontra] at hpos
  have : ((-x : S3E) : E4) = -(x : E4) := rfl
  rw [this, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp x.2] at hpos
  norm_num at hpos

/-- Descended-chart value: on the hemisphere, `rp3Chart x ∘ mkE = Φ x`. -/
theorem rp3Chart_apply_mkE (x : S3E) {s : S3E} (hs : s ∈ hemi x) :
    rp3Chart x (mkE s) = Φ x s := by
  rw [rp3Chart]
  rw [show mkE s = (fun y : ↥(hemi x) => mkE y.1) ⟨s, hs⟩ from rfl]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The descended chart's source is the image of the hemisphere. -/
theorem rp3Chart_source (x : S3E) : (rp3Chart x).source = mkE '' hemi x := by
  rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext p
  constructor
  · rintro ⟨⟨y, hy⟩, hy2, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, hemi_subset_source x hy, rfl⟩

/-- The descended chart's inverse, read on its target, is `mkE ∘ Φ x .symm`. -/
theorem rp3Chart_symm_apply (x : S3E) {t : E3} (ht : t ∈ (rp3Chart x).target) :
    (rp3Chart x).symm t = mkE ((Φ x).symm t) := by
  have ht' : t ∈ ((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).target := by
    rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht; exact ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht'
  rw [Function.comp_apply] at heq
  rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, heq]

/-- On the descended chart's target, the sphere-inverse lands in the hemisphere. -/
theorem rp3Chart_symm_mem_hemi (x : S3E) {t : E3} (ht : t ∈ (rp3Chart x).target) :
    (Φ x).symm t ∈ hemi x := by
  rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht
  rw [Function.comp_apply] at heq
  rw [heq]
  exact (((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).symm t).2

/-! ## §4. Coordinate-level smoothness and the `k`-generic `IsManifold (𝓡 3) k RP3E` -/

/-- Forward-apply of the `S³` stereographic chart in `repr ∘ stereoToFun` normal form (`rfl`). -/
theorem chartAt_S3E_apply (y w : S3E) :
    Φ y w = (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-y))).repr
        (stereoToFun ((-y : S3E) : E4) (w : E4)) := rfl

/-- **The raw `repr ∘ stereoToFun` composite is `C^k`** on the north-pole-excluded locus — the
reusable coordinate-level input to both transition classes. -/
theorem contDiffOn_reprStereo {k : WithTop ℕ∞} (y : S3E) :
    ContDiffOn ℝ k
      (fun w : E4 => (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-y))).repr (stereoToFun ((-y : S3E) : E4) w))
      {w : E4 | innerSL ℝ ((-y : S3E) : E4) w ≠ 1} :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
      (ne_zero_of_mem_unit_sphere (-y))).repr.contDiff.comp_contDiffOn contDiffOn_stereoToFun

/-- **The inverse `S³` stereographic chart is `C^k`** as a map into `ℝ⁴`. -/
theorem contDiff_chartSymm_coe_S3E {k : WithTop ℕ∞} (x : S3E) :
    ContDiff ℝ k (fun w : E3 => ((Φ x).symm w : E4)) := by
  have hcomp : ContDiff ℝ k (fun w : E3 =>
      stereoInvFunAux ((-x : S3E) : E4)
        (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
            (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
          (ℝ ∙ ((-x : S3E) : E4))ᗮ) : E4)) :=
    contDiff_stereoInvFunAux.comp
      ((ℝ ∙ ((-x : S3E) : E4))ᗮ.subtypeL.contDiff.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
          (ne_zero_of_mem_unit_sphere (-x))).repr.symm.contDiff)
  have heq : ∀ w : E3,
      ((Φ x).symm w : E4)
        = stereoInvFunAux ((-x : S3E) : E4)
          (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
              (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
            (ℝ ∙ ((-x : S3E) : E4))ᗮ) : E4) := by
    intro w
    show ((stereographic' 3 (-x)).symm w : E4) = _
    rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]
  simpa only [heq] using hcomp

/-- `(rp3Chart x).target ⊆ (Φ x).target`. -/
theorem rp3Chart_target_subset (x : S3E) : (rp3Chart x).target ⊆ (Φ x).target := by
  rw [rp3Chart, OpenPartialHomeomorph.lift_openEmbedding_target]
  exact OpenPartialHomeomorph.subtypeRestr_target_subset _ _

/-- Hemisphere/antipode bookkeeping: `s ∈ hemi (-y) ↔ (-s) ∈ hemi y`. -/
theorem mem_hemi_neg (y s : S3E) : s ∈ hemi (-y) ↔ (-s) ∈ hemi y := by
  show 0 < ⟪((-y : S3E) : E4), (s : E4)⟫ ↔ 0 < ⟪(y : E4), ((-s : S3E) : E4)⟫
  rw [show ((-y : S3E) : E4) = -(y : E4) from rfl, show ((-s : S3E) : E4) = -(s : E4) from rfl,
    inner_neg_left, inner_neg_right]

/-- `mkE s` lies in the `y`-descended-chart source iff `s` or its antipode is in `hemi y`. -/
theorem mkE_mem_source_iff (y : S3E) {s : S3E} :
    mkE s ∈ (rp3Chart y).source ↔ s ∈ hemi y ∨ (-s) ∈ hemi y := by
  rw [rp3Chart_source]
  constructor
  · rintro ⟨s', hs', hmk⟩
    rcases fiberE_pair hmk.symm with h | h
    · left; rw [h]; exact hs'
    · right
      have hneg : (-s) = s' := by
        apply Subtype.ext
        rw [show ((-s : S3E) : E4) = -(s : E4) from rfl, h, smul_coe]; norm_num
      rw [hneg]; exact hs'
  · rintro (h | h)
    · exact ⟨s, h, rfl⟩
    · exact ⟨-s, h, mkE_neg s⟩

/-- **Transition class A (deck element `1`)**: on the piece where `(Φ x).symm t ∈ hemi y`, the
`ℝP³` transition is the sphere-chart transition `Φ y ∘ (Φ x).symm`, which is `C^k`. -/
theorem contDiffOn_transition_A {k : WithTop ℕ∞} (x y : S3E) :
    ContDiffOn ℝ k (fun t : E3 => rp3Chart y ((rp3Chart x).symm t))
      ((rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  apply ContDiffOn.congr (f := fun t : E3 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S3E) : E4) ((Φ x).symm t : E4)))
  · refine (contDiffOn_reprStereo y).comp (contDiff_chartSymm_coe_S3E x).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪(y : E4), ((Φ x).symm t : E4)⟫ := hhemi
    show innerSL ℝ ((-y : S3E) : E4) ((Φ x).symm t : E4) ≠ 1
    rw [innerSL_apply_apply, show ((-y : S3E) : E4) = -(y : E4) from rfl, inner_neg_left]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp3Chart x).symm t = mkE ((Φ x).symm t) := rp3Chart_symm_apply x htgt
    rw [hmk, rp3Chart_apply_mkE y hhemi, chartAt_S3E_apply]

/-- **Transition class B (deck element `-1`)**: on the piece where `(Φ x).symm t ∈ hemi (-y)`, the
`ℝP³` transition is the sphere-chart transition composed with the antipodal map, which is `C^k`. -/
theorem contDiffOn_transition_B {k : WithTop ℕ∞} (x y : S3E) :
    ContDiffOn ℝ k (fun t : E3 => rp3Chart y ((rp3Chart x).symm t))
      ((rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  apply ContDiffOn.congr (f := fun t : E3 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S3E) : E4) (-((Φ x).symm t : E4))))
  · refine (contDiffOn_reprStereo y).comp ((contDiff_chartSymm_coe_S3E x).neg).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪((-y : S3E) : E4), ((Φ x).symm t : E4)⟫ := hhemi
    show innerSL ℝ ((-y : S3E) : E4) (-((Φ x).symm t : E4)) ≠ 1
    rw [innerSL_apply_apply, inner_neg_right]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp3Chart x).symm t = mkE ((Φ x).symm t) := rp3Chart_symm_apply x htgt
    have hneghemi : (-(Φ x).symm t) ∈ hemi y := (mem_hemi_neg y ((Φ x).symm t)).mp hhemi
    rw [hmk, ← mkE_neg ((Φ x).symm t), rp3Chart_apply_mkE y hneghemi, chartAt_S3E_apply,
      coe_neg_S3E ((Φ x).symm t)]

/-- Piece A is open in `ℝ³`. -/
theorem isOpen_VA (x y : S3E) : IsOpen ((rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen y)
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)
      = (rp3Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp3Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp3Chart x).open_target.inter h1

/-- Piece B is open in `ℝ³`. -/
theorem isOpen_VB (x y : S3E) : IsOpen ((rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen (-y))
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))
      = (rp3Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp3Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp3Chart x).open_target.inter h1

/-- **The `ℝP³_𝔼` chart transition is `C^k`** — assembled from the two disjoint open pieces (deck
elements `±1`), each a `C^k` sphere-chart transition. -/
theorem contDiffOn_rp3_transition {k : WithTop ℕ∞} (x y : S3E) :
    ContDiffOn ℝ k (fun t : E3 => rp3Chart y ((rp3Chart x).symm t))
      ((rp3Chart x).target ∩ ↑(rp3Chart x).symm ⁻¹' (rp3Chart y).source) := by
  intro t ht
  obtain ⟨htgt, hsrc⟩ := ht
  have hmk : (rp3Chart x).symm t = mkE ((Φ x).symm t) := rp3Chart_symm_apply x htgt
  rw [Set.mem_preimage, hmk] at hsrc
  rcases (mkE_mem_source_iff y).mp hsrc with hA | hB
  · have hVA : t ∈ (rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y) := ⟨htgt, hA⟩
    exact ((contDiffOn_transition_A x y).contDiffAt
      ((isOpen_VA x y).mem_nhds hVA)).contDiffWithinAt
  · have hnegB : (Φ x).symm t ∈ hemi (-y) := (mem_hemi_neg y ((Φ x).symm t)).mpr hB
    have hVB : t ∈ (rp3Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y)) := ⟨htgt, hnegB⟩
    exact ((contDiffOn_transition_B x y).contDiffAt
      ((isOpen_VB x y).mem_nhds hVB)).contDiffWithinAt

/-- **`ℝP³_𝔼` is a `C^k` manifold** for every regularity `k : WithTop ℕ∞` — the descended
stereographic atlas has `C^k` transitions. The Euclidean carrier of `KummerRP3EuclCharts` (used by
the `H₄ = H₅ = 0` telescope) had only `Homeomorph`-level charts before this instance. -/
instance isManifold_rp3E {k : WithTop ℕ∞} : IsManifold (𝓡 3) k RP3E := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have key := contDiffOn_rp3_transition (k := k) x y
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
    Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source]
  exact key

/-! ## §5. The descended homeomorphism `ℝP³_𝔼 ≃ₜ ℝP³_pinned`

`KummerRP3SphereHomeo.sphHomeoS3 : S³_𝔼 ≃ₜ S³_{ℂ²}` is the coordinate map
`v ↦ (v₀ + v₁i, v₂ + v₃i)`, which is `ℝ`-linear and therefore **intertwines the two antipodal
maps** — the `(-1 : ℤˣ)`-action on `S³_𝔼` and `KummerResolutionPiece.negS3` on `S³_{ℂ²}`. So it
descends to both quotients. The descent is built with an explicit two-sided inverse (rather than
compact-to-`T2`), so it needs no `T2Space` input on the pinned side. -/

open SKEFTHawking.KummerResolutionPiece (S3 negS3 negS3_involutive RP3 mkRP3 continuous_mkRP3
  mkRP3_neg antipSetoid)

/-- The homeomorphism's forward map is the coordinate map (`rfl`). -/
theorem sphHomeoS3_apply (y : S3E) : sphHomeoS3 y = sphToS3 y := rfl

/-- **The coordinate map intertwines the two antipodal maps**: `sphToS3 ((-1) • y) = negS3 (sphToS3
y)`. This is what lets `sphHomeoS3` descend through both `±1`-quotients. -/
theorem sphToS3_neg (y : S3E) : sphToS3 ((-1 : ℤˣ) • y) = negS3 (sphToS3 y) := by
  apply Subtype.ext
  have h0 := neg_one_smul_apply y 0
  have h1 := neg_one_smul_apply y 1
  have h2 := neg_one_smul_apply y 2
  have h3 := neg_one_smul_apply y 3
  show SKEFTHawking.KummerK7Opener.eucToC2 (((-1 : ℤˣ) • y : S3E) : E4)
    = (-(SKEFTHawking.KummerK7Opener.eucToC2 (y : E4)).1,
       -(SKEFTHawking.KummerK7Opener.eucToC2 (y : E4)).2)
  unfold SKEFTHawking.KummerK7Opener.eucToC2
  rw [h0, h1, h2, h3]
  refine Prod.ext ?_ ?_
  · show Complex.equivRealProdCLM.symm (-(y : E4) 0, -(y : E4) 1)
      = -Complex.equivRealProdCLM.symm ((y : E4) 0, (y : E4) 1)
    rw [show (-(y : E4) 0, -(y : E4) 1) = -((y : E4) 0, (y : E4) 1) from rfl, map_neg]
  · show Complex.equivRealProdCLM.symm (-(y : E4) 2, -(y : E4) 3)
      = -Complex.equivRealProdCLM.symm ((y : E4) 2, (y : E4) 3)
    rw [show (-(y : E4) 2, -(y : E4) 3) = -((y : E4) 2, (y : E4) 3) from rfl, map_neg]

/-- The inverse coordinate map intertwines the antipodal maps the other way. -/
theorem sphHomeoS3_symm_neg (x : S3) :
    sphHomeoS3.symm (negS3 x) = (-1 : ℤˣ) • sphHomeoS3.symm x := by
  apply sphHomeoS3.injective
  rw [sphHomeoS3.apply_symm_apply, sphHomeoS3_apply, sphToS3_neg, ← sphHomeoS3_apply,
    sphHomeoS3.apply_symm_apply]

/-- **The descended map `ℝP³_𝔼 → ℝP³_pinned`.** -/
def rp3EToRP3 : RP3E → RP3 :=
  Quotient.lift (fun y : S3E => mkRP3 (sphToS3 y)) (by
    rintro a b ⟨u, hu⟩
    have hu' : u • b = a := hu
    rcases Int.units_eq_one_or u with h1 | h1
    · rw [h1, one_smul] at hu'; rw [hu']
    · rw [h1] at hu'
      rw [← hu']
      show mkRP3 (sphToS3 ((-1 : ℤˣ) • b)) = mkRP3 (sphToS3 b)
      rw [sphToS3_neg, mkRP3_neg])

/-- **The descended map `ℝP³_pinned → ℝP³_𝔼`.** -/
def rp3ToRP3E : RP3 → RP3E :=
  Quotient.lift (fun x : S3 => mkE (sphHomeoS3.symm x)) (by
    rintro a b (rfl | rfl)
    · rfl
    · show mkE (sphHomeoS3.symm a) = mkE (sphHomeoS3.symm (negS3 a))
      rw [sphHomeoS3_symm_neg, mkE_neg_smul])

@[simp] theorem rp3EToRP3_mkE (y : S3E) : rp3EToRP3 (mkE y) = mkRP3 (sphToS3 y) := rfl

@[simp] theorem rp3ToRP3E_mkRP3 (x : S3) : rp3ToRP3E (mkRP3 x) = mkE (sphHomeoS3.symm x) := rfl

theorem rp3ToRP3E_rp3EToRP3 (q : RP3E) : rp3ToRP3E (rp3EToRP3 q) = q := by
  refine Quotient.inductionOn q fun y => ?_
  show rp3ToRP3E (rp3EToRP3 (mkE y)) = mkE y
  rw [rp3EToRP3_mkE, rp3ToRP3E_mkRP3, ← sphHomeoS3_apply, sphHomeoS3.symm_apply_apply]

theorem rp3EToRP3_rp3ToRP3E (p : RP3) : rp3EToRP3 (rp3ToRP3E p) = p := by
  refine Quotient.inductionOn p fun x => ?_
  show rp3EToRP3 (rp3ToRP3E (mkRP3 x)) = mkRP3 x
  rw [rp3ToRP3E_mkRP3, rp3EToRP3_mkE, ← sphHomeoS3_apply, sphHomeoS3.apply_symm_apply]

/-- **`ℝP³_𝔼 ≃ₜ ℝP³_pinned`** — the coordinate homeomorphism `sphHomeoS3` descended through both
antipodal quotients. Explicit two-sided inverse; no `T2Space` input on the pinned side. -/
def rp3EHomeoRP3 : RP3E ≃ₜ RP3 where
  toFun := rp3EToRP3
  invFun := rp3ToRP3E
  left_inv := rp3ToRP3E_rp3EToRP3
  right_inv := rp3EToRP3_rp3ToRP3E
  continuous_toFun := Continuous.quotient_lift (continuous_mkRP3.comp continuous_sphToS3) _
  continuous_invFun :=
    Continuous.quotient_lift (continuous_mkE.comp sphHomeoS3.symm.continuous) _

@[simp] theorem rp3EHomeoRP3_mkE (y : S3E) : rp3EHomeoRP3 (mkE y) = mkRP3 (sphToS3 y) := rfl

/-- The pinned quotient map factors as `mkRP3 ∘ sphToS3 = rp3EHomeoRP3 ∘ mkE` — the compatibility
the weld seam reads the charts through. -/
theorem mkRP3_sphToS3 (y : S3E) : mkRP3 (sphToS3 y) = rp3EHomeoRP3 (mkE y) := rfl

/-! ## §6. Transport: the pinned `ℝP³` is a `C^k` 3-manifold

`OpenPartialHomeomorph.lift_openEmbedding` lifts a chart along an open embedding, and Mathlib's
`lift_openEmbedding_trans` says the lifted transition is **equal** (not merely pointwise equal) to
the original: `(c.lift f).symm ≫ₕ (c'.lift f) = c.symm ≫ₕ c'`. A homeomorphism is an open
embedding, so the whole `RP3E` atlas transports to the pinned `RP3` with its transition classes
intact. -/

/-- The seam-carrier open embedding `ℝP³_𝔼 ↪ ℝP³_pinned` (a homeomorphism, hence open). -/
theorem isOpenEmbedding_rp3EHomeoRP3 : Topology.IsOpenEmbedding (rp3EHomeoRP3 : RP3E → RP3) :=
  rp3EHomeoRP3.isOpenEmbedding

/-- **The pinned-`ℝP³` chart at `x`** — the `ℝP³_𝔼` chart lifted along `rp3EHomeoRP3`. -/
noncomputable def rp3PinChart (x : S3E) : OpenPartialHomeomorph RP3 E3 :=
  (rp3Chart x).lift_openEmbedding isOpenEmbedding_rp3EHomeoRP3

/-- **The pinned `ℝP³` is a charted space over `ℝ³`.** -/
noncomputable instance instChartedSpaceRP3 : ChartedSpace E3 RP3 where
  atlas := Set.range rp3PinChart
  chartAt p := rp3PinChart (rp3ToRP3E p).out
  mem_chart_source p := by
    refine ⟨rp3ToRP3E p, ?_, rp3EToRP3_rp3ToRP3E p⟩
    exact mem_chart_source E3 (rp3ToRP3E p)
  chart_mem_atlas p := Set.mem_range_self _

/-- **The pinned `ℝP³` is a `C^k` manifold** for every regularity `k : WithTop ℕ∞` — the weld seam
carrier `KummerResolutionPiece.RP3` (the one `KummerWeld.qBdryMap` glues 16 copies of `∂E` along)
now lives in the smooth category, matching the two side-certificates
`KummerResolutionPieceManifold.isManifold_resE` and
`KummerQuotientManifold.isManifold_freeQuotient`. -/
instance isManifold_rp3 {k : WithTop ℕ∞} : IsManifold (𝓡 3) k RP3 := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  rw [rp3PinChart, rp3PinChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
  have key := contDiffOn_rp3_transition (k := k) x y
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
    Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source]
  exact key

/-- **`ℝP³` is a real-analytic (`Cω`) manifold** — the strongest regularity (`k = ⊤`), matching
`S³`'s own `ω`-smooth structure and a fortiori `C^∞`; the regularity the smooth-category weld
target needs. -/
theorem isManifold_rp3_analytic : IsManifold (𝓡 3) ⊤ RP3 := isManifold_rp3

end

end SKEFTHawking.KummerRP3Smooth
