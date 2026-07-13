import Mathlib
import SKEFTHawking.RP4PointSet

/-!
# Phase 5q.H (W-B opener) — the `k`-generic smooth structure on `ℝP⁴`

`RP4PointSet` gives `ℝP⁴ = S⁴/±` a `ChartedSpace (EuclideanSpace ℝ (Fin 4))` structure by
descending the sphere's stereographic charts along the hemisphere open embeddings
(`rp4Chart x = (chartAt _ x |_{hemi x}).lift_openEmbedding (mk|_{hemi x})`). The existing `rp4SM`
witness sits at `k = 0`, where `IsManifold I 0 M` fires for *any* charted space (the degree-0
`contDiffGroupoid` is the whole continuous groupoid).

This module supplies the **`k`-generic** `IsManifold (𝓡 4) k RP4` (all `k : WithTop ℕ∞`): the
transition between two descended charts `rp4Chart x` and `rp4Chart y` reduces — on the sphere —
to the sphere-chart transition on the disjoint opens `hemi x ∩ hemi y` (deck element `1`) and
`hemi x ∩ hemi (-y)` (deck element `-1`, i.e. the antipodal map). Both are `C^k` because `S⁴` is
`ω`-smooth (`EuclideanSpace.instIsManifoldSphere`) and negation on `ℝ⁵` is `C^k`. Since the
literature target `Ω₄^{Pin⁺} ≅ ℤ/16` is a *smooth-category* statement, this lifts the `ℝP⁴`
witness carrier to the smooth category at `k = ∞`.

Reuses the closed-ball campaign house style (`DiskManifoldSmooth.lean`): explicit `ContDiffOn`
transition classes assembled through `isManifold_of_contDiffOn`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/

open Metric Set
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.RP4PointSet

namespace SKEFTHawking.RP4Manifold

noncomputable section

/-- Ambient `ℝ⁵`. -/
abbrev E5 : Type := EuclideanSpace ℝ (Fin (4 + 1))
/-- Model `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Abbreviation for the sphere's stereographic chart at `x`. -/
noncomputable abbrev Φ (x : S4) : OpenPartialHomeomorph S4 E4 := chartAt E4 x

/-! ### §1. Foundational: `S⁴` is `C^k`-smooth, and the antipodal relation on classes -/

/-- Local dimension fact for `S⁴ ⊆ ℝ⁵`, needed by every `stereographic'` unfold. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- `S⁴` is a `C^k` manifold for every regularity `k` (from Mathlib's `ω`-smooth instance). -/
instance isManifold_S4 {k : WithTop ℕ∞} : IsManifold (𝓡 4) k S4 := IsManifold.of_le le_top

/-- The sphere's `Neg` coercion agrees with ambient negation (`rfl`). -/
theorem coe_neg_S4 (s : S4) : ((-s : S4) : E5) = -(s : E5) := rfl

/-- The class of a sphere point equals the class of its antipode (deck element `-1`). -/
theorem mk_neg (s : S4) :
    Quotient.mk (MulAction.orbitRel ℤˣ S4) (-s) = Quotient.mk (MulAction.orbitRel ℤˣ S4) s := by
  apply Quotient.sound
  refine ⟨(-1 : ℤˣ), ?_⟩
  apply Subtype.ext
  rw [smul_coe]
  norm_num

/-! ### §2. Bridge: `rp4Chart` in terms of the sphere charts -/

/-- The sphere chart's source is the complement of the antipode of the base point. -/
theorem chartAt_S4_source (x : S4) : (Φ x).source = {-x}ᶜ := stereographic'_source (-x)

/-- Every hemisphere point lies in the base chart's source (the antipode is the excluded pole). -/
theorem hemi_subset_source (x : S4) : hemi x ⊆ (Φ x).source := by
  intro s hs
  rw [chartAt_S4_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcontra
  have hpos : 0 < ⟪(x : E5), (s : E5)⟫ := hs
  rw [hcontra] at hpos
  have : ((-x : S4) : E5) = -(x : E5) := rfl
  rw [this, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp x.2] at hpos
  norm_num at hpos

/-- Descended-chart value: on the hemisphere, `rp4Chart x ∘ mk = Φ x`. -/
theorem rp4Chart_apply_mk (x : S4) {s : S4} (hs : s ∈ hemi x) :
    rp4Chart x (Quotient.mk (MulAction.orbitRel ℤˣ S4) s) = Φ x s := by
  rw [rp4Chart]
  rw [show Quotient.mk (MulAction.orbitRel ℤˣ S4) s
    = (fun y : ↥(hemi x) => Quotient.mk (MulAction.orbitRel ℤˣ S4) y.1) ⟨s, hs⟩ from rfl]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The descended chart's source is the image of the hemisphere. -/
theorem rp4Chart_source (x : S4) :
    (rp4Chart x).source = Quotient.mk (MulAction.orbitRel ℤˣ S4) '' hemi x := by
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext p
  constructor
  · rintro ⟨⟨y, hy⟩, hy2, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, hemi_subset_source x hy, rfl⟩

/-- The descended chart's inverse, read on its target, is `mk ∘ Φ x .symm`. -/
theorem rp4Chart_symm_apply (x : S4) {t : E4} (ht : t ∈ (rp4Chart x).target) :
    (rp4Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S4) ((Φ x).symm t) := by
  have ht' : t ∈ ((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).target := by
    rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht; exact ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht'
  rw [Function.comp_apply] at heq
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, heq]

/-- On the descended chart's target, the sphere-inverse lands in the hemisphere. -/
theorem rp4Chart_symm_mem_hemi (x : S4) {t : E4} (ht : t ∈ (rp4Chart x).target) :
    (Φ x).symm t ∈ hemi x := by
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht
  rw [Function.comp_apply] at heq
  rw [heq]
  exact (((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).symm t).2

/-! ### §3. Coordinate-level smoothness of the sphere charts (reusable primitives) -/

/-- Forward-apply of the `S⁴` stereographic chart in `repr ∘ stereoToFun` normal form (`rfl`). -/
theorem chartAt_S4_apply (y w : S4) :
    Φ y w = (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
        (ne_zero_of_mem_unit_sphere (-y))).repr
        (stereoToFun ((-y : S4) : E5) (w : E5)) := rfl

/-- **The raw `repr ∘ stereoToFun` composite is `C^k`** on the north-pole-excluded locus. The
`y`-chart read at coordinate level; the reusable input to both RP⁴ transition classes. -/
theorem contDiffOn_reprStereo {k : WithTop ℕ∞} (y : S4) :
    ContDiffOn ℝ k
      (fun w : E5 => (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
        (ne_zero_of_mem_unit_sphere (-y))).repr (stereoToFun ((-y : S4) : E5) w))
      {w : E5 | innerSL ℝ ((-y : S4) : E5) w ≠ 1} :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
      (ne_zero_of_mem_unit_sphere (-y))).repr.contDiff.comp_contDiffOn contDiffOn_stereoToFun

/-- **The inverse `S⁴` stereographic chart is `C^k`** as a map into `ℝ⁵` (`stereoInvFunAux`,
`repr.symm`, and the orthocomplement inclusion are all `C^k`). -/
theorem contDiff_chartSymm_coe_S4 {k : WithTop ℕ∞} (x : S4) :
    ContDiff ℝ k (fun w : E4 => ((Φ x).symm w : E5)) := by
  have hcomp : ContDiff ℝ k (fun w : E4 =>
      stereoInvFunAux ((-x : S4) : E5)
        (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
            (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
          (ℝ ∙ ((-x : S4) : E5))ᗮ) : E5)) :=
    contDiff_stereoInvFunAux.comp
      ((ℝ ∙ ((-x : S4) : E5))ᗮ.subtypeL.contDiff.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
          (ne_zero_of_mem_unit_sphere (-x))).repr.symm.contDiff)
  have heq : ∀ w : E4,
      ((Φ x).symm w : E5)
        = stereoInvFunAux ((-x : S4) : E5)
          (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
              (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
            (ℝ ∙ ((-x : S4) : E5))ᗮ) : E5) := by
    intro w
    show ((stereographic' 4 (-x)).symm w : E5) = _
    rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]
  simpa only [heq] using hcomp

/-! ### §4. The RP⁴ chart transition is `C^k` -/

/-- `(rp4Chart x).target ⊆ (Φ x).target`. -/
theorem rp4Chart_target_subset (x : S4) : (rp4Chart x).target ⊆ (Φ x).target := by
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_target]
  exact OpenPartialHomeomorph.subtypeRestr_target_subset _ _

/-- Hemisphere/antipode bookkeeping: `s ∈ hemi (-y) ↔ (-s) ∈ hemi y`. -/
theorem mem_hemi_neg (y s : S4) : s ∈ hemi (-y) ↔ (-s) ∈ hemi y := by
  show 0 < ⟪((-y : S4) : E5), (s : E5)⟫ ↔ 0 < ⟪(y : E5), ((-s : S4) : E5)⟫
  rw [show ((-y : S4) : E5) = -(y : E5) from rfl, show ((-s : S4) : E5) = -(s : E5) from rfl,
    inner_neg_left, inner_neg_right]

/-- `mk s` lies in the `y`-descended-chart source iff `s` or its antipode is in `hemi y`. -/
theorem mk_mem_source_iff (y : S4) {s : S4} :
    Quotient.mk (MulAction.orbitRel ℤˣ S4) s ∈ (rp4Chart y).source
      ↔ s ∈ hemi y ∨ (-s) ∈ hemi y := by
  rw [rp4Chart_source]
  constructor
  · rintro ⟨s', hs', hmk⟩
    obtain ⟨u, hu⟩ : s' ∈ MulAction.orbit ℤˣ s := Quotient.eq''.mp hmk
    have hu' : u • s = s' := hu
    rcases Int.units_eq_one_or u with h1 | h1
    · left; rw [h1, one_smul] at hu'; rw [hu']; exact hs'
    · right
      rw [h1] at hu'
      have hneg : (-s) = s' := by
        apply Subtype.ext
        rw [show ((-s : S4) : E5) = -(s : E5) from rfl, ← hu', smul_coe]; norm_num
      rw [hneg]; exact hs'
  · rintro (h | h)
    · exact ⟨s, h, rfl⟩
    · exact ⟨-s, h, mk_neg s⟩

/-- **Transition class A (deck element `1`)**: on the piece where `(Φ x).symm t ∈ hemi y`, the RP⁴
transition is the sphere-chart transition `Φ y ∘ (Φ x).symm`, which is `C^k`. -/
theorem contDiffOn_transition_A {k : WithTop ℕ∞} (x y : S4) :
    ContDiffOn ℝ k (fun t : E4 => rp4Chart y ((rp4Chart x).symm t))
      ((rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  apply ContDiffOn.congr (f := fun t : E4 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S4) : E5) ((Φ x).symm t : E5)))
  · refine (contDiffOn_reprStereo y).comp (contDiff_chartSymm_coe_S4 x).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪(y : E5), ((Φ x).symm t : E5)⟫ := hhemi
    show innerSL ℝ ((-y : S4) : E5) ((Φ x).symm t : E5) ≠ 1
    rw [innerSL_apply_apply, show ((-y : S4) : E5) = -(y : E5) from rfl, inner_neg_left]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp4Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S4) ((Φ x).symm t) :=
      rp4Chart_symm_apply x htgt
    rw [hmk, rp4Chart_apply_mk y hhemi, chartAt_S4_apply]

/-- **Transition class B (deck element `-1`)**: on the piece where `(Φ x).symm t ∈ hemi (-y)` (i.e.
its antipode is in `hemi y`), the RP⁴ transition is `Φ y ∘ (·)⁻ ∘ (Φ x).symm` — the sphere-chart
transition composed with the antipodal map — which is `C^k` (negation on `ℝ⁵` is `C^k`). -/
theorem contDiffOn_transition_B {k : WithTop ℕ∞} (x y : S4) :
    ContDiffOn ℝ k (fun t : E4 => rp4Chart y ((rp4Chart x).symm t))
      ((rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  apply ContDiffOn.congr (f := fun t : E4 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 4
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S4) : E5) (-((Φ x).symm t : E5))))
  · refine (contDiffOn_reprStereo y).comp ((contDiff_chartSymm_coe_S4 x).neg).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪((-y : S4) : E5), ((Φ x).symm t : E5)⟫ := hhemi
    show innerSL ℝ ((-y : S4) : E5) (-((Φ x).symm t : E5)) ≠ 1
    rw [innerSL_apply_apply, inner_neg_right]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp4Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S4) ((Φ x).symm t) :=
      rp4Chart_symm_apply x htgt
    have hneghemi : (-(Φ x).symm t) ∈ hemi y := (mem_hemi_neg y ((Φ x).symm t)).mp hhemi
    rw [hmk, ← mk_neg ((Φ x).symm t), rp4Chart_apply_mk y hneghemi, chartAt_S4_apply,
      coe_neg_S4 ((Φ x).symm t)]

/-- Piece A is open in `ℝ⁴`. -/
theorem isOpen_VA (x y : S4) :
    IsOpen ((rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen y)
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)
      = (rp4Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp4Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp4Chart x).open_target.inter h1

/-- Piece B is open in `ℝ⁴`. -/
theorem isOpen_VB (x y : S4) :
    IsOpen ((rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen (-y))
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))
      = (rp4Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp4Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp4Chart x).open_target.inter h1

/-- **The RP⁴ chart transition is `C^k`** on the transition source: assembled from the two disjoint
open pieces (deck elements `±1`), each a `C^k` sphere-chart transition. -/
theorem contDiffOn_rp4_transition {k : WithTop ℕ∞} (x y : S4) :
    ContDiffOn ℝ k (fun t : E4 => rp4Chart y ((rp4Chart x).symm t))
      ((rp4Chart x).target ∩ ↑(rp4Chart x).symm ⁻¹' (rp4Chart y).source) := by
  intro t ht
  obtain ⟨htgt, hsrc⟩ := ht
  have hmk : (rp4Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S4) ((Φ x).symm t) :=
    rp4Chart_symm_apply x htgt
  rw [Set.mem_preimage, hmk] at hsrc
  rcases (mk_mem_source_iff y).mp hsrc with hA | hB
  · have hVA : t ∈ (rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y) := ⟨htgt, hA⟩
    exact ((contDiffOn_transition_A x y).contDiffAt
      ((isOpen_VA x y).mem_nhds hVA)).contDiffWithinAt
  · have hnegB : (Φ x).symm t ∈ hemi (-y) := (mem_hemi_neg y ((Φ x).symm t)).mpr hB
    have hVB : t ∈ (rp4Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y)) := ⟨htgt, hnegB⟩
    exact ((contDiffOn_transition_B x y).contDiffAt
      ((isOpen_VB x y).mem_nhds hVB)).contDiffWithinAt

/-! ### §5. The `k`-generic `IsManifold` instance and the smooth witness -/

/-- **`ℝP⁴` is a `C^k` manifold** for every regularity `k : WithTop ℕ∞** — the descended
stereographic atlas has `C^k` transitions (§4). The literature target `Ω₄^{Pin⁺} ≅ ℤ/16` is a
smooth-category statement; this instance lets the `ℝP⁴` witness be instantiated at `k = ∞`. -/
instance isManifold_rp4 {k : WithTop ℕ∞} : IsManifold (𝓡 4) k RP4 := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have key := contDiffOn_rp4_transition (k := k) x y
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
    Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source]
  exact key

/-- **`ℝP⁴` is a real-analytic (`Cω`) manifold** — the strongest regularity (`k = ⊤`), matching
`S⁴`'s own `ω`-smooth structure and a fortiori `C^∞`. The descended stereographic transitions have
real-analytic transitions (`stereoToFun`, negation, and `repr` are all `Cω`). -/
theorem isManifold_rp4_analytic : IsManifold (𝓡 4) ⊤ RP4 := isManifold_rp4

/-- **`ℝP⁴` as a `C^k` singular manifold over `PUnit`** (every `k : WithTop ℕ∞`) — the `k`-generic
lift of the `RP4Witness.rp4SM` witness carrier into the smooth category. Instantiate at `k = ∞`
(`⊤`) for the smooth-category `Ω₄^{Pin⁺} ≅ ℤ/16` target. Its `IsManifold` field is the `§5`
instance above; the `k = 0` specialisation is defeq to the existing `RP4Witness.rp4SM`. -/
noncomputable def rp4SM_k (k : WithTop ℕ∞) : SingularManifold PUnit k (𝓡 4) where
  M := RP4
  f := fun _ => PUnit.unit
  hf := continuous_const

end

end SKEFTHawking.RP4Manifold
