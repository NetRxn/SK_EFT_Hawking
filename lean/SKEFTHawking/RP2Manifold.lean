import Mathlib
import SKEFTHawking.RP2PointSet
import SKEFTHawking.SingularSurfaceIntersectionForm

/-!
# W-A ℝP²-witness prerequisite (B4b/B4c analogue, one dimension down) — the `k`-generic smooth
structure on `ℝP²`

`RP2PointSet` gives `ℝP² = S²/±` a `ChartedSpace (EuclideanSpace ℝ (Fin 2))` structure by
descending the sphere's stereographic charts along the hemisphere open embeddings
(`rp2Chart x = (chartAt _ x |_{hemi x}).lift_openEmbedding (mk|_{hemi x})`), mirroring
`RP4PointSet`/`RP4Manifold` (Phase 5q.G/5q.H) one dimension down.

This module supplies the **`k`-generic** `IsManifold (𝓡 2) k RP2` (all `k : WithTop ℕ∞`): the
transition between two descended charts `rp2Chart x` and `rp2Chart y` reduces — on the sphere —
to the sphere-chart transition on the disjoint opens `hemi x ∩ hemi y` (deck element `1`) and
`hemi x ∩ hemi (-y)` (deck element `-1`, i.e. the antipodal map). Both are `C^k` because `S²` is
`ω`-smooth (`EuclideanSpace.instIsManifoldSphere`) and negation on `ℝ³` is `C^k`. This supplies
the `ChartedSpace`-on-`E²` + `T2Space` + `CompactSpace` + `Nonempty` carrier that
`SingularSurfaceIntersectionForm` needs to fire its generic mod-2 fundamental-class /
intersection-form machinery on `ℝP²` (the W-A stretch goal, §6).

Reuses the RP4 house style (`RP4Manifold.lean`): explicit `ContDiffOn` transition classes
assembled through `isManifold_of_contDiffOn`. Template fidelity: every step below mirrors the
RP4 counterpart verbatim modulo the dimension substitution `4 ↦ 2`, `5 ↦ 3` (ambient sphere
dimension, orthocomplement-basis index, and `Fin` literals) — no structural divergence was
needed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/

open Metric Set
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.RP2PointSet
open SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.RP2Manifold

noncomputable section

/-- Ambient `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin (2 + 1))
/-- Model `ℝ²`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- Abbreviation for the sphere's stereographic chart at `x`. -/
noncomputable abbrev Φ (x : S2) : OpenPartialHomeomorph S2 E2 := chartAt E2 x

/-! ### §1. Foundational: `S²` is `C^k`-smooth, and the antipodal relation on classes -/

/-- Local dimension fact for `S² ⊆ ℝ³`, needed by every `stereographic'` unfold. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- `S²` is a `C^k` manifold for every regularity `k` (from Mathlib's `ω`-smooth instance). -/
instance isManifold_S2 {k : WithTop ℕ∞} : IsManifold (𝓡 2) k S2 := IsManifold.of_le le_top

/-- The sphere's `Neg` coercion agrees with ambient negation (`rfl`). -/
theorem coe_neg_S2 (s : S2) : ((-s : S2) : E3) = -(s : E3) := rfl

/-- The class of a sphere point equals the class of its antipode (deck element `-1`). -/
theorem mk_neg (s : S2) :
    Quotient.mk (MulAction.orbitRel ℤˣ S2) (-s) = Quotient.mk (MulAction.orbitRel ℤˣ S2) s := by
  apply Quotient.sound
  refine ⟨(-1 : ℤˣ), ?_⟩
  apply Subtype.ext
  rw [smul_coe]
  norm_num

/-! ### §2. Bridge: `rp2Chart` in terms of the sphere charts -/

/-- The sphere chart's source is the complement of the antipode of the base point. -/
theorem chartAt_S2_source (x : S2) : (Φ x).source = {-x}ᶜ := stereographic'_source (-x)

/-- Every hemisphere point lies in the base chart's source (the antipode is the excluded pole). -/
theorem hemi_subset_source (x : S2) : hemi x ⊆ (Φ x).source := by
  intro s hs
  rw [chartAt_S2_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcontra
  have hpos : 0 < ⟪(x : E3), (s : E3)⟫ := hs
  rw [hcontra] at hpos
  have : ((-x : S2) : E3) = -(x : E3) := rfl
  rw [this, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp x.2] at hpos
  norm_num at hpos

/-- Descended-chart value: on the hemisphere, `rp2Chart x ∘ mk = Φ x`. -/
theorem rp2Chart_apply_mk (x : S2) {s : S2} (hs : s ∈ hemi x) :
    rp2Chart x (Quotient.mk (MulAction.orbitRel ℤˣ S2) s) = Φ x s := by
  rw [rp2Chart]
  rw [show Quotient.mk (MulAction.orbitRel ℤˣ S2) s
    = (fun y : ↥(hemi x) => Quotient.mk (MulAction.orbitRel ℤˣ S2) y.1) ⟨s, hs⟩ from rfl]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The descended chart's source is the image of the hemisphere. -/
theorem rp2Chart_source (x : S2) :
    (rp2Chart x).source = Quotient.mk (MulAction.orbitRel ℤˣ S2) '' hemi x := by
  rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext p
  constructor
  · rintro ⟨⟨y, hy⟩, hy2, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, hemi_subset_source x hy, rfl⟩

/-- The descended chart's inverse, read on its target, is `mk ∘ Φ x .symm`. -/
theorem rp2Chart_symm_apply (x : S2) {t : E2} (ht : t ∈ (rp2Chart x).target) :
    (rp2Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((Φ x).symm t) := by
  have ht' : t ∈ ((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).target := by
    rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht; exact ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht'
  rw [Function.comp_apply] at heq
  rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, heq]

/-- On the descended chart's target, the sphere-inverse lands in the hemisphere. -/
theorem rp2Chart_symm_mem_hemi (x : S2) {t : E2} (ht : t ∈ (rp2Chart x).target) :
    (Φ x).symm t ∈ hemi x := by
  rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht
  rw [Function.comp_apply] at heq
  rw [heq]
  exact (((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).symm t).2

/-! ### §3. Coordinate-level smoothness of the sphere charts (reusable primitives) -/

/-- Forward-apply of the `S²` stereographic chart in `repr ∘ stereoToFun` normal form (`rfl`). -/
theorem chartAt_S2_apply (y w : S2) :
    Φ y w = (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-y))).repr
        (stereoToFun ((-y : S2) : E3) (w : E3)) := rfl

/-- **The raw `repr ∘ stereoToFun` composite is `C^k`** on the north-pole-excluded locus. The
`y`-chart read at coordinate level; the reusable input to both RP² transition classes. -/
theorem contDiffOn_reprStereo {k : WithTop ℕ∞} (y : S2) :
    ContDiffOn ℝ k
      (fun w : E3 => (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-y))).repr (stereoToFun ((-y : S2) : E3) w))
      {w : E3 | innerSL ℝ ((-y : S2) : E3) w ≠ 1} :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
      (ne_zero_of_mem_unit_sphere (-y))).repr.contDiff.comp_contDiffOn contDiffOn_stereoToFun

/-- **The inverse `S²` stereographic chart is `C^k`** as a map into `ℝ³` (`stereoInvFunAux`,
`repr.symm`, and the orthocomplement inclusion are all `C^k`). -/
theorem contDiff_chartSymm_coe_S2 {k : WithTop ℕ∞} (x : S2) :
    ContDiff ℝ k (fun w : E2 => ((Φ x).symm w : E3)) := by
  have hcomp : ContDiff ℝ k (fun w : E2 =>
      stereoInvFunAux ((-x : S2) : E3)
        (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
            (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
          (ℝ ∙ ((-x : S2) : E3))ᗮ) : E3)) :=
    contDiff_stereoInvFunAux.comp
      ((ℝ ∙ ((-x : S2) : E3))ᗮ.subtypeL.contDiff.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-x))).repr.symm.contDiff)
  have heq : ∀ w : E2,
      ((Φ x).symm w : E3)
        = stereoInvFunAux ((-x : S2) : E3)
          (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
              (ne_zero_of_mem_unit_sphere (-x))).repr.symm w :
            (ℝ ∙ ((-x : S2) : E3))ᗮ) : E3) := by
    intro w
    show ((stereographic' 2 (-x)).symm w : E3) = _
    rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]
  simpa only [heq] using hcomp

/-! ### §4. The RP² chart transition is `C^k` -/

/-- `(rp2Chart x).target ⊆ (Φ x).target`. -/
theorem rp2Chart_target_subset (x : S2) : (rp2Chart x).target ⊆ (Φ x).target := by
  rw [rp2Chart, OpenPartialHomeomorph.lift_openEmbedding_target]
  exact OpenPartialHomeomorph.subtypeRestr_target_subset _ _

/-- Hemisphere/antipode bookkeeping: `s ∈ hemi (-y) ↔ (-s) ∈ hemi y`. -/
theorem mem_hemi_neg (y s : S2) : s ∈ hemi (-y) ↔ (-s) ∈ hemi y := by
  show 0 < ⟪((-y : S2) : E3), (s : E3)⟫ ↔ 0 < ⟪(y : E3), ((-s : S2) : E3)⟫
  rw [show ((-y : S2) : E3) = -(y : E3) from rfl, show ((-s : S2) : E3) = -(s : E3) from rfl,
    inner_neg_left, inner_neg_right]

/-- `mk s` lies in the `y`-descended-chart source iff `s` or its antipode is in `hemi y`. -/
theorem mk_mem_source_iff (y : S2) {s : S2} :
    Quotient.mk (MulAction.orbitRel ℤˣ S2) s ∈ (rp2Chart y).source
      ↔ s ∈ hemi y ∨ (-s) ∈ hemi y := by
  rw [rp2Chart_source]
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
        rw [show ((-s : S2) : E3) = -(s : E3) from rfl, ← hu', smul_coe]; norm_num
      rw [hneg]; exact hs'
  · rintro (h | h)
    · exact ⟨s, h, rfl⟩
    · exact ⟨-s, h, mk_neg s⟩

/-- **Transition class A (deck element `1`)**: on the piece where `(Φ x).symm t ∈ hemi y`, the RP²
transition is the sphere-chart transition `Φ y ∘ (Φ x).symm`, which is `C^k`. -/
theorem contDiffOn_transition_A {k : WithTop ℕ∞} (x y : S2) :
    ContDiffOn ℝ k (fun t : E2 => rp2Chart y ((rp2Chart x).symm t))
      ((rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  apply ContDiffOn.congr (f := fun t : E2 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S2) : E3) ((Φ x).symm t : E3)))
  · refine (contDiffOn_reprStereo y).comp (contDiff_chartSymm_coe_S2 x).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪(y : E3), ((Φ x).symm t : E3)⟫ := hhemi
    show innerSL ℝ ((-y : S2) : E3) ((Φ x).symm t : E3) ≠ 1
    rw [innerSL_apply_apply, show ((-y : S2) : E3) = -(y : E3) from rfl, inner_neg_left]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp2Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((Φ x).symm t) :=
      rp2Chart_symm_apply x htgt
    rw [hmk, rp2Chart_apply_mk y hhemi, chartAt_S2_apply]

/-- **Transition class B (deck element `-1`)**: on the piece where `(Φ x).symm t ∈ hemi (-y)` (i.e.
its antipode is in `hemi y`), the RP² transition is `Φ y ∘ (·)⁻ ∘ (Φ x).symm` — the sphere-chart
transition composed with the antipodal map — which is `C^k` (negation on `ℝ³` is `C^k`). -/
theorem contDiffOn_transition_B {k : WithTop ℕ∞} (x y : S2) :
    ContDiffOn ℝ k (fun t : E2 => rp2Chart y ((rp2Chart x).symm t))
      ((rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  apply ContDiffOn.congr (f := fun t : E2 =>
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
      (ne_zero_of_mem_unit_sphere (-y))).repr
      (stereoToFun ((-y : S2) : E3) (-((Φ x).symm t : E3))))
  · refine (contDiffOn_reprStereo y).comp ((contDiff_chartSymm_coe_S2 x).neg).contDiffOn ?_
    intro t ht
    obtain ⟨-, hhemi⟩ := ht
    have hpos : 0 < ⟪((-y : S2) : E3), ((Φ x).symm t : E3)⟫ := hhemi
    show innerSL ℝ ((-y : S2) : E3) (-((Φ x).symm t : E3)) ≠ 1
    rw [innerSL_apply_apply, inner_neg_right]
    intro heq; linarith
  · intro t ht
    obtain ⟨htgt, hhemi⟩ := ht
    have hmk : (rp2Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((Φ x).symm t) :=
      rp2Chart_symm_apply x htgt
    have hneghemi : (-(Φ x).symm t) ∈ hemi y := (mem_hemi_neg y ((Φ x).symm t)).mp hhemi
    rw [hmk, ← mk_neg ((Φ x).symm t), rp2Chart_apply_mk y hneghemi, chartAt_S2_apply,
      coe_neg_S2 ((Φ x).symm t)]

/-- Piece A is open in `ℝ²`. -/
theorem isOpen_VA (x y : S2) :
    IsOpen ((rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen y)
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)
      = (rp2Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp2Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp2Chart x).open_target.inter h1

/-- Piece B is open in `ℝ²`. -/
theorem isOpen_VB (x y : S2) :
    IsOpen ((rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
  have h1 := (Φ x).symm.isOpen_inter_preimage (hemi_isOpen (-y))
  rw [OpenPartialHomeomorph.symm_source] at h1
  have hset : (rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))
      = (rp2Chart x).target ∩ ((Φ x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y))) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ht1, ht2⟩; exact ⟨ht1, rp2Chart_target_subset x ht1, ht2⟩
    · rintro ⟨ht1, -, ht2⟩; exact ⟨ht1, ht2⟩
  rw [hset]
  exact (rp2Chart x).open_target.inter h1

/-- **The RP² chart transition is `C^k`** on the transition source: assembled from the two disjoint
open pieces (deck elements `±1`), each a `C^k` sphere-chart transition. -/
theorem contDiffOn_rp2_transition {k : WithTop ℕ∞} (x y : S2) :
    ContDiffOn ℝ k (fun t : E2 => rp2Chart y ((rp2Chart x).symm t))
      ((rp2Chart x).target ∩ ↑(rp2Chart x).symm ⁻¹' (rp2Chart y).source) := by
  intro t ht
  obtain ⟨htgt, hsrc⟩ := ht
  have hmk : (rp2Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S2) ((Φ x).symm t) :=
    rp2Chart_symm_apply x htgt
  rw [Set.mem_preimage, hmk] at hsrc
  rcases (mk_mem_source_iff y).mp hsrc with hA | hB
  · have hVA : t ∈ (rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi y) := ⟨htgt, hA⟩
    exact ((contDiffOn_transition_A x y).contDiffAt
      ((isOpen_VA x y).mem_nhds hVA)).contDiffWithinAt
  · have hnegB : (Φ x).symm t ∈ hemi (-y) := (mem_hemi_neg y ((Φ x).symm t)).mpr hB
    have hVB : t ∈ (rp2Chart x).target ∩ ↑(Φ x).symm ⁻¹' (hemi (-y)) := ⟨htgt, hnegB⟩
    exact ((contDiffOn_transition_B x y).contDiffAt
      ((isOpen_VB x y).mem_nhds hVB)).contDiffWithinAt

/-! ### §5. The `k`-generic `IsManifold` instance and the smooth witness -/

/-- **`ℝP²` is a `C^k` manifold** for every regularity `k : WithTop ℕ∞** — the descended
stereographic atlas has `C^k` transitions (§4). -/
instance isManifold_rp2 {k : WithTop ℕ∞} : IsManifold (𝓡 2) k RP2 := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have key := contDiffOn_rp2_transition (k := k) x y
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
    Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source]
  exact key

/-- **`ℝP²` is a real-analytic (`Cω`) manifold** — the strongest regularity (`k = ⊤`), matching
`S²`'s own `ω`-smooth structure and a fortiori `C^∞`. The descended stereographic transitions have
real-analytic transitions (`stereoToFun`, negation, and `repr` are all `Cω`). -/
theorem isManifold_rp2_analytic : IsManifold (𝓡 2) ⊤ RP2 := isManifold_rp2

/-- **`ℝP²` as a `C^k` singular manifold over `PUnit`** (every `k : WithTop ℕ∞`) — the closed-surface
witness carrier, mirroring `RP4Manifold.rp4SM_k` one dimension down. Instantiate at `k = ∞` (`⊤`)
for the smooth category, or `k = 0` for the `SingularSurfaceIntersectionForm` machinery (§6). -/
noncomputable def rp2SM_k (k : WithTop ℕ∞) : SingularManifold PUnit k (𝓡 2) where
  M := RP2
  f := fun _ => PUnit.unit
  hf := continuous_const

/-! ### §6. STRETCH — connecting to the closed-surface intersection-form machinery

`SingularSurfaceIntersectionForm` is stated for any `M` with `[TopologicalSpace M] [T2Space M]
[CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]`. `RP2` already
has `T2Space`/`CompactSpace`/`Nonempty` (`RP2PointSet`) and `ChartedSpace (EuclideanSpace ℝ
(Fin 2))` (§ above); the only gap is the `Fin 2` vs `Fin (0 + 2)` model spelling, bridged by a
defeq re-key exactly like `RP4Witness`'s `Fin (2 + 2)` re-key of the `Fin 4` instance. Once
re-keyed, the generic fundamental class `[ℝP²] ∈ H₂(ℝP²;ℤ/2)` and the mod-2 intersection form
fire automatically — no new mathematics, only the instance bridge. -/

/-- The charted instance re-keyed at the `Fin (0 + 2)` spelling
`SingularSurfaceIntersectionForm` uses (defeq to the `Fin 2` instance above; instance search is
syntactic on the model key). -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) RP2 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 2)) RP2)

/-- **The mod-2 fundamental class `[ℝP²] ∈ H₂(ℝP²;ℤ/2)`** — the generic closed-surface
`surfaceFundamentalClass` machinery fires on `RP2` given exactly the instance bridge above; no
new mathematics beyond the `ChartedSpace` re-key. -/
noncomputable def rp2FundamentalClass :
    Homology (TopCat.of RP2) (0 + 2) :=
  SKEFTHawking.SingularSurfaceIntersectionForm.surfaceFundamentalClass (M := RP2)

/-- **`[ℝP²] ≠ 0`** — the fundamental class is a genuine nonzero top-homology generator, the `RP2`
instance of `surfaceFundamentalClass_ne_zero`. Confirms the generic machinery is non-vacuous on
this carrier (not merely well-typed). -/
theorem rp2FundamentalClass_ne_zero : rp2FundamentalClass ≠ 0 :=
  SKEFTHawking.SingularSurfaceIntersectionForm.surfaceFundamentalClass_ne_zero (M := RP2)

end

end SKEFTHawking.RP2Manifold
