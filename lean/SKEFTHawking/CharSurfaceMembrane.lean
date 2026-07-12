/-
# Phase 5q.H (E2 · membrane layer) — the [G2]/[Q1] normal-framing/membrane primitives and the
Taylor-Theorem-1.1 debt DECOMPOSITION

The blueprint's [G2]/[Q1] nodes (`Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_
20260703.md`: *"[G2] SMOOTH: membrane D⊂X (∂D=C⊂F) … [Q1] q_F(x) := D·F + O(D) + d(C) mod 2
well-defined"*) specialized to Taylor `0802.0111` Theorem 1.1's bounding-3-manifold setting, where
the membrane lives in `V` (∂V = F) and the correction terms of the ambient [Q1] formula vanish —
so the [Q1] content IS "q dies on membrane-bounded circles". This module SHRINKS the frozen
`TaylorKernelVanishing` (Taylor Thm 1.1) into three strictly smaller named geometric Props, with
every reduction a THEOREM:

* `Membrane` — the honest [G2] datum: a compact 2-manifold-with-boundary `S` (model `𝓡∂ 2`), the
  circle injected onto `∂S` (the same collar encoding as `Bounding`/`TraceData`/`Bordism`), the
  membrane map `D : S → V` with boundary factorization, and the homological kill of the circle
  class as data (the LES-of-the-pair shadow, per the E1 checklist idiom).
* `cls_mem_kernelL_of_boundsMembraneIn` — PROVED: a membrane-bounding circle dies in the
  Taylor/Klug metabolizer (functoriality; generalizes the disk case).
* `cls_mem_kernelL_iff_topFactorization` — PROVED: at the PURELY TOPOLOGICAL level a membrane-like
  factorization is EXACTLY kernel membership (the tautological witness `S := V`). This pins where
  the [G2] content genuinely lives — in the 2-manifold-with-boundary structure of `S`, NOT in the
  factorization/kill topology. Do not rebuild topological membranes hoping for content.
* The DECOMPOSITION (Taylor Thm 1.1's proof steps, 1-1):
  - `ClassesEmbedded` — **pin-FREE, V-FREE** surface topology: nonzero `H₁` classes are
    represented by embedded circles;
  - `KernelCirclesBound` — **pin-FREE** 3-manifold topology: circles dying in `V` bound membranes
    (the mod-2 relative Seifert construction); the two combine to `MembraneRealizes`
    (`membraneRealizes_of_classesEmbedded`, PROVED — Taylor's realization step);
  - `MembraneTrivializesNormal` — **pin-FREE** intersection theory: membrane-bounding circles have
    vanishing mod-2 self-pairing (the trivial-normal-bundle shadow);
  - `MembraneSpinKill` — THE single remaining pin⁻ atom: the `Ω₁^{Spin} ≅ ℤ/2` bit of a
    detection-coherent framed circle dies when the circle bounds a membrane in the Pin⁻ bounding
    3-manifold (Taylor's "the induced spin structure bounds" argument);
  with `taylorKernelVanishing_of_membranes` (the SHRINK: realization + membrane-vanishing ⟹
  Thm 1.1's freeze), `taylorMembraneVanishing_of_taylorKernelVanishing` (NO INFLATION: the middle
  layer is subsumed back), and `taylorMembraneVanishing_iff` (EXACT accounting: middle layer ⟺
  spin-atom ∧ normal shadow, both ways) — plus the composed end `gmrelation_null_of_membranes`
  and the summation-step algebra `q_add_of_B_eq_zero` (disjoint-circle additivity, DERIVED).
* The framing bookkeeping tying the `Ω₁^{Spin}` bit to `q`, DERIVED: `embed2_toZ2_of_two_mul_self`
  (pointwise halving section), `EmbeddedCircle.framed` + `framed_detects` (every circle with the
  trivial-normal shadow carries a canonical detection-coherent framing — detection-coherence is
  inhabited exactly when it should be), and `FramedCircle.not_detects_flip` (detection pins
  EXACTLY ONE of the two spin bits — the freeze is never vacuously two-sided).
* `TraceData.Core` — the `D² × D¹` trace construction as an honest datum: the CORE DISK of the
  attached 2-handle inside the trace, with `Core.fund_dies` PROVED (the surgered circle's class
  dies in the trace — the homological signature of `(F×I) ∪_{S¹×D¹} (D²×D¹)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceTrace

namespace SKEFTHawking.Brown.Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- **Pointwise halving section**: on a class with vanishing self-pairing (`B v v = 0`, i.e. the
enhancement value is even by polarization), `embed2 (toZ2 v) = q v` — the pointwise refinement of
`embed2_toZ2_of_even` (which demands evenness everywhere). This is the arithmetic that lets a
trivially-normally-framed circle carry its canonical spin bit. -/
lemma embed2_toZ2_of_B_self_eq_zero {v : ι → ZMod 2} (h : Q.B v v = 0) :
    embed2 (Q.toZ2 v) = Q.q v := by
  have h2 : 2 * Q.q v = 0 := by
    have hbs := Q.embed2_B_self v
    rw [h, show embed2 (0 : ZMod 2) = 0 from by decide] at hbs
    exact hbs.symm
  have key : ∀ a : ZMod 4, 2 * a = 0 → embed2 (((a.val / 2 : ℕ) : ZMod 2)) = a := by decide
  exact key _ h2

/-- **Disjoint-circle additivity**: the enhancement is additive on `B`-orthogonal classes —
Taylor Theorem 1.1's summation step (`q(Σ γᵢ) = Σ q(γᵢ)` for disjoint embedded circles, whose
classes pair to zero). Direct from the enhancement axiom. -/
lemma q_add_of_B_eq_zero {x y : ι → ZMod 2} (h : Q.B x y = 0) :
    Q.q (x + y) = Q.q x + Q.q y := by
  rw [Q.refine' x y, h, show embed2 (0 : ZMod 2) = 0 from by decide, add_zero]

end SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularDiskAcyclic (Disk)
open scoped Manifold

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-! ## The framing bookkeeping: the canonical detection-coherent spin bit (DERIVED) -/

variable {C : PinCharSurface X k}

/-- **The canonical framing datum** of an embedded circle with the trivial-normal-bundle shadow:
the spin bit is the halving reduction `toZ2` of the enhancement value — the framing whose induced
spin structure is the one the Pin⁻ shadow names (Taylor Lemma 1.2's proof paragraph, at datum
level). Detection-coherence is a THEOREM for it (`framed_detects`), so `SpinClassDetectsQ`-
hypotheses range over an inhabited class exactly when the normal shadow is trivial. -/
noncomputable def EmbeddedCircle.framed (γ : EmbeddedCircle C) (h : γ.selfPair = 0) :
    FramedCircle C where
  toEmbeddedCircle := γ
  spinClass := C.Q.toZ2 γ.cls
  trivNormal := h

@[simp] lemma EmbeddedCircle.framed_toEmbeddedCircle (γ : EmbeddedCircle C)
    (h : γ.selfPair = 0) : (γ.framed h).toEmbeddedCircle = γ := rfl

@[simp] lemma EmbeddedCircle.framed_spinClass (γ : EmbeddedCircle C) (h : γ.selfPair = 0) :
    (γ.framed h).spinClass = C.Q.toZ2 γ.cls := rfl

/-- **The canonical framing detects** (PROVED — the framing bookkeeping tying the `Ω₁^{Spin}` bit
to `q`): `embed2 (toZ2 cls) = q(cls)` holds because the trivial-normal shadow forces the
enhancement value even. Together with `spinClass_eq_toZ2_of_detects` this says the canonical
framing is THE detection-coherent one. -/
theorem EmbeddedCircle.framed_detects (γ : EmbeddedCircle C) (h : γ.selfPair = 0) :
    (γ.framed h).SpinClassDetectsQ :=
  C.Q.embed2_toZ2_of_B_self_eq_zero h

/-- **Detection pins exactly one of the two framings**: if a framed circle is detection-coherent,
the SAME embedded circle carrying the OPPOSITE spin bit is NOT — `q` genuinely remembers the
framing, so the detection freeze is never vacuously satisfied by both `Ω₁^{Spin}` classes. -/
theorem FramedCircle.not_detects_flip (γ : FramedCircle C) (h : γ.SpinClassDetectsQ) :
    ¬ (⟨γ.toEmbeddedCircle, γ.spinClass + 1, γ.trivNormal⟩ : FramedCircle C).SpinClassDetectsQ := by
  intro hflip
  have hs : γ.spinClass + 1 = γ.spinClass := embed2_injective (hflip.trans h.symm)
  exact absurd hs (by generalize γ.spinClass = s; revert s; decide)

/-! ## The membrane datum ([G2]) and its kernel-membership derivations -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}

/-- **A membrane datum ([G2])** for the embedded circle `γ` in the bounding 3-manifold `V`: a
compact 2-manifold-with-boundary `S` (model `𝓡∂ 2`) with the circle injected onto `∂S` (the same
collar encoding as `Bounding`/`TraceData`), a membrane map `D : S → V` factoring the circle's push
into `V` through the surface, and the homological kill of the carried circle class in `S` — the
LES-of-the-pair shadow (`[∂S]` dies in `H₁(S;ℤ/2)`), carried as DATA in the E1-checklist idiom
since the pair-LES for manifolds-with-boundary is not in tree. Falsifiability: `S = S¹` fails
`bd_boundary` (empty boundary), an annulus with `bd` onto one boundary circle fails it too (the
range must be ALL of `∂S`), and a hypothetical datum with `kill` violated is refuted by
`cls_mem_kernelL_of_boundsMembraneIn`'s proof shape. Smoothness of the maps is deliberately not
demanded — the homological consumers ride continuity; the manifold-with-boundary structure of `S`
plus the boundary collar carry the [G2] honesty (see `cls_mem_kernelL_iff_topFactorization` for
the kernel-checked reason a bare topological datum would carry none). -/
structure Membrane (γ : EmbeddedCircle C) (b : C.Bounding J) where
  /-- The membrane's underlying compact 2-manifold-with-boundary. -/
  S : Type
  [topS : TopologicalSpace S]
  [chartS : ChartedSpace (EuclideanHalfSpace 2) S]
  [mfdS : IsManifold (𝓡∂ 2) k S]
  [compactS : CompactSpace S]
  /-- The boundary identification: a continuous injection of the circle onto `∂S`. -/
  bd : ↑Circle1 → S
  bd_cont : Continuous bd
  bd_inj : Function.Injective bd
  bd_boundary : Set.range bd = (𝓡∂ 2).boundary S
  /-- The membrane map into the bounding 3-manifold. -/
  D : S → b.V
  D_cont : Continuous D
  /-- Boundary factorization: pushing the circle through the membrane agrees with pushing it
  through the surface's boundary identification. -/
  factor : ∀ p, D (bd p) = b.e (γ.f p)
  /-- The homological kill (the LES-of-the-pair shadow, as data): the carried circle class dies
  in the membrane. -/
  kill : Homology.map (X := Circle1) (Y := TopCat.of S) (ContinuousMap.mk bd bd_cont) 1 γ.fund = 0

namespace Membrane

variable {γ : EmbeddedCircle C} {b : C.Bounding J}

instance (m : Membrane γ b) : TopologicalSpace m.S := m.topS
instance (m : Membrane γ b) : ChartedSpace (EuclideanHalfSpace 2) m.S := m.chartS
instance (m : Membrane γ b) : IsManifold (𝓡∂ 2) k m.S := m.mfdS
instance (m : Membrane γ b) : CompactSpace m.S := m.compactS

end Membrane

/-- **The circle bounds a membrane in the bounding 3-manifold** — the [G2] existence Prop for a
single circle (Taylor Theorem 1.1's per-class geometric witness). -/
def EmbeddedCircle.BoundsMembraneIn (γ : EmbeddedCircle C) (b : C.Bounding J) : Prop :=
  Nonempty (Membrane γ b)

/-- **A membrane-bounding circle dies in `V`** (PROVED): its class lies in the Taylor/Klug
metabolizer `kernelL` — functoriality of singular homology through the membrane factorization plus
the carried kill. Generalizes `cls_mem_kernelL_of_boundsDiskIn` from disks to arbitrary membranes. -/
theorem EmbeddedCircle.cls_mem_kernelL_of_boundsMembraneIn (γ : EmbeddedCircle C)
    (b : C.Bounding J) (hm : γ.BoundsMembraneIn b) : γ.cls ∈ b.kernelL := by
  obtain ⟨m⟩ := hm
  refine Submodule.mem_map.mpr
    ⟨Homology.map (X := Circle1) (Y := TopCat.of C.F.M) γ.f 1 γ.fund, ?_, rfl⟩
  have hfac : (ContinuousMap.mk b.e b.he_smooth.continuous).comp γ.f
      = (ContinuousMap.mk m.D m.D_cont :
          C(↑(TopCat.of m.S), ↑(TopCat.of b.V))).comp
        (ContinuousMap.mk m.bd m.bd_cont : C(↑Circle1, ↑(TopCat.of m.S))) := by
    ext p
    exact (m.factor p).symm
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← Homology.map_comp, hfac, Homology.map_comp,
    LinearMap.comp_apply, m.kill, map_zero]

/-- **Where the membrane content genuinely lives** (PROVED, both ways): at the purely TOPOLOGICAL
level, "the circle factors through SOME space killing its class" is EXACTLY kernel membership —
the tautological witness is `S := V` itself. So a membrane datum whose `S` is an arbitrary space
carries ZERO geometric content beyond `kernelL`; ALL of [G2]'s debt sits in `S` being a compact
2-manifold-with-boundary with the circle as its full boundary. This theorem is the guard against
re-deriving a contentless "topological membrane" layer. -/
theorem EmbeddedCircle.cls_mem_kernelL_iff_topFactorization (γ : EmbeddedCircle C)
    (b : C.Bounding J) :
    γ.cls ∈ b.kernelL ↔ ∃ (S : TopCat) (bd : C(↑Circle1, ↑S)) (D : C(↑S, ↑(TopCat.of b.V))),
      D.comp bd = (ContinuousMap.mk b.e b.he_smooth.continuous :
        C(↑(TopCat.of C.F.M), ↑(TopCat.of b.V))).comp γ.f ∧
      Homology.map (X := Circle1) (Y := S) bd 1 γ.fund = 0 := by
  constructor
  · intro hl
    obtain ⟨y, hy, hcls⟩ := Submodule.mem_map.mp hl
    have hy' : y = Homology.map (X := Circle1) (Y := TopCat.of C.F.M) γ.f 1 γ.fund := by
      apply C.H1Iso.injective
      exact hcls
    subst hy'
    refine ⟨TopCat.of b.V,
      (ContinuousMap.mk b.e b.he_smooth.continuous :
        C(↑(TopCat.of C.F.M), ↑(TopCat.of b.V))).comp γ.f,
      ContinuousMap.id _, ?_, ?_⟩
    · ext p
      rfl
    · rw [LinearMap.mem_ker] at hy
      rw [Homology.map_comp, LinearMap.comp_apply]
      exact hy
  · rintro ⟨S, bd, D, hfac, hkill⟩
    refine Submodule.mem_map.mpr
      ⟨Homology.map (X := Circle1) (Y := TopCat.of C.F.M) γ.f 1 γ.fund, ?_, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← Homology.map_comp, ← hfac,
      Homology.map_comp, LinearMap.comp_apply, hkill, map_zero]

/-! ## The Taylor-Theorem-1.1 debt decomposition: strictly smaller named Props -/

/-- **Embedded representation of `H₁` classes** (pin-free, `V`-free CLASSICAL surface topology:
every nonzero mod-2 class on a closed surface is represented by an embedded circle): the finest
realization ingredient — it mentions only the surface datum, no bounding 3-manifold, no Pin⁻
data. Taylor Theorem 1.1's proof consumes it through the handle decomposition's attaching
circles. -/
def PinCharSurface.ClassesEmbedded (C : PinCharSurface X k) : Prop :=
  ∀ l : C.ι → ZMod 2, l ≠ 0 → ∃ γ : EmbeddedCircle C, γ.cls = l

namespace PinCharSurface.Bounding

variable {C : PinCharSurface X k}

/-- **Membrane existence for dying circles** (pin-FREE 3-manifold topology: a circle whose mod-2
class dies in `V` bounds a compact — possibly non-orientable — surface in `V`, the mod-2 relative
Seifert construction): the second realization ingredient, per-circle. No Pin⁻ data and no
enhancement value appear in the statement. -/
def KernelCirclesBound (b : C.Bounding J) : Prop :=
  ∀ γ : EmbeddedCircle C, γ.cls ∈ b.kernelL → γ.BoundsMembraneIn b

/-- **[G2] existence — the realization freeze** (pin-FREE 3-manifold/surface topology): every
NONZERO class of the Taylor/Klug metabolizer is realized by an embedded circle bounding a membrane
in `V`. This is Taylor `0802.0111` Theorem 1.1's realization step (his 0-handle-free handle
decomposition produces exactly such circles-with-bounding-data for classes dying in `M`); no Pin⁻
structure and no enhancement value appear in the statement. Falsifiable: a bounding pair whose
kernel contains a class not representable by any membrane-bounding embedded circle refutes it.
Derivable from the two finer ingredients (`membraneRealizes_of_classesEmbedded`). -/
def MembraneRealizes (b : C.Bounding J) : Prop :=
  ∀ l ∈ b.kernelL, l ≠ 0 → ∃ γ : EmbeddedCircle C, γ.cls = l ∧ γ.BoundsMembraneIn b

/-- **The realization freeze splits** (PROVED): embedded representation of classes (surface-only)
plus membrane existence for dying circles (3-manifold-only) yield the realization freeze — the
two classical-topology ingredients are independent debts. -/
theorem membraneRealizes_of_classesEmbedded (b : C.Bounding J)
    (h1 : C.ClassesEmbedded) (h2 : b.KernelCirclesBound) : b.MembraneRealizes := by
  intro l hl h0
  obtain ⟨γ, hcls⟩ := h1 l h0
  exact ⟨γ, hcls, h2 γ (hcls ▸ hl)⟩

/-- **[Q1] at visible witnesses — the membrane-vanishing freeze**: the enhancement value dies on
every membrane-bounding embedded circle. This is the [Q1] node (`q_F = D·F + O(D) + d(C)`
well-defined) specialized to Taylor Theorem 1.1's bounding setting, where the reference membrane
framing bounds and all correction terms vanish. Strictly smaller than `TaylorKernelVanishing`: the
geometric witness is IN HAND (no homological quantification), and it decomposes further —
EXACTLY — into a pin-free normal shadow plus a single spin bit (`taylorMembraneVanishing_iff`). -/
def TaylorMembraneVanishing (b : C.Bounding J) : Prop :=
  ∀ γ : EmbeddedCircle C, γ.BoundsMembraneIn b → C.Q.q γ.cls = 0

/-- **The pin-FREE normal shadow**: a membrane-bounding circle has vanishing mod-2 self-pairing
(the membrane trivializes the normal Euler shadow). Pure intersection theory — no Pin⁻ data in
the statement. Taylor's "trivial normal bundle" input to Lemma 1.2, at class level. -/
def MembraneTrivializesNormal (b : C.Bounding J) : Prop :=
  ∀ γ : EmbeddedCircle C, γ.BoundsMembraneIn b → γ.selfPair = 0

/-- **THE remaining pin⁻ atom**: for a detection-coherent framed circle bounding a membrane in the
Pin⁻ bounding 3-manifold, the `Ω₁^{Spin} ≅ ℤ/2` bit dies — Taylor's "the induced spin structure on
the framed circle bounds" argument, isolated. This single ℤ/2-valued statement on explicit
geometric witnesses is ALL of Theorem 1.1's Pin⁻ content after the decomposition
(`taylorMembraneVanishing_iff`); everything else is pin-free topology or in-tree algebra. -/
def MembraneSpinKill (b : C.Bounding J) : Prop :=
  ∀ γ : FramedCircle C, γ.SpinClassDetectsQ → γ.toEmbeddedCircle.BoundsMembraneIn b →
    γ.spinClass = 0

/-- **The SHRINK** (PROVED): the two membrane Props imply Taylor Theorem 1.1's frozen target — the
enhancement vanishes on the whole metabolizer. The zero class is handled by the in-tree
`q_zero`; a nonzero kernel class is realized by a membrane-bounding circle (`MembraneRealizes`)
on which the enhancement dies (`TaylorMembraneVanishing`). -/
theorem taylorKernelVanishing_of_membranes (b : C.Bounding J)
    (hreal : b.MembraneRealizes) (hvan : b.TaylorMembraneVanishing) :
    b.TaylorKernelVanishing := by
  intro l hl
  by_cases h0 : l = 0
  · rw [h0]
    exact C.Q.q_zero
  · obtain ⟨γ, hcls, hm⟩ := hreal l hl h0
    rw [← hcls]
    exact hvan γ hm

/-- **No inflation** (PROVED): the membrane-vanishing freeze is subsumed by the Theorem 1.1 freeze
— a membrane-bounding circle's class lies in the kernel, so kernel-vanishing already kills it. The
decomposition never enlarges the debt. -/
theorem taylorMembraneVanishing_of_taylorKernelVanishing (b : C.Bounding J)
    (h : b.TaylorKernelVanishing) : b.TaylorMembraneVanishing :=
  fun γ hm => h _ (γ.cls_mem_kernelL_of_boundsMembraneIn b hm)

/-- **Exact accounting for the membrane layer** (PROVED, both ways): membrane-vanishing is
EQUIVALENT to the conjunction of the single spin-bit atom and the pin-free normal shadow. Forward:
`q = 0` forces the shadow (`B_self_eq_zero_of_q_eq_zero`) and kills the detected bit
(`spinClass_eq_zero_iff_of_detects`). Backward: the shadow admits the canonical detection-coherent
framing (`framed_detects`), whose killed bit forces `q = 0`
(`qVal_eq_zero_of_spinClass_eq_zero`). -/
theorem taylorMembraneVanishing_iff (b : C.Bounding J) :
    b.TaylorMembraneVanishing ↔ b.MembraneSpinKill ∧ b.MembraneTrivializesNormal := by
  constructor
  · intro h
    refine ⟨fun γ hdet hm => ?_, fun γ hm => C.Q.B_self_eq_zero_of_q_eq_zero (h γ hm)⟩
    exact (γ.spinClass_eq_zero_iff_of_detects hdet).mpr (h γ.toEmbeddedCircle hm)
  · rintro ⟨hspin, hnorm⟩ γ hm
    have hdet := γ.framed_detects (hnorm γ hm)
    exact (γ.framed (hnorm γ hm)).qVal_eq_zero_of_spinClass_eq_zero hdet
      (hspin _ hdet hm)

/-- **The composed end through the membrane primitives** (PROVED): the three membrane Props plus
Poincaré–Lefschetz maximality force the null Guillou–Marin residue for a bounded characteristic
surface — `gmrelation_null` with Taylor Theorem 1.1's freeze DERIVED from the decomposition
rather than hypothesized. -/
theorem gmrelation_null_of_membranes (b : C.Bounding J)
    (hreal : b.MembraneRealizes) (hspin : b.MembraneSpinKill)
    (hnorm : b.MembraneTrivializesNormal) (hmax : b.KernelHalfLivesHalfDies) :
    GMrelation 0 0 C.Q :=
  b.gmrelation_null
    (taylorKernelVanishing_of_membranes b hreal
      ((taylorMembraneVanishing_iff b).mpr ⟨hspin, hnorm⟩)) hmax

end PinCharSurface.Bounding

/-! ## The `D²×D¹` trace construction as an honest datum: the core disk -/

namespace TraceData

variable {C : PinCharSurface X k} {γ : FramedCircle C}

/-- **The core-disk datum of a genuine surgery trace**: the core `D² × {pt}` of the attached
2-handle, sitting inside the trace 3-manifold with boundary the framed circle pushed to the near
end. An abstract `TraceData` is any collar bordism with the class-level surgery tie; carrying a
core disk is what makes it the honest `(F×I) ∪_{S¹×D¹} (D²×D¹)` — the disk the surgery glues in.
Falsifiable: a product bordism `F×I` on a homologically nontrivial circle admits no core (its
near-end circle class survives, contradicting `Core.fund_dies`). -/
structure Core (T : TraceData J C γ) where
  /-- The core disk of the attached 2-handle. -/
  core : C(↑(Disk 2), T.V)
  /-- The core's boundary is the framed circle pushed to the near end of the trace. -/
  core_bd : core.comp diskIncl
      = (ContinuousMap.mk (T.bdry ∘ Sum.inl)
          (T.bdry_smooth.continuous.comp continuous_inl)).comp γ.f

omit [FiniteDimensional ℝ E'] in
/-- **The trace kills the surgered circle** (PROVED): with a core disk in hand, the framed
circle's carried class dies in the trace 3-manifold — the homological signature of the honest
trace construction, by functoriality through the disk and disk acyclicity. -/
theorem Core.fund_dies {T : TraceData J C γ} (c : T.Core) :
    Homology.map (X := Circle1) (Y := TopCat.of T.V)
      ((ContinuousMap.mk (T.bdry ∘ Sum.inl)
        (T.bdry_smooth.continuous.comp continuous_inl)).comp γ.f) 1 γ.fund = 0 := by
  rw [← c.core_bd, Homology.map_comp, LinearMap.comp_apply,
    disk_homology_eq_zero 0 (Homology.map (X := Circle1) (Y := Disk 2) diskIncl 1 γ.fund),
    map_zero]

end TraceData

end SKEFTHawking.CharSurface
