/-
# Phase 5q.H — inhabiting `SeamGlueChart` for CONCRETE families (the cylinder arc)

`T2BordismGluing` reduced manifold-level bordism gluing to exactly four residual fields, bundled as
`SeamGlueChart b₁ b₂`; the other eight `Bordism` fields are discharged generically there. This module
supplies the FIRST honest inhabitants of that structure, for concrete composable families — no collar
neighbourhood theorem, no new axiom, no weakening of `SeamGlueChart`.

Everything is stated `k`-generically (`k0-to-k1-transport-refuted` fence).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.T2BordismGluing
import SKEFTHawking.SingularSurgeryManifold

namespace SKEFTHawking.T2BordismGlueFamilies

open scoped Manifold
open SKEFTHawking.BordismTheory SKEFTHawking.T2BordismGluing SKEFTHawking.SurgeryFoundation

/-! ## §1. Generic transport of the whole manifold stack along a homeomorphism -/

section Transport

variable {H' : Type*} [TopologicalSpace H']
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H' Y]

/-- **The transported charted space.** A homeomorphism `e : X ≃ₜ Y` onto a charted space makes `X`
charted: `e` is a single global chart onto `Y`, composed with `Y`'s own atlas. -/
@[reducible] def homeoChartedSpace (e : X ≃ₜ Y) : ChartedSpace H' X :=
  letI := chartedSpaceOfHomeo e
  ChartedSpace.comp H' Y X

theorem homeoChartedSpace_chartAt (e : X ≃ₜ Y) (x : X) :
    @chartAt H' _ X _ (homeoChartedSpace e) x
      = e.toOpenPartialHomeomorph ≫ₕ chartAt H' (e x) := rfl

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {J : ModelWithCorners ℝ E' H'}
  {k : WithTop ℕ∞}

/-- **The transported manifold structure.** -/
theorem isManifold_homeoChartedSpace (e : X ≃ₜ Y) [IsManifold J k Y] :
    @IsManifold ℝ _ E' _ _ H' _ J k X _ (homeoChartedSpace e) := by
  letI : ChartedSpace H' X := homeoChartedSpace e
  haveI : HasGroupoid X (contDiffGroupoid k J) :=
    hasGroupoid_comp_of_homeo e (contDiffGroupoid k J)
  exact IsManifold.mk' _ _ _

/-- **`ContMDiff` transports**: a map into `X` is smooth for the transported structure exactly when
its `e`-composite into `Y` is. -/
theorem contMDiff_homeoChartedSpace_iff {M : Type*} [TopologicalSpace M]
    {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [ChartedSpace HM M] (e : X ≃ₜ Y) {f : M → X} :
    @ContMDiff ℝ _ EM _ _ HM _ IM M _ _ E' _ _ H' _ J X _ (homeoChartedSpace e) k f
      ↔ ContMDiff IM J k (e ∘ f) := by
  letI : ChartedSpace H' X := homeoChartedSpace e
  constructor
  · intro h x
    refine ⟨?_, (h x).2⟩
    exact e.continuous.continuousWithinAt.comp (h x).1 (Set.mapsTo_univ _ _)
  · intro h x
    refine ⟨?_, (h x).2⟩
    have := e.symm.continuous.continuousWithinAt.comp (h x).1 (Set.mapsTo_univ _ _)
    simpa [Function.comp_def] using this

/-- **The boundary transports**: the boundary of the transported structure is the `e`-preimage of
`Y`'s boundary. -/
theorem boundary_homeoChartedSpace (e : X ≃ₜ Y) :
    @ModelWithCorners.boundary ℝ _ E' _ _ H' _ J X _ (homeoChartedSpace e)
      = e ⁻¹' J.boundary Y := rfl

end Transport

/-! ## §2. The straightening homeomorphism for a composite of two cylinders -/

noncomputable section Cylinder

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem coe_Icc_bot : ((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by norm_num

theorem coe_Icc_top : ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := by norm_num

/-- `t ↦ t/2` on `[0,1]` — the left half of the doubled interval. -/
def half₁ (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨t.1 / 2, ⟨by have := t.2.1; linarith, by have := t.2.2; linarith⟩⟩

/-- `t ↦ (t+1)/2` on `[0,1]` — the right half of the doubled interval. -/
def half₂ (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(t.1 + 1) / 2, ⟨by have := t.2.1; linarith, by have := t.2.2; linarith⟩⟩

theorem continuous_half₁ : Continuous half₁ :=
  Continuous.subtype_mk (continuous_subtype_val.div_const 2) _

theorem continuous_half₂ : Continuous half₂ :=
  Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const 2) _

variable (s : SingularManifold X k I)

/-- The straightening map on the **un-welded** sum of the two cylinders: rescale the left copy onto
`[0,½]` and the right copy onto `[½,1]`. -/
def cylPairMap :
    (s.M × Set.Icc (0 : ℝ) 1) ⊕ (s.M × Set.Icc (0 : ℝ) 1) → s.M × Set.Icc (0 : ℝ) 1 :=
  Sum.elim (fun x => (x.1, half₁ x.2)) (fun x => (x.1, half₂ x.2))

omit [I.Boundaryless] in
theorem continuous_cylPairMap : Continuous (cylPairMap s) :=
  Continuous.sumElim (continuous_fst.prodMk (continuous_half₁.comp continuous_snd))
    (continuous_fst.prodMk (continuous_half₂.comp continuous_snd))

/-- **The straightening map on the seam pushout** `(Σ × [0,1]) ⊔_Σ (Σ × [0,1]) → Σ × [0,1]`. It is
well defined precisely because the weld identifies the top of the left cylinder with the bottom of
the right one, and both are sent to the mid-level `½`. -/
def cylGlue : glueCarrier (reflCylinder s) (reflCylinder s) → s.M × Set.Icc (0 : ℝ) 1 :=
  Quotient.lift (cylPairMap s) (by
    rintro x y (rfl | ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩)
    · rfl
    · refine Prod.ext rfl (Subtype.ext ?_)
      show ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) / 2 = (((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) + 1) / 2
      rw [coe_Icc_bot, coe_Icc_top]; norm_num
    · refine Prod.ext rfl (Subtype.ext ?_)
      show (((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) + 1) / 2 = ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) / 2
      rw [coe_Icc_bot, coe_Icc_top]; norm_num)

theorem cylGlue_mk (x : (reflCylinder s).W ⊕ (reflCylinder s).W) :
    cylGlue s (glueMk (reflCylinder s) (reflCylinder s) x) = cylPairMap s x := rfl

theorem continuous_cylGlue : Continuous (cylGlue s) :=
  continuous_quot_lift _ (continuous_cylPairMap s)

/-- **The straightening map is injective.** Two points of the doubled cylinder with the same image
either sit in the same copy at the same height, or are the two seam representatives — which the weld
has already identified. -/
theorem cylGlue_injective : Function.Injective (cylGlue s) := by
  refine fun a b => Quotient.inductionOn₂ a b ?_
  rintro (⟨m, t⟩ | ⟨m, t⟩) (⟨m', t'⟩ | ⟨m', t'⟩) hab
  · have h1 : m = m' := congrArg Prod.fst hab
    have h2 : (t : ℝ) / 2 = (t' : ℝ) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    subst h1
    have : t = t' := Subtype.ext (by linarith)
    subst this; rfl
  · have h1 : m = m' := congrArg Prod.fst hab
    have h2 : (t : ℝ) / 2 = ((t' : ℝ) + 1) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    subst h1
    have hb := t.2.2
    have hb' := t'.2.1
    have ht : t = ⊤ := Subtype.ext (by rw [coe_Icc_top]; linarith)
    have ht' : t' = ⊥ := Subtype.ext (by rw [coe_Icc_bot]; linarith)
    subst ht; subst ht'
    exact Quotient.sound (Or.inr (Or.inl ⟨m, rfl, rfl⟩))
  · have h1 : m = m' := congrArg Prod.fst hab
    have h2 : ((t : ℝ) + 1) / 2 = (t' : ℝ) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    subst h1
    have hb := t.2.1
    have hb' := t'.2.2
    have ht : t = ⊥ := Subtype.ext (by rw [coe_Icc_bot]; linarith)
    have ht' : t' = ⊤ := Subtype.ext (by rw [coe_Icc_top]; linarith)
    subst ht; subst ht'
    exact Quotient.sound (Or.inr (Or.inr ⟨m, rfl, rfl⟩))
  · have h1 : m = m' := congrArg Prod.fst hab
    have h2 : ((t : ℝ) + 1) / 2 = ((t' : ℝ) + 1) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    subst h1
    have : t = t' := Subtype.ext (by linarith)
    subst this; rfl

/-- **The straightening map is surjective**: a level `u ≤ ½` comes from the left copy at `2u`, a
level `u ≥ ½` from the right copy at `2u - 1`. -/
theorem cylGlue_surjective : Function.Surjective (cylGlue s) := by
  rintro ⟨m, u⟩
  rcases le_total (u : ℝ) (1 / 2) with hu | hu
  · refine ⟨glueMk (reflCylinder s) (reflCylinder s) (Sum.inl (m, ⟨2 * u.1, ?_, ?_⟩)), ?_⟩
    · have := u.2.1; linarith
    · linarith
    · refine Prod.ext rfl (Subtype.ext ?_)
      show 2 * (u : ℝ) / 2 = (u : ℝ)
      ring
  · refine ⟨glueMk (reflCylinder s) (reflCylinder s) (Sum.inr (m, ⟨2 * u.1 - 1, ?_, ?_⟩)), ?_⟩
    · linarith
    · have := u.2.2; linarith
    · refine Prod.ext rfl (Subtype.ext ?_)
      show (2 * (u : ℝ) - 1 + 1) / 2 = (u : ℝ)
      ring

/-- The straightening map as an equivalence. -/
def cylGlueEquiv : glueCarrier (reflCylinder s) (reflCylinder s) ≃ (s.M × Set.Icc (0 : ℝ) 1) :=
  Equiv.ofBijective (cylGlue s) ⟨cylGlue_injective s, cylGlue_surjective s⟩

/-- **THE STRAIGHTENING HOMEOMORPHISM.** The seam pushout of two cylinders over `Σ` *is* a cylinder
over `Σ`: a continuous bijection from the (compact) weld to the (Hausdorff) cylinder. This is the
concrete, family-specific substitute for the collar neighbourhood theorem — the weld is straightened
by an explicit reparametrisation, not by an abstract collar. -/
def cylGlueHomeo [T2Space s.M] :
    glueCarrier (reflCylinder s) (reflCylinder s) ≃ₜ (s.M × Set.Icc (0 : ℝ) 1) :=
  haveI := compactSpace_glueCarrier (reflCylinder s) (reflCylinder s)
  Continuous.homeoOfEquivCompactToT2 (f := cylGlueEquiv s) (continuous_cylGlue s)

@[simp] theorem cylGlueHomeo_apply [T2Space s.M]
    (x : glueCarrier (reflCylinder s) (reflCylinder s)) : cylGlueHomeo s x = cylGlue s x := rfl

/-! ## §3. `SeamGlueChart` inhabited for the cylinder pair -/

/-- **The straightening carries the welded ends onto the cylinder's own ends.** The `⊥`-end of the
left copy lands at level `0` and the `⊤`-end of the right copy at level `1`; this is what makes the
transported charts see `glueEnds` as the honest boundary map of a cylinder. -/
theorem cylGlue_comp_glueEnds [T2Space s.M] :
    (cylGlueHomeo s) ∘ (glueEnds (reflCylinder s) (reflCylinder s)) = (reflCylinder s).e := by
  funext a
  cases a with
  | inl m =>
    refine Prod.ext rfl (Subtype.ext ?_)
    show ((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) / 2 = ((⊥ : Set.Icc (0 : ℝ) 1) : ℝ)
    rw [coe_Icc_bot]; norm_num
  | inr m =>
    refine Prod.ext rfl (Subtype.ext ?_)
    show (((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) + 1) / 2 = ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ)
    rw [coe_Icc_top]; norm_num

/-- **THE INHABITANT — `SeamGlueChart` for a composite of two cylinders.**

All four residual fields of `T2BordismGluing.SeamGlueChart` are supplied, with no collar theorem, no
axiom, and no weakening of the structure:

* `chart` / `mfd` — transported through the straightening homeomorphism from the honest product
  manifold `Σ × [0,1]` (`homeoChartedSpace` / `isManifold_homeoChartedSpace`);
* `smooth` — the welded ends are the cylinder's own ends under the straightening
  (`cylGlue_comp_glueEnds`), so `reflCylinder`'s `he_smooth` transports;
* `boundary` — likewise from `reflCylinder`'s `he_boundary`, which is Mathlib's computed
  `∂(Σ × [0,1]) = Σ × {⊥,⊤}`; the seam level `½` is *not* in it (`seam_notMem_boundary`). -/
def cylSeamGlueChart [T2Space s.M] : SeamGlueChart (reflCylinder s) (reflCylinder s) where
  chart := homeoChartedSpace (cylGlueHomeo s)
  mfd := isManifold_homeoChartedSpace (cylGlueHomeo s)
  smooth := by
    rw [contMDiff_homeoChartedSpace_iff, cylGlue_comp_glueEnds]
    exact (reflCylinder s).he_smooth
  boundary := by
    have hb : Set.range ((reflCylinder s).e)
        = (I.prod (𝓡∂ 1)).boundary (s.M × Set.Icc (0 : ℝ) 1) := (reflCylinder s).he_boundary
    rw [boundary_homeoChartedSpace, ← hb, ← cylGlue_comp_glueEnds]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, congrArg (cylGlueHomeo s) ha⟩,
      fun ⟨a, ha⟩ => ⟨a, (cylGlueHomeo s).injective ha⟩⟩

/-- **The composite bordism** `s ⇝ s` carried by the seam pushout of the two cylinders. Its total
space is the weld `glueCarrier`, not a re-labelled cylinder: the eight generic fields come from
`T2BordismGluing` §3 and the four chart fields from `cylSeamGlueChart`. -/
def cylComposite [T2Space s.M] : Bordism (I.prod (𝓡∂ 1)) s s :=
  haveI : T2Space (reflCylinder s).W := inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
  Bordism.ofSeamGlueChart (reflCylinder s) (reflCylinder s) (cylSeamGlueChart s)

@[simp] theorem cylComposite_W [T2Space s.M] :
    (cylComposite s).W = glueCarrier (reflCylinder s) (reflCylinder s) := rfl

/-- **THE SEAM IS HEALED — at manifold level, not merely set level.** The mid-level point
`glueMk (Sum.inl (m, ⊤))` is a *boundary* point of the left cylinder and of the right cylinder, yet
is an INTERIOR point of the glued manifold. This is the non-vacuity certificate for
`cylSeamGlueChart`: an instance that trivialised `boundary` could not distinguish the seam from the
ends. -/
theorem seam_notMem_boundary [T2Space s.M] (m : s.M) :
    glueMk (reflCylinder s) (reflCylinder s) (Sum.inl ((reflCylinder s).e (Sum.inr m)))
      ∉ @ModelWithCorners.boundary ℝ _ (E × EuclideanSpace ℝ (Fin 1)) _ _
          (ModelProd H (EuclideanHalfSpace 1)) _ (I.prod (𝓡∂ 1))
          (glueCarrier (reflCylinder s) (reflCylinder s)) _ (cylSeamGlueChart s).chart := by
  rw [← (cylSeamGlueChart s).boundary]
  exact seam_notMem_range_glueEnds (reflCylinder s) (reflCylinder s) m

end Cylinder

/-! ## §4. The degenerate-seam family: composing through an EMPTY middle

The other end of the range: when `q.M` is empty the weld identifies nothing and the pushout is the
honest disjoint union, which Mathlib already knows is a manifold-with-boundary
(`IsManifold.disjointUnion`, `ModelWithCorners.boundary_disjointUnion`). This is the base case — it
does **not** exercise the collar — but it is exactly the middle object of the `hker` extraction
(`nullBordism_of_class_eq_zero` composes through `emptySM`), so it is worth having as a discharged
instance rather than an assumption. -/

noncomputable section EmptySeam

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {p q r : SingularManifold X k I}
  (b₁ : Bordism (I.prod (𝓡∂ 1)) p q) (b₂ : Bordism (I.prod (𝓡∂ 1)) q r)

/-- With no `q`-points there are no seam joins, so the weld relation is plain equality. -/
theorem seamRel_eq_of_isEmpty [IsEmpty q.M] {x y : b₁.W ⊕ b₂.W} (h : seamRel b₁ b₂ x y) : x = y := by
  rcases h with h | ⟨m, -, -⟩ | ⟨m, -, -⟩
  · exact h
  · exact (IsEmpty.false m).elim
  · exact (IsEmpty.false m).elim

/-- The inverse of the weld map when the seam is empty. -/
def emptySeamSplit [IsEmpty q.M] : glueCarrier b₁ b₂ → b₁.W ⊕ b₂.W :=
  Quotient.lift id fun _ _ h => seamRel_eq_of_isEmpty b₁ b₂ h

/-- **The empty seam pushout is the disjoint union**, as a homeomorphism (no compactness or
Hausdorff hypothesis needed — the weld map is a continuous bijection with a continuous inverse). -/
def emptySeamHomeo [IsEmpty q.M] : glueCarrier b₁ b₂ ≃ₜ (b₁.W ⊕ b₂.W) where
  toFun := emptySeamSplit b₁ b₂
  invFun := glueMk b₁ b₂
  left_inv x := Quotient.inductionOn x fun _ => rfl
  right_inv _ := rfl
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_glueMk b₁ b₂

theorem emptySeamHomeo_comp_glueEnds [IsEmpty q.M] :
    (emptySeamHomeo b₁ b₂) ∘ (glueEnds b₁ b₂) = endRep b₁ b₂ := rfl

/-- The un-welded end map is smooth for the disjoint-union structure: each half is a piece's own
boundary map composed with a summand inclusion. -/
theorem contMDiff_endRep : ContMDiff I (I.prod (𝓡∂ 1)) k (endRep b₁ b₂) :=
  ContMDiff.sumElim (ContMDiff.inl.comp (b₁.he_smooth.comp ContMDiff.inl))
    (ContMDiff.inr.comp (b₂.he_smooth.comp ContMDiff.inr))

/-- With an empty middle, the two outer ends already exhaust both pieces' boundaries, so the
disjoint union's boundary is exactly the range of the un-welded end map. -/
theorem range_endRep_eq [IsEmpty q.M] :
    Set.range (endRep b₁ b₂) = (I.prod (𝓡∂ 1)).boundary (b₁.W ⊕ b₂.W) := by
  rw [ModelWithCorners.boundary_disjointUnion, ← b₁.he_boundary, ← b₂.he_boundary]
  ext z
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact Or.inl ⟨b₁.e (Sum.inl a), ⟨Sum.inl a, rfl⟩, rfl⟩
    · exact Or.inr ⟨b₂.e (Sum.inr a), ⟨Sum.inr a, rfl⟩, rfl⟩
  · rintro (⟨-, ⟨a | a, rfl⟩, rfl⟩ | ⟨-, ⟨a | a, rfl⟩, rfl⟩)
    · exact ⟨Sum.inl a, rfl⟩
    · exact (IsEmpty.false a).elim
    · exact (IsEmpty.false a).elim
    · exact ⟨Sum.inr a, rfl⟩

/-- **THE SECOND INHABITANT — `SeamGlueChart` for an empty seam.** The charts come from Mathlib's
disjoint-union manifold structure through `emptySeamHomeo`; the boundary field is Mathlib's
`boundary_disjointUnion` combined with each piece's own `he_boundary`. -/
def emptySeamGlueChart [IsEmpty q.M] : SeamGlueChart b₁ b₂ where
  chart := homeoChartedSpace (emptySeamHomeo b₁ b₂)
  mfd := isManifold_homeoChartedSpace (emptySeamHomeo b₁ b₂)
  smooth := by
    rw [contMDiff_homeoChartedSpace_iff, emptySeamHomeo_comp_glueEnds]
    exact contMDiff_endRep b₁ b₂
  boundary := by
    rw [boundary_homeoChartedSpace, ← range_endRep_eq b₁ b₂, ← emptySeamHomeo_comp_glueEnds]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, congrArg (emptySeamHomeo b₁ b₂) ha⟩,
      fun ⟨a, ha⟩ => ⟨a, (emptySeamHomeo b₁ b₂).injective ha⟩⟩

/-- **Composition through a null-bordism, at arc A.** Composable bordisms whose middle is empty
compose: `p` bounds and `r` bounds ⟹ `p` and `r` are bordant, with the composite carried by the
(now discharged) seam pushout. -/
theorem isBordant_of_emptySeam [IsEmpty q.M] [T2Space b₁.W] [T2Space b₂.W] :
    IsBordant (I.prod (𝓡∂ 1)) p r :=
  ⟨Bordism.ofSeamGlueChart b₁ b₂ (emptySeamGlueChart b₁ b₂)⟩

end EmptySeam

end SKEFTHawking.T2BordismGlueFamilies
