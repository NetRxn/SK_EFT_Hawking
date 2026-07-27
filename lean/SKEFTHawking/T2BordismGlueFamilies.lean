/-
# Phase 5q.H — `SeamGlueChart` INHABITED for concrete families (arc A, discharged)

`T2BordismGluing` reduced manifold-level bordism gluing to exactly four residual fields, bundled as
`SeamGlueChart b₁ b₂` (`chartW`, `mfdW`, `he_smooth`, `he_boundary`); the other eight `Bordism`
fields are discharged generically there, and `Bordism.ofSeamGlueChart` assembles the composite. That
module could only *name* the residue — the collar-neighbourhood content — and left it open.

This module supplies the first honest **inhabitants** of `SeamGlueChart`: no collar theorem, no new
axiom, and no weakening of the structure (all four fields are supplied as stated).

## §1 — the reusable engine: transport the whole manifold stack along a homeomorphism

For any homeomorphism `e : X ≃ₜ Y` onto a charted space:

| transported | how |
|---|---|
| `ChartedSpace H' X` | `homeoChartedSpace` (`chartedSpaceOfHomeo` ≫ `ChartedSpace.comp`) |
| `IsManifold J k X` | `isManifold_homeoChartedSpace` (via the banked `SurgeryFoundation.hasGroupoid_comp_of_homeo`) |
| `ContMDiff … f` | `contMDiff_homeoChartedSpace_iff` — smooth into `X` ⟺ smooth into `Y` after `e` |
| `J.boundary X` | `boundary_homeoChartedSpace` — `e ⁻¹' (J.boundary Y)` |

The last two are the new pieces: they are exactly what turns a topological identification of the
seam pushout into the two *geometric* `SeamGlueChart` fields. This is the **template**: exhibit the
pushout as homeomorphic to a manifold-with-boundary whose boundary matches `range glueEnds`, and the
whole chart stack follows.

## §2–§3 — family 1: a composable pair of MAPPING CYLINDERS

`mapCylGlueHomeo` straightens the seam pushout of `mapCylinder φ` and `mapCylinder ψ` onto a single
cylinder over `Σ`, by the explicit reparametrisation `τ ↦ τ/2` on the left copy and
`τ ↦ (τ+1)/2` (with base transported by `φ⁻¹`) on the right. That reparametrisation is the
family-specific substitute for a collar — concrete, not abstract.

* `mapCylSeamGlueChart` — the inhabitant. Endpoints `s`, `t`, `u` and the two bordisms may all
  differ; this is **not** the `p = q = r` degenerate case.
* `mapCylGlue_comp_glueEnds` — the composite is not merely *some* bordism `s ⇝ u`: under the
  straightening its end map is exactly `mapCylinder (φ.trans ψ)`'s. Mapping-cylinder bordisms
  compose, and compose to the mapping cylinder of the composed diffeomorphism.
* `mapCyl_seam_notMem_boundary` — **the non-vacuity certificate.** The welded seam level is a
  *boundary* point of each piece yet an *interior* point of the glued manifold. An instance that
  trivialised `boundary` could not separate the seam from the ends.
* `reflCylinder_eq_mapCylinder` — `reflCylinder` is *definitionally* the `φ = id` case, so
  `cylSeamGlueChart` (the pure reflexivity cylinder, the one `IsT2DataBordant.refl` produces) is a
  corollary with no extra work.
* `isT2DataBordant_of_mapCyl` — the wiring into `T2BordismGluing.isT2DataBordant_of_seamGlue`: on
  this family arc A is *fully* discharged and the only remaining input is arc B (`ξ.Bor` on the
  composite), which is taken as a hypothesis, never assumed away.

## §4 — family 2: an EMPTY seam

The other end of the range. `emptySeamHomeo` identifies the pushout with the honest disjoint union
(no compactness or Hausdorff hypothesis needed), which Mathlib already knows is a
manifold-with-boundary; `emptySeamGlueChart` is the inhabitant and `isBordant_of_emptySeam` composes
bordisms through a null-bordism — the middle object of `nullBordism_of_class_eq_zero`. Honest
caveat: an empty seam does **not** exercise the collar; this is the base case, not evidence about
the general one.

## Scope note (the residue these families do NOT close)

`SeamGlueChart` asks exactly what `Bordism` asks of the glued object, and no more — in particular it
does **not** require the glued smooth structure to *restrict* to the pieces' own structures (i.e.
that `w ↦ glueMk (Sum.inl w)` be `ContMDiff`). That is not an arc-A defect: the bordism relation
only needs *some* compact manifold-with-boundary with the right boundary. It becomes load-bearing at
**arc B**, where a glued `ξ.Bor` must be built from the pieces' structures — that construction will
need the piece inclusions to be smooth, which for the cylinder family reduces to
`ContMDiff (𝓡∂ 1) (𝓡∂ 1) k (τ ↦ τ/2)` on `[0,1]`. Mathlib has no `ContMDiff`-on-`Icc` API, so that
is a separate brick, flagged here rather than papered over.

Everything is stated `k`-generically — no `k = 0` specialisation anywhere
(`k0-to-k1-transport-refuted` fence).

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

omit [I.Boundaryless] in
/-- The composite diffeomorphism is compatible with the maps to `X`, so `φ ∘ ψ` again spans a
mapping-cylinder bordism — the object the composite will turn out to be. -/
theorem comp_compat {s t u : SingularManifold X k I} {φ : Diffeomorph I I s.M t.M k}
    {ψ : Diffeomorph I I t.M u.M k} (hφ : t.f ∘ φ = s.f) (hψ : u.f ∘ ψ = t.f) :
    u.f ∘ (φ.trans ψ) = s.f := by
  funext m
  exact (congrFun hψ (φ m)).trans (congrFun hφ m)

variable {s t u : SingularManifold X k I}
  (φ : Diffeomorph I I s.M t.M k) (hφ : t.f ∘ φ = s.f)
  (ψ : Diffeomorph I I t.M u.M k) (hψ : u.f ∘ ψ = t.f)

/-- The straightening map on the **un-welded** sum of the two mapping cylinders: rescale the left
copy onto `[0,½]`, and the right copy onto `[½,1]` after transporting its base back along `φ`. -/
def mapCylPairMap :
    (s.M × Set.Icc (0 : ℝ) 1) ⊕ (t.M × Set.Icc (0 : ℝ) 1) → s.M × Set.Icc (0 : ℝ) 1 :=
  Sum.elim (fun x => (x.1, half₁ x.2)) (fun x => (φ.symm x.1, half₂ x.2))

omit [I.Boundaryless] in
theorem continuous_mapCylPairMap : Continuous (mapCylPairMap φ) :=
  Continuous.sumElim (continuous_fst.prodMk (continuous_half₁.comp continuous_snd))
    ((φ.symm.continuous.comp continuous_fst).prodMk (continuous_half₂.comp continuous_snd))

/-- **The straightening map on the seam pushout** of two mapping cylinders. It is well defined
precisely because the weld identifies the `φ`-reparametrised top of the left cylinder with the bottom
of the right one, and both are sent to the mid-level `½`. -/
def mapCylGlue :
    glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ) → s.M × Set.Icc (0 : ℝ) 1 :=
  Quotient.lift (mapCylPairMap φ) (by
    rintro x y (rfl | ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩)
    · rfl
    · refine Prod.ext rfl (Subtype.ext ?_)
      show ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) / 2 = (((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) + 1) / 2
      rw [coe_Icc_bot, coe_Icc_top]; norm_num
    · refine Prod.ext rfl (Subtype.ext ?_)
      show (((⊥ : Set.Icc (0 : ℝ) 1) : ℝ) + 1) / 2 = ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ) / 2
      rw [coe_Icc_bot, coe_Icc_top]; norm_num)

theorem mapCylGlue_mk (x : (mapCylinder φ hφ).W ⊕ (mapCylinder ψ hψ).W) :
    mapCylGlue φ hφ ψ hψ (glueMk (mapCylinder φ hφ) (mapCylinder ψ hψ) x) = mapCylPairMap φ x := rfl

theorem continuous_mapCylGlue : Continuous (mapCylGlue φ hφ ψ hψ) :=
  continuous_quot_lift _ (continuous_mapCylPairMap φ)

/-- **The straightening map is injective.** Two points of the doubled cylinder with the same image
either sit in the same copy at the same height, or are the two seam representatives — which the weld
has already identified. (`φ.symm` injective is what makes the right-copy case work.) -/
theorem mapCylGlue_injective : Function.Injective (mapCylGlue φ hφ ψ hψ) := by
  refine fun a b => Quotient.inductionOn₂ a b ?_
  rintro (⟨m, τ⟩ | ⟨m, τ⟩) (⟨m', τ'⟩ | ⟨m', τ'⟩) hab
  · have h1 : m = m' := congrArg Prod.fst hab
    have h2 : (τ : ℝ) / 2 = (τ' : ℝ) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    subst h1
    have : τ = τ' := Subtype.ext (by linarith)
    subst this; rfl
  · have h1 : m = φ.symm m' := congrArg Prod.fst hab
    have h2 : (τ : ℝ) / 2 = ((τ' : ℝ) + 1) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    have hb := τ.2.2
    have hb' := τ'.2.1
    have hτ : τ = ⊤ := Subtype.ext (by rw [coe_Icc_top]; linarith)
    have hτ' : τ' = ⊥ := Subtype.ext (by rw [coe_Icc_bot]; linarith)
    subst h1; subst hτ; subst hτ'
    exact Quotient.sound (Or.inr (Or.inl ⟨m', rfl, rfl⟩))
  · have h1 : φ.symm m = m' := congrArg Prod.fst hab
    have h2 : ((τ : ℝ) + 1) / 2 = (τ' : ℝ) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    have hb := τ.2.1
    have hb' := τ'.2.2
    have hτ : τ = ⊥ := Subtype.ext (by rw [coe_Icc_bot]; linarith)
    have hτ' : τ' = ⊤ := Subtype.ext (by rw [coe_Icc_top]; linarith)
    subst h1; subst hτ; subst hτ'
    exact Quotient.sound (Or.inr (Or.inr ⟨m, rfl, rfl⟩))
  · have h1 : φ.symm m = φ.symm m' := congrArg Prod.fst hab
    have h2 : ((τ : ℝ) + 1) / 2 = ((τ' : ℝ) + 1) / 2 := congrArg (fun z => (z.2 : ℝ)) hab
    have : m = m' := φ.symm.injective h1
    subst this
    have : τ = τ' := Subtype.ext (by linarith)
    subst this; rfl

/-- **The straightening map is surjective**: a level `u ≤ ½` comes from the left copy at `2u`, a
level `u ≥ ½` from the right copy at `2u - 1` over the `φ`-image of the base point. -/
theorem mapCylGlue_surjective : Function.Surjective (mapCylGlue φ hφ ψ hψ) := by
  rintro ⟨m, v⟩
  rcases le_total (v : ℝ) (1 / 2) with hv | hv
  · refine ⟨glueMk (mapCylinder φ hφ) (mapCylinder ψ hψ) (Sum.inl (m, ⟨2 * v.1, ?_, ?_⟩)), ?_⟩
    · have := v.2.1; linarith
    · linarith
    · refine Prod.ext rfl (Subtype.ext ?_)
      show 2 * (v : ℝ) / 2 = (v : ℝ)
      ring
  · refine ⟨glueMk (mapCylinder φ hφ) (mapCylinder ψ hψ) (Sum.inr (φ m, ⟨2 * v.1 - 1, ?_, ?_⟩)), ?_⟩
    · linarith
    · have := v.2.2; linarith
    · refine Prod.ext (φ.symm_apply_apply m) (Subtype.ext ?_)
      show (2 * (v : ℝ) - 1 + 1) / 2 = (v : ℝ)
      ring

/-- The straightening map as an equivalence. -/
def mapCylGlueEquiv :
    glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ) ≃ (s.M × Set.Icc (0 : ℝ) 1) :=
  Equiv.ofBijective (mapCylGlue φ hφ ψ hψ)
    ⟨mapCylGlue_injective φ hφ ψ hψ, mapCylGlue_surjective φ hφ ψ hψ⟩

/-- **THE STRAIGHTENING HOMEOMORPHISM.** The seam pushout of two mapping cylinders over `Σ ⇝ Σ' ⇝ Σ''`
*is* a cylinder over `Σ`: a continuous bijection from the (compact) weld to the (Hausdorff) cylinder.
This is the concrete, family-specific substitute for the collar neighbourhood theorem — the weld is
straightened by an explicit reparametrisation, not by an abstract collar. -/
def mapCylGlueHomeo [T2Space s.M] :
    glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ) ≃ₜ (s.M × Set.Icc (0 : ℝ) 1) :=
  haveI := compactSpace_glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ)
  Continuous.homeoOfEquivCompactToT2 (f := mapCylGlueEquiv φ hφ ψ hψ)
    (continuous_mapCylGlue φ hφ ψ hψ)

@[simp] theorem mapCylGlueHomeo_apply [T2Space s.M]
    (x : glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ)) :
    mapCylGlueHomeo φ hφ ψ hψ x = mapCylGlue φ hφ ψ hψ x := rfl

/-! ### §3. `SeamGlueChart` inhabited for a composable pair of mapping cylinders -/

/-- **The straightening carries the welded ends onto the ends of the COMPOSITE mapping cylinder.**
The `⊥`-end of the left copy lands at level `0` over the same base point, and the `⊤`-end of the
right copy lands at level `1` over `(φ ∘ ψ)⁻¹` of it — i.e. exactly `mapCylinder (φ.trans ψ)`'s own
boundary map. So the composite is not merely *some* bordism `s ⇝ u`: it is the mapping cylinder of
the composed diffeomorphism. -/
theorem mapCylGlue_comp_glueEnds [T2Space s.M] :
    (mapCylGlueHomeo φ hφ ψ hψ) ∘ (glueEnds (mapCylinder φ hφ) (mapCylinder ψ hψ))
      = (mapCylinder (φ.trans ψ) (comp_compat hφ hψ)).e := by
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

/-- **THE INHABITANT — `SeamGlueChart` for a composable pair of mapping cylinders.**

All four residual fields of `T2BordismGluing.SeamGlueChart` are supplied, with no collar theorem, no
axiom, and no weakening of the structure:

* `chart` / `mfd` — transported through the straightening homeomorphism from the honest product
  manifold `Σ × [0,1]` (`homeoChartedSpace` / `isManifold_homeoChartedSpace`);
* `smooth` — the welded ends are the *composite* mapping cylinder's own ends under the straightening
  (`mapCylGlue_comp_glueEnds`), so that cylinder's `he_smooth` transports;
* `boundary` — likewise from its `he_boundary`, which is Mathlib's computed
  `∂(Σ × [0,1]) = Σ × {⊥,⊤}`; the seam level `½` is *not* in it
  (`mapCyl_seam_notMem_boundary`).

The endpoints `s`, `t`, `u` and the two bordisms are all allowed to differ — this is not the
`p = q = r` degenerate case. -/
def mapCylSeamGlueChart [T2Space s.M] : SeamGlueChart (mapCylinder φ hφ) (mapCylinder ψ hψ) where
  chart := homeoChartedSpace (mapCylGlueHomeo φ hφ ψ hψ)
  mfd := isManifold_homeoChartedSpace (mapCylGlueHomeo φ hφ ψ hψ)
  smooth := by
    rw [contMDiff_homeoChartedSpace_iff, mapCylGlue_comp_glueEnds]
    exact (mapCylinder (φ.trans ψ) (comp_compat hφ hψ)).he_smooth
  boundary := by
    have hb : Set.range ((mapCylinder (φ.trans ψ) (comp_compat hφ hψ)).e)
        = (I.prod (𝓡∂ 1)).boundary (s.M × Set.Icc (0 : ℝ) 1) :=
      (mapCylinder (φ.trans ψ) (comp_compat hφ hψ)).he_boundary
    rw [boundary_homeoChartedSpace, ← hb, ← mapCylGlue_comp_glueEnds φ hφ ψ hψ]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, congrArg (mapCylGlueHomeo φ hφ ψ hψ) ha⟩,
      fun ⟨a, ha⟩ => ⟨a, (mapCylGlueHomeo φ hφ ψ hψ).injective ha⟩⟩

/-- **The composite bordism** `s ⇝ u`, carried by the seam pushout of the two mapping cylinders. Its
total space is the weld `glueCarrier`, not a re-labelled cylinder: the eight generic fields come from
`T2BordismGluing` §3 and the four chart fields from `mapCylSeamGlueChart`. -/
def mapCylComposite [T2Space s.M] [T2Space t.M] : Bordism (I.prod (𝓡∂ 1)) s u :=
  haveI : T2Space (mapCylinder φ hφ).W :=
    inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
  haveI : T2Space (mapCylinder ψ hψ).W :=
    inferInstanceAs (T2Space (t.M × Set.Icc (0 : ℝ) 1))
  Bordism.ofSeamGlueChart (mapCylinder φ hφ) (mapCylinder ψ hψ) (mapCylSeamGlueChart φ hφ ψ hψ)

@[simp] theorem mapCylComposite_W [T2Space s.M] [T2Space t.M] :
    (mapCylComposite φ hφ ψ hψ).W = glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ) := rfl

/-- **THE SEAM IS HEALED — at manifold level, not merely set level.** The mid-level point
`glueMk (Sum.inl (φ.symm m, ⊤))` is a *boundary* point of the left cylinder and of the right
cylinder, yet is an INTERIOR point of the glued manifold. This is the non-vacuity certificate for
`mapCylSeamGlueChart`: an instance that trivialised `boundary` could not distinguish the seam from
the ends. -/
theorem mapCyl_seam_notMem_boundary [T2Space s.M] (m : t.M) :
    glueMk (mapCylinder φ hφ) (mapCylinder ψ hψ) (Sum.inl ((mapCylinder φ hφ).e (Sum.inr m)))
      ∉ @ModelWithCorners.boundary ℝ _ (E × EuclideanSpace ℝ (Fin 1)) _ _
          (ModelProd H (EuclideanHalfSpace 1)) _ (I.prod (𝓡∂ 1))
          (glueCarrier (mapCylinder φ hφ) (mapCylinder ψ hψ)) _
          (mapCylSeamGlueChart φ hφ ψ hψ).chart := by
  rw [← (mapCylSeamGlueChart φ hφ ψ hψ).boundary]
  exact seam_notMem_range_glueEnds (mapCylinder φ hφ) (mapCylinder ψ hψ) m

/-! ### §3b. The pure-cylinder specialisation

`reflCylinder s` is *definitionally* `mapCylinder (Diffeomorph.refl …)`, so the reflexivity cylinder
— the one `IsT2DataBordant.refl` actually produces — is covered with no extra work. -/

theorem reflCylinder_eq_mapCylinder (s : SingularManifold X k I) :
    reflCylinder s = mapCylinder (Diffeomorph.refl I s.M k) (by funext m; rfl) := rfl

/-- **`SeamGlueChart` for the reflexivity cylinder composed with itself** — the `p = q = r` case,
obtained from the general mapping-cylinder inhabitant. -/
def cylSeamGlueChart (s : SingularManifold X k I) [T2Space s.M] :
    SeamGlueChart (reflCylinder s) (reflCylinder s) :=
  mapCylSeamGlueChart (Diffeomorph.refl I s.M k) (by funext m; rfl)
    (Diffeomorph.refl I s.M k) (by funext m; rfl)

/-- The composite of the reflexivity cylinder with itself, as a bordism `s ⇝ s`. -/
def cylComposite (s : SingularManifold X k I) [T2Space s.M] : Bordism (I.prod (𝓡∂ 1)) s s :=
  haveI : T2Space (reflCylinder s).W := inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
  Bordism.ofSeamGlueChart (reflCylinder s) (reflCylinder s) (cylSeamGlueChart s)

/-! ### §3c. Wiring: what is left after arc A on this family

`isT2DataBordant_of_seamGlue` is the `T2BordismGluing` consumer of a `SeamGlueChart`. Feeding it the
mapping-cylinder inhabitant shows the exact residue: on this family the manifold arc (arc A) is
*fully* discharged, and the **only** remaining input is the tethered structure across the seam
(arc B, `ξ.Bor` on the composite) — which is supplied as a hypothesis here, never assumed away. -/
theorem isT2DataBordant_of_mapCyl [T2Space s.M] [T2Space t.M]
    (ξ : SKEFTHawking.T2TangentialBordism.T2TangentialData X k I)
    {σ : ξ.Mfd s} {τ : ξ.Mfd u}
    (str : ξ.Bor (mapCylComposite φ hφ ψ hψ) σ τ) :
    SKEFTHawking.T2TangentialBordism.IsT2DataBordant ξ ⟨s, σ⟩ ⟨u, τ⟩ :=
  haveI : T2Space (mapCylinder φ hφ).W := inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
  haveI : T2Space (mapCylinder ψ hψ).W := inferInstanceAs (T2Space (t.M × Set.Icc (0 : ℝ) 1))
  isT2DataBordant_of_seamGlue (mapCylinder φ hφ) (mapCylinder ψ hψ) ξ
    (mapCylSeamGlueChart φ hφ ψ hψ) str

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
