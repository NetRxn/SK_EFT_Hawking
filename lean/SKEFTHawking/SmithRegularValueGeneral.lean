/-
# Regular value theorem — GENERAL NONLINEAR case (global smooth-manifold structure)

This module upgrades the *local* chart of `SmithRegularValue.lean` (`levelSetChart`, valid for a general
strictly-differentiable real submersion) to a genuine **global** `ChartedSpace` / `IsManifold` structure
on the level set `↥(zeroLocus f)` of a `C^∞` real submersion `f : E → ℝ`, in the fully nonlinear case
where the model kernel `ker (fderiv f p)` varies with the base point `p`.

The fixed model is the Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))`; each per-point chart
of `SmithRegularValue.levelSetChart` is composed with a continuous-linear identification
`ker (fderiv f p) ≃L EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` (every codim-1 subspace of a finite-dim
space is linearly isomorphic to the Euclidean space of that dimension).

## Headline results

* `levelSetChartedSpace` — the level set is a `ChartedSpace` over the fixed Euclidean model.
* `levelSetHasGroupoid` — chart transitions lie in `contDiffGroupoid ⊤` (the `C^∞` structure groupoid).
* `levelSetIsManifold` — the level set is a `C^∞` manifold modelled on `EuclideanSpace ℝ (Fin (n-1))`.
* `isEmbedding_subtypeVal` / `contMDiff_subtypeVal` — the inclusion `↥(zeroLocus f) ↪ E` is a smooth
  embedding (topological embedding and `C^∞`).

## The smoothness bridge (the key gap, resolved)

The `C^∞`-ness of the IFT chart inverse (`HasStrictFDerivAt.implicitFunction`) is *not* directly in
Mathlib for the strict-fderiv form. It is obtained here *pointwise* on the open regular locus by
`OpenPartialHomeomorph.contDiffAt_symm` (`iftChart_symm_contDiffAt`): the IFT chart's forward map is the
manifestly-`C^∞` `(f, P (· - a))`, and at every point of the open set where its derivative
`(fderiv f x).prod P` is a continuous linear equivalence (an open condition — `isOpen_isInvertible` ∘
`continuous_fderiv_prod_chartProj`, automatic at a regular point via `prod_chartProj_isInvertible`),
the inverse is `C^∞At`. Deliverables: `contDiffOn_iftChart_symm` (chart inverse `C^∞` on regular set),
`contDiffOn_transition` (transition between two charts `C^∞`).

Kernel-pure; no axioms beyond Mathlib's core {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import SKEFTHawking.SmithRegularValue

namespace SKEFTHawking.SmithRegularValueGeneral

open scoped Topology Classical Manifold
open SKEFTHawking.SmithRegularValue

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Foundational smoothness bricks

We work with a `C^∞` function `f : E → ℝ` and a regular point `a` (`HasStrictFDerivAt f f' a`,
`range f' = ⊤`). The IFT homeomorphism `Φ : E ≈ ℝ × ker f'` has forward map `prodFun = (f, P∘(·-a))`
for a chosen projection `P : E →L ker f'`. We need: (i) `Φ`'s forward map is `C^∞`; (ii) `Φ`'s symm is
`C^∞` on the open subset of its target whose preimage has invertible forward-derivative. -/

section Bricks

variable (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)

/-- The chosen continuous-linear projection `E →L ker f'` underlying the IFT chart at a regular point
(the `Classical.choose` of the complemented-kernel witness, which `implicitToOpenPartialHomeomorph`
uses internally). -/
def chartProj (_hf' : (f' : E →L[ℝ] ℝ).range = ⊤) : E →L[ℝ] LinearMap.ker (f' : E →ₗ[ℝ] ℝ) :=
  Classical.choose (f'.ker_closedComplemented_of_finiteDimensional_range)

/-- The IFT chart's forward map is `x ↦ (f x, P (x - a))`. -/
theorem iftChart_eq (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (x : E) :
    (iftChart f f' a hf hf' x) = (f x, chartProj f' hf' (x - a)) := rfl

/-- The IFT chart's forward map, as a function, equals `x ↦ (f x, P (x - a))`. -/
theorem iftChart_coe (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    (⇑(iftChart f f' a hf hf') : E → ℝ × LinearMap.ker (f' : E →ₗ[ℝ] ℝ)) =
      fun x => (f x, chartProj f' hf' (x - a)) := rfl

/-- The forward map of the IFT chart is `C^∞` (the second coordinate is `P (· - a)`, a continuous
affine map; the first is `f`). -/
theorem iftChart_contDiff (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤)
    (hfC : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (⇑(iftChart f f' a hf hf')) := by
  rw [iftChart_coe]
  exact hfC.prodMk ((chartProj f' hf').contDiff.comp (contDiff_id.sub contDiff_const))

/-- The derivative of the IFT chart's forward map at any point `x` (where `f` is differentiable) is
`(fderiv f x).prod P`. -/
theorem iftChart_hasFDerivAt (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤)
    {x : E} (hx : DifferentiableAt ℝ f x) :
    HasFDerivAt (⇑(iftChart f f' a hf hf'))
      ((fderiv ℝ f x).prod (chartProj f' hf')) x := by
  rw [iftChart_coe]
  exact hx.hasFDerivAt.prodMk
    (((chartProj f' hf').hasFDerivAt).comp x ((hasFDerivAt_id x).sub_const a))

/-- **The inverse of the IFT chart is `C^∞` at any chart point `iftChart x` whose forward derivative
`(fderiv f x).prod P` is invertible.** This is the load-bearing smoothness fact: applying
`OpenPartialHomeomorph.contDiffAt_symm`, the only nontrivial hypothesis is that the forward map's
derivative at `x` is a continuous linear equivalence — which holds exactly on the open regular locus
(for a submersion, where `fderiv f x ≠ 0`, the prod with the projection is invertible). -/
theorem iftChart_symm_contDiffAt (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤)
    (hfC : ContDiff ℝ ⊤ f) {y : ℝ × LinearMap.ker (f' : E →ₗ[ℝ] ℝ)}
    (hy : y ∈ (iftChart f f' a hf hf').target)
    (hinv : ((fderiv ℝ f ((iftChart f f' a hf hf').symm y)).prod (chartProj f' hf')).IsInvertible) :
    ContDiffAt ℝ ⊤ (iftChart f f' a hf hf').symm y := by
  obtain ⟨g, hg⟩ := hinv
  refine (iftChart f f' a hf hf').contDiffAt_symm (f₀' := g) hy ?_ ?_
  · have hd : HasFDerivAt (⇑(iftChart f f' a hf hf'))
        ((fderiv ℝ f ((iftChart f f' a hf hf').symm y)).prod (chartProj f' hf'))
        ((iftChart f f' a hf hf').symm y) :=
      iftChart_hasFDerivAt f f' a hf hf' ((hfC.differentiable (by norm_num)).differentiableAt)
    rw [← hg] at hd
    exact hd
  · exact (iftChart_contDiff f f' a hf hf' hfC).contDiffAt

/-- The chosen projection is a genuine projection onto `ker f'`: `P x = x` for `x ∈ ker f'`. -/
theorem chartProj_apply_coe (hf' : (f' : E →L[ℝ] ℝ).range = ⊤)
    (x : LinearMap.ker (f' : E →ₗ[ℝ] ℝ)) : chartProj f' hf' (x : E) = x :=
  Classical.choose_spec (f'.ker_closedComplemented_of_finiteDimensional_range) x

/-- **`f'.prod P` is invertible** — built from the pure-linear-algebra equivalence
`LinearMap.equivProdOfSurjectiveOfIsCompl` (surjective `f'` plus complementary kernel), promoted to a
continuous linear equivalence by finite-dimensional automatic continuity. No `CompleteSpace (F × G)`
hypothesis is needed (unlike the continuous-map `equivProdOfSurjectiveOfIsCompl`). -/
theorem prod_chartProj_isInvertible (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    (((f' : E →L[ℝ] ℝ)).prod (chartProj f' hf')).IsInvertible := by
  have hrange : (chartProj f' hf' : E →ₗ[ℝ] _).range = ⊤ :=
    LinearMap.range_eq_of_proj (fun x => chartProj_apply_coe f' hf' x)
  have hcompl : IsCompl (f' : E →ₗ[ℝ] ℝ).ker (chartProj f' hf' : E →ₗ[ℝ] _).ker :=
    LinearMap.isCompl_of_proj (fun x => chartProj_apply_coe f' hf' x)
  exact ⟨(LinearMap.equivProdOfSurjectiveOfIsCompl (f' : E →ₗ[ℝ] ℝ)
    (chartProj f' hf' : E →ₗ[ℝ] _) hf' hrange hcompl).toContinuousLinearEquiv, rfl⟩

/-- The set of invertible continuous linear maps `E →L[ℝ] ℝ × ker f'` is open (it is the range of the
coercion `(· : E ≃L ℝ × ker f') → (E →L ℝ × ker f')`, a neighbourhood of each of its points). -/
theorem isOpen_isInvertible :
    IsOpen {L : E →L[ℝ] ℝ × kerModel f' | L.IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  rintro L ⟨e, rfl⟩
  refine Filter.mem_of_superset e.nhds ?_
  rintro M ⟨e', rfl⟩
  exact ⟨e', rfl⟩

/-- The map `x ↦ (fderiv f x).prod P` (the derivative of the IFT chart's forward map) is continuous,
since `fderiv f` is continuous (`f` is `C^∞`) and `L ↦ L.prod P` is a continuous-linear operation. -/
theorem continuous_fderiv_prod_chartProj (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (hfC : ContDiff ℝ ⊤ f) :
    Continuous (fun x => (fderiv ℝ f x).prod (chartProj f' hf')) := by
  have hd : Continuous (fderiv ℝ f) := hfC.continuous_fderiv (by norm_num)
  have key : (fun x => (fderiv ℝ f x).prod (chartProj f' hf')) =
      fun x => (ContinuousLinearMap.inl ℝ ℝ (kerModel f')).comp (fderiv ℝ f x) +
        (ContinuousLinearMap.inr ℝ ℝ (kerModel f')).comp (chartProj f' hf') := by
    ext x v <;> simp
  rw [key]
  exact (continuous_const.clm_comp hd).add continuous_const

/-- The **regular target set** of the IFT chart at `a`: chart points `(0, k)` whose preimage under the
chart is a point where the forward map's derivative is invertible. This is the open set on which the
implicit function (chart inverse) is `C^∞`. -/
def regularKerTarget (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    Set (kerModel f') :=
  {k | (0, k) ∈ (iftChart f f' a hf hf').target ∧
    ((fderiv ℝ f ((iftChart f f' a hf hf').symm (0, k))).prod (chartProj f' hf')).IsInvertible}

theorem isOpen_regularKerTarget (hf : HasStrictFDerivAt f f' a)
    (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (hfC : ContDiff ℝ ⊤ f) :
    IsOpen (regularKerTarget f f' a hf hf') := by
  have hcont : Continuous (fun k : kerModel f' => ((0 : ℝ), k)) :=
    continuous_const.prodMk continuous_id
  have h1 : IsOpen ((fun k : kerModel f' => ((0 : ℝ), k)) ⁻¹' (iftChart f f' a hf hf').target) :=
    (iftChart f f' a hf hf').open_target.preimage hcont
  have hsymm_cont : ContinuousOn (fun k : kerModel f' => (iftChart f f' a hf hf').symm (0, k))
      ((fun k : kerModel f' => ((0 : ℝ), k)) ⁻¹' (iftChart f f' a hf hf').target) :=
    (iftChart f f' a hf hf').continuousOn_symm.comp hcont.continuousOn (fun _ hk => hk)
  -- The invertibility condition pulled back through the continuous symm and the continuous
  -- `x ↦ (fderiv f x).prod P`.
  have hopen2 : IsOpen {x : E | ((fderiv ℝ f x).prod (chartProj f' hf')).IsInvertible} :=
    (isOpen_isInvertible f').preimage (continuous_fderiv_prod_chartProj f f' hf' hfC)
  have heq : regularKerTarget f f' a hf hf' =
      ((fun k : kerModel f' => ((0 : ℝ), k)) ⁻¹' (iftChart f f' a hf hf').target) ∩
        (fun k : kerModel f' => (iftChart f f' a hf hf').symm (0, k)) ⁻¹'
          {x : E | ((fderiv ℝ f x).prod (chartProj f' hf')).IsInvertible} := by
    ext k; simp only [regularKerTarget, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [heq]
  exact hsymm_cont.isOpen_inter_preimage h1 hopen2

/-- **DELIVERABLE (i) — the chart inverse (implicit function) is `C^∞` on the regular set.** In ambient
coordinates `k ↦ iftChart.symm (0, k)` (the map `ker f' → E` whose image is the level set near `a`) is
`ContDiffOn ℝ ⊤` on the open regular target. This is the load-bearing smoothness of the inverse chart
that the manifold's transition maps require. -/
theorem contDiffOn_iftChart_symm (hf : HasStrictFDerivAt f f' a)
    (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (hfC : ContDiff ℝ ⊤ f) :
    ContDiffOn ℝ ⊤ (fun k : kerModel f' => (iftChart f f' a hf hf').symm (0, k))
      (regularKerTarget f f' a hf hf') := by
  rw [(isOpen_regularKerTarget f f' a hf hf' hfC).contDiffOn_iff]
  intro k hk
  obtain ⟨hkt, hinv⟩ := hk
  have hcd : ContDiffAt ℝ ⊤ (iftChart f f' a hf hf').symm (0, k) :=
    iftChart_symm_contDiffAt f f' a hf hf' hfC hkt hinv
  exact hcd.comp k (contDiffAt_const.prodMk contDiffAt_id)

/-- **DELIVERABLE (i), forward direction — the chart map is `C^∞` in ambient coordinates.** The
forward chart `levelSetChart` in ambient coordinates is `x ↦ P (x - a)` (the second IFT coordinate),
a continuous-affine map, hence `C^∞` on all of `E`. -/
theorem contDiff_levelSetChart_ambient (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    ContDiff ℝ ⊤ (fun x : E => chartProj f' hf' (x - a)) :=
  (chartProj f' hf').contDiff.comp (contDiff_id.sub contDiff_const)

end Bricks

/-! ## Transition maps between two charts (DELIVERABLE (ii))

The raw chart-transition between the level-set charts at two regular points `p` (data `f'`, `a`) and
`q` (data `g'`, `b`) of the *same* `C^∞` submersion `f` is, in the kernel models,
`k ↦ (iftChart_q (iftChart_p.symm (0, k))).2 = P_q (iftChart_p.symm (0, k) - b)`. It is `C^∞` on the
regular set because the inverse chart at `p` is `C^∞` there (Deliverable (i)) and the forward chart at
`q` is `C^∞` (its second coordinate is the continuous-affine `P_q (· - b)`). -/

section Transition

variable (f : E → ℝ) (f' g' : E →L[ℝ] ℝ) (a b : E)

/-- **DELIVERABLE (ii) — the chart-transition map is `C^∞` on the regular set.** For two regular
points with chart data `(f', a)` and `(g', b)` of the same `C^∞` submersion `f`, the transition
`k ↦ (iftChart_q (iftChart_p.symm (0, k))).2` (in kernel coordinates) is `ContDiffOn ℝ ⊤` on the
regular target set of the first chart. This is the structure-groupoid compatibility the manifold
atlas requires. -/
theorem contDiffOn_transition (hf : HasStrictFDerivAt f f' a)
    (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (hg : HasStrictFDerivAt f g' b)
    (hg' : (g' : E →L[ℝ] ℝ).range = ⊤) (hfC : ContDiff ℝ ⊤ f) :
    ContDiffOn ℝ ⊤
      (fun k : kerModel f' => (iftChart f g' b hg hg' ((iftChart f f' a hf hf').symm (0, k))).2)
      (regularKerTarget f f' a hf hf') := by
  have hsymm : ContDiffOn ℝ ⊤ (fun k : kerModel f' => (iftChart f f' a hf hf').symm (0, k))
      (regularKerTarget f f' a hf hf') :=
    contDiffOn_iftChart_symm f f' a hf hf' hfC
  have hforward : ContDiff ℝ ⊤ (fun x : E => (iftChart f g' b hg hg' x).2) := by
    simp only [iftChart_eq]
    exact (chartProj g' hg').contDiff.comp (contDiff_id.sub contDiff_const)
  exact hforward.comp_contDiffOn hsymm

end Transition

/-! ## The fixed Euclidean model and per-point identification

For the global manifold structure on `↥(zeroLocus f)` with a *fixed* model, each per-point kernel
`ker (fderiv f p)` (which varies with `p`) is identified with the single Euclidean space
`EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` of the right codimension-1 dimension, via
`ContinuousLinearEquiv.ofFinrankEq` (all finite-dim real spaces of equal dimension are continuously
linearly isomorphic). -/

section EuclideanModel

/-- The fixed codimension-1 Euclidean model `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))`. -/
abbrev euclideanModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))

variable (f : E → ℝ) (f' : E →L[ℝ] ℝ)

/-- At a regular point (`range f' = ⊤`, i.e. `f' ≠ 0`), the kernel `ker f'` has dimension
`finrank E - 1`, matching the fixed Euclidean model. -/
theorem finrank_kerModel_eq (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    Module.finrank ℝ (kerModel f') = Module.finrank ℝ (euclideanModel E) := by
  have hcodim : Module.finrank ℝ (kerModel f') + 1 = Module.finrank ℝ E :=
    SKEFTHawking.SmithTransversality.submersion_ker_codim_one f' hf'
  simp only [euclideanModel, finrank_euclideanSpace, Fintype.card_fin]
  omega

/-- The continuous linear identification `ker f' ≃L EuclideanSpace ℝ (Fin (finrank E - 1))` at a
regular point, used to give every per-point chart the same fixed Euclidean model. -/
noncomputable def kerEquivEuclidean (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    kerModel f' ≃L[ℝ] euclideanModel E :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_kerModel_eq f' hf')

end EuclideanModel

/-! ## Global smooth-manifold structure (general nonlinear case)

We now assemble the full `ChartedSpace`/`IsManifold` structure on `↥(zeroLocus f)` for a `C^∞`
submersion `f : E → ℝ` (`ContDiff ℝ ⊤ f`, and `fderiv f x` surjective at every `x ∈ f⁻¹(0)`). Each
point `p` of the level set gets a chart obtained from `levelSetChart` at `p` (with derivative
`fderiv f p`), restricted to the open regular set and composed with the fixed Euclidean
identification `kerEquivEuclidean`. -/

section Manifold

variable (f : E → ℝ) (hfC : ContDiff ℝ ⊤ f)
  (hsub : ∀ x ∈ zeroLocus f, LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] ℝ) = ⊤)

omit [FiniteDimensional ℝ E] in
/-- The derivative `fderiv f p` at a point of the level set, packaged as the strict derivative
(`C^∞ ⟹ HasStrictFDerivAt`). -/
theorem hasStrictFDerivAt_fderiv (hfC : ContDiff ℝ ⊤ f) (x : E) :
    HasStrictFDerivAt f (fderiv ℝ f x) x :=
  ContDiff.hasStrictFDerivAt hfC (by norm_num)

variable (hfC : ContDiff ℝ ⊤ f)
  (hsub : ∀ x ∈ zeroLocus f, LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] ℝ) = ⊤)

/-- The IFT chart at a point `p` of the level set (using the derivative `fderiv f p`). -/
noncomputable def iftChartAt (p : zeroLocus f) :
    OpenPartialHomeomorph E (ℝ × kerModel (fderiv ℝ f p.1)) :=
  iftChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2)

/-- The open regular set inside `E` for the chart at `p`: points of `iftChartAt p`'s source where the
forward-chart derivative `(fderiv f x).prod P_p` is invertible. The chart inverse is `C^∞` on its
image (Deliverable (i)). -/
def regularSetAt (p : zeroLocus f) : Set E :=
  (iftChartAt f hfC hsub p).source ∩
    {x | ((fderiv ℝ f x).prod (chartProj (fderiv ℝ f p.1) (hsub p.1 p.2))).IsInvertible}

theorem isOpen_regularSetAt (p : zeroLocus f) : IsOpen (regularSetAt f hfC hsub p) :=
  (iftChartAt f hfC hsub p).open_source.inter
    ((isOpen_isInvertible (fderiv ℝ f p.1)).preimage
      (continuous_fderiv_prod_chartProj f (fderiv ℝ f p.1)
        (hsub p.1 p.2) hfC))

/-- The basepoint `p.1` lies in its own regular set (its forward-chart derivative is invertible by
`prod_chartProj_isInvertible`, and it is in the chart source). -/
theorem mem_regularSetAt (p : zeroLocus f) : p.1 ∈ regularSetAt f hfC hsub p := by
  refine ⟨mem_iftChart_source f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
    (hsub p.1 p.2), ?_⟩
  show ((fderiv ℝ f p.1).prod (chartProj (fderiv ℝ f p.1) (hsub p.1 p.2))).IsInvertible
  exact prod_chartProj_isInvertible (fderiv ℝ f p.1) (hsub p.1 p.2)

/-- The level-set chart at `p`, valued in the per-point kernel model and restricted to the open
regular set (where its inverse is `C^∞`, Deliverable (i)). -/
noncomputable def levelChartKer (p : zeroLocus f) :
    OpenPartialHomeomorph (zeroLocus f) (kerModel (fderiv ℝ f p.1)) :=
  (levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2) p.2).restrOpen
    (Subtype.val ⁻¹' regularSetAt f hfC hsub p)
    ((isOpen_regularSetAt f hfC hsub p).preimage continuous_subtype_val)

/-- **The per-point chart of the general-nonlinear level-set manifold**, valued in the *fixed*
Euclidean model `EuclideanSpace ℝ (Fin (finrank E - 1))`: the regular-restricted level-set chart at
`p` composed with the continuous-linear identification `ker (fderiv f p) ≃L EuclideanSpace …`. -/
noncomputable def levelChartE (p : zeroLocus f) :
    OpenPartialHomeomorph (zeroLocus f) (euclideanModel E) :=
  (levelChartKer f hfC hsub p).transHomeomorph
    (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).toHomeomorph

@[simp] theorem levelChartE_source (p : zeroLocus f) :
    (levelChartE f hfC hsub p).source = (levelChartKer f hfC hsub p).source := by
  rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_source]

theorem levelChartKer_source (p : zeroLocus f) :
    (levelChartKer f hfC hsub p).source =
      (levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
        (hsub p.1 p.2) p.2).source ∩ (Subtype.val ⁻¹' regularSetAt f hfC hsub p) := by
  rw [levelChartKer, OpenPartialHomeomorph.restrOpen_source]

/-- **Every point of the level set lies in the source of its own chart.** -/
theorem mem_levelChartE_source (p : zeroLocus f) : p ∈ (levelChartE f hfC hsub p).source := by
  rw [levelChartE_source, levelChartKer_source]
  refine ⟨?_, ?_⟩
  · have hbase := mem_levelSetChart_source f (fderiv ℝ f p.1) p.1
      (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2) p.2
    have hpe : (⟨p.1, p.2⟩ : zeroLocus f) = p := Subtype.ext rfl
    rwa [hpe] at hbase
  · exact mem_regularSetAt f hfC hsub p

/-- **The level set of a `C^∞` real submersion is a charted space over the fixed Euclidean model**
`EuclideanSpace ℝ (Fin (finrank E - 1))`. The atlas consists of the per-point Euclidean charts
`levelChartE`; each point lies in the source of its own chart. -/
@[reducible] noncomputable def levelSetChartedSpace :
    ChartedSpace (euclideanModel E) (zeroLocus f) where
  atlas := Set.range (levelChartE f hfC hsub)
  chartAt p := levelChartE f hfC hsub p
  mem_chart_source p := mem_levelChartE_source f hfC hsub p
  chart_mem_atlas p := Set.mem_range_self p

/-- The coercion of the chart inverse at `p`, in ambient coordinates, on the chart target: it is
`v ↦ iftChart_p.symm (0, e_p.symm v)` (the implicit function), where `e_p` is the Euclidean
identification. Holds where the corresponding IFT-chart point lies in the IFT target (i.e. on the
chart's own target). -/
theorem levelChartE_symm_apply (p : zeroLocus f) (v : euclideanModel E)
    (hv : (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) ∈
      (iftChartAt f hfC hsub p).target) :
    ((levelChartE f hfC hsub p).symm v : E) =
      (iftChartAt f hfC hsub p).symm
        (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) := by
  rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, levelChartKer,
    OpenPartialHomeomorph.coe_restrOpen_symm]
  show (((levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
    (hsub p.1 p.2) p.2).symm) ((kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) : E) = _
  rw [levelSetChart]
  rw [show (iftChartAt f hfC hsub p) = iftChart f (fderiv ℝ f p.1) p.1
    (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2) from rfl] at hv
  simp only [OpenPartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  rw [dif_pos hv]
  rfl

/-- The forward chart at `q`, in ambient coordinates, equals the Euclidean identification applied to
the second IFT coordinate: `x ↦ e_q (P_q (x - q))`. -/
theorem levelChartE_apply (q : zeroLocus f) (x : zeroLocus f) :
    levelChartE f hfC hsub q x =
      (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2)) ((iftChartAt f hfC hsub q x.1).2) := by
  rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]
  rfl

/-- The source of the chart at `p`, in ambient terms: it is `Subtype.val ⁻¹'` of the open regular set
(intersected with the IFT chart source). In particular every point of the source is regular. -/
theorem levelChartE_source_eq (p : zeroLocus f) :
    (levelChartE f hfC hsub p).source =
      Subtype.val ⁻¹' ((iftChartAt f hfC hsub p).source ∩
        {x | ((fderiv ℝ f x).prod (chartProj (fderiv ℝ f p.1) (hsub p.1 p.2))).IsInvertible}) := by
  rw [levelChartE_source, levelChartKer_source]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, regularSetAt, levelSetChart_source, iftChartAt]
  tauto

/-- The explicit composite that the chart transition equals on its domain:
`v ↦ e_q (P_q (iftChart_p.symm (0, e_p.symm v) - q))`. This is `e_q ∘ (Deliverable (ii) transition) ∘
e_p.symm`, hence `C^∞` wherever `e_p.symm v` lands in the regular target of the chart at `p`. -/
theorem contDiffOn_transitionE (p q : zeroLocus f) :
    ContDiffOn ℝ ⊤
      (fun v : euclideanModel E => (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2))
        ((iftChartAt f hfC hsub q
          ((iftChartAt f hfC hsub p).symm
            (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v))).2))
      ((kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm ⁻¹'
        (regularKerTarget f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
          (hsub p.1 p.2))) := by
  have hsymm : ContDiff ℝ ⊤ (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm :=
    (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm.contDiff
  have hek : ContDiff ℝ ⊤ (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2)) :=
    (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2)).contDiff
  have htrans := contDiffOn_transition f (fderiv ℝ f p.1) (fderiv ℝ f q.1) p.1 q.1
    (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2)
    (hasStrictFDerivAt_fderiv f hfC q.1) (hsub q.1 q.2) hfC
  -- e_q ∘ (transition) ∘ e_p.symm
  have : (fun v : euclideanModel E => (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2))
      ((iftChartAt f hfC hsub q
        ((iftChartAt f hfC hsub p).symm
          (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v))).2)) =
      (fun k => (kerEquivEuclidean (fderiv ℝ f q.1) (hsub q.1 q.2))
        ((iftChart f (fderiv ℝ f q.1) q.1 (hasStrictFDerivAt_fderiv f hfC q.1) (hsub q.1 q.2)
          ((iftChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
            (hsub p.1 p.2)).symm (0, k))).2)) ∘
        (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm := rfl
  rw [this]
  exact (hek.comp_contDiffOn htrans).comp hsymm.contDiffOn (Set.mapsTo_preimage _ _)

/-- Helper: the transition `e.symm ≫ₕ e'` between two atlas charts, evaluated on its source, equals the
explicit smooth composite `contDiffOn_transitionE`; and the source lands in the regular target of the
chart at `p`. This is the bridge from the abstract groupoid transition to Deliverable (ii). -/
theorem contDiffOn_chart_trans (p q : zeroLocus f) :
    ContDiffOn ℝ ⊤ (↑((levelChartE f hfC hsub p).symm ≫ₕ levelChartE f hfC hsub q))
      ((levelChartE f hfC hsub p).symm ≫ₕ levelChartE f hfC hsub q).source := by
  apply (contDiffOn_transitionE f hfC hsub p q).congr_mono (s₁ :=
    ((levelChartE f hfC hsub p).symm ≫ₕ levelChartE f hfC hsub q).source)
  · intro v hv
    -- On the transition source, the transition coincides with the explicit composite.
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    have hv1 : v ∈ (levelChartE f hfC hsub p).target := by
      have h2 := hv
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h2
      exact h2.1
    have hvmem : (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) ∈
        (iftChartAt f hfC hsub p).target := by
      rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_target,
        ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage] at hv1
      have hker : (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v ∈
          (levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
            (hsub p.1 p.2) p.2).target := by
        rw [levelChartKer, OpenPartialHomeomorph.restrOpen] at hv1
        exact hv1.1
      rw [levelSetChart_target, Set.mem_preimage] at hker
      exact hker
    rw [levelChartE_apply, levelChartE_symm_apply f hfC hsub p v hvmem]
  · -- The transition source lands in `e_p.symm ⁻¹' regularKerTarget`.
    intro v hv
    have hv1 : v ∈ (levelChartE f hfC hsub p).target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hv
      exact hv.1
    -- (0, e_p.symm v) ∈ iftChart.target  (same derivation as above)
    have hvmem : (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) ∈
        (iftChartAt f hfC hsub p).target := by
      rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_target,
        ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage] at hv1
      have hker : (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v ∈
          (levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
            (hsub p.1 p.2) p.2).target := by
        rw [levelChartKer, OpenPartialHomeomorph.restrOpen] at hv1
        exact hv1.1
      rw [levelSetChart_target, Set.mem_preimage] at hker
      exact hker
    -- the preimage point is in the chart source, hence regular
    have hsrc : (levelChartE f hfC hsub p).symm v ∈ (levelChartE f hfC hsub p).source :=
      (levelChartE f hfC hsub p).map_target hv1
    rw [levelChartE_source_eq, Set.mem_preimage, levelChartE_symm_apply f hfC hsub p v hvmem]
      at hsrc
    refine ⟨hvmem, ?_⟩
    exact hsrc.2

/-- **The general-nonlinear level set has a `C^∞` structure groupoid (`HasGroupoid`).** Every chart
transition `e.symm ≫ₕ e'` between atlas charts is a `C^∞` diffeomorphism of the Euclidean model — the
content of Deliverable (ii), lifted through the Euclidean identifications and chart restrictions. -/
theorem levelSetHasGroupoid :
    @HasGroupoid (euclideanModel E) _ (zeroLocus f) _ (levelSetChartedSpace f hfC hsub)
      (contDiffGroupoid ⊤ (modelWithCornersSelf ℝ (euclideanModel E))) := by
  letI := levelSetChartedSpace f hfC hsub
  apply hasGroupoid_of_pregroupoid
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  rw [contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.id_comp, Function.comp_id]
  exact contDiffOn_chart_trans f hfC hsub p q

/-- **The level set of a `C^∞` real submersion `f : E → ℝ` is a `C^∞` manifold** modelled on the
fixed Euclidean space `EuclideanSpace ℝ (Fin (finrank E - 1))` — the general-nonlinear regular value
theorem. -/
theorem levelSetIsManifold :
    @IsManifold ℝ _ (euclideanModel E) _ _ (euclideanModel E) _
      (modelWithCornersSelf ℝ (euclideanModel E)) ⊤ (zeroLocus f) _
      (levelSetChartedSpace f hfC hsub) :=
  letI := levelSetChartedSpace f hfC hsub
  { compatible := fun he he' => (levelSetHasGroupoid f hfC hsub).compatible he he' }

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The inclusion of the level set into `E` is a topological embedding.** -/
theorem isEmbedding_subtypeVal :
    Topology.IsEmbedding (Subtype.val : zeroLocus f → E) :=
  Topology.IsEmbedding.subtypeVal

/-- If `v` is in the chart target at `p`, then `(0, e_p.symm v)` is in the IFT chart target — the key
membership used to unfold the chart inverse. -/
theorem mem_iftChartAt_target_of (p : zeroLocus f) (v : euclideanModel E)
    (hv : v ∈ (levelChartE f hfC hsub p).target) :
    (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v) ∈
      (iftChartAt f hfC hsub p).target := by
  rw [levelChartE, OpenPartialHomeomorph.transHomeomorph_target,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage] at hv
  have hker : (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v ∈
      (levelSetChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
        (hsub p.1 p.2) p.2).target := by
    rw [levelChartKer, OpenPartialHomeomorph.restrOpen] at hv
    exact hv.1
  rw [levelSetChart_target, Set.mem_preimage] at hker
  exact hker

/-- **The inclusion `Subtype.val : ↥(zeroLocus f) → E` is `C^∞`** — i.e. the level set, as a manifold
over the fixed Euclidean model, includes smoothly into the ambient `E`. Together with the topological
embedding this is the smooth-embedding property. In each chart the inclusion reads
`v ↦ iftChart_p.symm (0, e_p.symm v)`, the (regular-set) implicit function (Deliverable (i)) composed
with the Euclidean identification, hence `C^∞`. -/
theorem contMDiff_subtypeVal :
    letI := levelSetChartedSpace f hfC hsub
    ContMDiff (modelWithCornersSelf ℝ (euclideanModel E)) (modelWithCornersSelf ℝ E) ⊤
      (fun x : zeroLocus f => (x : E)) := by
  letI := levelSetChartedSpace f hfC hsub
  letI := levelSetIsManifold f hfC hsub
  refine contMDiff_iff.mpr ⟨continuous_subtype_val, fun p y => ?_⟩
  rw [extChartAt_self_eq]
  simp only [modelWithCornersSelf_coe, Function.id_comp]
  -- In the chart at `p`, the inclusion is `v ↦ iftChart_p.symm (0, e_p.symm v)`.
  apply ContDiffOn.congr_mono
    (f := fun v : euclideanModel E => (iftChartAt f hfC hsub p).symm
      (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v))
    (s := (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm ⁻¹'
      regularKerTarget f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2))
  · -- smoothness of the implicit function (Deliverable (i)) ∘ Euclidean iso
    have hsymm : ContDiff ℝ ⊤ (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm :=
      (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm.contDiff
    have hi := contDiffOn_iftChart_symm f (fderiv ℝ f p.1) p.1
      (hasStrictFDerivAt_fderiv f hfC p.1) (hsub p.1 p.2) hfC
    have : (fun v : euclideanModel E => (iftChartAt f hfC hsub p).symm
        (0, (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm v)) =
        (fun k => (iftChart f (fderiv ℝ f p.1) p.1 (hasStrictFDerivAt_fderiv f hfC p.1)
          (hsub p.1 p.2)).symm (0, k)) ∘
          (kerEquivEuclidean (fderiv ℝ f p.1) (hsub p.1 p.2)).symm := rfl
    rw [this]
    exact hi.comp hsymm.contDiffOn (Set.mapsTo_preimage _ _)
  · -- the chart inverse (= Subtype.val ∘ chart.symm) coincides with the implicit function on the target
    intro v hv
    have hv1 : v ∈ (levelChartE f hfC hsub p).target := by
      have := hv.1; simpa only [mfld_simps] using this
    have hvmem := mem_iftChartAt_target_of f hfC hsub p v hv1
    rw [Function.comp_apply, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe_symm, Function.comp_id]
    exact levelChartE_symm_apply f hfC hsub p v hvmem
  · -- the chart target lands in the regular set
    intro v hv
    have hv1 : v ∈ (levelChartE f hfC hsub p).target := by
      have := hv.1; simpa only [mfld_simps] using this
    have hvmem := mem_iftChartAt_target_of f hfC hsub p v hv1
    have hsrc : (levelChartE f hfC hsub p).symm v ∈ (levelChartE f hfC hsub p).source :=
      (levelChartE f hfC hsub p).map_target hv1
    rw [levelChartE_source_eq, Set.mem_preimage, levelChartE_symm_apply f hfC hsub p v hvmem]
      at hsrc
    exact ⟨hvmem, hsrc.2⟩

end Manifold

end

end SKEFTHawking.SmithRegularValueGeneral
