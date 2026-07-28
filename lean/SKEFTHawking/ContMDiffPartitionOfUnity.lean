/-
Copyright (c) 2026 SK-EFT Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Partitions of unity at finite regularity

Mathlib's manifold partitions of unity are `C^∞`-only. `SmoothPartitionOfUnity ι I M s` is valued
in `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `SmoothPartitionOfUnity.exists_isSubordinate` runs through
`BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(ℝ) ∞)`, and the smoothness-on-`M` lemmas
for `SmoothBumpFunction` live under `variable [IsManifold I ∞ M]`. Nothing about *boundarylessness*
is assumed anywhere in that development — partitions of unity work perfectly well on manifolds with
boundary — but a `C^k` partition of unity on a merely `C^k` manifold is not available.

This file supplies it. Nothing here is new mathematics: the standard bump is `C^∞` *in a chart*,
so it is a `C^k` function on a `C^k` manifold, and the combinatorial half of Mathlib's construction
(`SmoothBumpCovering.exists_isSubordinate`, `BumpCovering.toPartitionOfUnity`) turns out to be
regularity-agnostic already. The work is threading a finite regularity through the chain.

The regularity is `n : ℕ∞`, not `n : WithTop ℕ∞`: analytic bump functions do not exist, so the
analytic grade `ω` is excluded by mathematics, not by a gap in the formalisation.
-/

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace SKEFTHawking.Collar

universe uι uE uF uH uM

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-! ### A smooth bump function is `C^n` on a `C^n` manifold -/

/-- **A `SmoothBumpFunction` is `C^n` on a `C^n` manifold.**

This is the finite-regularity form of `SmoothBumpFunction.contMDiff`, which Mathlib states only
under `[IsManifold I ∞ M]`. The proof is unchanged: in the chart the bump is a `ContDiffBump`,
which is `C^n` for every `n : ℕ∞`, and the extended chart is `C^n` on a `C^n` manifold. -/
theorem contMDiff_smoothBumpFunction {n : ℕ∞} [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I n M] {c : M} (f : SmoothBumpFunction I c) :
    ContMDiff I 𝓘(ℝ) n f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have hx' : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| f.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H c).open_source.mem_nhds hx'
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' (I := I) (n := n) hx')

/-- A `SmoothBumpFunction` is continuous on an arbitrary charted space.

Mathlib derives continuity of a smooth bump function from its `C^∞` smoothness, hence only on a
`C^∞` manifold; here it is the `n = 0` case of `contMDiff_smoothBumpFunction`, for which the
`IsManifold` hypothesis is vacuous. -/
theorem continuous_smoothBumpFunction [FiniteDimensional ℝ E] [T2Space M] {c : M}
    (f : SmoothBumpFunction I c) : Continuous f := by
  haveI : IsManifold I ((0 : ℕ∞) : WithTop ℕ∞) M := inferInstanceAs (IsManifold I 0 M)
  exact (contMDiff_smoothBumpFunction (I := I) (n := 0) f).continuous

/-! ### `C^n` partitions of unity -/

variable (ι I M) in
/-- A `C^n` partition of unity on a set `s : Set M`: a continuous partition of unity all of whose
members are `C^n`.

Unlike Mathlib's `SmoothPartitionOfUnity`, which stores its members as `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯` and is
therefore locked to `n = ∞`, this extends the purely topological `PartitionOfUnity` by a regularity
field, so the whole `PartitionOfUnity` API is inherited verbatim. -/
structure ContMDiffPartitionOfUnity (n : ℕ∞) (s : Set M := univ)
    extends PartitionOfUnity ι M s where
  /-- each member of the partition is `C^n` -/
  contMDiff' : ∀ i, ContMDiff I 𝓘(ℝ) n (toFun i)

namespace ContMDiffPartitionOfUnity

variable {n : ℕ∞} {s : Set M} (f : ContMDiffPartitionOfUnity ι I M n s)

instance : FunLike (ContMDiffPartitionOfUnity ι I M n s) ι C(M, ℝ) where
  coe f := f.toPartitionOfUnity
  coe_injective' f g h := by
    cases f; cases g
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_toPartitionOfUnity (i : ι) : (f.toPartitionOfUnity i : M → ℝ) = f i := rfl

protected theorem contMDiff (i : ι) : ContMDiff I 𝓘(ℝ) n (f i) := f.contMDiff' i

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.toPartitionOfUnity.locallyFinite

theorem nonneg (i : ι) (x : M) : 0 ≤ f i x := f.toPartitionOfUnity.nonneg i x

theorem sum_eq_one {x : M} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.toPartitionOfUnity.sum_eq_one hx

theorem sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 := f.toPartitionOfUnity.sum_le_one x

theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x := f.toPartitionOfUnity.sum_nonneg x

theorem le_one (i : ι) (x : M) : f i x ≤ 1 := f.toPartitionOfUnity.le_one i x

/-- The sum of a `C^n` partition of unity is `C^n` (it equals `1` on `s`, but the sum is globally
defined and globally `C^n`). -/
theorem contMDiff_sum : ContMDiff I 𝓘(ℝ) n fun x => ∑ᶠ i, f i x :=
  contMDiff_finsum (fun i => ContMDiffPartitionOfUnity.contMDiff f i)
    (ContMDiffPartitionOfUnity.locallyFinite f)

/-- If `g` is `C^n` at every point of the topological support of `f i`, then `f i • g` is `C^n`
on the whole manifold — the point being that `f i` kills whatever `g` does elsewhere. -/
theorem contMDiff_smul {g : M → F} {i : ι} (hg : ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n g x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => f i x • g x :=
  contMDiff_of_tsupport fun x hx =>
    (ContMDiffPartitionOfUnity.contMDiff f i).contMDiffAt.smul <|
      hg x <| tsupport_smul_subset_left _ _ hx

/-- **Patching lemma.** If `g i` is `C^n` at every point of the topological support of `f i`, then
`fun x => ∑ᶠ i, f i x • g i x` is `C^n` on the whole manifold. This is what turns a family of
locally defined objects into a single global `C^n` one, and is the reason the collar construction
needs a partition of unity in the first place. -/
theorem contMDiff_finsum_smul {g : ι → M → F}
    (hg : ∀ i, ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n (g i) x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  (contMDiff_finsum fun i => ContMDiffPartitionOfUnity.contMDiff_smul f (hg i)) <|
    (ContMDiffPartitionOfUnity.locallyFinite f).subset fun _ => support_smul_subset_left _ _

/-- A `C^n` partition of unity is *subordinate* to a family of sets `U i` if the closure of the
support of each member is contained in the corresponding set. -/
def IsSubordinate (f : ContMDiffPartitionOfUnity ι I M n s) (U : ι → Set M) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

theorem isSubordinate_iff_toPartitionOfUnity {U : ι → Set M} :
    IsSubordinate f U ↔ f.toPartitionOfUnity.IsSubordinate U := Iff.rfl

end ContMDiffPartitionOfUnity

/-! ### From a bump covering -/

/-- The partition of unity built from a `BumpCovering` of `C^n` functions is `C^n`. -/
theorem contMDiff_bumpCovering_toPartitionOfUnity {n : ℕ∞} {s : Set M} (f : BumpCovering ι M s)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) (i : ι) :
    ContMDiff I 𝓘(ℝ) n (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

/-- A `BumpCovering` all of whose members are `C^n` generates a `C^n` partition of unity. -/
noncomputable def bumpCoveringToContMDiffPartitionOfUnity {n : ℕ∞} {s : Set M}
    (f : BumpCovering ι M s)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) : ContMDiffPartitionOfUnity ι I M n s where
  toPartitionOfUnity := f.toPartitionOfUnity
  contMDiff' i := contMDiff_bumpCovering_toPartitionOfUnity f hf i

@[simp] theorem coe_bumpCoveringToContMDiffPartitionOfUnity {n : ℕ∞} {s : Set M}
    (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) (i : ι) :
    ⇑(bumpCoveringToContMDiffPartitionOfUnity (I := I) f hf i) = f.toPartitionOfUnity i := rfl

theorem isSubordinate_bumpCoveringToContMDiffPartitionOfUnity {n : ℕ∞} {s : Set M}
    {f : BumpCovering ι M s} {U : ι → Set M} (h : f.IsSubordinate U)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) :
    ContMDiffPartitionOfUnity.IsSubordinate
      (bumpCoveringToContMDiffPartitionOfUnity (I := I) f hf) U :=
  h.toPartitionOfUnity

/-- Reinterpret a `SmoothBumpCovering` as a `BumpCovering`, at no regularity cost.

Mathlib's `SmoothBumpCovering.toBumpCovering` needs `[IsManifold I ∞ M]`, only because it obtains
continuity of the members from their `C^∞` smoothness. Continuity is available outright. -/
noncomputable def smoothBumpCoveringToBumpCovering [FiniteDimensional ℝ E] [T2Space M] {s : Set M}
    (fs : SmoothBumpCovering ι I M s) : BumpCovering ι M s where
  toFun i := ⟨fs i, continuous_smoothBumpFunction (fs i)⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp] theorem coe_smoothBumpCoveringToBumpCovering [FiniteDimensional ℝ E] [T2Space M]
    {s : Set M} (fs : SmoothBumpCovering ι I M s) (i : ι) :
    ⇑(smoothBumpCoveringToBumpCovering fs i) = fs i := rfl

/-- Every `SmoothBumpCovering` of a `C^n` manifold defines a `C^n` partition of unity. -/
noncomputable def smoothBumpCoveringToContMDiffPartitionOfUnity {n : ℕ∞} [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I n M] {s : Set M} (fs : SmoothBumpCovering ι I M s) :
    ContMDiffPartitionOfUnity ι I M n s :=
  bumpCoveringToContMDiffPartitionOfUnity (smoothBumpCoveringToBumpCovering fs)
    fun i => contMDiff_smoothBumpFunction (fs i)

theorem isSubordinate_smoothBumpCoveringToContMDiffPartitionOfUnity {n : ℕ∞}
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I n M] {s : Set M} {U : M → Set M}
    {fs : SmoothBumpCovering ι I M s} (h : fs.IsSubordinate U) :
    ContMDiffPartitionOfUnity.IsSubordinate
      (smoothBumpCoveringToContMDiffPartitionOfUnity (n := n) fs) fun i => U (fs.c i) :=
  isSubordinate_bumpCoveringToContMDiffPartitionOfUnity
    (f := smoothBumpCoveringToBumpCovering fs) h _

theorem smoothBumpCoveringToContMDiffPartitionOfUnity_zero_of_zero {n : ℕ∞}
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I n M] {s : Set M}
    {fs : SmoothBumpCovering ι I M s} {i : ι} {x : M} (h : fs i x = 0) :
    smoothBumpCoveringToContMDiffPartitionOfUnity (n := n) fs i x = 0 :=
  BumpCovering.toPartitionOfUnity_zero_of_zero _ h

/-! ### Existence -/

/-- **Finite-regularity `C^n` Urysohn lemma on a manifold.** Given two disjoint closed sets in a
Hausdorff, σ-compact, finite-dimensional `C^n` manifold, there is a `C^n` function that is `0` on
the first, `1` on the second, and takes values in `[0,1]`.

This is `exists_contMDiffMap_zero_one_of_isClosed` with `[IsManifold I ∞ M]` weakened to
`[IsManifold I n M]`: the smooth structure need only be as regular as the function produced. -/
theorem exists_contMDiff_zero_one_of_isClosed {n : ℕ∞} [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] [IsManifold I n M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) n f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have hnhds : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  obtain ⟨κ, fs, hfs⟩ := SmoothBumpCovering.exists_isSubordinate I ht hnhds
  set g := smoothBumpCoveringToContMDiffPartitionOfUnity (n := n) fs with hg
  refine ⟨fun x => ∑ᶠ i, g i x, g.contMDiff_sum, fun x hx => ?_,
    fun x hx => g.sum_eq_one hx, fun x => ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  have hzero : ∀ i, g i x = 0 := by
    intro i
    refine smoothBumpCoveringToContMDiffPartitionOfUnity_zero_of_zero ?_
    exact notMem_support.1 (subset_compl_comm.1 (hfs.support_subset i) hx)
  simp only [hzero, finsum_zero, Pi.zero_apply]

namespace ContMDiffPartitionOfUnity

/-- **A `C^n` partition of unity subordinate to any open cover of a closed set.**

The finite-regularity form of `SmoothPartitionOfUnity.exists_isSubordinate`. Note that no
boundarylessness is assumed anywhere: this holds verbatim on a manifold with boundary or corners.
What Mathlib's version assumes and this one does not is that the manifold is `C^∞`. -/
theorem exists_isSubordinate {n : ℕ∞} [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [IsManifold I n M] {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : ContMDiffPartitionOfUnity ι I M n s, f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hex := BumpCovering.exists_isSubordinate_of_prop
    (ContMDiff I 𝓘(ℝ) (n : WithTop ℕ∞)) ?_ hs U ho hU
  · obtain ⟨f, hf, hfU⟩ := hex
    exact ⟨bumpCoveringToContMDiffPartitionOfUnity f hf,
      isSubordinate_bumpCoveringToContMDiffPartitionOfUnity hfU hf⟩
  · intro a b ha hb hab
    obtain ⟨f, hfsm, hf0, hf1, hf01⟩ := exists_contMDiff_zero_one_of_isClosed
      (I := I) (n := n) ha hb hab
    exact ⟨⟨f, hfsm.continuous⟩, hfsm, hf0, hf1, hf01⟩

/-- **A `C^n` partition of unity subordinate to the chart cover of a closed set** — the form the
collar construction consumes: each member is supported in a single chart domain, so a locally
defined object (e.g. the inward-pointing coordinate vector field of a boundary chart) can be
patched into a global `C^n` one. -/
theorem exists_isSubordinate_chartAt_source_of_isClosed {n : ℕ∞} [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I n M] {s : Set M} (hs : IsClosed s) :
    ∃ f : ContMDiffPartitionOfUnity s I M n s,
      f.IsSubordinate fun x : s => (chartAt H (x : M)).source := by
  refine exists_isSubordinate hs _ (fun _ => (chartAt H _).open_source) fun x hx => ?_
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

end ContMDiffPartitionOfUnity

end SKEFTHawking.Collar
