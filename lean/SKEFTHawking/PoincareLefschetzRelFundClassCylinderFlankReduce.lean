import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

/-!
# Phase 5q.H — the cylinder `HasRelFundClass`, connectedness-FREE modulo the flank leaf

The connected cylinder fundamental-class existence `…CrossLocalAlphaU.hasRelFundClass_cylGen` carries a
`[PreconnectedSpace M]` instance, but a full audit of its dependency chain shows the connectedness use
is **localised to a single named leaf**: the flank inclusion injectivity
`ι_U = relIncl (puncU x ⊆ {x}ᶜ)` (`…CrossLocalBridge.relIncl_puncU_compl_injective`, whose only
connectedness step is `…PuncturedFlankInjective.overlapSub_top_eq_zero`'s use of the punctured-top
vanishing `openManifold_top_homology_eq_zero (M := M) x.1` = `H₄(M∖{x.1}) = 0`). Every other link —

* `…CrossLocalBridge.crossHloc_eq_relIncl_alphaU` (`crossHloc([M]|σ) = ι_U(αU)`, `omit [PreconnectedSpace]`),
* `…CrossLocalAlphaU.alphaU_ne_zero` (`αU = crossH_puncU([M]) ≠ 0`, `omit [PreconnectedSpace]`),
* `…CrossLocalInj.hasRelFundClass_cylGen_of_localClass_ne_zero` (no `[PreconnectedSpace]` in scope),

— is already connectedness-free.

This module threads that chain with the flank injectivity as an **explicit per-interior-point
hypothesis** rather than a `[PreconnectedSpace M]` instance, yielding `hasRelFundClass_cylGen_of_flankInjective`
for a general (possibly DISCONNECTED) closed charted manifold `M`. Feeding it into
`cylinderRelFundClassDatum` gives `cylinderRelFundClassDatum_of_flankInjective` — the cylinder
relative-fundamental-class datum `D` reduced to exactly the flank leaf.

## What this means for the disconnected residual

For a DISCONNECTED `M` the flank leaf FAILS globally (it is precisely the punctured-top-vanishing no-go:
removing a point from one component leaves the other closed components, each with `H₄ ≅ ℤ/2 ≠ 0`, so the
global `ι_U` is not injective — the KernelNoGos punctured-top fence). This module does **not** claim to
inhabit that leaf for disconnected `M`; it isolates the disconnected `D`-field obstruction as the single
kernel-checked flank-injectivity leaf, connectedness-free otherwise, and provides the general-`M`
`HasRelFundClass`/`D` builders that any per-piece supply of the leaf (route (b), the clopen split) or a
future homeomorphism-transport route plugs directly into. The connected specialisation
`hasRelFundClass_cylGen_of_flankInjective`-via-`relIncl_puncU_compl_injective` recovers the existing
`…CrossLocalAlphaU.hasRelFundClass_cylGen` (sanity `example`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalInj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankInjective

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderFlankReduce

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The cylinder `HasRelFundClass`, connectedness-FREE modulo the flank leaf.** For a general
(possibly DISCONNECTED) closed charted manifold `M`, if at every interior point `x` the flank inclusion
`ι_U = relIncl (puncU x ⊆ {x}ᶜ)` is injective, then the cylinder's interior generator family has a
relative fundamental class. The proof threads the connectedness-free chain
`hasRelFundClass_cylGen_of_localClass_ne_zero` ∘ `crossHloc_eq_relIncl_alphaU` ∘ `alphaU_ne_zero`, with
the flank injectivity supplied by hypothesis in place of `relIncl_puncU_compl_injective`. -/
theorem hasRelFundClass_cylGen_of_flankInjective [T1Space (cylW M)]
    (hflank : ∀ (x : ↑(cyl (TopCat.of M))) (_ht0 : (0 : ℝ) < (x.2 : ℝ)) (_ht1 : (x.2 : ℝ) < 1),
      Function.Injective (relIncl (puncU_subset_compl x) (m' + 3))) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))
  refine hasRelFundClass_cylGen_of_localClass_ne_zero z hz.symm (fun x hx => ?_)
  rw [crossHloc_eq_relIncl_alphaU x hx z hz.symm]
  intro hcontra
  obtain ⟨ht0, ht1⟩ := interior_real_bounds x hx
  exact alphaU_ne_zero x hx z hz.symm
    (hflank (x : ↑(cyl (TopCat.of M))) ht0 ht1 (by rw [map_zero]; exact hcontra))

/-- **The cylinder relative-fundamental-class datum `D`, reduced to the flank leaf.** The general-`M`
`D`-field builder: `cylinderRelFundClassDatum` fed by `hasRelFundClass_cylGen_of_flankInjective`. For a
DISCONNECTED `M` this reduces the `D` field of `DisconnectedCylCore`/`DisconnectedCylCoreND` to exactly
the per-interior-point flank-injectivity leaf, connectedness-free otherwise — no `[PreconnectedSpace M]`
instance. -/
def cylinderRelFundClassDatum_of_flankInjective [T1Space (cylW M)]
    (hflank : ∀ (x : ↑(cyl (TopCat.of M))) (_ht0 : (0 : ℝ) < (x.2 : ℝ)) (_ht1 : (x.2 : ℝ) < 1),
      Function.Injective (relIncl (puncU_subset_compl x) (m' + 3))) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum (hasRelFundClass_cylGen_of_flankInjective hflank)

/-- **Sanity — the connected specialisation recovers the existing existence result.** Supplying the
flank leaf from `relIncl_puncU_compl_injective` (the connected `[PreconnectedSpace M]` derivation)
reproduces `…CrossLocalAlphaU.hasRelFundClass_cylGen`. -/
example [PreconnectedSpace M] [T1Space (cylW M)] :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_cylGen_of_flankInjective
    (fun x ht0 ht1 => relIncl_puncU_compl_injective x ht0 ht1)

/-! ## §2. The flank leaf pushed to the recognizable punctured-top-vanishing no-go.

The sole connectedness step in the flank chain is `…OpenTopVanish.openManifold_top_homology_eq_zero`
(`H_{m'+2}(M∖σ) = 0`, `[PreconnectedSpace M]`) inside `…PuncturedFlankInjective.overlapSub_top_eq_zero`.
Threading that vanishing as an explicit hypothesis `hpunc` re-derives the whole flank chain
connectedness-free, so `hasRelFundClass_cylGen`/the `D` datum reduce to EXACTLY the punctured-top leaf —
the recognizable statement the KernelNoGos punctured-top fence refutes for disconnected `M`. Each lemma
below is the connectedness-free twin of its `…PuncturedFlankInjective`/`…CrossLocalBridge` original, with
the single `openManifold_top_homology_eq_zero` call replaced by `hpunc`. -/

/-- **The punctured-top-vanishing leaf** as a `Prop`: `H_{m'+2}(M∖σ) = 0` at every base point `σ`. Holds
for connected `M` (`openManifold_top_homology_eq_zero`); FALSE for disconnected `M` (removing a point
from one component leaves the other closed components with `H₄ ≅ ℤ/2 ≠ 0` — the punctured-top no-go). -/
def PuncturedTopVanish : Prop :=
  ∀ (σ : M) (w : Homology (sub ({σ}ᶜ : Set ↑(TopCat.of M))) (m' + 2)), w = 0

variable (hpunc : PuncturedTopVanish (m' := m') (M := M))

include hpunc

omit [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] in
/-- Connectedness-free twin of `overlapSub_top_eq_zero`: the overlap SUBSPACE top homology vanishes,
from the punctured-top leaf. -/
theorem overlapSub_top_eq_zero_of_puncturedTopVanish (x : ↑(cyl (TopCat.of M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)
    (w : Homology (sub (overlap x)) (m' + 2)) : w = 0 := by
  refine (overlapSubHomEquiv (N := TopCat.of M) x ht0 ht1 (m' + 1)).injective ?_
  rw [map_zero]
  refine Prod.ext ?_ ?_ <;> exact hpunc x.1 _

/-- Connectedness-free twin of `overlapPair_top_eq_zero`: the overlap PAIR top homology vanishes. -/
theorem overlapPair_top_eq_zero_of_puncturedTopVanish (x : ↑(cyl (TopCat.of M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)
    (p : RelativeHomology (overlap x) (m' + 3)) : p = 0 := by
  have hdelta : connecting (X := cyl (TopCat.of M)) (overlap x) (m' + 2) p = 0 :=
    overlapSub_top_eq_zero_of_puncturedTopVanish hpunc x ht0 ht1 _
  obtain ⟨q, hq⟩ :=
    (exact_homProj_connecting (X := cyl (TopCat.of M)) (overlap x) (m' + 2) p).mp hdelta
  rw [← hq, cyl_homology_above_eq_zero q, map_zero]

/-- Connectedness-free twin of `relMvHomSum_top_injective`. -/
theorem relMvHomSum_top_injective_of_puncturedTopVanish (x : ↑(cyl (TopCat.of M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective (relMvHomSum (puncU x) (puncV x) (m' + 3)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨w, hw⟩ := (relMv_exact_middle' (puncU x) (puncV x) (isOpen_puncU x) (isOpen_puncV x)
    (m' + 2) a).mp ha
  rw [← hw, overlapPair_top_eq_zero_of_puncturedTopVanish hpunc x ht0 ht1 w, map_zero]

/-- Connectedness-free twin of `puncU_flank_injective`. -/
theorem puncU_flank_injective_of_puncturedTopVanish (x : ↑(cyl (TopCat.of M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective
      (relIncl (Set.subset_union_left : puncU x ⊆ puncU x ∪ puncV x) (m' + 3)) := by
  intro a b hab
  have hsum : relMvHomSum (puncU x) (puncV x) (m' + 3) (a, 0)
      = relMvHomSum (puncU x) (puncV x) (m' + 3) (b, 0) := by
    show relIncl Set.subset_union_left (m' + 3) a + relIncl Set.subset_union_right (m' + 3) 0
      = relIncl Set.subset_union_left (m' + 3) b + relIncl Set.subset_union_right (m' + 3) 0
    rw [hab]
  have := relMvHomSum_top_injective_of_puncturedTopVanish hpunc x ht0 ht1 hsum
  exact (Prod.ext_iff.mp this).1

/-- Connectedness-free twin of `…CrossLocalBridge.relIncl_puncU_compl_injective`: the flank inclusion
`ι_U = relIncl (puncU ⊆ {x}ᶜ)` is injective, from the punctured-top leaf. -/
theorem relIncl_puncU_compl_injective_of_puncturedTopVanish (x : ↑(cyl (TopCat.of M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective (relIncl (puncU_subset_compl x) (m' + 3)) := by
  have hUV : puncU x ∪ puncV x = ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := puncU_union_puncV x
  intro a b hab
  apply puncU_flank_injective_of_puncturedTopVanish hpunc x ht0 ht1
  apply (SKEFTHawking.SingularConvexStageIso.relHomologySetCongr hUV.subset hUV.symm.subset
    (m' + 3)).injective
  show relIncl hUV.subset (m' + 3) (relIncl Set.subset_union_left (m' + 3) a)
    = relIncl hUV.subset (m' + 3) (relIncl Set.subset_union_left (m' + 3) b)
  rw [relIncl_trans, relIncl_trans]
  exact hab

/-- **The cylinder `HasRelFundClass`, reduced to the punctured-top-vanishing leaf.** For a general
(possibly DISCONNECTED) closed charted `M`, the punctured-top leaf `hpunc` (`H_{m'+2}(M∖σ) = 0` at every
base point) discharges the cylinder relative fundamental class — connectedness-free. This is the sharpest
statement of the disconnected `D`-field obstruction: it IS exactly the punctured-top-vanishing, nothing
more, which is precisely what fails (kernel-checked no-go) for disconnected `M`. -/
theorem hasRelFundClass_cylGen_of_puncturedTopVanish [T1Space (cylW M)] :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_cylGen_of_flankInjective
    (fun x ht0 ht1 => relIncl_puncU_compl_injective_of_puncturedTopVanish hpunc x ht0 ht1)

/-- **The `D` datum, reduced to the punctured-top-vanishing leaf.** `cylinderRelFundClassDatum` fed by
`hasRelFundClass_cylGen_of_puncturedTopVanish`. -/
def cylinderRelFundClassDatum_of_puncturedTopVanish [T1Space (cylW M)] :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum (hasRelFundClass_cylGen_of_puncturedTopVanish hpunc)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderFlankReduce
