import Mathlib
import SKEFTHawking.SingularFundamentalClass

/-!
# Phase 5q.F (w₂-foundation, brick 72c-5) — existence of the fundamental class (Hatcher 3.27(b))

The **surjective / existence** half of `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`. A class `α : Hₘ₊₂(M|K)`
**restricts to the local generator** when `restrictToPoint hx α = (manifoldLocalIso x).symm 1` (the
generator of `Hₘ₊₂(M|x) ≅ ℤ/2`) for every `x ∈ K`; `hasFundClass K` asserts such a class exists.
Hatcher 3.27(b) builds it by induction over a finite chart-ball cover:

* **base case** (`hasFundClass_chartBall`): on a chart ball `K`, `Hₘ₊₂(M|K) ≅ ℤ/2` (`localComposite` at
  the centre is bijective), so the preimage of `1` is a class whose per-point value is the local
  generator everywhere on the ball (`localComposite_agree_chartBall`).
* **union step** (`hasFundClass_union`): the relative Mayer–Vietoris middle exactness
  `relMv_exact_middle'` glues fundamental classes on `A`, `B` — they agree on `A ∩ B` because both
  restrict to the *same* generator there, so `(αA, αB) ∈ ker (relMvHomSum) = im (relMvHomDiag)`.

The per-point condition is an *element* equality in `Hₘ₊₂(M|x)` (not a `localComposite = 1` scalar
equation), so the Mayer–Vietoris transports stay at the cheap `relIncl` level — no `manifoldLocalIso`
composite unfolding. Combined with the injective half (`restrictHomologyToPoint_injective`) this gives
`Hₘ₊₂(M;ℤ/2) ≅ ℤ/2` and the fundamental class `[M]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.SingularFundamentalClass

/-- **A class restricts to the local generator on `K`**: `restrictToPoint hx α = (manifoldLocalIso x).symm 1`
(the generator of `Hₘ₊₂(M|x) ≅ ℤ/2`) for every `x ∈ K`. An *element* equality in `Hₘ₊₂(M|x)`, so the MV
transports of the union step stay at the `relIncl` level. -/
def restrictsToGenerator {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M}
    (α : RelativeHomology (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) (m + 2)) : Prop :=
  ∀ (x : M) (hx : x ∈ K),
    SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hx (m + 2) α
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1

/-- **`Hₘ₊₂(M|K)` has a fundamental class**: some class restricts to the local generator at every
point of `K`. For `K = univ` (`M` compact) this is the fundamental class `[M]`. -/
def hasFundClass {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (K : Set M) : Prop :=
  ∃ α : RelativeHomology (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) (m + 2),
    restrictsToGenerator (m := m) α

/-- **Base case of the existence induction** (Hatcher 3.27(b)): a chart ball
`K = (chartAt y₀).symm '' B̄(chartAt y₀ · y₀, r)` (`r ≥ 0`, `B̄ ⊆ target`) **has a fundamental class**.
`localComposite` at the centre `y₀` is bijective (`localComposite_bijective` via
`restrictToPoint_chartBall_bijective`), so `α := localComposite⁻¹ 1` exists; on the ball its local value
is constant (`localComposite_agree_chartBall`), i.e. `restrictToPoint hx α = (manifoldLocalIso x).symm 1`. -/
theorem hasFundClass_chartBall {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (y₀ : M) {r : ℝ} (hr : 0 ≤ r)
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).target) :
    hasFundClass (m := m) ((chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r) := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ with hc
  set K : Set M := c.symm '' Metric.closedBall (c y₀) r with hK
  have hy₀K : y₀ ∈ K := ⟨c y₀, Metric.mem_closedBall_self hr, c.left_inv (mem_chart_source _ y₀)⟩
  obtain ⟨α, hα⟩ := (localComposite_bijective hy₀K
    (SingularGoodCompactManifold.restrictToPoint_chartBall_bijective y₀ hrsub hy₀K)).surjective 1
  refine ⟨α, fun x hx => ?_⟩
  -- `manifoldLocalIso x (restrictToPoint hx α) = localComposite hx α = localComposite hy₀ α = 1`
  have key : SKEFTHawking.SingularChartBridge.manifoldLocalIso x (restrictToPoint hx (m + 2) α) = 1 :=
    (localComposite_agree_chartBall (m := m) y₀ hrsub hx hy₀K α).trans hα
  rw [← (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm_apply_apply
        (restrictToPoint hx (m + 2) α), key]

/-! ### Mayer–Vietoris transport helpers for the de Morgan set equalities -/

/-- **A `relIncl` over a set equality is left-inverted by its reverse** (`relIncl hTS ∘ relIncl hST = id`
when `S = T`, as `relIncl_trans` collapses to `relIncl (S ⊆ S) = id`). Used to inject across the de
Morgan identities `(A∪B)ᶜ = Aᶜ∩Bᶜ`, `(A∩B)ᶜ = Aᶜ∪Bᶜ` in the existence union step. -/
theorem relIncl_leftInverse {X : TopCat} {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S) (n : ℕ)
    (p : RelativeHomology S n) : relIncl hTS n (relIncl hST n p) = p := by
  rw [relIncl_trans, relIncl, SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map_id]; rfl

/-- **A `relIncl` over a set equality is injective** (from `relIncl_leftInverse`). -/
theorem relIncl_injective_of_setEq {X : TopCat} {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S) (n : ℕ) :
    Function.Injective (relIncl hST n) :=
  Function.LeftInverse.injective (relIncl_leftInverse hST hTS n)

/-- **The Mayer–Vietoris union step of the existence induction** (Hatcher 3.27(b)): if `A`, `B` are
closed, `A ∩ B` is determined-by-points, and both `A`, `B` have a fundamental class, then so does
`A ∪ B`. The two classes `αA`, `αB` restrict to the *same* generator at each point of `A ∩ B`, so they
agree there; hence `(αA, αB) ∈ ker (relMvHomSum) = im (relMvHomDiag)` (`relMv_exact_middle'`), and the
preimage `v`, pushed to `Hₘ₊₂(M | (A∪B)ᶜ)` by `relIncl`, restricts to the generator everywhere. -/
theorem hasFundClass_union {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B)
    (hDAB : SKEFTHawking.SingularManifoldFundamentalClass.determinedByPoints
      (X := TopCat.of M) (m + 2) (A ∩ B))
    (hfA : hasFundClass (m := m) A) (hfB : hasFundClass (m := m) B) :
    hasFundClass (m := m) (A ∪ B) := by
  obtain ⟨αA, hαA⟩ := hfA
  obtain ⟨αB, hαB⟩ := hfB
  have hge : (Aᶜ ∩ Bᶜ : Set ↑(TopCat.of M)) ⊆ (A ∪ B)ᶜ := (Set.compl_union A B).ge
  have hUVsub : (Aᶜ ∪ Bᶜ : Set ↑(TopCat.of M)) ⊆ (A ∩ B)ᶜ := (Set.compl_inter A B).ge
  have hVUsub : ((A ∩ B)ᶜ : Set ↑(TopCat.of M)) ⊆ (Aᶜ ∪ Bᶜ) := (Set.compl_inter A B).le
  -- `Σ(αA, αB) = 0`: transport into `Hₘ₊₂(M | A∩B)` and apply `determinedByPoints`; at each `y` the two
  -- restrictions equal the *same* generator, so their ℤ/2 sum vanishes.
  have hsum0 : relMvHomSum (M := TopCat.of M) Aᶜ Bᶜ (m + 2) (αA, αB) = 0 := by
    apply relIncl_injective_of_setEq hUVsub hVUsub (m + 2)
    rw [map_zero]
    refine hDAB _ (fun y hy => ?_)
    have keyA : restrictToPoint hy (m + 2)
        (relIncl hUVsub (m + 2) (relIncl Set.subset_union_left (m + 2) αA))
        = restrictToPoint hy.1 (m + 2) αA := by
      show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) (m + 2)
          (relIncl hUVsub (m + 2) (relIncl Set.subset_union_left (m + 2) αA))
        = relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy.1)) (m + 2) αA
      rw [relIncl_trans, relIncl_trans]
    have keyB : restrictToPoint hy (m + 2)
        (relIncl hUVsub (m + 2) (relIncl Set.subset_union_right (m + 2) αB))
        = restrictToPoint hy.2 (m + 2) αB := by
      show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) (m + 2)
          (relIncl hUVsub (m + 2) (relIncl Set.subset_union_right (m + 2) αB))
        = relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy.2)) (m + 2) αB
      rw [relIncl_trans, relIncl_trans]
    have hsumeq : relMvHomSum (M := TopCat.of M) Aᶜ Bᶜ (m + 2) (αA, αB)
        = relIncl Set.subset_union_left (m + 2) αA + relIncl Set.subset_union_right (m + 2) αB := rfl
    rw [hsumeq, map_add, map_add, keyA, keyB, hαA y hy.1, hαB y hy.2, ZModModule.add_self]
  -- exactness: `(αA, αB) = relMvHomDiag v` for some `v ∈ Hₘ₊₂(M | Aᶜ∩Bᶜ)`.
  obtain ⟨v, hv⟩ :=
    ((relMv_exact_middle' (M := TopCat.of M) Aᶜ Bᶜ hA.isOpen_compl hB.isOpen_compl (m + 1))
      (αA, αB)).mp hsum0
  have hvA : relIncl Set.inter_subset_left (m + 2) v = αA := congrArg Prod.fst hv
  have hvB : relIncl Set.inter_subset_right (m + 2) v = αB := congrArg Prod.snd hv
  refine ⟨relIncl hge (m + 2) v, fun x hx => ?_⟩
  rcases hx with hxA | hxB
  · -- `restrictToPoint hx (relIncl hge v) = restrictToPoint (x∈A) αA = generator` (relIncl collapse)
    rw [show restrictToPoint (Set.mem_union_left B hxA) (m + 2) (relIncl hge (m + 2) v)
        = restrictToPoint hxA (m + 2) αA from ?_]
    · exact hαA x hxA
    · show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
          (Set.mem_union_left B hxA))) (m + 2) (relIncl hge (m + 2) v)
        = relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxA)) (m + 2) αA
      rw [← hvA, relIncl_trans, relIncl_trans]
  · rw [show restrictToPoint (Set.mem_union_right A hxB) (m + 2) (relIncl hge (m + 2) v)
        = restrictToPoint hxB (m + 2) αB from ?_]
    · exact hαB x hxB
    · show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
          (Set.mem_union_right A hxB))) (m + 2) (relIncl hge (m + 2) v)
        = relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxB)) (m + 2) αB
      rw [← hvB, relIncl_trans, relIncl_trans]

end SKEFTHawking.SingularFundamentalClass
