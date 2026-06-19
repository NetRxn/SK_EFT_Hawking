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

/-- **Finite-union existence** (Hatcher 3.27(b)): for a nonempty finite family `K i` (`i ∈ s`) each of
which **has a fundamental class** and all of whose nonempty sub-intersections `⋂ i∈t, K i` are closed
and `goodCompact`, the union `⋃ i∈s, K i` has a fundamental class. Induction on `s` via
`hasFundClass_union`, mirroring `goodCompact_biUnion`; the union step's `determinedByPoints (A∩B)` for
`A = K a`, `B = ⋃_{i∈s} K i` comes from `goodCompact (K a ∩ ⋃ K i) = goodCompact (⋃ (K a ∩ K i))`,
itself supplied by `goodCompact_biUnion` over the sub-intersection family (covered by the hypothesis). -/
theorem hasFundClass_biUnion {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {ι : Type*} [DecidableEq ι] :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set M),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧
           SKEFTHawking.SingularGoodCompact.goodCompact (X := TopCat.of M) (m + 2) (⋂ i ∈ t, K i)) →
      (∀ i ∈ s, hasFundClass (m := m) (K i)) →
      hasFundClass (m := m) (⋃ i ∈ s, K i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro K _hgc hfc
      simpa using hfc a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
      intro K hgc hfc
      have hUnion : (⋃ i ∈ Finset.cons a s ha, K i) = K a ∪ ⋃ i ∈ s, K i := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨i, rfl | hi, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hUnion]
      have hKa := hgc {a} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_self a s))
        (Finset.singleton_nonempty a)
      have hKac : IsClosed (K a) := by simpa using hKa.1
      have hBc : IsClosed (⋃ i ∈ s, K i) := by
        refine Set.Finite.isClosed_biUnion s.finite_toSet (fun i hi => ?_)
        have := hgc {i} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_of_mem hi))
          (Finset.singleton_nonempty i)
        simpa using this.1
      have hfKa : hasFundClass (m := m) (K a) := hfc a (Finset.mem_cons_self a s)
      have hfB : hasFundClass (m := m) (⋃ i ∈ s, K i) :=
        ih K (fun t ht htne => hgc t (ht.trans (Finset.subset_cons ha)) htne)
          (fun i hi => hfc i (Finset.mem_cons_of_mem hi))
      have hdist : K a ∩ (⋃ i ∈ s, K i) = ⋃ i ∈ s, (K a ∩ K i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨hxa, i, hi, hx⟩; exact ⟨i, hi, hxa, hx⟩
        · rintro ⟨i, hi, hxa, hx⟩; exact ⟨hxa, i, hi, hx⟩
      have hgcInter : SKEFTHawking.SingularGoodCompact.goodCompact (X := TopCat.of M) (m + 2)
          (K a ∩ (⋃ i ∈ s, K i)) := by
        rw [hdist]
        refine SKEFTHawking.SingularGoodCompact.goodCompact_biUnion (X := TopCat.of M) hs
          (fun i => K a ∩ K i) (fun t ht htne => ?_)
        have heq : (⋂ i ∈ t, (K a ∩ K i)) = ⋂ i ∈ insert a t, K i := by
          obtain ⟨j, hj⟩ := htne
          ext x
          simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
          constructor
          · rintro h i (rfl | hi)
            · exact (h j hj).1
            · exact (h i hi).2
          · intro h
            exact fun i hi => ⟨h a (Or.inl rfl), h i (Or.inr hi)⟩
        rw [heq]
        exact hgc (insert a t)
          (Finset.insert_subset (Finset.mem_cons_self a s) (ht.trans (Finset.subset_cons ha)))
          (Finset.insert_nonempty a t)
      exact hasFundClass_union hKac hBc hgcInter.2 hfKa hfB

/-- **A compact charted manifold has a fundamental class on all of `M`** (Hatcher 3.27(b), manifold
level): cover `M` by finitely many chart balls (`exists_finite_chartBall_cover`), each with a
fundamental class (`hasFundClass_chartBall`); every nonempty sub-intersection is a closed compact subset
of one piece's chart source, hence `goodCompact` (`goodCompact_compact_in_chart_source`), so
`hasFundClass_biUnion` glues them into `hasFundClass (univ : Set M)`. The surjective half of the
fundamental class `[M]`. -/
theorem hasFundClass_univ {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    hasFundClass (m := m) (Set.univ : Set M) := by
  classical
  obtain ⟨s, r, hs, hr0, hrsub, hcov⟩ :=
    SingularCompactChartCover.exists_finite_chartBall_cover (m := m) (M := M)
  set K : M → Set M := fun x => (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).symm ''
    Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x x) (r x) with hK
  have hKcompact : ∀ x ∈ s, IsCompact (K x) := fun x hx =>
    (ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).continuousOn_symm.mono (hrsub x hx))
  have hKsource : ∀ x ∈ s, K x ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).source := by
    intro x hx
    rw [hK, Set.image_subset_iff]
    exact fun y hy => (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).symm_mapsTo (hrsub x hx hy)
  rw [← hcov]
  refine hasFundClass_biUnion hs K (fun t ht htne => ?_)
    (fun x hx => hasFundClass_chartBall x (hr0 x hx) (hrsub x hx))
  obtain ⟨j, hj⟩ := htne
  have hsubKj : (⋂ i ∈ t, K i) ⊆ K j := Set.biInter_subset_of_mem hj
  have hclosed : IsClosed (⋂ i ∈ t, K i) :=
    isClosed_biInter (fun i hi => (hKcompact i (ht hi)).isClosed)
  have hcompInter : IsCompact (⋂ i ∈ t, K i) :=
    (hKcompact j (ht hj)).of_isClosed_subset hclosed hsubKj
  exact ⟨hclosed, SingularGoodCompactManifold.goodCompact_compact_in_chart_source hcompInter
    (hsubKj.trans (hKsource j (ht hj)))⟩

/-! ### The fundamental class `[M]` and `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2` (Hatcher 3.26) -/

/-- **The fundamental class `[M] ∈ Hₘ₊₂(M;ℤ/2)`**: the `hasFundClass univ` witness transported from
`Hₘ₊₂(M | univ) = Hₘ₊₂(M, ∅)` to `Hₘ₊₂(M)` via `relHomologyEmptyEquiv` (across `(univ)ᶜ = ∅`). -/
noncomputable def fundamentalClass {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    Homology (TopCat.of M) (m + 2) :=
  relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)
    (relIncl (Set.compl_univ (α := ↑(TopCat.of M))).subset (m + 2)
      (hasFundClass_univ (m := m) (M := M)).choose)

/-- **`[M]` restricts to the local generator at every point** (Hatcher 3.26): `restrictHomologyToPoint x [M]
= (manifoldLocalIso x).symm 1`. Unfolds `[M]` through `relHomologyEmptyEquiv` and collapses the `relIncl`
chain to the `hasFundClass univ` witness's per-point value. -/
theorem fundamentalClass_restricts {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    restrictHomologyToPoint (X := TopCat.of M) x (m + 2) fundamentalClass
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1 := by
  rw [← (hasFundClass_univ (m := m) (M := M)).choose_spec x (Set.mem_univ x)]
  show relIncl (Set.empty_subset ({x}ᶜ : Set ↑(TopCat.of M))) (m + 2)
      ((relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm fundamentalClass)
    = relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (Set.mem_univ x))) (m + 2)
      (hasFundClass_univ (m := m) (M := M)).choose
  rw [fundamentalClass, LinearEquiv.symm_apply_apply, relIncl_trans]

/-- **The local-degree map `Φ_{x₀} : Hₘ₊₂(M) → ℤ/2`** at a basepoint, `α ↦ manifoldLocalIso x₀
(restrictHomologyToPoint x₀ α)`. A manual `LinearMap` (the `manifoldLocalIso ∘ₗ restrictHomologyToPoint`
formation hits the `{x₀}ᶜ`↔`{y|y≠x₀}` wall; the application does not). -/
noncomputable def localDegree {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    Homology (TopCat.of M) (m + 2) →ₗ[ZMod 2] ZMod 2 where
  toFun α := SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
    (restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) α)
  map_add' a b := by rw [map_add]; exact map_add _ _ _
  map_smul' c a := by rw [map_smul]; exact map_smul _ _ _

/-- **`Φ_{x₀}([M]) = 1`**: the fundamental class has local degree `1` at every basepoint
(`fundamentalClass_restricts` + `apply_symm_apply`). -/
theorem localDegree_fundamentalClass {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    localDegree (m := m) x₀ fundamentalClass = 1 := by
  show SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
      (restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) fundamentalClass) = 1
  rw [fundamentalClass_restricts, LinearEquiv.apply_symm_apply]

/-- **`Φ_{x₀}` is bijective** (Hatcher 3.26): injective by `restrictHomologyToPoint_injective` (and
`manifoldLocalIso x₀` injective), surjective since `Φ_{x₀}([M]) = 1` generates `ℤ/2`. -/
theorem localDegree_bijective {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    Function.Bijective (localDegree (m := m) x₀) := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · have hab' : SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
        (restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) a)
      = SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
        (restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) b) := hab
    have hr := (SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀).injective hab'
    have hz : restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) (a - b) = 0 := by
      rw [map_sub, hr, sub_self]
    exact sub_eq_zero.mp (restrictHomologyToPoint_injective hz)
  · exact ⟨w • fundamentalClass, by rw [map_smul, localDegree_fundamentalClass, smul_eq_mul, mul_one]⟩

/-- **`Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`** for a connected closed charted manifold (Hatcher 3.26), via the bijective
local-degree map at a basepoint `x₀`. The closed-manifold top-homology computation; the fundamental
class `[M]` is `Φ_{x₀}⁻¹ 1`. -/
noncomputable def homologyTopEquivZMod2 {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    Homology (TopCat.of M) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (localDegree (m := m) x₀) (localDegree_bijective x₀)

/-- **The fundamental class is nonzero** (`Φ_{x₀}([M]) = 1 ≠ 0`). -/
theorem fundamentalClass_ne_zero {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    fundamentalClass (m := m) (M := M) ≠ 0 := by
  intro h
  have := localDegree_fundamentalClass (m := m) x₀
  rw [h, map_zero] at this
  exact absurd this.symm (by decide)

end SKEFTHawking.SingularFundamentalClass
