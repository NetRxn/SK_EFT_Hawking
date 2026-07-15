/-
# Phase 5q.H (W-A arm 4) — two general Hatcher-3.27 bricks for the interior-slab determination `hdet`

The cylinder residual-set's `hdet` field is `determinedByPoints 5 (M × [¼,¾])` in `W = M × [0,1]`, a
manifold-WITH-boundary. The prior triage verdict named TWO gaps for this: (i) an in-tree good-compact
statement covers only *whole closed manifolds* (`goodCompact_univ`), not a **general compact subset**
of a (possibly non-compact) manifold; and (ii) the **excision transport** carrying a determination
statement from a boundaryless product interior back to `W`. Both are settled here, as GENERAL reusable
bricks (no cylinder specialisation):

* **§1 — `goodCompact_compact`**: any compact `K` in a boundaryless charted `(m+2)`-manifold `M` is
  `goodCompact (m+2) K`. Generalises `goodCompact_univ` from `univ` on a compact manifold to a compact
  SUBSET of an arbitrary charted manifold — cover `K` (compact) by finitely many chart-ball opens
  (`IsCompact.elim_finite_subcover`), each `K ∩ (chart-ball)` compact-in-a-chart-source
  (`goodCompact_compact_in_chart_source`), and combine by `goodCompact_biUnion`. This is the piece the
  old note called "in-tree good-compact covers only whole closed manifolds".

* **§2 — `determinedByPoints_of_open_excision`**: the excision transport of the degree-`(n+1)`
  determined-by-points property from an open `U ⊇ K` (as the subtype `↥U`) back to the ambient `X`. If
  the copy `Subtype.val ⁻¹' K` is determined-by-points inside `↥U`, then `K` is determined-by-points
  in `X`. Proof: the open-set excision isomorphism `openSetExcisionEquiv : Hₙ(U|K) ≅ Hₙ(X|K)` (valid
  since `K ⊆ U`) conjugates the restriction-to-point maps on the two sides — `relIncl_excisionMap` is
  exactly that naturality square, and the `{xU}ᶜ ↔ Subtype.val ⁻¹' {x}ᶜ` set-spelling seam is crossed
  once by `relIncl_injective_of_setEq` — so a class in `Hₙ(X|K)` killed at every point pulls back to a
  class in `Hₙ(U|K)` killed at every point, hence `0`.

Together these reduce the manifold-with-boundary `hdet` to the SAME determination on the boundaryless
product **interior** `M × (0,1)` — a strictly more tractable target (the good-compact machinery of §1
applies to the interior once it carries a boundaryless Euclidean charted structure, whereas NO in-tree
good-compact machinery applies to the boundary manifold `W`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularGoodCompactManifold
import SKEFTHawking.SingularGoodCompactEuclidean
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularFundamentalClassExist

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularGoodCompact
open SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.SingularGoodCompactCompactExcision

/-! ## §1. A general compact subset of a boundaryless charted manifold is `goodCompact` -/

/-- **A compact subset of a boundaryless charted `(m+2)`-manifold is `goodCompact`.** Generalises
`SingularGoodCompactManifold.goodCompact_univ` (which handles `K = univ` on a *compact* manifold) to an
arbitrary compact `K ⊆ M`: cover `K` by finitely many chart-ball opens (`IsCompact.elim_finite_subcover`),
each intersection `K ∩ (chart-ball closure)` being compact inside a single chart source
(`goodCompact_compact_in_chart_source`); every sub-intersection is a closed subset of one such piece,
hence again compact-in-a-chart-source and `goodCompact`, so `goodCompact_biUnion` assembles
`goodCompact (m+2) K`. -/
theorem goodCompact_compact {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} (hK : IsCompact K) :
    goodCompact (X := TopCat.of M) (m + 2) K := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact SingularGoodCompactEuclidean.goodCompact_empty (X := TopCat.of M) (m + 2)
  set c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 2))) :=
    fun x => chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
  have hball : ∀ x : M, ∃ r : ℝ, 0 < r ∧ Metric.closedBall ((c x) x) r ⊆ (c x).target := by
    intro x
    have hmem : (c x) x ∈ (c x).target := mem_chart_target _ x
    have hopen : IsOpen (c x).target := (c x).open_target
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨r, hr, hsub⟩ := hopen _ hmem
    exact ⟨r / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  choose r hr_pos hr_sub using hball
  set O : M → Set M := fun x => (c x).symm '' Metric.ball ((c x) x) (r x) with hO
  have hball_sub_target : ∀ x : M, Metric.ball ((c x) x) (r x) ⊆ (c x).target := fun x =>
    (Metric.ball_subset_closedBall).trans (hr_sub x)
  have hO_open : ∀ x : M, IsOpen (O x) := fun x =>
    (c x).isOpen_image_symm_of_subset_target Metric.isOpen_ball (hball_sub_target x)
  have hO_mem : ∀ x : M, x ∈ O x := fun x =>
    ⟨(c x) x, Metric.mem_ball_self (hr_pos x), (c x).left_inv (mem_chart_source _ x)⟩
  have hcover : K ⊆ ⋃ x, O x := fun y _ => Set.mem_iUnion.mpr ⟨y, hO_mem y⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO_open hcover
  set B : M → Set M := fun x => (c x).symm '' Metric.closedBall ((c x) x) (r x) with hB
  set Kp : M → Set M := fun x => K ∩ B x with hKp
  have hB_compact : ∀ x, IsCompact (B x) := fun x =>
    (isCompact_closedBall _ _).image_of_continuousOn ((c x).continuousOn_symm.mono (hr_sub x))
  have hB_source : ∀ x, B x ⊆ (c x).source := by
    intro x
    rw [hB, Set.image_subset_iff]
    exact fun y hy => (c x).symm_mapsTo (hr_sub x hy)
  have hKp_closed : ∀ x, IsClosed (Kp x) := fun x => hK.isClosed.inter (hB_compact x).isClosed
  have hOK : ∀ x, O x ⊆ B x := fun x => Set.image_mono Metric.ball_subset_closedBall
  have hcov : (⋃ x ∈ s, Kp x) = K := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun x _ => Set.inter_subset_left
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hs hy)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hy, hOK i hyi⟩
  have hs_ne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hKne
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact ⟨i, hi⟩
  rw [← hcov]
  refine goodCompact_biUnion (X := TopCat.of M) hs_ne Kp (fun t ht htne => ?_)
  obtain ⟨j, hj⟩ := htne
  have hsubKj : (⋂ x ∈ t, Kp x) ⊆ Kp j := Set.biInter_subset_of_mem hj
  have hclosed : IsClosed (⋂ x ∈ t, Kp x) :=
    isClosed_biInter (fun x _ => hKp_closed x)
  have hcompInter : IsCompact (⋂ x ∈ t, Kp x) :=
    hK.of_isClosed_subset hclosed (hsubKj.trans Set.inter_subset_left)
  exact ⟨hclosed, SingularGoodCompactManifold.goodCompact_compact_in_chart_source hcompInter
    (hsubKj.trans (Set.inter_subset_right.trans (hB_source j)))⟩

/-! ## §2. Excision transport of `determinedByPoints` from an open subset back to the ambient space -/

/-- **Excision transport of `determinedByPoints`.** For a closed `K` inside an open `U` of a `T1`
space `X`, if the copy `Subtype.val ⁻¹' K` is degree-`(n+1)` determined-by-points *inside the subtype*
`↥U`, then `K` is degree-`(n+1)` determined-by-points in `X`. The open-set excision isomorphism
`openSetExcisionEquiv : Hₙ₊₁(U|K) ≅ Hₙ₊₁(X|K)` conjugates each restriction-to-point map
(`relIncl_excisionMap` is the naturality square; the `{xU}ᶜ ↔ Subtype.val ⁻¹' {x}ᶜ` spelling seam is
crossed once by `relIncl_injective_of_setEq`), so a class in `Hₙ₊₁(X|K)` killed at every point of `K`
pulls back to a class killed at every point of `Subtype.val ⁻¹' K`, which `hdetU` forces to `0`; the
excision map then sends it to `0`, recovering the original class. -/
theorem determinedByPoints_of_open_excision {X : TopCat} [T1Space ↑X] {n : ℕ}
    {K : Set ↑X} {U : Set ↑X} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hdetU : determinedByPoints (X := sub U) (n + 1) (Subtype.val ⁻¹' K)) :
    determinedByPoints (X := X) (n + 1) K := by
  set EK := openSetExcisionEquiv hK hU hKU n with hEK
  intro α hα
  set β := EK.symm α with hβ
  have hβα : EK β = α := EK.apply_symm_apply α
  have hβ0 : β = 0 := by
    refine hdetU β (fun xU hxU => ?_)
    set x : ↑X := (xU : ↑X) with hx
    have hxK : x ∈ K := hxU
    have hxU' : x ∈ U := xU.2
    have hKxc : (Kᶜ : Set ↑X) ⊆ ({x}ᶜ : Set ↑X) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxK)
    set Ex := openSetExcisionEquiv (X := X) (K := ({x} : Set ↑X)) isClosed_singleton hU
      (Set.singleton_subset_iff.mpr hxU') n with hExdef
    -- The `{xU}ᶜ = Subtype.val ⁻¹' {x}ᶜ` set-spelling seam, both inclusions.
    have hST : ({xU} : Set ↑(sub U))ᶜ ⊆ restr ({x}ᶜ) U := by
      intro yU hyU
      simp only [restr, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyU ⊢
      exact fun hval => hyU (Subtype.ext (by rw [hval]))
    have hTS : restr ({x}ᶜ) U ⊆ ({xU} : Set ↑(sub U))ᶜ := by
      intro yU hyU
      simp only [restr, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyU ⊢
      exact fun hval => hyU (by rw [hval])
    -- The excision transport produces vanishing in the `Subtype.val ⁻¹' {x}ᶜ` spelling.
    have hzero : relIncl (Set.preimage_mono hKxc) (n + 1) β = 0 := by
      apply Ex.injective
      rw [map_zero]
      show excisionMap ({x}ᶜ) U (n + 1) (relIncl (Set.preimage_mono hKxc) (n + 1) β) = 0
      rw [← relIncl_excisionMap hKxc (n + 1) β]
      show relIncl hKxc (n + 1) (excisionMap Kᶜ U (n + 1) β) = 0
      rw [show excisionMap Kᶜ U (n + 1) β = α from hβα]
      exact hα x hxK
    -- Cross the spelling seam: `restrictToPoint hxU β = 0`.
    refine relIncl_injective_of_setEq hST hTS (n + 1) ?_
    rw [map_zero]
    show relIncl hST (n + 1) (relIncl _ (n + 1) β) = 0
    rw [relIncl_trans]
    exact hzero
  rw [← hβα, hβ0, map_zero]

end SKEFTHawking.SingularGoodCompactCompactExcision
