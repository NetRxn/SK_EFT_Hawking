import Mathlib
import SKEFTHawking.SingularSubHomSumEnd
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularPDWindow

/-!
# Phase 5q.G (G1 (1,2)-window extension, X4) — `H₀` of a closed charted manifold is
finite-dimensional

`H₀(Y)` is spanned by point classes (`h0Class` of constant simplices), and joined points give
equal classes (the path simplex bounds their difference). A compact charted manifold is covered
by finitely many chart-ball pullbacks, each path-connected (the `chartSubHomeo` transport of a
convex ball), so finitely many point classes span — `H₀` is finite-dimensional. The `H⁰/H⁴`
findim input of the `PoincareDual4Mid/Lo` instances.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularSubHomSumEnd SKEFTHawking.SingularH0PathConnected
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularCapHomology SKEFTHawking.SingularPDWindow

namespace SKEFTHawking.SingularH0Finite

/-- **Joined points have equal point classes**: the path simplex bounds their difference. -/
theorem h0Class_single_eq_of_joined {Y : TopCat} {b x : ↑Y} (h : Joined b x) :
    h0Class Y (Finsupp.single (constSimplex b 0) 1)
      = h0Class Y (Finsupp.single (constSimplex x 0) 1) := by
  obtain ⟨p⟩ := h
  have hbd : h0Class Y (Finsupp.single (constSimplex x 0) 1
      + Finsupp.single (constSimplex b 0) 1) = 0 := by
    rw [h0Class]
    rw [SKEFTHawking.SingularCapHomology.Homology.mk_eq_zero]
    refine Submodule.mem_comap.mpr ?_
    exact ⟨Finsupp.single (pathSimplex p) 1, chainBoundary_pathSimplex p⟩
  have hadd := h0Class_add Y (Finsupp.single (constSimplex x 0) 1)
    (Finsupp.single (constSimplex b 0) 1)
  rw [hbd] at hadd
  rw [← zero_add (h0Class Y (Finsupp.single (constSimplex b 0) 1)),
    ← ZModModule.add_self (h0Class Y (Finsupp.single (constSimplex x 0) 1)),
    add_assoc, show h0Class Y (Finsupp.single (constSimplex x 0) 1)
      + h0Class Y (Finsupp.single (constSimplex b 0) 1) = 0 from hadd.symm, add_zero]

/-- **The point classes of a joined-cover span**: every `h0Class` lies in the span of the cover's
base-point classes. -/
theorem h0Class_mem_span {Y : TopCat} {ι : Type*} (t : Finset ι) (p : ι → ↑Y)
    (hcov : ∀ x : ↑Y, ∃ i ∈ t, Joined x (p i)) (c : SingularChain Y 0) :
    h0Class Y c ∈ Submodule.span (ZMod 2)
      ((fun i => h0Class Y (Finsupp.single (constSimplex (p i) 0) 1)) '' ↑t) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [h0Class_zero]; exact Submodule.zero_mem _
  | add c d hc hd => rw [h0Class_add]; exact Submodule.add_mem _ hc hd
  | single σ a =>
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha
    · rw [ha, Finsupp.single_zero, h0Class_zero]
      exact Submodule.zero_mem _
    · rw [ha]
      obtain ⟨i, hit, hji⟩ := hcov (simplexPoint σ)
      have hσ : σ = constSimplex (simplexPoint σ) 0 := eq_constSimplex σ
      rw [hσ, h0Class_single_eq_of_joined hji]
      exact Submodule.subset_span ⟨i, hit, rfl⟩

/-- **`H₀` is finite-dimensional from a finite joined-cover.** -/
theorem finiteDimensional_h0_of_cover {Y : TopCat} {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (p : ι → ↑Y) (hcov : ∀ x : ↑Y, ∃ i ∈ t, Joined x (p i)) :
    FiniteDimensional (ZMod 2) (Homology Y 0) := by
  classical
  refine ⟨⟨t.image (fun i => h0Class Y (Finsupp.single (constSimplex (p i) 0) 1)), ?_⟩⟩
  rw [Finset.coe_image]
  refine eq_top_iff.mpr (fun y _ => ?_)
  obtain ⟨c, rfl⟩ := h0Class_surjective Y y
  exact h0Class_mem_span t p hcov c

open SKEFTHawking.SingularConvexSubAcyclic in
/-- **X4: `H₀` of a closed charted 4-manifold is finite-dimensional** — finitely many chart-ball
pullbacks cover, each path-connected by the `chartSubHomeo` transport of the ball. -/
theorem finiteDimensional_h0 {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 0) := by
  classical
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  haveI : CompactSpace ↑(TopCat.of M) := inferInstanceAs (CompactSpace M)
  -- the chart-ball pullback around each point
  have hball : ∀ x : M, ∃ ε > 0, Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) ε
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).target :=
    fun x => Metric.isOpen_iff.mp (chartAt _ x).open_target _ (mem_chart_target _ x)
  choose ε hε hballT using hball
  set Wx : M → Set ↑(TopCat.of M) := fun x =>
    chartPull (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x)) with hWxdef
  have hWopen : ∀ x, IsOpen (Wx x) := fun x =>
    chartPull_isOpen (chartAt _ x).open_source _ Metric.isOpen_ball
  have hWmem : ∀ x : M, x ∈ Wx x := by
    intro x
    have := (mem_chartPull
      (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x))
      ⟨x, mem_chart_source _ x⟩).mpr
    refine this ?_
    show ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      ⟨x, mem_chart_source _ x⟩ : EuclideanSpace ℝ (Fin (2 + 2)))
      ∈ Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x)
    rw [show ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
        ⟨x, mem_chart_source _ x⟩ : EuclideanSpace ℝ (Fin (2 + 2)))
      = chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x from rfl]
    exact Metric.mem_ball_self (hε x)
  -- each pullback is path-connected (transported from the ball)
  have hWjoin : ∀ (x : M) (y : ↑(TopCat.of M)), y ∈ Wx x → Joined y (x : ↑(TopCat.of M)) := by
    intro x y hy
    haveI hpcsB : PathConnectedSpace ↥(sub (X := SingularEuclideanAcyclic.Eucl (2 + 2))
        (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x))) :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_ball _ _).isPathConnected ⟨_, Metric.mem_ball_self (hε x)⟩)
    haveI hpcsW : PathConnectedSpace ↥(sub (X := TopCat.of M) (Wx x)) := by
      have φ := chartSubHomeo (M := TopCat.of M)
        (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
        (hballT x) (chartPull_subset _ _)
        (fun u => mem_chartPull _ _ u)
      exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous
    have hj := PathConnectedSpace.joined
      (⟨y, hy⟩ : ↥(sub (X := TopCat.of M) (Wx x)))
      (⟨x, hWmem x⟩ : ↥(sub (X := TopCat.of M) (Wx x)))
    exact ⟨hj.some.map continuous_subtype_val⟩
  -- finite subcover
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := ↑(TopCat.of M)))
    Wx hWopen (fun y _ => Set.mem_iUnion.mpr ⟨y, hWmem y⟩)
  refine finiteDimensional_h0_of_cover t (fun x => (x : ↑(TopCat.of M))) (fun y => ?_)
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact ⟨x, hxt, hWjoin x y hyx⟩

end SKEFTHawking.SingularH0Finite
