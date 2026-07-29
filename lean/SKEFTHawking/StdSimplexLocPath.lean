import Mathlib

/-!
# Phase 5q.G (B-arc, M2-b prelude) — the standard simplex is simply connected and locally
path-connected

The two instances `existsUnique_continuousMap_lifts` needs of its domain, for the singular
simplices of the Smith-sequence transfer: `Δⁿ` is **contractible** (convex, nonempty — hence
`SimplyConnectedSpace` by the priority instance) and **locally path-connected** (the metric-ball
neighborhood basis pulls back to convex-intersection sets, path-connected by `preimage_coe`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric

namespace SKEFTHawking.StdSimplexLocPath

instance instContractibleStdSimplex (n : ℕ) :
    ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    (Set.nonempty_coe_sort.mp inferInstance)

example (n : ℕ) : SimplyConnectedSpace (stdSimplex ℝ (Fin (n + 1))) := inferInstance

/-- **The standard simplex is locally path-connected**: the metric-ball basis of the subtype
consists of preimages of convex intersections. -/
instance instLocPathConnectedStdSimplex (n : ℕ) :
    LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) := by
  refine LocallyPathConnectedSpace.of_bases
    (p := fun _ (ε : ℝ) => 0 < ε)
    (s := fun x ε => Subtype.val ⁻¹' Metric.ball (x : Fin (n + 1) → ℝ) ε)
    (fun x => ?_) (fun x ε hε => ?_)
  · -- the pulled-back ball basis is the subtype's neighborhood basis
    have h := Metric.nhds_basis_ball (α := ↥(stdSimplex ℝ (Fin (n + 1)))) (x := x)
    refine h.congr (fun ε => Iff.rfl) (fun ε hε => ?_)
    ext y
    exact Iff.rfl
  · -- each pulled-back ball is path-connected: it is the coe-preimage of ball ∩ simplex
    have hW : IsPathConnected
        (Metric.ball (x : Fin (n + 1) → ℝ) ε ∩ stdSimplex ℝ (Fin (n + 1))) :=
      ((convex_ball _ _).inter (convex_stdSimplex ℝ (Fin (n + 1)))).isPathConnected
        ⟨x, Metric.mem_ball_self hε, x.2⟩
    have hsub : Metric.ball (x : Fin (n + 1) → ℝ) ε ∩ stdSimplex ℝ (Fin (n + 1))
        ⊆ stdSimplex ℝ (Fin (n + 1)) := Set.inter_subset_right
    have h2 := hW.preimage_coe hsub
    have heq : (Subtype.val ⁻¹' (Metric.ball (x : Fin (n + 1) → ℝ) ε ∩ stdSimplex ℝ (Fin (n + 1)))
        : Set ↥(stdSimplex ℝ (Fin (n + 1))))
        = Subtype.val ⁻¹' Metric.ball (x : Fin (n + 1) → ℝ) ε := by
      ext y
      simp
    rwa [heq] at h2

end SKEFTHawking.StdSimplexLocPath
