import Mathlib
import SKEFTHawking.RP2SmithCochain

/-!
# Phase 5q.G (B-arc, M3-h) — the projection formula of the cochain Smith transfer

**`τ^#(π^#a ⌣ y) = a ⌣ τ^#y` on the nose at cochain level.** The Alexander–Whitney front
factor of a pulled-back cochain sees only the base (`π(front(σ±)) = front σ` by
front-face naturality), and the back faces of the two lifts are exactly the two lifts of the
back face (membership through the pushforward pair + distinctness through covering uniqueness
at the back-embedded barycenter). This makes the cohomological Smith connecting `δS` a
`H^*(ℝP²)`-module map (M3-i) — the engine that turns the ladder `δSᵏ(1)` into cup powers.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP2PointSet SKEFTHawking.RP2Transfer SKEFTHawking.RP2SmithCochain
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality

namespace SKEFTHawking.RP2ProjectionFormula

/-- The realization of the back face is the realization precomposed with the topological back
inclusion — `toSSetObjEquiv`-naturality (`rfl`, as for `toSSetObjEquiv_face`). -/
theorem toSSetObjEquiv_backFace {X : TopCat} {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    X.toSSetObjEquiv (op (SimplexCategory.mk q)) (backFace σ)
      = (X.toSSetObjEquiv (op (SimplexCategory.mk (p + q))) σ).comp
          ⟨_root_.stdSimplex.map (backIncl p q),
            _root_.stdSimplex.continuous_map (backIncl p q)⟩ :=
  rfl

/-- **The back faces of the two lifts are distinct**: were they equal, the two lifts would agree
at the back-embedded barycenter, forcing them equal by covering uniqueness. -/
theorem backFace_liftPlus_ne_backFace_liftMinus {p q : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (p := p) (liftPlus σ) ≠ backFace (p := p) (liftMinus σ) := by
  intro h
  refine liftPlus_ne_liftMinus σ ?_
  refine liftSimplex_eq_of_agree (liftPlus σ) (liftMinus σ)
    (by rw [mapSimplex_liftPlus, mapSimplex_liftMinus])
    ((⟨_root_.stdSimplex.map (backIncl p q),
      _root_.stdSimplex.continuous_map (backIncl p q)⟩ :
        C(stdSimplex ℝ (Fin (q + 1)), stdSimplex ℝ (Fin (p + q + 1)))) (bary q)) ?_
  have h2 := congrArg ((TopCat.of S2).toSSetObjEquiv (op (SimplexCategory.mk q))) h
  rw [toSSetObjEquiv_backFace, toSSetObjEquiv_backFace] at h2
  exact congrFun (congrArg DFunLike.coe h2) (bary q)

/-- **The back face of a lift is a lift of the back face** — membership in the pushforward
pair, through back-face naturality. -/
theorem backFace_lift_mem_pair {p q : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q))))
    (τ : (TopCat.toSSet.obj (TopCat.of S2)).obj (op (SimplexCategory.mk (p + q))))
    (hτ : mapSimplex mkC τ = σ) :
    backFace (p := p) τ = liftPlus (backFace σ)
      ∨ backFace (p := p) τ = liftMinus (backFace σ) := by
  have h := mem_pair_of_pushforward (backFace (p := p) τ)
  rwa [show mapSimplex mkC (backFace (p := p) τ) = backFace σ from by
    rw [← backFace_mapSimplex, hτ]] at h

/-- **The back-pair value identity**: any cochain sums equally over the back faces of the two
lifts and the two lifts of the back face. -/
theorem backFace_pair_value {p q : ℕ} (y : SingularCochain (TopCat.of S2) q)
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q)))) :
    y (backFace (liftPlus σ)) + y (backFace (liftMinus σ))
      = y (liftPlus (backFace (p := p) σ)) + y (liftMinus (backFace (p := p) σ)) := by
  rcases backFace_lift_mem_pair σ (liftPlus σ) (mapSimplex_liftPlus σ) with h1 | h1 <;>
    rcases backFace_lift_mem_pair σ (liftMinus σ) (mapSimplex_liftMinus σ) with h2 | h2
  · exact absurd (h1.trans h2.symm) (backFace_liftPlus_ne_backFace_liftMinus σ)
  · rw [h1, h2]
  · rw [h1, h2]
    exact add_comm _ _
  · exact absurd (h1.trans h2.symm) (backFace_liftPlus_ne_backFace_liftMinus σ)

/-- The front factor of a pulled-back cochain on a lift sees only the base:
`(π^#a)(front(τ)) = a(front σ)` for any lift `τ` of `σ`. -/
theorem cochainPullback_frontFace_lift {p q : ℕ}
    (a : SingularCochain (TopCat.of RP2) p)
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q))))
    (τ : (TopCat.toSSet.obj (TopCat.of S2)).obj (op (SimplexCategory.mk (p + q))))
    (hτ : mapSimplex mkC τ = σ) :
    cochainPullback mkC p a (frontFace (q := q) τ) = a (frontFace σ) := by
  rw [cochainPullback_apply, ← frontFace_mapSimplex, hτ]

/-- **THE PROJECTION FORMULA**: `τ^#(π^#a ⌣ y) = a ⌣ τ^#y` — exactly, at the cochain level. -/
theorem cochainTransfer_cup_pullback {p q : ℕ}
    (a : SingularCochain (TopCat.of RP2) p) (y : SingularCochain (TopCat.of S2) q) :
    cochainTransfer (p + q) (cup (cochainPullback mkC p a) y)
      = cup a (cochainTransfer q y) := by
  funext σ
  show cup (cochainPullback mkC p a) y (liftPlus σ)
      + cup (cochainPullback mkC p a) y (liftMinus σ)
    = cup a (cochainTransfer q y) σ
  rw [cup_apply, cup_apply, cup_apply,
    cochainPullback_frontFace_lift a σ (liftPlus σ) (mapSimplex_liftPlus σ),
    cochainPullback_frontFace_lift a σ (liftMinus σ) (mapSimplex_liftMinus σ),
    ← mul_add, backFace_pair_value y σ, cochainTransfer_apply]

end SKEFTHawking.RP2ProjectionFormula
