import Mathlib
import SKEFTHawking.SingularWuTransport
import SKEFTHawking.SingularCochainGlue
import SKEFTHawking.SingularFundamentalClassSum

/-!
# Phase 5q.G (G3 F-ladder, F7d — the final rung) — the Wu class ⊔-splits and the certificate iff

On the genuine PD instances of a disjoint union of closed charted 4-manifolds:

* **μ-additivity** (`mu_sum`): `μ_{M⊕N}(ω) = μ_M(inl*ω) + μ_N(inr*ω)` — F7c's
  `[M⊕N] = inl₊[M] + inr₊[N]` through the F3 Kronecker adjunction;
* **Wu-class splits** (`wuClass2_sum_inl/…`): `inl*(v₂(M⊕N)) = v₂(M)` etc. — the F6a uniqueness
  route with the *glued* test class `y := glue(x, 0)` (`exists_glue_class`), whose `inr`-component
  vanishes so every cross-term dies (`cup` with `0`, `Sq¹ 0 = 0`);
* **`w₂` splits** (`wuW2_sum_inl/inr`) and the consumer-facing certificate criterion
  (`wuW2_sum_eq_zero_iff`): `w₂(M⊕N) = 0 ↔ w₂(M) = 0 ∧ w₂(N) = 0` — the ⊔-transport of the
  `PinPlusCert`, closing the F-ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularFundamentalClassPushforward
open SKEFTHawking.PoincareDualityConstruct SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances SKEFTHawking.SingularWuTransport
open SKEFTHawking.SingularCochainGlue SKEFTHawking.SingularFundamentalClassSum

namespace SKEFTHawking.SingularWuSum

/-- `Sq¹`-pullback naturality at the literal `H³ → H⁴` spelling, for an arbitrary map (the
φ-generic form of `SingularWuTransport.sq1_pullback`). -/
theorem sq1_pullback_map {X Y : TopCat} (φ : C(↑X, ↑Y)) (w : Cohomology Y 3) :
    cohomologyPullback φ 4 (SKEFTHawking.SingularBockstein.Sq1 (n := 2) w)
      = SKEFTHawking.SingularBockstein.Sq1 (n := 2) (cohomologyPullback φ 3 w) :=
  Sq1_cohomologyPullback φ w

variable {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N]

/-- **μ-additivity over the disjoint union**: `μ_{M⊕N}(ω) = μ_M(inl*ω) + μ_N(inr*ω)` — the F7c
fundamental-class sum through the F3 Kronecker adjunction. -/
theorem mu_sum (w : Cohomology (TopCat.of (M ⊕ N)) 4) :
    (poincareDual4Mid_of_closed (M := M ⊕ N)).mu w
      = (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4 w)
        + (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4 w) := by
  show kroneckerH (X := TopCat.of (M ⊕ N)) (2 + 2) w (fundamentalClass (m := 2) (M := M ⊕ N))
    = kroneckerH (X := TopCat.of M) (2 + 2) (cohomologyPullback (inlC M N) (2 + 2) w)
        (fundamentalClass (m := 2) (M := M))
      + kroneckerH (X := TopCat.of N) (2 + 2) (cohomologyPullback (inrC M N) (2 + 2) w)
        (fundamentalClass (m := 2) (M := N))
  rw [kroneckerH_cohomologyPullback, kroneckerH_cohomologyPullback, ← map_add,
    ← fundamentalClass_sum (m := 2)]

/-- The `M`-component extraction (char-2 rearrangement of `mu_sum`):
`μ_M(inl*ω) = μ_{M⊕N}(ω) + μ_N(inr*ω)`. -/
theorem mu_comp_inl (w : Cohomology (TopCat.of (M ⊕ N)) 4) :
    (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4 w)
      = (poincareDual4Mid_of_closed (M := M ⊕ N)).mu w
        + (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4 w) := by
  rw [mu_sum w, add_assoc, ZModModule.add_self, add_zero]

/-- The `N`-component extraction: `μ_N(inr*ω) = μ_{M⊕N}(ω) + μ_M(inl*ω)`. -/
theorem mu_comp_inr (w : Cohomology (TopCat.of (M ⊕ N)) 4) :
    (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4 w)
      = (poincareDual4Mid_of_closed (M := M ⊕ N)).mu w
        + (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4 w) := by
  rw [mu_sum w, add_comm ((poincareDual4Mid_of_closed (M := M)).mu _), add_assoc,
    ZModModule.add_self, add_zero]

/-- **The middle Wu class splits, `inl`-side**: `inl*(v₂(M⊕N)) = v₂(M)` — uniqueness with the
glued test class `glue(x, 0)`; all `inr`-cross-terms vanish. -/
theorem wuClass2_sum_inl :
    cohomologyPullback (inlC M N) 2 (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N)))
      = wuClass2 (poincareDual4Mid_of_closed (M := M)) := by
  apply (pairing_bijective (poincareDual4Mid_of_closed (M := M))).1
  have hR : pairing (poincareDual4Mid_of_closed (M := M))
      (wuClass2 (poincareDual4Mid_of_closed (M := M)))
      = wuFunctional (poincareDual4Mid_of_closed (M := M)) :=
    LinearMap.ext (wu_relation (poincareDual4Mid_of_closed (M := M)))
  rw [hR]
  ext x
  obtain ⟨y, hy_inl, hy_inr⟩ := exists_glue_class (M := M) (N := N) 2 x 0
  rw [← hy_inl]
  show (poincareDual4Mid_of_closed (M := M)).mu
      (cupH24
        (cohomologyPullback (inlC M N) 2 (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N))))
        (cohomologyPullback (inlC M N) 2 y))
    = (poincareDual4Mid_of_closed (M := M)).mu
      (cupH24 (cohomologyPullback (inlC M N) 2 y) (cohomologyPullback (inlC M N) 2 y))
  rw [← cohomologyPullback_cupH24, ← cohomologyPullback_cupH24, mu_comp_inl, mu_comp_inl,
    cohomologyPullback_cupH24, cohomologyPullback_cupH24, hy_inr,
    map_zero (cupH24 (cohomologyPullback (inrC M N) 2
      (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N))))),
    map_zero (cupH24 (0 : Cohomology (TopCat.of N) 2)), map_zero, add_zero, add_zero]
  exact wu_relation (poincareDual4Mid_of_closed (M := M ⊕ N)) y

/-- **The middle Wu class splits, `inr`-side**: `inr*(v₂(M⊕N)) = v₂(N)`. -/
theorem wuClass2_sum_inr :
    cohomologyPullback (inrC M N) 2 (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N)))
      = wuClass2 (poincareDual4Mid_of_closed (M := N)) := by
  apply (pairing_bijective (poincareDual4Mid_of_closed (M := N))).1
  have hR : pairing (poincareDual4Mid_of_closed (M := N))
      (wuClass2 (poincareDual4Mid_of_closed (M := N)))
      = wuFunctional (poincareDual4Mid_of_closed (M := N)) :=
    LinearMap.ext (wu_relation (poincareDual4Mid_of_closed (M := N)))
  rw [hR]
  ext x
  obtain ⟨y, hy_inl, hy_inr⟩ := exists_glue_class (M := M) (N := N) 2 0 x
  rw [← hy_inr]
  show (poincareDual4Mid_of_closed (M := N)).mu
      (cupH24
        (cohomologyPullback (inrC M N) 2 (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N))))
        (cohomologyPullback (inrC M N) 2 y))
    = (poincareDual4Mid_of_closed (M := N)).mu
      (cupH24 (cohomologyPullback (inrC M N) 2 y) (cohomologyPullback (inrC M N) 2 y))
  rw [← cohomologyPullback_cupH24, ← cohomologyPullback_cupH24, mu_comp_inr, mu_comp_inr,
    cohomologyPullback_cupH24, cohomologyPullback_cupH24, hy_inl,
    map_zero (cupH24 (cohomologyPullback (inlC M N) 2
      (wuClass2 (poincareDual4Mid_of_closed (M := M ⊕ N))))),
    map_zero (cupH24 (0 : Cohomology (TopCat.of M) 2)), map_zero, add_zero, add_zero]
  exact wu_relation (poincareDual4Mid_of_closed (M := M ⊕ N)) y

/-- **The first Wu class splits, `inl`-side**: `inl*(v₁(M⊕N)) = v₁(M)` — the `(1,3)` mirror;
the Bockstein side uses `Sq1_cohomologyPullback` (φ-generic) + `Sq¹ 0 = 0`. -/
theorem wuClass1_sum_inl :
    cohomologyPullback (inlC M N) 1 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N)))
      = wuClass1 (poincareDual4Lo_of_closed (M := M)) := by
  apply (pairing13_bijective (poincareDual4Lo_of_closed (M := M))).1
  have hR : pairing13 (poincareDual4Lo_of_closed (M := M))
      (wuClass1 (poincareDual4Lo_of_closed (M := M)))
      = wuFunctional1 (poincareDual4Lo_of_closed (M := M)) :=
    LinearMap.ext (wu_relation_v1 (poincareDual4Lo_of_closed (M := M)))
  rw [hR]
  ext x
  obtain ⟨y, hy_inl, hy_inr⟩ := exists_glue_class (M := M) (N := N) 3 x 0
  rw [← hy_inl]
  show (poincareDual4Lo_of_closed (M := M)).mu
      (cupH13
        (cohomologyPullback (inlC M N) 1 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))))
        (cohomologyPullback (inlC M N) 3 y))
    = (poincareDual4Lo_of_closed (M := M)).mu
      (SKEFTHawking.SingularBockstein.Sq1 (n := 2) (cohomologyPullback (inlC M N) 3 y))
  rw [← cohomologyPullback_cupH13, ← sq1_pullback_map (inlC M N)]
  show (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4
      (cupH13 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))) y))
    = (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4
      (SKEFTHawking.SingularBockstein.Sq1 (n := 2) y))
  rw [mu_comp_inl, mu_comp_inl, cohomologyPullback_cupH13, sq1_pullback_map (inrC M N), hy_inr,
    map_zero (cupH13 (cohomologyPullback (inrC M N) 1
      (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))))),
    map_zero (SKEFTHawking.SingularBockstein.Sq1 (n := 2) (X := TopCat.of N)),
    map_zero, add_zero, add_zero]
  exact wu_relation_v1 (poincareDual4Lo_of_closed (M := M ⊕ N)) y

/-- **The first Wu class splits, `inr`-side**: `inr*(v₁(M⊕N)) = v₁(N)`. -/
theorem wuClass1_sum_inr :
    cohomologyPullback (inrC M N) 1 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N)))
      = wuClass1 (poincareDual4Lo_of_closed (M := N)) := by
  apply (pairing13_bijective (poincareDual4Lo_of_closed (M := N))).1
  have hR : pairing13 (poincareDual4Lo_of_closed (M := N))
      (wuClass1 (poincareDual4Lo_of_closed (M := N)))
      = wuFunctional1 (poincareDual4Lo_of_closed (M := N)) :=
    LinearMap.ext (wu_relation_v1 (poincareDual4Lo_of_closed (M := N)))
  rw [hR]
  ext x
  obtain ⟨y, hy_inl, hy_inr⟩ := exists_glue_class (M := M) (N := N) 3 0 x
  rw [← hy_inr]
  show (poincareDual4Lo_of_closed (M := N)).mu
      (cupH13
        (cohomologyPullback (inrC M N) 1 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))))
        (cohomologyPullback (inrC M N) 3 y))
    = (poincareDual4Lo_of_closed (M := N)).mu
      (SKEFTHawking.SingularBockstein.Sq1 (n := 2) (cohomologyPullback (inrC M N) 3 y))
  rw [← cohomologyPullback_cupH13, ← sq1_pullback_map (inrC M N)]
  show (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4
      (cupH13 (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))) y))
    = (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4
      (SKEFTHawking.SingularBockstein.Sq1 (n := 2) y))
  rw [mu_comp_inr, mu_comp_inr, cohomologyPullback_cupH13, sq1_pullback_map (inlC M N), hy_inl,
    map_zero (cupH13 (cohomologyPullback (inlC M N) 1
      (wuClass1 (poincareDual4Lo_of_closed (M := M ⊕ N))))),
    map_zero (SKEFTHawking.SingularBockstein.Sq1 (n := 2) (X := TopCat.of M)),
    map_zero, add_zero, add_zero]
  exact wu_relation_v1 (poincareDual4Lo_of_closed (M := M ⊕ N)) y

/-- **`w₂` splits, `inl`-side**: `inl*(w₂(M⊕N)) = w₂(M)` (componentwise `v₂ + v₁²`). -/
theorem wuW2_sum_inl :
    cohomologyPullback (inlC M N) 2
        (wuW2 (poincareDual4Mid_of_closed (M := M ⊕ N)) (poincareDual4Lo_of_closed (M := M ⊕ N)))
      = wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) := by
  rw [wuW2_eq, wuW2_eq, map_add, wuClass2_sum_inl, cohomologyPullback_cupH, wuClass1_sum_inl]

/-- **`w₂` splits, `inr`-side**: `inr*(w₂(M⊕N)) = w₂(N)`. -/
theorem wuW2_sum_inr :
    cohomologyPullback (inrC M N) 2
        (wuW2 (poincareDual4Mid_of_closed (M := M ⊕ N)) (poincareDual4Lo_of_closed (M := M ⊕ N)))
      = wuW2 (poincareDual4Mid_of_closed (M := N)) (poincareDual4Lo_of_closed (M := N)) := by
  rw [wuW2_eq, wuW2_eq, map_add, wuClass2_sum_inr, cohomologyPullback_cupH, wuClass1_sum_inr]

/-- **F7d apex — the certificate ⊔-criterion**: `w₂(M ⊕ N) = 0 ↔ w₂(M) = 0 ∧ w₂(N) = 0` — the
`PinPlusCert` transport for the disjoint-union op, closing the F-ladder. -/
theorem wuW2_sum_eq_zero_iff :
    wuW2 (poincareDual4Mid_of_closed (M := M ⊕ N)) (poincareDual4Lo_of_closed (M := M ⊕ N)) = 0
      ↔ (wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) = 0
        ∧ wuW2 (poincareDual4Mid_of_closed (M := N)) (poincareDual4Lo_of_closed (M := N)) = 0) := by
  constructor
  · intro h
    exact ⟨by rw [← wuW2_sum_inl (M := M) (N := N), h, map_zero],
      by rw [← wuW2_sum_inr (M := M) (N := N), h, map_zero]⟩
  · rintro ⟨hM, hN⟩
    exact eq_zero_of_pullbacks_zero 2 _ (by rw [wuW2_sum_inl, hM]) (by rw [wuW2_sum_inr, hN])

end SKEFTHawking.SingularWuSum
