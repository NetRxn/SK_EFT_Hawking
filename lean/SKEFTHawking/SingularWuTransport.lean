import Mathlib
import SKEFTHawking.SingularFundamentalClassPushforward
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.SingularPD4Instances

/-!
# Phase 5q.G (G3 F-ladder, F5 + F6a) — the Wu data transport along homeomorphisms

**F5**: the fundamental-class functional transports — `μ_M(e*ω) = μ_N(ω)` (the F3 Kronecker
adjunction + the F4 pushforward `Hₘ₊₂(e)[M] = [N]`).

**F6a**: the middle Wu class transports — `e*(v₂(N)) = v₂(M)` on the GENUINE PD instances
(`poincareDual4Mid_of_closed`), via the uniqueness characterization: `v₂` is the unique class
whose pairing equals the Wu functional (`pairing_bijective`), and the pulled-back class satisfies
the defining relation because every `x ∈ H²(M)` is a pullback (`cohomologyHomeoEquiv` surjective),
cup commutes with pullback (F2), and μ transports (F5).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularFundamentalClassPushforward
open SKEFTHawking.PoincareDualityConstruct SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances

namespace SKEFTHawking.SingularWuTransport

variable {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N]

/-- **F5 — the fundamental-class functional transports**: `μ_M(e*ω) = μ_N(ω)` — the F3 Kronecker
adjunction turns the pullback into a pushforward on `[M]`, and F4 identifies `e₊[M] = [N]`. -/
theorem fundamentalFunctional_pullback (e : M ≃ₜ N) (ω : Cohomology (TopCat.of N) (2 + 2)) :
    fundamentalFunctional (m := 2) (M := M)
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) (2 + 2) ω)
      = fundamentalFunctional (m := 2) (M := N) ω := by
  show kroneckerH (X := TopCat.of M) (2 + 2)
      (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) (2 + 2) ω)
      (fundamentalClass (m := 2) (M := M))
    = kroneckerH (X := TopCat.of N) (2 + 2) ω (fundamentalClass (m := 2) (M := N))
  rw [kroneckerH_cohomologyPullback, fundamentalClass_map_homeo e]

/-- F5 at the `.mu` field of the genuine `PoincareDual4Mid` instance (degree-4 spelling). -/
theorem mu_pullback (e : M ≃ₜ N) (w : Cohomology (TopCat.of N) 4) :
    (poincareDual4Mid_of_closed (M := M)).mu
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 4 w)
      = (poincareDual4Mid_of_closed (M := N)).mu w :=
  fundamentalFunctional_pullback e w

/-- **F6a — the middle Wu class transports**: `e*(v₂(N)) = v₂(M)` on the genuine PD data. The
pulled-back class satisfies the defining Wu relation on `M` (every test class is a pullback;
F2 + F5 + the `N`-relation), so uniqueness (`pairing_bijective`) identifies it with `v₂(M)`. -/
theorem wuClass2_pullback (e : M ≃ₜ N) :
    cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2
        (wuClass2 (poincareDual4Mid_of_closed (M := N)))
      = wuClass2 (poincareDual4Mid_of_closed (M := M)) := by
  apply (pairing_bijective (poincareDual4Mid_of_closed (M := M))).1
  have hR : pairing (poincareDual4Mid_of_closed (M := M))
      (wuClass2 (poincareDual4Mid_of_closed (M := M)))
      = wuFunctional (poincareDual4Mid_of_closed (M := M)) :=
    LinearMap.ext (wu_relation (poincareDual4Mid_of_closed (M := M)))
  rw [hR]
  ext x
  obtain ⟨y, rfl⟩ := (cohomologyHomeoEquiv (X := TopCat.of M) (Y := TopCat.of N) e 2).surjective x
  show (poincareDual4Mid_of_closed (M := M)).mu
      (cupH24
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2
          (wuClass2 (poincareDual4Mid_of_closed (M := N))))
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2 y))
    = (poincareDual4Mid_of_closed (M := M)).mu
      (cupH24
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2 y)
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2 y))
  rw [← cohomologyPullback_cupH24, ← cohomologyPullback_cupH24, mu_pullback e, mu_pullback e]
  exact wu_relation (poincareDual4Mid_of_closed (M := N)) y

/-! ## F6b step 1 — Sq¹-pullback naturality (the Bockstein is a stable operation) -/

section Sq1Naturality

open CategoryTheory Opposite SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularBockstein

/-- **The signed ℤ/4 coboundary of the lift commutes with the pullback** — pointwise:
`lift (φ*a) = (lift a) ∘ φ₊` on simplices (`rfl`) + face-naturality (`face_mapSimplex`). -/
theorem coboundary4_lift_cochainPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochain Y n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    coboundary4 X n (lift (cochainPullback φ n a)) σ
      = coboundary4 Y n (lift a) (mapSimplex φ σ) := by
  show (∑ i : Fin (n + 2), (-1 : ZMod 4) ^ (i : ℕ) * lift (cochainPullback φ n a) (face i σ))
    = ∑ i : Fin (n + 2), (-1 : ZMod 4) ^ (i : ℕ) * lift a (face i (mapSimplex φ σ))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [face_mapSimplex]
  rfl

/-- **`Sq¹` is natural on cochains**: `Sq1cochain (φ*a) = φ*(Sq1cochain a)`. -/
theorem Sq1cochain_cochainPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (a : SingularCochain Y n) :
    Sq1cochain (cochainPullback φ n a) = cochainPullback φ (n + 1) (Sq1cochain a) := by
  funext σ
  show half (coboundary4 X n (lift (cochainPullback φ n a)) σ)
    = half (coboundary4 Y n (lift a) (mapSimplex φ σ))
  rw [coboundary4_lift_cochainPullback]

/-- `cohomologyPullback_mk` restated at the `Submodule.Quotient.mk` spelling (the one `Sq1_apply`
produces), so the `Sq¹`-naturality rewrite chain stays fully syntactic. -/
theorem cohomologyPullback_quotient_mk {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ Y n)) :
    cohomologyPullback φ n (Submodule.Quotient.mk a)
      = Submodule.Quotient.mk ⟨cochainPullback φ n a.1, cochainPullback_mem_ker φ a⟩ :=
  cohomologyPullback_mk φ n a

/-- **`Sq¹` is natural on cohomology**: `φ*(Sq¹ w) = Sq¹(φ* w)` — the Bockstein commutes with
the pullback (a stable cohomology operation). The one new ingredient of the `v₁`-transport. -/
theorem Sq1_cohomologyPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) {m : ℕ}
    (w : Cohomology Y (m + 1)) :
    cohomologyPullback φ (m + 1 + 1) (Sq1 w) = Sq1 (cohomologyPullback φ (m + 1) w) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [Sq1_apply, cohomologyPullback_quotient_mk, cohomologyPullback_quotient_mk, Sq1_apply]
  exact congrArg _ (Subtype.ext (Sq1cochain_cochainPullback φ a.1).symm)

end Sq1Naturality

/-! ## F6b — the first Wu class transports; F6 — `w₂` transports -/

/-- F5 at the `.mu` field of the genuine `PoincareDual4Lo` instance (degree-4 spelling). -/
theorem muLo_pullback (e : M ≃ₜ N) (w : Cohomology (TopCat.of N) 4) :
    (poincareDual4Lo_of_closed (M := M)).mu
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 4 w)
      = (poincareDual4Lo_of_closed (M := N)).mu w :=
  fundamentalFunctional_pullback e w

omit [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T2Space N] [CompactSpace N] [Nonempty N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N] in
/-- `Sq¹`-pullback naturality at the literal `H³ → H⁴` spelling of the genuine `sq1₃` field. -/
theorem sq1_pullback (e : M ≃ₜ N) (w : Cohomology (TopCat.of N) 3) :
    cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 4
        (SKEFTHawking.SingularBockstein.Sq1 (n := 2) w)
      = SKEFTHawking.SingularBockstein.Sq1 (n := 2)
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 3 w) :=
  Sq1_cohomologyPullback _ w

/-- **F6b — the first Wu class transports**: `e*(v₁(N)) = v₁(M)` on the genuine PD data — the
F6a uniqueness route with `pairing13`/`wu_relation_v1`, plus the `Sq¹`-naturality for the
Bockstein side of the defining relation. -/
theorem wuClass1_pullback (e : M ≃ₜ N) :
    cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 1
        (wuClass1 (poincareDual4Lo_of_closed (M := N)))
      = wuClass1 (poincareDual4Lo_of_closed (M := M)) := by
  apply (pairing13_bijective (poincareDual4Lo_of_closed (M := M))).1
  have hR : pairing13 (poincareDual4Lo_of_closed (M := M))
      (wuClass1 (poincareDual4Lo_of_closed (M := M)))
      = wuFunctional1 (poincareDual4Lo_of_closed (M := M)) :=
    LinearMap.ext (wu_relation_v1 (poincareDual4Lo_of_closed (M := M)))
  rw [hR]
  ext x
  obtain ⟨y, rfl⟩ := (cohomologyHomeoEquiv (X := TopCat.of M) (Y := TopCat.of N) e 3).surjective x
  show (poincareDual4Lo_of_closed (M := M)).mu
      (cupH13
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 1
          (wuClass1 (poincareDual4Lo_of_closed (M := N))))
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 3 y))
    = (poincareDual4Lo_of_closed (M := M)).mu
      (SKEFTHawking.SingularBockstein.Sq1 (n := 2)
        (cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 3 y))
  rw [← cohomologyPullback_cupH13, muLo_pullback e, ← sq1_pullback e, muLo_pullback e]
  exact wu_relation_v1 (poincareDual4Lo_of_closed (M := N)) y

/-- **F6 — the singular Wu class `w₂` transports along homeomorphisms**:
`e*(w₂(N)) = w₂(M)` on the genuine PD data — componentwise from F6a + F6b + the F2 cup
compatibility (`w₂ = v₂ + v₁²`). The engine of the `PinPlusCert` homeo-invariance. -/
theorem wuW2_pullback (e : M ≃ₜ N) :
    cohomologyPullback (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) 2
        (wuW2 (poincareDual4Mid_of_closed (M := N)) (poincareDual4Lo_of_closed (M := N)))
      = wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) := by
  rw [wuW2_eq, wuW2_eq, map_add, wuClass2_pullback e, cohomologyPullback_cupH,
    wuClass1_pullback e]

end SKEFTHawking.SingularWuTransport
