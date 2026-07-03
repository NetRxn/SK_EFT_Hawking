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

end SKEFTHawking.SingularWuTransport
