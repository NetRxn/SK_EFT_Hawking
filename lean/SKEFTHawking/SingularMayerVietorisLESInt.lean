/-
# Phase 5q.H (E1 integral topology) — the absolute homology Mayer–Vietoris maps
# `Hₙ(A∩B;ℤ) → Hₙ(A;ℤ)⊕Hₙ(B;ℤ) → Hₙ(X;ℤ)` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularMayerVietorisLES` — the "easy half" of the absolute homology
Mayer–Vietoris sequence of a space `X` under a two-set open cover `{A, B}`: the diagonal/sum maps and the
complex condition `Σ ∘ Δ = 0`. Built on the integral functoriality `Homology.mapInt` applied to the subspace
inclusions `subIncl`/`ambIncl` (coefficient-agnostic continuous maps, reused from the mod-2 module).

The mod-2 `mvHomSum` was a `coprod` (a difference over `ℤ/2`, where `+ = −`); over ℤ the sum is the honest
**difference** `(ι_A)_* u − (ι_B)_* v`, so the complex condition `Σ ∘ Δ = 0` closes by `sub_self` (both
inclusion routes `A∩B ↪ A ↪ X` and `A∩B ↪ B ↪ X` equal the single `A∩B ↪ X`) rather than `c + c = 0`.

The connecting map `δ : Hₙ₊₁(X;ℤ) → Hₙ(A∩B;ℤ)` + the three exactness statements are the next bricks (built
on the integral pair LES `homProjInt`/`connectingInt` + the integral excision `excisionEquivInt`), completing
the integral MV LES — the bottom row of the integral Poincaré-duality 5-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularSubsetHomologyInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.SingularLocalHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)
open SKEFTHawking.SingularMayerVietorisLES
  (ambIncl subIncl ambIncl_comp_subIncl_left ambIncl_comp_subIncl_right seamHomeo)

namespace SKEFTHawking.SingularMayerVietorisLESInt

variable {X : TopCat}

/-- **The integral MV diagonal** `Hₙ(A∩B;ℤ) → Hₙ(A;ℤ) ⊕ Hₙ(B;ℤ)`, `w ↦ ((ι_A)_* w, (ι_B)_* w)`. -/
noncomputable def mvHomDiagInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub (A ∩ B)) n →ₗ[ℤ] Homology (sub A) n × Homology (sub B) n :=
  (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n).prod
    (Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n)

/-- **The integral MV sum** `Hₙ(A;ℤ) ⊕ Hₙ(B;ℤ) → Hₙ(X;ℤ)`, `(u, v) ↦ (ι_A)_* u − (ι_B)_* v` (the honest
ℤ-difference; the mod-2 `coprod` becomes a `sub`). -/
noncomputable def mvHomSumInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub A) n × Homology (sub B) n →ₗ[ℤ] Homology X n :=
  (Homology.mapInt (ambIncl A) n).comp (LinearMap.fst _ _ _)
    - (Homology.mapInt (ambIncl B) n).comp (LinearMap.snd _ _ _)

@[simp] theorem mvHomDiagInt_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomDiagInt A B n w
      = (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n w,
         Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n w) := rfl

@[simp] theorem mvHomSumInt_apply (A B : Set ↑X) (n : ℕ)
    (p : Homology (sub A) n × Homology (sub B) n) :
    mvHomSumInt A B n p
      = Homology.mapInt (ambIncl A) n p.1 - Homology.mapInt (ambIncl B) n p.2 := rfl

/-- **The integral MV chain-complex condition** `mvHomSumInt ∘ mvHomDiagInt = 0`: both inclusion routes
from `A∩B` land in `Hₙ(X;ℤ)` as the same map, so the difference is `c − c = 0`. -/
theorem mvHomSumInt_mvHomDiagInt (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomSumInt A B n (mvHomDiagInt A B n w) = 0 := by
  rw [mvHomDiagInt_apply, mvHomSumInt_apply]
  rw [show Homology.mapInt (ambIncl A) n
          (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n w)
        = Homology.mapInt (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ambIncl_comp_subIncl_left],
    show Homology.mapInt (ambIncl B) n
          (Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n w)
        = Homology.mapInt (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ambIncl_comp_subIncl_right]]
  exact sub_self _

/-! ## The integral Mayer–Vietoris connecting homomorphism `δ : Hₙ₊₁(X;ℤ) → Hₙ(A ∩ B;ℤ)` -/

/-- **The integral MV connecting homomorphism (pre-seam)** `Hₙ₊₁(X;ℤ) → Hₙ(sub (restr A B);ℤ)`, assembled
Barratt–Whitehead-style from the integral pair LES (`homProjInt`/`connectingInt`) and integral excision
(`excisionEquivInt`): project to the relative group, cross the excision iso backwards, then apply the pair
connecting map. Integral mirror of `SingularMayerVietorisLES.mvConnecting`. -/
noncomputable def mvConnectingInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ℤ] Homology (sub (restr A B)) n :=
  (connectingInt (restr A B) n).comp
    (((excisionEquivInt A B n hcov).symm.toLinearMap).comp (homProjInt A (n + 1)))

/-- The seam **homology isomorphism** `Hₙ(sub (restr A B);ℤ) ≅ Hₙ(sub (A ∩ B);ℤ)`, induced by the
(coefficient-agnostic) reassociation homeomorphism `seamHomeo A B` (a homeomorphism, so integral
functoriality + `mapInt_bijective_of_comp_id_all` give the iso in every degree). Bridges `mvConnectingInt`'s
codomain (`sub (restr A B)`) to `mvHomDiagInt`'s domain (`sub (A ∩ B)`). -/
noncomputable def seamHomologyEquivInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub (restr A B)) n ≃ₗ[ℤ] Homology (sub (A ∩ B)) n :=
  LinearEquiv.ofBijective
    (Homology.mapInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n)
    (Homology.mapInt_bijective_of_comp_id_all ⟨seamHomeo A B, (seamHomeo A B).continuous⟩
      ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n)

@[simp] theorem seamHomologyEquivInt_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (restr A B)) n) :
    seamHomologyEquivInt A B n w
      = Homology.mapInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n w := rfl

/-- **The integral Mayer–Vietoris connecting map** `δ : Hₙ₊₁(X;ℤ) → Hₙ(A ∩ B;ℤ)` in the `sub (A ∩ B)`
representation — `mvConnectingInt` post-composed with the seam iso, so its codomain matches `mvHomDiagInt`'s
domain. Closes the bottom-row integral MV LES
`⋯ → Hₙ₊₁(X;ℤ) →[δ] Hₙ(A∩B;ℤ) →[mvHomDiagInt] Hₙ(A;ℤ)⊕Hₙ(B;ℤ) →[mvHomSumInt] Hₙ(X;ℤ) → ⋯`. -/
noncomputable def mvDeltaInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ℤ] Homology (sub (A ∩ B)) n :=
  (seamHomologyEquivInt A B n).toLinearMap.comp (mvConnectingInt A B n hcov)

end SKEFTHawking.SingularMayerVietorisLESInt
