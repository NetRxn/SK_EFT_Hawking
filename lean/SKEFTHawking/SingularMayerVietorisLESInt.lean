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

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularMayerVietorisLES
  (ambIncl subIncl ambIncl_comp_subIncl_left ambIncl_comp_subIncl_right)

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

end SKEFTHawking.SingularMayerVietorisLESInt
