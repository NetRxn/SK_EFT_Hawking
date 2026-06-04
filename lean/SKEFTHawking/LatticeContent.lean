/-
Phase 5q.B: content extraction for the indefinite-case input [HM].

The local-global Hasse–Minkowski input [HM-LG] naturally produces a *nonzero* (rational, hence after clearing
denominators integer) isotropic vector — not necessarily a *primitive* one. The downstream hyperbolic-plane
split-off (`LatticePrimitive.exists_hyperbolic_pair`) requires a primitive isotropic vector. This module bridges
the gap: dividing a nonzero integer isotropic vector by the content (gcd of its entries = the generator of the
principal ideal `span ℤ (range v)`) yields a *primitive* isotropic vector, since isotropy is homogeneous of
degree 2 (`v ⬝ᵥ M *ᵥ v = g² · (w ⬝ᵥ M *ᵥ w)` when `v = g • w`).

Consequently the [HM] hypothesis of `VanDerBlijReduction.eight_dvd_latticeSig_of_HM_of_Theta` can be supplied
from the weaker "indefinite even unimodular form has a *nonzero* (not necessarily primitive) integer isotropic
vector" — exactly the shape the classical local-global theorem delivers (`exists_primitive_isotropic_of_isotropic`).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.VanDerBlijReduction

namespace SKEFTHawking

open Matrix QuadraticForm

/-- **Content extraction / primitivisation of an isotropic vector.** A *nonzero* integer vector `v` that is
isotropic for `M` (`v ⬝ᵥ M *ᵥ v = 0`) yields a *primitive* isotropic vector `w` (obtained by dividing `v` by
the generator `g` of the principal ideal `span ℤ (range v)`; isotropy transfers because the form is homogeneous
of degree 2: `v ⬝ᵥ M *ᵥ v = g² · (w ⬝ᵥ M *ᵥ w)`). This lets [HM] be invoked with plain (non-primitive)
isotropy. -/
theorem exists_primitive_isotropic_of_isotropic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) (hv : v ≠ 0) (hiso : v ⬝ᵥ M *ᵥ v = 0) :
    ∃ w : Fin n → ℤ, IsPrimitiveVec w ∧ w ⬝ᵥ M *ᵥ w = 0 := by
  classical
  set S : Submodule ℤ ℤ := Submodule.span ℤ (Set.range v) with hS
  set g : ℤ := Submodule.IsPrincipal.generator S with hg
  -- `g` generates `S`, so `g ∈ S` and `g ∣ v i` for every `i`.
  have hgmem : g ∈ S := Submodule.IsPrincipal.generator_mem S
  have hdvd : ∀ i, g ∣ v i := by
    intro i
    have hmem : v i ∈ S := Submodule.subset_span (Set.mem_range_self i)
    rw [← Submodule.IsPrincipal.span_singleton_generator S, Submodule.mem_span_singleton] at hmem
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, by rw [← hb, smul_eq_mul, mul_comm]⟩
  -- Bézout: `g = ∑ c i • v i`.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hS ▸ hgmem)
  -- `g ≠ 0` because `v ≠ 0`.
  have hg0 : g ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro h0
    exact hi (by simpa [h0] using (hdvd i))
  -- the primitivised vector `w = v / g`, with `v = g • w`.
  set w : Fin n → ℤ := fun i => v i / g with hw
  have hvgw : v = g • w := by
    funext i
    rw [hw, Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  refine ⟨w, ?_, ?_⟩
  · -- primitivity: `∑ c i • w i = 1`, hence `w ⬝ᵥ c = 1`.
    rw [isPrimitiveVec_iff_exists_dot]
    refine ⟨c, ?_⟩
    have hkey : g * ∑ i, c i * w i = g := by
      conv_rhs => rw [← hc]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hvi : v i = g * w i := congrFun hvgw i
      rw [smul_eq_mul, hvi]; ring
    have hsum : ∑ i, c i * w i = 1 := mul_left_cancel₀ hg0 (by rw [mul_one]; exact hkey)
    rw [dotProduct]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · -- isotropy transfers: `0 = v ⬝ᵥ M *ᵥ v = g • g • (w ⬝ᵥ M *ᵥ w)`.
    have hscale : v ⬝ᵥ M *ᵥ v = g • g • (w ⬝ᵥ M *ᵥ w) := by
      rw [hvgw, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    rw [hiso] at hscale
    have := hscale.symm
    simp only [smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg0
    · rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd h2 hg0
      · exact h2

/-- **van der Blij from [HM-weak] + [Θ].** The same reduction as `eight_dvd_latticeSig_of_HM_of_Theta`, but
with the indefinite input weakened to its natural classical form: an indefinite even unimodular form has merely
a *nonzero* (not necessarily primitive) integer isotropic vector — exactly what local-global Hasse–Minkowski
delivers. Primitivity is recovered internally via `exists_primitive_isotropic_of_isotropic`. -/
theorem eight_dvd_latticeSig_of_HMweak_of_Theta
    (hHM : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      ∃ v : Fin m → ℤ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0)
    (hΘ : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ), IsEvenUnimodular A →
      (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∨
       sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0) → 8 ∣ latticeSig A) :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ), IsEvenUnimodular M → 8 ∣ latticeSig M := by
  apply eight_dvd_latticeSig_of_HM_of_Theta ?_ hΘ
  intro m A hA hsp hsn
  obtain ⟨v, hv0, hviso⟩ := hHM A hA hsp hsn
  exact exists_primitive_isotropic_of_isotropic A v hv0 hviso

end SKEFTHawking
