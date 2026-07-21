/-
# Phase 5q.H — SUBDIVISION IS NATURAL UNDER PUSHFORWARD (`f_# ∘ Sd = Sd ∘ f_#`)

The one missing naturality square of the singular subdivision engine: the subdivision operator
`Sd`, its chain homotopy `D`, and the iterated homotopy `Dₘ` all commute with the pushforward
`mapChain f` along a continuous map `f : X → Y`.

Everything reduces to the *simplex*-level identity
`mapSimplex f (pushSimplex σ w) = pushSimplex (mapSimplex f σ) w` — post-composing by `f` and
pre-composing by an affine map are independent operations on the realization `Δⁿ → X`. Since
`Sd σ := σ_# (Sd ιₙ)` and `D σ := σ_# (D ιₙ)` are *pure pushforwards of a fixed affine model chain*,
naturality of `pushChainM` in `σ` is naturality of `Sd`/`D`.

## Why it is load-bearing (Phase 5q.H #212)

The capstone collar-pair producer glues a subdivided cylinder chain and a subdivided disk chain into
the trace carrier. With a *unified* subdivision count on the two sides, this file's
`mapChain_singularSd_iterate` collapses that glued chain to `Sdᵘ` of the FROZEN glued chain — which
is what lets the dossier's highest-risk `hbridge` field (the canonical-disk subdivision bridge) be
DERIVED rather than assumed. See `PinPlusTraceCapstoneCollarPairGeom`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularSubdivision
import SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularSubdivisionPushNatural

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularExcisionMod2
open SKEFTHawking.SingularExcisionPushforward
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularFunctoriality

/-! ## §1. Simplex level -/

/-- **Pushforward commutes with the affine pushforward, on simplices.** `pushSimplex σ w` is
`σ̃ ∘ affineSimplexStd w`; post-composing with `f` only touches the `σ̃` factor. -/
theorem mapSimplex_pushSimplex {X Y : TopCat} {N n : ℕ} (f : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) :
    mapSimplex f (pushSimplex σ w) = pushSimplex (mapSimplex f σ) w := by
  rw [mapSimplex, pushSimplex, pushSimplex, mapSimplex, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, ← ContinuousMap.comp_assoc]

/-- **Pushforward commutes with the module-valued affine pushforward, on simplices.** The
`Δᴺ`-membership side condition of `pushSimplexM` does not mention `σ`, so both branches of the
`dite` transport. -/
theorem mapSimplex_pushSimplexM {X Y : TopCat} {N n : ℕ} (f : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (u : Fin (n + 1) → (Fin (N + 1) → ℝ)) :
    mapSimplex f (pushSimplexM σ u) = pushSimplexM (mapSimplex f σ) u := by
  by_cases hu : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1))
  · rw [pushSimplexM_of_mem σ hu, pushSimplexM_of_mem _ hu, mapSimplex_pushSimplex]
  · rw [pushSimplexM, dif_neg hu, pushSimplexM, dif_neg hu, mapSimplex_pushSimplex]

/-! ## §2. Chain level -/

/-- **Pushforward commutes with the module-valued affine pushforward, on chains.** -/
theorem mapChain_pushChainM {X Y : TopCat} {N n : ℕ} (f : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (c : LinChain (Fin (N + 1) → ℝ) n) :
    mapChain f n (pushChainM σ c) = pushChainM (mapSimplex f σ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single u a => rw [pushChainM_single, mapChain_single, pushChainM_single, mapSimplex_pushSimplexM]

/-- The iterated subdivision is additive (it is an iterate of a linear map). -/
theorem singularSd_iterate_add {X : TopCat} {n : ℕ} (m : ℕ) (a b : SingularChain X n) :
    (⇑(singularSd X n))^[m] (a + b)
      = (⇑(singularSd X n))^[m] a + (⇑(singularSd X n))^[m] b := by
  simp only [← Module.End.coe_pow, map_add]

/-- **THE SUBDIVISION NATURALITY SQUARE**: `f_# (Sd c) = Sd (f_# c)`. -/
theorem mapChain_singularSd {X Y : TopCat} {n : ℕ} (f : C(↑X, ↑Y)) (c : SingularChain X n) :
    mapChain f n (singularSd X n c) = singularSd Y n (mapChain f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) from by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    simp only [map_smul]
    rw [singularSd_single, mapChain_pushChainM, mapChain_single, singularSd_single]

/-- **The iterated subdivision is natural**: `f_# (Sdᵐ c) = Sdᵐ (f_# c)`. -/
theorem mapChain_singularSd_iterate {X Y : TopCat} {n : ℕ} (f : C(↑X, ↑Y)) (m : ℕ)
    (c : SingularChain X n) :
    mapChain f n ((⇑(singularSd X n))^[m] c) = (⇑(singularSd Y n))^[m] (mapChain f n c) := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, mapChain_singularSd]

/-- **The subdivision chain homotopy is natural**: `f_# (D c) = D (f_# c)`. -/
theorem mapChain_singularD {X Y : TopCat} {n : ℕ} (f : C(↑X, ↑Y)) (c : SingularChain X n) :
    mapChain f (n + 1) (singularD X n c) = singularD Y n (mapChain f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) from by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    simp only [map_smul]
    rw [singularD_single, mapChain_pushChainM, mapChain_single, singularD_single]

/-- **The iterated subdivision homotopy is natural**: `f_# (Dₘ c) = Dₘ (f_# c)`. -/
theorem mapChain_iterHomotopy {X Y : TopCat} {n : ℕ} (f : C(↑X, ↑Y)) (m : ℕ)
    (c : SingularChain X n) :
    mapChain f (n + 1) (iterHomotopy X n m c) = iterHomotopy Y n m (mapChain f n c) := by
  rw [iterHomotopy, iterHomotopy, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mapChain_singularSd_iterate, mapChain_singularD]

end SKEFTHawking.SingularSubdivisionPushNatural
