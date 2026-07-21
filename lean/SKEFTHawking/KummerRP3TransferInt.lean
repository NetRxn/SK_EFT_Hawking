import Mathlib
import SKEFTHawking.KummerRP3CoveringMap
import SKEFTHawking.StdSimplexLocPath
import SKEFTHawking.SingularInvolutionSmithInt

/-!
# The integral two-fold lift of `ℝP³`-simplices and the transfer SES facts

Integral (`ZMod 2 → ℤ`) mirror of `RP4Transfer`, on the K7 seam carrier `ℝP³ = S³/±`
(`KummerResolutionPiece`): every singular simplex of `ℝP³` lifts uniquely through the antipodal
covering `mkRP3` (`rp3_isCoveringMap` + Mathlib's `existsUnique_continuousMap_lifts`; `Δⁿ` is
simply connected and locally path-connected). The fiber is the antipodal pair, so each simplex has
exactly two lifts `liftPlus/liftMinus`, exchanged by the deck involution
(`mapSimplex_negS3C_liftPlus`). This file delivers the **chain-level short-exact-sequence facts**
of the interlocking integral Smith sequences:

* `transferChainInt` — the transfer `tr : Cₙ(ℝP³;ℤ) → Cₙ(S³;ℤ)`, `σ ↦ lift₊σ + lift₋σ`, a chain
  map (`chainBoundary_transferChainInt`), injective, with `range tr = range N_#`
  (`range_transferChainInt_eq_range_normChain`) — the chain iso `C_*(ℝP³) ≅ A_* = N·C_*(S³)`;
* `mapChainInt_surjective` — `p_# : Cₙ(S³;ℤ) → Cₙ(ℝP³;ℤ)` is onto (SES-III's epi);
* `ker_mapChainInt_eq_range_diffChain` — `ker p_# = im D_#` (SES-III's exactness heart);
* `mapChainInt_transferChainInt` — `p_# ∘ tr = 2` (the integral transfer composite).

Together with the generic free-involution exactness (`SingularInvolutionSmithInt`) these are all
the levelwise inputs of the two interlocking SESs
`0 → A → C(S³) → B → 0`, `0 → B → C(S³) → C(ℝP³) → 0` (`B = D·C`, `A = N·C`) whose long exact
sequences compute `H_*(ℝP³; ℤ)` — the K7 seam's homology (`H₂ = 0` is the `b₂`-accounting
priority). The same engine will drive the `Q = T⁴°/τ` transfer downstream.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C negS3C negS3_free
  mkRP3C_comp_negS3C negS3C_comp_negS3C normChain diffChain)
open SKEFTHawking.KummerRP3CoveringMap (rp3_isCoveringMap fiber_pair)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary chainBoundary_single_smul
  boundaryBasis)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single)
open SKEFTHawking.SingularFunctoriality (mapSimplex face_mapSimplex mapSimplex_comp mapSimplex_id)
open SKEFTHawking.SingularCohomologyInt (face)
open SKEFTHawking.SingularInvolutionSmithInt (mapSimplex_mapSimplex mapSimplex_ne_of_forall_ne
  normChain_single diffChain_single)

namespace SKEFTHawking.KummerRP3TransferInt

/-- The barycenter of the standard simplex. -/
noncomputable def bary (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun _ => ((n : ℝ) + 1)⁻¹,
    fun _ => by positivity,
    by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      field_simp⟩

/-- The realization of an `ℝP³`-simplex. -/
noncomputable def rlP {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    C(stdSimplex ℝ (Fin (n + 1)), RP3) :=
  RP3top.toSSetObjEquiv (op (SimplexCategory.mk n)) σ

/-- **The freeness of the deck involution at simplex level**: `negS3C` moves every `S³`-simplex. -/
theorem mapSimplex_negS3C_ne {n : ℕ}
    (τ : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n))) :
    mapSimplex negS3C τ ≠ τ :=
  mapSimplex_ne_of_forall_ne (fun x => negS3_free x) τ

/-! ## §1. The unique two-fold lift -/

/-- **The unique lift of an `ℝP³`-simplex** at a chosen fiber point over its barycenter value. -/
noncomputable def liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) (e₀ : S3)
    (he : mkRP3 e₀ = rlP σ (bary n)) :
    (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n)) :=
  (S3top.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (rp3_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).exists.choose

/-- The lift's defining properties, packaged: it sits over `σ` and hits `e₀` at the barycenter. -/
theorem liftSimplex_spec {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) (e₀ : S3)
    (he : mkRP3 e₀ = rlP σ (bary n)) :
    (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he)) (bary n) = e₀ ∧
      mkRP3 ∘ (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
        = rlP σ := by
  have hspec :=
    (rp3_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).exists.choose_spec
  rw [liftSimplex, Equiv.apply_symm_apply]
  exact hspec

/-- **The lift sits over `σ`**: pushing forward along the covering recovers `σ`. -/
theorem mapSimplex_liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) (e₀ : S3)
    (he : mkRP3 e₀ = rlP σ (bary n)) :
    mapSimplex mkRP3C (liftSimplex σ e₀ he) = σ := by
  rw [mapSimplex, Equiv.symm_apply_eq]
  refine ContinuousMap.ext (fun d => ?_)
  have h := (liftSimplex_spec σ e₀ he).2
  exact congrFun h d

/-- **Uniqueness**: any simplex over `σ` hitting `e₀` at the barycenter IS the lift. -/
theorem liftSimplex_unique {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) (e₀ : S3)
    (he : mkRP3 e₀ = rlP σ (bary n))
    (τ : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n)))
    (hτ0 : (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) = e₀)
    (hτ : mkRP3 ∘ (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlP σ) :
    τ = liftSimplex σ e₀ he := by
  have huniq :=
    (rp3_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).unique
      (y₁ := S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      (y₂ := S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
      ⟨hτ0, hτ⟩ (liftSimplex_spec σ e₀ he)
  exact (S3top.toSSetObjEquiv (op (SimplexCategory.mk n))).injective huniq

/-- The canonical fiber point over a simplex's barycenter value. -/
noncomputable def outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) : S3 :=
  Quotient.out (rlP σ (bary n))

theorem mk_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mkRP3 (outFiber σ) = rlP σ (bary n) :=
  Quotient.out_eq _

theorem mk_neg_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mkRP3 (negS3 (outFiber σ)) = rlP σ (bary n) :=
  (mkRP3_neg _).trans (mk_outFiber σ)

/-- The `+`-lift (at the canonical fiber point). -/
noncomputable def liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ (outFiber σ) (mk_outFiber σ)

/-- The `−`-lift (at the antipodal fiber point). -/
noncomputable def liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ (negS3 (outFiber σ)) (mk_neg_outFiber σ)

/-- **The two lifts are distinct** — they differ at the barycenter (`negS3` is free). -/
theorem liftPlus_ne_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    liftPlus σ ≠ liftMinus σ := by
  intro h
  have h1 := (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).1
  have h2 := (liftSimplex_spec σ (negS3 (outFiber σ)) (mk_neg_outFiber σ)).1
  have hval := congrArg
    (fun τ => (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  simp only at hval
  rw [show liftSimplex σ (outFiber σ) (mk_outFiber σ) = liftPlus σ from rfl] at h1
  rw [show liftSimplex σ (negS3 (outFiber σ)) (mk_neg_outFiber σ) = liftMinus σ from rfl] at h2
  rw [h1, h2] at hval
  exact negS3_free (outFiber σ) hval.symm

@[simp] theorem mapSimplex_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mapSimplex mkRP3C (liftPlus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

@[simp] theorem mapSimplex_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mapSimplex mkRP3C (liftMinus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

/-- **The deck involution exchanges the two lifts**: `τ_#(lift₊σ) = lift₋σ`. -/
theorem mapSimplex_negS3C_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mapSimplex negS3C (liftPlus σ) = liftMinus σ := by
  refine liftSimplex_unique σ (negS3 (outFiber σ)) (mk_neg_outFiber σ) _ ?_ ?_
  · rw [mapSimplex, Equiv.apply_symm_apply]
    show negS3C ((S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) (bary n))
      = negS3 (outFiber σ)
    have h1 : (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) (bary n)
        = outFiber σ := (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).1
    rw [h1]
    rfl
  · rw [mapSimplex, Equiv.apply_symm_apply]
    funext d
    show mkRP3 (negS3 ((S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) d))
      = rlP σ d
    rw [mkRP3_neg]
    exact congrFun (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).2 d

/-- **The deck involution exchanges the two lifts**: `τ_#(lift₋σ) = lift₊σ`. -/
theorem mapSimplex_negS3C_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mapSimplex negS3C (liftMinus σ) = liftPlus σ := by
  have h := congrArg (mapSimplex negS3C) (mapSimplex_negS3C_liftPlus σ)
  rw [mapSimplex_mapSimplex negS3C_comp_negS3C] at h
  exact h.symm

/-- **Every `S³`-simplex is one of the two lifts of its pushforward.** -/
theorem mem_pair_of_pushforward {n : ℕ}
    (τ : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n))) :
    τ = liftPlus (mapSimplex mkRP3C τ) ∨ τ = liftMinus (mapSimplex mkRP3C τ) := by
  set F := mapSimplex mkRP3C τ with hF
  have h1 : rlP F = mkRP3C.comp (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
    rw [rlP, hF, mapSimplex, Equiv.apply_symm_apply]
  set y := (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) with hy
  have hmk : mkRP3 y = rlP F (bary n) :=
    (congrFun (congrArg DFunLike.coe h1) (bary n)).symm
  have hcirc : mkRP3 ∘ (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlP F :=
    (congrArg DFunLike.coe h1).symm
  rcases fiber_pair (hmk.trans (mk_outFiber F).symm) with hcase | hcase
  · left
    exact liftSimplex_unique F (outFiber F) (mk_outFiber F) τ (hy ▸ hcase) hcirc
  · right
    exact liftSimplex_unique F (negS3 (outFiber F)) (mk_neg_outFiber F) τ (hy ▸ hcase) hcirc

/-- **Two lifts of the same simplex agreeing anywhere are equal** — covering uniqueness on the
preconnected simplex (`IsCoveringMap.eq_of_comp_eq`). -/
theorem liftSimplex_eq_of_agree {n : ℕ}
    (τ τ' : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk n)))
    (hover : mapSimplex mkRP3C τ = mapSimplex mkRP3C τ')
    (d : stdSimplex ℝ (Fin (n + 1)))
    (hd : (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) d
      = (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ') d) : τ = τ' := by
  have hcomp : mkRP3 ∘ (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      = mkRP3 ∘ (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ') := by
    have h1 := congrArg (RP3top.toSSetObjEquiv (op (SimplexCategory.mk n))) hover
    rw [mapSimplex, mapSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact congrArg DFunLike.coe h1
  have := rp3_isCoveringMap.eq_of_comp_eq
    (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous
    (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ').continuous
    hcomp d hd
  exact (S3top.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    (ContinuousMap.coe_injective this)

/-! ## §2. The face calculus of the lift pair -/

/-- **A face of a lift is one of the two lifts of the face.** -/
theorem face_lift_mem_pair {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2))
    (τ : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk (n + 1))))
    (hτ : mapSimplex mkRP3C τ = σ) :
    face i τ = liftPlus (face i σ) ∨ face i τ = liftMinus (face i σ) := by
  have hover : mapSimplex mkRP3C (face i τ) = face i σ := by
    rw [show mapSimplex mkRP3C (face i τ) = face i (mapSimplex mkRP3C τ) from
      (face_mapSimplex mkRP3C τ i).symm, hτ]
  rcases mem_pair_of_pushforward (face i τ) with h | h
  · left; rw [h, hover]
  · right; rw [h, hover]

/-- **Faces of the two lifts are distinct** — else the lifts agree at a face-embedded point,
forcing them equal by covering uniqueness, contradicting the barycenter separation. -/
theorem face_liftPlus_ne_face_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    face i (liftPlus σ) ≠ face i (liftMinus σ) := by
  intro h
  refine liftPlus_ne_liftMinus σ ?_
  refine liftSimplex_eq_of_agree (liftPlus σ) (liftMinus σ)
    ((mapSimplex_liftPlus σ).trans (mapSimplex_liftMinus σ).symm)
    ((⟨_root_.stdSimplex.map (SimplexCategory.δ i),
      _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩ :
        C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2)))) (bary n)) ?_
  have h1 : (S3top.toSSetObjEquiv (op (SimplexCategory.mk n))
        (SKEFTHawking.SingularCohomologyMod2.face i (liftPlus σ))) (bary n)
      = (S3top.toSSetObjEquiv (op (SimplexCategory.mk n))
        (SKEFTHawking.SingularCohomologyMod2.face i (liftMinus σ))) (bary n) :=
    congrArg (fun τ => (S3top.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  rwa [SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face,
    SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face] at h1

/-- **The face pair-sum identity** (integral): the faces of the two lifts of `σ` are, as a chain,
the two lifts of the face. -/
theorem face_pair_sum {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    Finsupp.single (face i (liftPlus σ)) (1 : ℤ)
        + Finsupp.single (face i (liftMinus σ)) 1
      = Finsupp.single (liftPlus (face i σ)) 1
        + Finsupp.single (liftMinus (face i σ)) 1 := by
  rcases face_lift_mem_pair σ i (liftPlus σ) (mapSimplex_liftPlus σ) with hP | hP <;>
    rcases face_lift_mem_pair σ i (liftMinus σ) (mapSimplex_liftMinus σ) with hM | hM
  · exact absurd (hP.trans hM.symm) (face_liftPlus_ne_face_liftMinus σ i)
  · rw [hP, hM]
  · rw [hP, hM]
    exact add_comm _ _
  · exact absurd (hP.trans hM.symm) (face_liftPlus_ne_face_liftMinus σ i)

/-! ## §3. The integral transfer chain map -/

/-- **The integral transfer** `tr : Cₙ(ℝP³;ℤ) → Cₙ(S³;ℤ)`: each simplex to the sum of its two
lifts (at the fixed canonical fiber choice `Quotient.out`). -/
noncomputable def transferChainInt (n : ℕ) :
    SingularChainInt RP3top n →ₗ[ℤ] SingularChainInt S3top n :=
  Finsupp.linearCombination ℤ
    (fun σ => Finsupp.single (liftPlus σ) 1 + Finsupp.single (liftMinus σ) 1)

@[simp] theorem transferChainInt_single {n : ℕ}
    (σ : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    transferChainInt n (Finsupp.single σ a)
      = Finsupp.single (liftPlus σ) a + Finsupp.single (liftMinus σ) a := by
  rw [transferChainInt, Finsupp.linearCombination_single, smul_add, Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **`p_# ∘ tr = 2`** (integral): both lifts push forward to the same simplex. -/
theorem mapChainInt_transferChainInt (n : ℕ) (c : SingularChainInt RP3top n) :
    mapChainInt mkRP3C n (transferChainInt n c) = 2 • c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, smul_add]
  | single σ a =>
      rw [transferChainInt_single, map_add, mapChainInt_single, mapChainInt_single,
        mapSimplex_liftPlus, mapSimplex_liftMinus, ← Finsupp.single_add, two_smul,
        Finsupp.single_add]

/-- **The transfer is a chain map**: `∂ ∘ tr = tr ∘ ∂` — per-face via the pair-sum identity,
with the alternating signs riding along. -/
theorem chainBoundary_transferChainInt (n : ℕ) (c : SingularChainInt RP3top (n + 1)) :
    chainBoundary S3top n (transferChainInt (n + 1) c)
      = transferChainInt n (chainBoundary RP3top n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
      have hone : chainBoundary S3top n (transferChainInt (n + 1) (Finsupp.single σ (1 : ℤ)))
          = transferChainInt n (chainBoundary RP3top n (Finsupp.single σ 1)) := by
        rw [transferChainInt_single, map_add,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          boundaryBasis, boundaryBasis, boundaryBasis, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, transferChainInt_single, ← smul_add, face_pair_sum]
      calc chainBoundary S3top n (transferChainInt (n + 1) (Finsupp.single σ a))
          = chainBoundary S3top n (transferChainInt (n + 1) (a • Finsupp.single σ (1 : ℤ))) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        _ = a • chainBoundary S3top n (transferChainInt (n + 1) (Finsupp.single σ (1 : ℤ))) := by
            rw [map_smul, map_smul]
        _ = a • transferChainInt n (chainBoundary RP3top n (Finsupp.single σ (1 : ℤ))) := by
            rw [hone]
        _ = transferChainInt n (chainBoundary RP3top n (Finsupp.single σ a)) := by
            rw [← map_smul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §4. The coefficient calculus and the SES facts -/

/-- **The 2-to-1 coefficient formula**: the pushforward's coefficient at `β` is the sum of the
coefficients at `β`'s two lifts. -/
theorem mapChainInt_apply_pair {n : ℕ} (c : SingularChainInt S3top n)
    (β : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    mapChainInt mkRP3C n c β = c (liftPlus β) + c (liftMinus β) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply, Finsupp.add_apply]
      ring
  | single σ a =>
      classical
      rw [mapChainInt_single, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hβ : mapSimplex mkRP3C σ = β
      · rcases mem_pair_of_pushforward σ with hσ | hσ
        · have hσ' : σ = liftPlus β := by rw [hβ] at hσ; exact hσ
          rw [if_pos hβ, if_pos hσ',
            if_neg (fun h => liftPlus_ne_liftMinus β (hσ'.symm.trans h)), add_zero]
        · have hσ' : σ = liftMinus β := by rw [hβ] at hσ; exact hσ
          rw [if_pos hβ, if_neg (fun h => liftPlus_ne_liftMinus β (h.symm.trans hσ')),
            if_pos hσ', zero_add]
      · rw [if_neg hβ, if_neg (fun h => hβ (by rw [h, mapSimplex_liftPlus])),
          if_neg (fun h => hβ (by rw [h, mapSimplex_liftMinus])), add_zero]

/-- **The transfer's coefficient at a `+`-lift is the source coefficient**. -/
theorem transferChainInt_apply_liftPlus {n : ℕ} (c : SingularChainInt RP3top n)
    (β : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk n))) :
    transferChainInt n c (liftPlus β) = c β := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single σ a =>
      classical
      have hML : liftMinus σ ≠ liftPlus β := by
        intro h
        have h2 := congrArg (mapSimplex mkRP3C) h
        rw [mapSimplex_liftMinus, mapSimplex_liftPlus] at h2
        subst h2
        exact liftPlus_ne_liftMinus σ h.symm
      rw [transferChainInt_single, Finsupp.add_apply, Finsupp.single_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases hσ : σ = β
      · rw [if_pos (show liftPlus σ = liftPlus β by rw [hσ]), if_neg hML, add_zero, if_pos hσ]
      · rw [if_neg (fun h => hσ (by
            have h2 := congrArg (mapSimplex mkRP3C) h
            rwa [mapSimplex_liftPlus, mapSimplex_liftPlus] at h2)),
          if_neg hML, if_neg hσ, add_zero]

/-- **The transfer is injective** — read off the `+`-lift coefficients. -/
theorem transferChainInt_injective (n : ℕ) : Function.Injective (transferChainInt n) := by
  intro c d h
  ext β
  have h1 := congrArg (fun x => x (liftPlus β)) h
  simpa only [transferChainInt_apply_liftPlus] using h1

/-- **`p_#` is surjective** — every base simplex lifts through `liftPlus` (SES-III's epi). -/
theorem mapChainInt_surjective (n : ℕ) : Function.Surjective (mapChainInt mkRP3C n) := by
  intro c
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add c d hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb⟩ := hd
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | single σ a =>
      exact ⟨Finsupp.single (liftPlus σ) a, by rw [mapChainInt_single, mapSimplex_liftPlus]⟩

/-- `p_# ∘ D_# = 0`: the pushforward kills the difference operator (`p ∘ τ = p`). -/
theorem mapChainInt_diffChain (n : ℕ) (c : SingularChainInt S3top n) :
    mapChainInt mkRP3C n (diffChain negS3C n c) = 0 := by
  show mapChainInt mkRP3C n (c - mapChainInt negS3C n c) = 0
  rw [map_sub, ← SKEFTHawking.SingularFunctorialityInt.mapChainInt_comp, mkRP3C_comp_negS3C,
    sub_self]

/-- **`ker p_# = im D_#`** — the exactness heart of the integral Smith SES-III: an integral chain
killed by `p_#` has its coefficients antipodally opposite (`mapChainInt_apply_pair`), so
subtracting `D`-images strips its support one orbit at a time. -/
theorem mem_range_diffChain_of_mapChainInt_eq_zero {n : ℕ}
    (c : SingularChainInt S3top n) (hc : mapChainInt mkRP3C n c = 0) :
    c ∈ LinearMap.range (diffChain negS3C n) := by
  classical
  suffices H : ∀ (N : ℕ) (c : SingularChainInt S3top n), c.support.card ≤ N →
      mapChainInt mkRP3C n c = 0 → c ∈ LinearMap.range (diffChain negS3C n) from
    H _ c le_rfl hc
  intro N
  induction N with
  | zero =>
      intro c hcard _
      have hc0 : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact ⟨0, by rw [map_zero, hc0]⟩
  | succ N ih =>
      intro c hcard hc
      rcases Finset.eq_empty_or_nonempty c.support with hemp | ⟨σ₀, hσ₀⟩
      · exact ⟨0, by rw [map_zero, Finsupp.support_eq_empty.mp hemp]⟩
      · set β := mapSimplex mkRP3C σ₀ with hβ
        have hsum : c (liftPlus β) + c (liftMinus β) = 0 := by
          rw [← mapChainInt_apply_pair, hc]
          rfl
        set a := c (liftPlus β) with ha
        have hM : c (liftMinus β) = -a := by linarith [hsum]
        set c' := c - diffChain negS3C n (Finsupp.single (liftPlus β) a) with hc'
        have hc'0 : mapChainInt mkRP3C n c' = 0 := by
          rw [hc', map_sub, hc, mapChainInt_diffChain, sub_zero]
        have hDσ : diffChain negS3C n (Finsupp.single (liftPlus β) a)
            = Finsupp.single (liftPlus β) a - Finsupp.single (liftMinus β) a := by
          rw [diffChain_single, mapSimplex_negS3C_liftPlus]
        have hsupp : c'.support ⊆ c.support.erase (liftPlus β) := by
          intro x hx
          have hx0 : c' x ≠ 0 := Finsupp.mem_support_iff.mp hx
          rw [hc', hDσ, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_apply,
            Finsupp.single_apply] at hx0
          rw [Finset.mem_erase, Finsupp.mem_support_iff]
          by_cases h1 : liftPlus β = x
          · exfalso
            apply hx0
            rw [if_pos h1, if_neg (fun h2 : liftMinus β = x =>
              liftPlus_ne_liftMinus β (h1.trans h2.symm)), ← h1, ← ha]
            ring
          · by_cases h2 : liftMinus β = x
            · exfalso
              apply hx0
              rw [if_neg h1, if_pos h2, ← h2, hM]
              ring
            · rw [if_neg h1, if_neg h2] at hx0
              refine ⟨fun h => h1 h.symm, ?_⟩
              intro hcx
              apply hx0
              rw [hcx]
              ring
        have hPmem : liftPlus β ∈ c.support := by
          rcases mem_pair_of_pushforward σ₀ with hp | hp
          · rw [← hβ] at hp
            rw [← hp]
            exact hσ₀
          · rw [← hβ] at hp
            rw [Finsupp.mem_support_iff, ← ha]
            intro ha0
            have : c (liftMinus β) = 0 := by rw [hM, ha0, neg_zero]
            rw [← hp] at this
            exact Finsupp.mem_support_iff.mp hσ₀ this
        have hcard' : c'.support.card ≤ N := by
          have h1 := Finset.card_le_card hsupp
          have h2 : (c.support.erase (liftPlus β)).card = c.support.card - 1 :=
            Finset.card_erase_of_mem hPmem
          omega
        obtain ⟨d, hd⟩ := ih c' hcard' hc'0
        refine ⟨d + Finsupp.single (liftPlus β) a, ?_⟩
        rw [map_add, hd, hc']
        abel

/-- **`ker p_# = im D_#`**, packaged (SES-III exactness at the middle). -/
theorem ker_mapChainInt_eq_range_diffChain (n : ℕ) :
    LinearMap.ker (mapChainInt mkRP3C n) = LinearMap.range (diffChain negS3C n) := by
  ext c
  constructor
  · exact fun hc => mem_range_diffChain_of_mapChainInt_eq_zero c (LinearMap.mem_ker.mp hc)
  · rintro ⟨d, rfl⟩
    exact LinearMap.mem_ker.mpr (mapChainInt_diffChain n d)

/-- **`im tr = im N_#`** — the transfer lands exactly on the norm subcomplex `A_* = N·C_*(S³)`:
`tr` is the chain iso `C_*(ℝP³;ℤ) ≅ A_*` (with `transferChainInt_injective` and
`chainBoundary_transferChainInt`). -/
theorem range_transferChainInt_eq_range_normChain (n : ℕ) :
    LinearMap.range (transferChainInt n) = LinearMap.range (normChain negS3C n) := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    induction d using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add c d hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
    | single σ a =>
        refine ⟨Finsupp.single (liftPlus σ) a, ?_⟩
        rw [normChain_single, mapSimplex_negS3C_liftPlus, transferChainInt_single]
  · rintro ⟨d, rfl⟩
    induction d using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add c d hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
    | single σ a =>
        rw [normChain_single]
        rcases mem_pair_of_pushforward σ with hp | hp
        · refine ⟨Finsupp.single (mapSimplex mkRP3C σ) a, ?_⟩
          rw [transferChainInt_single, ← hp, ← mapSimplex_negS3C_liftPlus, ← hp]
        · refine ⟨Finsupp.single (mapSimplex mkRP3C σ) a, ?_⟩
          rw [transferChainInt_single, ← hp, ← mapSimplex_negS3C_liftMinus, ← hp, add_comm]

end SKEFTHawking.KummerRP3TransferInt
