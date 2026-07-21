import Mathlib
import SKEFTHawking.KummerQuotientCovering
import SKEFTHawking.KummerRP3TransferInt
import SKEFTHawking.SingularInvolutionSmithInt

/-!
# The integral two-fold lift of `Q`-simplices and the transfer SES facts (`Q = T⁴°/τ`)

The `Q`-side mirror of `KummerRP3TransferInt`, one dimension up: every singular simplex of the
free quotient `Q = T⁴°/τ` lifts uniquely through the covering `qmk : T⁴° ↠ Q`
(`qmk_isCoveringMap` + Mathlib's `existsUnique_continuousMap_lifts`; `Δⁿ` is simply connected and
locally path-connected). The fibre is the deck pair, so each simplex has exactly two lifts
`liftPlus/liftMinus`, exchanged by the deck involution `tauC`. This file delivers the
**chain-level short-exact-sequence facts** of the interlocking integral Smith sequences for `Q`:

* `transferChainInt` — the transfer `tr : Cₙ(Q;ℤ) → Cₙ(T⁴°;ℤ)`, `σ ↦ lift₊σ + lift₋σ`, a chain
  map (`chainBoundary_transferChainInt`), injective, with `range tr = range N_#`;
* `mapChainInt_surjective` — `p_# : Cₙ(T⁴°;ℤ) → Cₙ(Q;ℤ)` is onto (SES-III's epi);
* `ker_mapChainInt_eq_range_diffChain` — `ker p_# = im D_#` (SES-III's exactness heart);
* `mapChainInt_transferChainInt` — `p_# ∘ tr = 2`;
* `transferChainInt_mapChainInt` — **`tr ∘ p_# = N_#`** (the norm identity driving the
  `H₂(Q)`-solve's injectivity leg `t ∘ p̄ = 1 + τ_*`).

These are all the levelwise inputs of the two interlocking SESs
`0 → A → C(T⁴°) → B → 0`, `0 → B → C(T⁴°) → C(Q) → 0` (`B = D·C`, `A = N·C`) whose long exact
sequences compute `H₂(Q;ℤ) ≅ ℤ⁶` — the single open input of the K7 `b₂ = 22` window
(`kummerK3_b2_window_of_qH2`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.KummerFreeQuotient (FreeQuotient qmk qmk_neg_one_smul)
open SKEFTHawking.KummerPuncturedTorus (puncturedTorus)
open SKEFTHawking.KummerRP3Covering (normChain diffChain)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop tauC qmkC tauC_comp_self tauC_free
  qmkC_comp_tauC qmk_isCoveringMap fiber_pair)
open SKEFTHawking.KummerRP3TransferInt (bary)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary chainBoundary_single_smul
  boundaryBasis)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single)
open SKEFTHawking.SingularFunctoriality (mapSimplex face_mapSimplex mapSimplex_comp mapSimplex_id)
open SKEFTHawking.SingularCohomologyInt (face)
open SKEFTHawking.SingularInvolutionSmithInt (mapSimplex_mapSimplex mapSimplex_ne_of_forall_ne
  normChain_single diffChain_single)

namespace SKEFTHawking.KummerQuotientTransferInt

/-- The `τ`-image of a point, unbundled (`qmk`-fibre mate). -/
noncomputable abbrev tauPt (x : ↥puncturedTorus) : ↥puncturedTorus := tauC x

/-- `qmk (τ x) = qmk x` — the projection coequalizes the deck involution pointwise. -/
theorem qmk_tauPt (x : ↥puncturedTorus) : qmk (tauPt x) = qmk x := qmk_neg_one_smul x

/-- The realization of a `Q`-simplex. -/
noncomputable def rlQ {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    C(stdSimplex ℝ (Fin (n + 1)), FreeQuotient) :=
  Qtop.toSSetObjEquiv (op (SimplexCategory.mk n)) σ

/-- **The freeness of the deck involution at simplex level**: `tauC` moves every `T⁴°`-simplex. -/
theorem mapSimplex_tauC_ne {n : ℕ}
    (τ : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n))) :
    mapSimplex tauC τ ≠ τ :=
  mapSimplex_ne_of_forall_ne (fun x => tauC_free x) τ

/-! ## §1. The unique two-fold lift -/

/-- **The unique lift of a `Q`-simplex** at a chosen fibre point over its barycenter value. -/
noncomputable def liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) (e₀ : ↥puncturedTorus)
    (he : qmk e₀ = rlQ σ (bary n)) :
    (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n)) :=
  (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (qmk_isCoveringMap.existsUnique_continuousMap_lifts (rlQ σ) (bary n) e₀ he).exists.choose

/-- The lift's defining properties, packaged: it sits over `σ` and hits `e₀` at the barycenter. -/
theorem liftSimplex_spec {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) (e₀ : ↥puncturedTorus)
    (he : qmk e₀ = rlQ σ (bary n)) :
    (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he)) (bary n) = e₀ ∧
      qmk ∘ (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
        = rlQ σ := by
  have hspec :=
    (qmk_isCoveringMap.existsUnique_continuousMap_lifts (rlQ σ) (bary n) e₀ he).exists.choose_spec
  rw [liftSimplex, Equiv.apply_symm_apply]
  exact hspec

/-- **The lift sits over `σ`**: pushing forward along the covering recovers `σ`. -/
theorem mapSimplex_liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) (e₀ : ↥puncturedTorus)
    (he : qmk e₀ = rlQ σ (bary n)) :
    mapSimplex qmkC (liftSimplex σ e₀ he) = σ := by
  rw [mapSimplex, Equiv.symm_apply_eq]
  refine ContinuousMap.ext (fun d => ?_)
  have h := (liftSimplex_spec σ e₀ he).2
  exact congrFun h d

/-- **Uniqueness**: any simplex over `σ` hitting `e₀` at the barycenter IS the lift. -/
theorem liftSimplex_unique {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) (e₀ : ↥puncturedTorus)
    (he : qmk e₀ = rlQ σ (bary n))
    (τ : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n)))
    (hτ0 : (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) = e₀)
    (hτ : qmk ∘ (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlQ σ) :
    τ = liftSimplex σ e₀ he := by
  have huniq :=
    (qmk_isCoveringMap.existsUnique_continuousMap_lifts (rlQ σ) (bary n) e₀ he).unique
      (y₁ := PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      (y₂ := PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
      ⟨hτ0, hτ⟩ (liftSimplex_spec σ e₀ he)
  exact (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n))).injective huniq

/-- The canonical fibre point over a simplex's barycenter value. -/
noncomputable def outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) : ↥puncturedTorus :=
  Quotient.out (rlQ σ (bary n))

theorem mk_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    qmk (outFiber σ) = rlQ σ (bary n) :=
  Quotient.out_eq _

theorem mk_tau_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    qmk (tauPt (outFiber σ)) = rlQ σ (bary n) :=
  (qmk_tauPt _).trans (mk_outFiber σ)

/-- The `+`-lift (at the canonical fibre point). -/
noncomputable def liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ (outFiber σ) (mk_outFiber σ)

/-- The `−`-lift (at the deck-translated fibre point). -/
noncomputable def liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ (tauPt (outFiber σ)) (mk_tau_outFiber σ)

/-- **The two lifts are distinct** — they differ at the barycenter (`tauC` is free). -/
theorem liftPlus_ne_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    liftPlus σ ≠ liftMinus σ := by
  intro h
  have h1 := (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).1
  have h2 := (liftSimplex_spec σ (tauPt (outFiber σ)) (mk_tau_outFiber σ)).1
  have hval := congrArg
    (fun τ => (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  simp only at hval
  rw [show liftSimplex σ (outFiber σ) (mk_outFiber σ) = liftPlus σ from rfl] at h1
  rw [show liftSimplex σ (tauPt (outFiber σ)) (mk_tau_outFiber σ) = liftMinus σ from rfl] at h2
  rw [h1, h2] at hval
  exact tauC_free (outFiber σ) hval.symm

@[simp] theorem mapSimplex_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    mapSimplex qmkC (liftPlus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

@[simp] theorem mapSimplex_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    mapSimplex qmkC (liftMinus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

/-- **The deck involution exchanges the two lifts**: `τ_#(lift₊σ) = lift₋σ`. -/
theorem mapSimplex_tauC_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    mapSimplex tauC (liftPlus σ) = liftMinus σ := by
  refine liftSimplex_unique σ (tauPt (outFiber σ)) (mk_tau_outFiber σ) _ ?_ ?_
  · rw [mapSimplex, Equiv.apply_symm_apply]
    show tauC ((PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) (bary n))
      = tauPt (outFiber σ)
    have h1 : (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) (bary n)
        = outFiber σ := (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).1
    rw [h1]
  · rw [mapSimplex, Equiv.apply_symm_apply]
    funext d
    show qmk (tauC ((PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) d))
      = rlQ σ d
    rw [show qmk (tauC ((PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) d))
        = qmk ((PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) (liftPlus σ)) d) from
      qmk_tauPt _]
    exact congrFun (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).2 d

/-- **The deck involution exchanges the two lifts**: `τ_#(lift₋σ) = lift₊σ`. -/
theorem mapSimplex_tauC_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    mapSimplex tauC (liftMinus σ) = liftPlus σ := by
  have h := congrArg (mapSimplex tauC) (mapSimplex_tauC_liftPlus σ)
  rw [mapSimplex_mapSimplex tauC_comp_self] at h
  exact h.symm

/-- **Every `T⁴°`-simplex is one of the two lifts of its pushforward.** -/
theorem mem_pair_of_pushforward {n : ℕ}
    (τ : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n))) :
    τ = liftPlus (mapSimplex qmkC τ) ∨ τ = liftMinus (mapSimplex qmkC τ) := by
  set F := mapSimplex qmkC τ with hF
  have h1 : rlQ F = qmkC.comp (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
    rw [rlQ, hF, mapSimplex, Equiv.apply_symm_apply]
  set y := (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) with hy
  have hmk : qmk y = rlQ F (bary n) :=
    (congrFun (congrArg DFunLike.coe h1) (bary n)).symm
  have hcirc : qmk ∘ (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlQ F :=
    (congrArg DFunLike.coe h1).symm
  rcases fiber_pair (hmk.trans (mk_outFiber F).symm) with hcase | hcase
  · left
    exact liftSimplex_unique F (outFiber F) (mk_outFiber F) τ (hy ▸ hcase) hcirc
  · right
    exact liftSimplex_unique F (tauPt (outFiber F)) (mk_tau_outFiber F) τ (hy ▸ hcase) hcirc

/-- **Two lifts of the same simplex agreeing anywhere are equal** — covering uniqueness on the
preconnected simplex (`IsCoveringMap.eq_of_comp_eq`). -/
theorem liftSimplex_eq_of_agree {n : ℕ}
    (τ τ' : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk n)))
    (hover : mapSimplex qmkC τ = mapSimplex qmkC τ')
    (d : stdSimplex ℝ (Fin (n + 1)))
    (hd : (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) d
      = (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ') d) : τ = τ' := by
  have hcomp : qmk ∘ (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      = qmk ∘ (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ') := by
    have h1 := congrArg (Qtop.toSSetObjEquiv (op (SimplexCategory.mk n))) hover
    rw [mapSimplex, mapSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact congrArg DFunLike.coe h1
  have := qmk_isCoveringMap.eq_of_comp_eq
    (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous
    (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ').continuous
    hcomp d hd
  exact (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    (ContinuousMap.coe_injective this)

/-! ## §2. The face calculus of the lift pair -/

/-- **A face of a lift is one of the two lifts of the face.** -/
theorem face_lift_mem_pair {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2))
    (τ : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk (n + 1))))
    (hτ : mapSimplex qmkC τ = σ) :
    face i τ = liftPlus (face i σ) ∨ face i τ = liftMinus (face i σ) := by
  have hover : mapSimplex qmkC (face i τ) = face i σ := by
    rw [show mapSimplex qmkC (face i τ) = face i (mapSimplex qmkC τ) from
      (face_mapSimplex qmkC τ i).symm, hτ]
  rcases mem_pair_of_pushforward (face i τ) with h | h
  · left; rw [h, hover]
  · right; rw [h, hover]

/-- **Faces of the two lifts are distinct** — else the lifts agree at a face-embedded point,
forcing them equal by covering uniqueness, contradicting the barycenter separation. -/
theorem face_liftPlus_ne_face_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    face i (liftPlus σ) ≠ face i (liftMinus σ) := by
  intro h
  refine liftPlus_ne_liftMinus σ ?_
  refine liftSimplex_eq_of_agree (liftPlus σ) (liftMinus σ)
    ((mapSimplex_liftPlus σ).trans (mapSimplex_liftMinus σ).symm)
    ((⟨_root_.stdSimplex.map (SimplexCategory.δ i),
      _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩ :
        C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2)))) (bary n)) ?_
  have h1 : (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n))
        (SKEFTHawking.SingularCohomologyMod2.face i (liftPlus σ))) (bary n)
      = (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n))
        (SKEFTHawking.SingularCohomologyMod2.face i (liftMinus σ))) (bary n) :=
    congrArg (fun τ => (PTtop.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  rwa [SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face,
    SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face] at h1

/-- **The face pair-sum identity** (integral): the faces of the two lifts of `σ` are, as a chain,
the two lifts of the face. -/
theorem face_pair_sum {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk (n + 1))))
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

/-- **The integral transfer** `tr : Cₙ(Q;ℤ) → Cₙ(T⁴°;ℤ)`: each simplex to the sum of its two
lifts (at the fixed canonical fibre choice `Quotient.out`). -/
noncomputable def transferChainInt (n : ℕ) :
    SingularChainInt Qtop n →ₗ[ℤ] SingularChainInt PTtop n :=
  Finsupp.linearCombination ℤ
    (fun σ => Finsupp.single (liftPlus σ) 1 + Finsupp.single (liftMinus σ) 1)

@[simp] theorem transferChainInt_single {n : ℕ}
    (σ : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    transferChainInt n (Finsupp.single σ a)
      = Finsupp.single (liftPlus σ) a + Finsupp.single (liftMinus σ) a := by
  rw [transferChainInt, Finsupp.linearCombination_single, smul_add, Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **`p_# ∘ tr = 2`** (integral): both lifts push forward to the same simplex. -/
theorem mapChainInt_transferChainInt (n : ℕ) (c : SingularChainInt Qtop n) :
    mapChainInt qmkC n (transferChainInt n c) = 2 • c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, smul_add]
  | single σ a =>
      rw [transferChainInt_single, map_add, mapChainInt_single, mapChainInt_single,
        mapSimplex_liftPlus, mapSimplex_liftMinus, ← Finsupp.single_add, two_smul,
        Finsupp.single_add]

/-- **`tr ∘ p_# = N_#`** — the transfer of the pushforward is the norm: simplex-wise, the two
lifts of `p σ` are `{σ, τ_# σ}`. The chain-level engine of the solve's injectivity leg
`t ∘ p̄ = 1 + τ_*` on homology. -/
theorem transferChainInt_mapChainInt (n : ℕ) (c : SingularChainInt PTtop n) :
    transferChainInt n (mapChainInt qmkC n c) = normChain tauC n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single σ a =>
      rw [mapChainInt_single, transferChainInt_single, normChain_single]
      rcases mem_pair_of_pushforward σ with hp | hp
      · rw [← hp, show mapSimplex tauC σ = liftMinus (mapSimplex qmkC σ) by
          rw [show liftMinus (mapSimplex qmkC σ) = mapSimplex tauC (liftPlus (mapSimplex qmkC σ))
            from (mapSimplex_tauC_liftPlus _).symm, ← hp]]
      · rw [← hp, show mapSimplex tauC σ = liftPlus (mapSimplex qmkC σ) by
          rw [show liftPlus (mapSimplex qmkC σ) = mapSimplex tauC (liftMinus (mapSimplex qmkC σ))
            from (mapSimplex_tauC_liftMinus _).symm, ← hp], add_comm]

/-- **The transfer is a chain map**: `∂ ∘ tr = tr ∘ ∂` — per-face via the pair-sum identity,
with the alternating signs riding along. -/
theorem chainBoundary_transferChainInt (n : ℕ) (c : SingularChainInt Qtop (n + 1)) :
    chainBoundary PTtop n (transferChainInt (n + 1) c)
      = transferChainInt n (chainBoundary Qtop n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
      have hone : chainBoundary PTtop n (transferChainInt (n + 1) (Finsupp.single σ (1 : ℤ)))
          = transferChainInt n (chainBoundary Qtop n (Finsupp.single σ 1)) := by
        rw [transferChainInt_single, map_add,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          SKEFTHawking.SingularHomologyInt.chainBoundary_single,
          boundaryBasis, boundaryBasis, boundaryBasis, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, transferChainInt_single, ← smul_add, face_pair_sum]
      calc chainBoundary PTtop n (transferChainInt (n + 1) (Finsupp.single σ a))
          = chainBoundary PTtop n (transferChainInt (n + 1) (a • Finsupp.single σ (1 : ℤ))) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        _ = a • chainBoundary PTtop n (transferChainInt (n + 1) (Finsupp.single σ (1 : ℤ))) := by
            rw [map_smul, map_smul]
        _ = a • transferChainInt n (chainBoundary Qtop n (Finsupp.single σ (1 : ℤ))) := by
            rw [hone]
        _ = transferChainInt n (chainBoundary Qtop n (Finsupp.single σ a)) := by
            rw [← map_smul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §4. The coefficient calculus and the SES facts -/

/-- **The 2-to-1 coefficient formula**: the pushforward's coefficient at `β` is the sum of the
coefficients at `β`'s two lifts. -/
theorem mapChainInt_apply_pair {n : ℕ} (c : SingularChainInt PTtop n)
    (β : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    mapChainInt qmkC n c β = c (liftPlus β) + c (liftMinus β) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply, Finsupp.add_apply]
      ring
  | single σ a =>
      classical
      rw [mapChainInt_single, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hβ : mapSimplex qmkC σ = β
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
theorem transferChainInt_apply_liftPlus {n : ℕ} (c : SingularChainInt Qtop n)
    (β : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk n))) :
    transferChainInt n c (liftPlus β) = c β := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single σ a =>
      classical
      have hML : liftMinus σ ≠ liftPlus β := by
        intro h
        have h2 := congrArg (mapSimplex qmkC) h
        rw [mapSimplex_liftMinus, mapSimplex_liftPlus] at h2
        subst h2
        exact liftPlus_ne_liftMinus σ h.symm
      rw [transferChainInt_single, Finsupp.add_apply, Finsupp.single_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases hσ : σ = β
      · rw [if_pos (show liftPlus σ = liftPlus β by rw [hσ]), if_neg hML, add_zero, if_pos hσ]
      · rw [if_neg (fun h => hσ (by
            have h2 := congrArg (mapSimplex qmkC) h
            rwa [mapSimplex_liftPlus, mapSimplex_liftPlus] at h2)),
          if_neg hML, if_neg hσ, add_zero]

/-- **The transfer is injective** — read off the `+`-lift coefficients. -/
theorem transferChainInt_injective (n : ℕ) : Function.Injective (transferChainInt n) := by
  intro c d h
  ext β
  have h1 := congrArg (fun x => x (liftPlus β)) h
  simpa only [transferChainInt_apply_liftPlus] using h1

/-- **`p_#` is surjective** — every base simplex lifts through `liftPlus` (SES-III's epi). -/
theorem mapChainInt_surjective (n : ℕ) : Function.Surjective (mapChainInt qmkC n) := by
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
theorem mapChainInt_diffChain (n : ℕ) (c : SingularChainInt PTtop n) :
    mapChainInt qmkC n (diffChain tauC n c) = 0 := by
  show mapChainInt qmkC n (c - mapChainInt tauC n c) = 0
  rw [map_sub, ← SKEFTHawking.SingularFunctorialityInt.mapChainInt_comp, qmkC_comp_tauC,
    sub_self]

/-- **`ker p_# = im D_#`** — the exactness heart of the integral Smith SES-III: an integral chain
killed by `p_#` has its coefficients deck-opposite (`mapChainInt_apply_pair`), so subtracting
`D`-images strips its support one orbit at a time. -/
theorem mem_range_diffChain_of_mapChainInt_eq_zero {n : ℕ}
    (c : SingularChainInt PTtop n) (hc : mapChainInt qmkC n c = 0) :
    c ∈ LinearMap.range (diffChain tauC n) := by
  classical
  suffices H : ∀ (N : ℕ) (c : SingularChainInt PTtop n), c.support.card ≤ N →
      mapChainInt qmkC n c = 0 → c ∈ LinearMap.range (diffChain tauC n) from
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
      · set β := mapSimplex qmkC σ₀ with hβ
        have hsum : c (liftPlus β) + c (liftMinus β) = 0 := by
          rw [← mapChainInt_apply_pair, hc]
          rfl
        set a := c (liftPlus β) with ha
        have hM : c (liftMinus β) = -a := by linarith [hsum]
        set c' := c - diffChain tauC n (Finsupp.single (liftPlus β) a) with hc'
        have hc'0 : mapChainInt qmkC n c' = 0 := by
          rw [hc', map_sub, hc, mapChainInt_diffChain, sub_zero]
        have hDσ : diffChain tauC n (Finsupp.single (liftPlus β) a)
            = Finsupp.single (liftPlus β) a - Finsupp.single (liftMinus β) a := by
          rw [diffChain_single, mapSimplex_tauC_liftPlus]
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
    LinearMap.ker (mapChainInt qmkC n) = LinearMap.range (diffChain tauC n) := by
  ext c
  constructor
  · exact fun hc => mem_range_diffChain_of_mapChainInt_eq_zero c (LinearMap.mem_ker.mp hc)
  · rintro ⟨d, rfl⟩
    exact LinearMap.mem_ker.mpr (mapChainInt_diffChain n d)

/-- **`im tr = im N_#`** — the transfer lands exactly on the norm subcomplex `A_* = N·C_*(T⁴°)`:
`tr` is the chain iso `C_*(Q;ℤ) ≅ A_*` (with `transferChainInt_injective` and
`chainBoundary_transferChainInt`). -/
theorem range_transferChainInt_eq_range_normChain (n : ℕ) :
    LinearMap.range (transferChainInt n) = LinearMap.range (normChain tauC n) := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    induction d using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add c d hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
    | single σ a =>
        refine ⟨Finsupp.single (liftPlus σ) a, ?_⟩
        rw [normChain_single, mapSimplex_tauC_liftPlus, transferChainInt_single]
  · rintro ⟨d, rfl⟩
    induction d using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add c d hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
    | single σ a =>
        rw [normChain_single]
        rcases mem_pair_of_pushforward σ with hp | hp
        · refine ⟨Finsupp.single (mapSimplex qmkC σ) a, ?_⟩
          rw [transferChainInt_single, ← hp, ← mapSimplex_tauC_liftPlus, ← hp]
        · refine ⟨Finsupp.single (mapSimplex qmkC σ) a, ?_⟩
          rw [transferChainInt_single, ← hp, ← mapSimplex_tauC_liftMinus, ← hp, add_comm]

end SKEFTHawking.KummerQuotientTransferInt


