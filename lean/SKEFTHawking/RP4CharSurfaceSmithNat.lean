import Mathlib
import SKEFTHawking.RP4CharSurfacePushforward
import SKEFTHawking.RP4SmithCochain
import SKEFTHawking.RP2SmithCochain

/-!
# W-A (n = 2 witness) — the residual geometry: naturality of the covering transfer under `emb`

The geometric heart of the degree-1 crux `emb* x = xRP2` (`RP4CharSurfacePushforward`): the
equatorial inclusion `emb : ℝP² ↪ ℝP⁴` lifts to the equivariant `embS2 : S² → S⁴` on the antipodal
double covers, so it commutes with the **cochain transfers** `τ^# : Cⁿ(S) → Cⁿ(ℝP)`.

The transfer `(τ^#y)(σ) = y(σ₊) + y(σ₋)` is a *symmetric sum over the two lifts*, so it is natural
even though the individual lifts (`liftPlus`/`liftMinus`, chosen via `Quotient.out`) are not: the
image pair `{embS2·σ₊^{ℝP²}, embS2·σ₋^{ℝP²}}` is exactly the lift pair `{τ₊^{ℝP⁴}, τ₋^{ℝP⁴}}` of
`τ = emb·σ` (both cover `τ`, and `embS2` is injective so they are distinct), hence the sums agree.

This banks `cochainTransfer_natural` — one leg of the map of Smith transfer short exact sequences
that the connecting-map naturality (`hnat` in `RP4CharSurfacePushforward`) rides on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/

open Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.RP2PointSet SKEFTHawking.RP4PointSet
open SKEFTHawking.RP2EquatorialInclusion
open SKEFTHawking.RP4CharSurfacePushforward

namespace SKEFTHawking.RP4CharSurfaceSmithNat

/-- **`embS2` as a bundled `ContinuousMap`** `S² → S⁴` — the equivariant lift of `emb`. -/
noncomputable def embS2C : C(↑(TopCat.of S2), ↑(TopCat.of S4)) :=
  ⟨embS2, continuous_embS2⟩

/-- **The covering square** `mkC_{S⁴} ∘ embS2 = emb ∘ mkC_{S²}` — `embS2` intertwines the two
antipodal quotient maps (the point-set `embRP2_mk`). -/
theorem covering_square :
    (RP4Transfer.mkC).comp embS2C = embRP2C.comp (RP2Transfer.mkC) := by
  refine ContinuousMap.ext (fun s => ?_)
  exact (embRP2_mk' s).symm

/-- **`mapSimplex embS2` is injective** — post-composition by the injective `embS2`. -/
theorem mapSimplex_embS2C_injective {n : ℕ} :
    Function.Injective (mapSimplex (X := TopCat.of S2) (Y := TopCat.of S4) (n := n) embS2C) := by
  intro a b hab
  have h1 := congrArg ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n))) hab
  rw [mapSimplex, mapSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
  refine ((TopCat.of S2).toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    (ContinuousMap.ext (fun x => ?_))
  exact embS2_injective (ContinuousMap.congr_fun h1 x)

/-- The image of an RP²-lift under `embS2` covers `emb·σ` in `S⁴` — the covering-square + lift
descent. -/
theorem mapSimplex_mkC_mapSimplex_embS2C_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk n))) :
    mapSimplex RP4Transfer.mkC (mapSimplex embS2C (RP2Transfer.liftPlus σ))
      = mapSimplex embRP2C σ := by
  rw [← mapSimplex_comp, covering_square, mapSimplex_comp, RP2Transfer.mapSimplex_liftPlus]

theorem mapSimplex_mkC_mapSimplex_embS2C_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk n))) :
    mapSimplex RP4Transfer.mkC (mapSimplex embS2C (RP2Transfer.liftMinus σ))
      = mapSimplex embRP2C σ := by
  rw [← mapSimplex_comp, covering_square, mapSimplex_comp, RP2Transfer.mapSimplex_liftMinus]

/-- **Naturality of the cochain transfer under `emb`**:
`emb^#(τ^#_{ℝP⁴} y) = τ^#_{ℝP²}(embS2^# y)`. The symmetric sum over the two lifts is preserved
because `{embS2·σ₊, embS2·σ₋}` is the lift pair of `emb·σ` (distinct via `embS2` injective). -/
theorem cochainTransfer_natural (n : ℕ) (y : SingularCochain (TopCat.of S4) n) :
    cochainPullback embRP2C n (RP4SmithCochain.cochainTransfer n y)
      = RP2SmithCochain.cochainTransfer n (cochainPullback embS2C n y) := by
  funext σ
  rw [cochainPullback_apply, RP4SmithCochain.cochainTransfer_apply,
    RP2SmithCochain.cochainTransfer_apply, cochainPullback_apply, cochainPullback_apply]
  -- Goal: y(τ₊) + y(τ₋) = y(embS2·σ₊) + y(embS2·σ₋), τ = emb·σ.
  set τ := mapSimplex embRP2C σ
  set P2 := mapSimplex embS2C (RP2Transfer.liftPlus σ)
  set M2 := mapSimplex embS2C (RP2Transfer.liftMinus σ)
  have hPτ : mapSimplex RP4Transfer.mkC P2 = τ := mapSimplex_mkC_mapSimplex_embS2C_liftPlus σ
  have hMτ : mapSimplex RP4Transfer.mkC M2 = τ := mapSimplex_mkC_mapSimplex_embS2C_liftMinus σ
  have hne : P2 ≠ M2 := by
    intro h
    exact RP2Transfer.liftPlus_ne_liftMinus σ (mapSimplex_embS2C_injective h)
  have hP := RP4Transfer.mem_pair_of_pushforward P2
  have hM := RP4Transfer.mem_pair_of_pushforward M2
  rw [hPτ] at hP
  rw [hMτ] at hM
  -- P2, M2 ∈ {liftPlus τ, liftMinus τ}, distinct ⟹ they are the two lifts (in some order).
  rcases hP with hP | hP <;> rcases hM with hM | hM
  · exact absurd (hP.trans hM.symm) hne
  · rw [← hP, ← hM]
  · rw [← hP, ← hM]; exact add_comm _ _
  · exact absurd (hP.trans hM.symm) hne

end SKEFTHawking.RP4CharSurfaceSmithNat
