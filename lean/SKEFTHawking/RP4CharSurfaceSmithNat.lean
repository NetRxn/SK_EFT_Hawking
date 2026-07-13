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
open SKEFTHawking.SingularSurfaceIntersectionForm
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu

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

/-! ## The covering-pullback naturality and the connecting-map naturality -/

/-- **Covering-pullback naturality**: `embS2^# ∘ π^#_{S⁴} = π^#_{S²} ∘ emb^#` (both are the pullback
along `mkC_{S⁴} ∘ embS2 = emb ∘ mkC_{S²}`, `covering_square`). -/
theorem cochainPullback_covering_nat (n : ℕ) (a : SingularCochain (TopCat.of RP4) n) :
    cochainPullback embS2C n (cochainPullback RP4Transfer.mkC n a)
      = cochainPullback RP2Transfer.mkC n (cochainPullback embRP2C n a) := by
  funext σ
  show a (mapSimplex RP4Transfer.mkC (mapSimplex embS2C σ))
    = a (mapSimplex embRP2C (mapSimplex RP2Transfer.mkC σ))
  rw [← mapSimplex_comp, ← mapSimplex_comp, covering_square]

/-- The pullback of a cocycle is a cocycle (`δ(emb^# g) = emb^#(δg) = 0`). -/
theorem cochainPullback_embRP2C_cocycle {n : ℕ} (g : SingularCochain (TopCat.of RP4) n)
    (hg : coboundaryₗ (TopCat.of RP4) n g = 0) :
    coboundaryₗ (TopCat.of RP2) n (cochainPullback embRP2C n g) = 0 := by
  show coboundary (TopCat.of RP2) n (cochainPullback embRP2C n g) = 0
  rw [coboundary_cochainPullback,
    show coboundary (TopCat.of RP4) n g = coboundaryₗ (TopCat.of RP4) n g from rfl, hg, map_zero]

/-- **The section-defect is `τ^#_{ℝP²}`-killed**: the `S²`-cochain
`E = embS2^#(s^#_{ℝP⁴} g) − s^#_{ℝP²}(emb^# g)` transfers to `emb^# g − emb^# g = 0`, using the
transfer naturality (`cochainTransfer_natural`) and `τ^# ∘ s^# = id` on both spaces. -/
theorem transfer_section_defect_eq_zero {n : ℕ} (g : SingularCochain (TopCat.of RP4) n) :
    RP2SmithCochain.cochainTransfer n
      (cochainPullback embS2C n (RP4SmithCochain.cochainSection n g)
        - RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g)) = 0 := by
  rw [map_sub, ← cochainTransfer_natural n (RP4SmithCochain.cochainSection n g),
    RP4SmithCochain.cochainTransfer_cochainSection,
    RP2SmithCochain.cochainTransfer_cochainSection, sub_self]

/-- **Connecting-cochain naturality, mod coboundary**: for a cocycle `g`,
`emb^#(conn₄ g) − conn₂(emb^# g) = δF` for some `F` — the section defect `E` is `τ^#₂`-killed
(`transfer_section_defect_eq_zero`), hence `E = π^#₂ F` (`ker τ^# = im π^#`); applying `π^#₂` (which
is injective) to both sides reduces the claim to `δ_{S²}E = δ_{S²}E`. This is the snake naturality of
the covering Smith SES, with the only geometric input the transfer brick. -/
theorem connectingCochain_natural {n : ℕ}
    (g : SingularCochain (TopCat.of RP4) n) (hg : coboundaryₗ (TopCat.of RP4) n g = 0) :
    ∃ F : SingularCochain (TopCat.of RP2) n,
      coboundaryₗ (TopCat.of RP2) n F
        = cochainPullback embRP2C (n + 1) (RP4SmithCochain.connectingCochain n g)
          - RP2SmithCochain.connectingCochain n (cochainPullback embRP2C n g) := by
  obtain ⟨F, hF⟩ := RP2SmithCochain.mem_range_cochainPullback_of_cochainTransfer_eq_zero
    (cochainPullback embS2C n (RP4SmithCochain.cochainSection n g)
      - RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g))
    (transfer_section_defect_eq_zero g)
  refine ⟨F, ?_⟩
  apply RP2SmithCochain.cochainPullback_injective (n + 1)
  have hLHS : cochainPullback RP2Transfer.mkC (n + 1) (coboundaryₗ (TopCat.of RP2) n F)
      = coboundary (TopCat.of S2) n
          (cochainPullback embS2C n (RP4SmithCochain.cochainSection n g)
            - RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g)) := by
    rw [show cochainPullback RP2Transfer.mkC (n + 1) (coboundaryₗ (TopCat.of RP2) n F)
          = coboundary (TopCat.of S2) n (cochainPullback RP2Transfer.mkC n F) from
        (coboundary_cochainPullback RP2Transfer.mkC n F).symm, hF]
  have hRHS : cochainPullback RP2Transfer.mkC (n + 1)
        (cochainPullback embRP2C (n + 1) (RP4SmithCochain.connectingCochain n g)
          - RP2SmithCochain.connectingCochain n (cochainPullback embRP2C n g))
      = coboundary (TopCat.of S2) n (cochainPullback embS2C n (RP4SmithCochain.cochainSection n g))
        - coboundary (TopCat.of S2) n
            (RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g)) := by
    rw [map_sub, ← cochainPullback_covering_nat (n + 1) (RP4SmithCochain.connectingCochain n g),
      RP4SmithCochain.cochainPullback_connectingCochain g hg,
      show coboundaryₗ (TopCat.of S4) n (RP4SmithCochain.cochainSection n g)
          = coboundary (TopCat.of S4) n (RP4SmithCochain.cochainSection n g) from rfl,
      ← coboundary_cochainPullback embS2C n (RP4SmithCochain.cochainSection n g),
      RP2SmithCochain.cochainPullback_connectingCochain (cochainPullback embRP2C n g)
        (cochainPullback_embRP2C_cocycle g hg),
      show coboundaryₗ (TopCat.of S2) n (RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g))
          = coboundary (TopCat.of S2) n
              (RP2SmithCochain.cochainSection n (cochainPullback embRP2C n g)) from rfl]
  rw [hLHS, hRHS]
  exact (coboundaryₗ (TopCat.of S2) n).map_sub _ _

/-- **Naturality of the Smith connecting map under `emb`** (cohomology level):
`emb* (δS_{ℝP⁴} w) = δS_{ℝP²} (emb* w)`. Descends `connectingCochain_natural` through the
cohomology quotient — the difference of representatives is a coboundary. This is exactly the
hypothesis `hnat` of `RP4CharSurfacePushforward.crux_of_smithConnecting_natural`. -/
theorem smithCoConnecting_natural (n : ℕ) (w : Cohomology (TopCat.of RP4) n) :
    cohomologyPullback embRP2C (n + 1) (RP4SmithCochain.smithCoConnecting n w)
      = RP2SmithCochain.smithCoConnecting n (cohomologyPullback embRP2C n w) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show cohomologyPullback embRP2C (n + 1)
      (RP4SmithCochain.smithCoConnecting n (Cohomology.mk (TopCat.of RP4) n g))
    = RP2SmithCochain.smithCoConnecting n
        (cohomologyPullback embRP2C n (Cohomology.mk (TopCat.of RP4) n g))
  rw [RP4SmithCochain.smithCoConnecting_mk, cohomologyPullback_mk, cohomologyPullback_mk,
    RP2SmithCochain.smithCoConnecting_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  obtain ⟨F, hF⟩ := connectingCochain_natural g.1 (LinearMap.mem_ker.mp g.2)
  exact ⟨F, hF⟩

/-- **The degree-1 crux, discharged**: `emb* x = xRP2` — the cohomology pullback of the RP4 degree-1
generator is the RP2 generator, via Smith-connecting naturality + `emb* 1 = 1`. The residual
geometry is closed; nothing is assumed. -/
theorem cruxPullbackGen : RP4CharSurfacePushforward.CruxPullbackGen :=
  RP4CharSurfacePushforward.crux_of_smithConnecting_natural (fun w => smithCoConnecting_natural 0 w)

/-- **THE `hchar` PUSHFORWARD IDENTITY — UNCONDITIONAL.** For every `a ∈ H²(ℝP⁴;ℤ/2)`,
`⟨a, emb₊[ℝP²]⟩ = μ(a ⌣ x²)`: the equatorial surface `ℝP²` is the characteristic surface dual to
`w₁²(ℝP⁴) = x²`. The full `hchar` obligation of the `ℝP⁴` witness — its residual geometry now
discharged (the degree-1 crux `cruxPullbackGen`), so the ∀-pairing identity holds outright. -/
theorem hchar_pairing (a : Cohomology (TopCat.of RP4) 2) :
    kroneckerH 2 a (Homology.map embRP2C 2 (surfaceFundamentalClass (M := RP2)))
      = (poincareDual4Mid_of_closed (M := RP4)).mu
          (cupH24 a (RP4CohomologyLadder.xpow 2)) :=
  RP4CharSurfacePushforward.hchar_pairing cruxPullbackGen a

end SKEFTHawking.RP4CharSurfaceSmithNat
