/-
# Mod-2 reduction naturality of the integral Mayer–Vietoris connecting map

`SingularLocalHomologyRedCompatInt` proves that the ℤ→ℤ/2 reduction commutes with every *stage* map
of the singular tower: the pushforward (`redHomology_homologyMapInt`), the pair connecting map
(`redHomology_connectingInt`), the pair projection (`redRelHomology_homProjInt`) and the excision map
(`redRelHomology_excisionMap`). The Mayer–Vietoris connecting map `δ` is by construction the
Barratt–Whitehead composite of exactly those four stages,

    `mvDeltaInt A B n hcov = seam_* ∘ connectingInt ∘ excisionEquivInt⁻¹ ∘ homProjInt A`,

so its reduction-naturality is a pure composition of the banked squares. This module performs that
composition once, banking

    `redHomology (sub (A∩B)) n ∘ mvDeltaInt A B n hcov = mvDelta A B n hcov ∘ redHomology X (n+1)`,

the bridge that lets an integral MV connecting-map computation be *detected mod 2* — i.e. lets the
unconditional mod-2 Mayer–Vietoris (where every closed manifold is orientable, so the top-degree
local machinery is available without an orientation) certify a parity fact about the integral `δ`.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1** `redRelHomology_excisionEquivInt_symm` — the backwards excision square (the one direction the
  local-homology `redCompat` file did not need, since it only ever pushed excision forwards).
* **§2** `redHomology_mvConnectingInt` — naturality in the `sub (restr A B)` representation.
* **§3** `redHomology_mvDeltaInt` — naturality of the seam-corrected `δ`, the consumer-facing form.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularLocalHomologyRedCompatInt
import SKEFTHawking.SingularMayerVietorisLESInt

namespace SKEFTHawking.SingularMayerVietorisRedCompatInt

open SKEFTHawking.SingularHomologyInt (Homology redHomology)
open SKEFTHawking.SingularRelHomologyInt (RelHomologyInt redRelHomology connectingInt homProjInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularLocalHomologyRedCompatInt

noncomputable section

variable {X : TopCat}

/-! ## §1. The backwards excision square -/

/-- **The reduction commutes with the excision iso RUN BACKWARDS**:
`redRelHomology (restr A B) ∘ excisionEquivInt⁻¹ = excisionEquiv⁻¹ ∘ redRelHomology A`.
Obtained from the forward square (`redRelHomology_excisionMap`) by cancelling the (bijective)
excision maps on both sides — the Mayer–Vietoris `δ` traverses excision in this direction. -/
theorem redRelHomology_excisionEquivInt_symm (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (z : RelHomologyInt A (n + 1)) :
    redRelHomology (restr A B) (n + 1) ((excisionEquivInt A B n hcov).symm z)
      = (SKEFTHawking.SingularExcisionIso.excisionEquiv A B n hcov).symm
          (redRelHomology A (n + 1) z) := by
  refine (SKEFTHawking.SingularExcisionIso.excisionEquiv A B n hcov).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  show SKEFTHawking.SingularExcisionIso.excisionMap A B (n + 1)
      (redRelHomology (restr A B) (n + 1) ((excisionEquivInt A B n hcov).symm z))
    = redRelHomology A (n + 1) z
  rw [← redRelHomology_excisionMap]
  exact congrArg (redRelHomology A (n + 1)) ((excisionEquivInt A B n hcov).apply_symm_apply z)

/-! ## §2. Naturality in the `sub (restr A B)` representation -/

/-- **`redHomology ∘ mvConnectingInt = mvConnecting ∘ redHomology`.** The Barratt–Whitehead composite
`connectingInt ∘ excisionEquivInt⁻¹ ∘ homProjInt A` reduced stage by stage: `redRelHomology_homProjInt`
(§10 of the local-homology `redCompat` file), `redRelHomology_excisionEquivInt_symm` (§1 above), and
`redHomology_connectingInt` (§5 there). -/
theorem redHomology_mvConnectingInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (h : Homology X (n + 1)) :
    redHomology (sub (restr A B)) n
        (SKEFTHawking.SingularMayerVietorisLESInt.mvConnectingInt (X := X) A B n hcov h)
      = SKEFTHawking.SingularMayerVietorisLES.mvConnecting (X := X) A B n hcov
          (redHomology X (n + 1) h) := by
  show redHomology (sub (restr A B)) n
      (connectingInt (restr A B) n ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) h)))
    = SKEFTHawking.SingularPairLES.connecting (restr A B) n
        ((SKEFTHawking.SingularExcisionIso.excisionEquiv A B n hcov).symm
          (SKEFTHawking.SingularPairLES.homProj A (n + 1) (redHomology X (n + 1) h)))
  rw [redHomology_connectingInt, redRelHomology_excisionEquivInt_symm, redRelHomology_homProjInt]

/-! ## §3. Naturality of the seam-corrected `δ` -/

/-- **THE MAYER–VIETORIS `δ` REDUCTION SQUARE**:
`redHomology (sub (A∩B)) n (mvDeltaInt A B n hcov h) = mvDelta A B n hcov (redHomology X (n+1) h)`.
Post-composes §2 with the seam pushforward square (`redHomology_homologyMapInt`), since both seam isos
are `Homology.map`/`Homology.mapInt` of the same coefficient-agnostic homeomorphism `seamHomeo A B`.

This is the bridge that makes an integral MV connecting-map class *detectable mod 2*: a non-vanishing
proved in the (orientation-free, unconditional) mod-2 Mayer–Vietoris transfers to the statement that
the integral `δ`-class survives reduction — hence is not divisible by 2. -/
theorem redHomology_mvDeltaInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (h : Homology X (n + 1)) :
    redHomology (sub (A ∩ B)) n
        (SKEFTHawking.SingularMayerVietorisLESInt.mvDeltaInt (X := X) A B n hcov h)
      = SKEFTHawking.SingularMayerVietorisLES.mvDelta (X := X) A B n hcov
          (redHomology X (n + 1) h) := by
  show redHomology (sub (A ∩ B)) n
      (SKEFTHawking.SingularFunctorialityInt.Homology.mapInt
        ⟨SKEFTHawking.SingularMayerVietorisLES.seamHomeo A B,
          (SKEFTHawking.SingularMayerVietorisLES.seamHomeo A B).continuous⟩ n
        (SKEFTHawking.SingularMayerVietorisLESInt.mvConnectingInt (X := X) A B n hcov h))
    = SKEFTHawking.SingularFunctoriality.Homology.map
        ⟨SKEFTHawking.SingularMayerVietorisLES.seamHomeo A B,
          (SKEFTHawking.SingularMayerVietorisLES.seamHomeo A B).continuous⟩ n
        (SKEFTHawking.SingularMayerVietorisLES.mvConnecting (X := X) A B n hcov
          (redHomology X (n + 1) h))
  rw [redHomology_homologyMapInt, redHomology_mvConnectingInt]

end

end SKEFTHawking.SingularMayerVietorisRedCompatInt
