/-
# The homology-level transfer relation `p_* ∘ tr_* = 2` on `H_*(ℝP³;ℤ)`

The degree-2 pin of the antipodal double cover `S³ → ℝP³` at homology level, in every degree:
the chain-level composite identity `p_# ∘ tr = 2` (`mapChainInt_transferChainInt`, banked) pushed
through the abstract-homology functor. The route is the `Hmap`-functoriality one: the composite
`p_* ∘ tr_*` **is** the map induced by the single chain map `p_# ∘ tr` (`Hmap_comp`), and a chain
map whose values are uniformly `2 • x` induces `2 • id` (`Hmap_eq_smul_of_forall`) — no reduction
through any corestriction is ever attempted.

* `transferHml` — the homology-level transfer `tr_* : Hₙ(ℝP³;ℤ) → Hₙ(S³;ℤ)`;
* `projHml_transferHml` — `p_* ∘ tr_* = 2 • id` in engine (`Hml`) form;
* `projHomRP3_transferHml` — the same relation tied to the banked covering-projection
  `KummerRP3Covering.projHomRP3` on the `Homology` carrier.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.KummerRP3TransferInt
import SKEFTHawking.ChainComplexLESInt

open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C projHomRP3)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt chainBoundary_mapChainInt Homology.mapInt)
open SKEFTHawking.KummerRP3TransferInt (transferChainInt chainBoundary_transferChainInt
  mapChainInt_transferChainInt)

namespace SKEFTHawking.KummerRP3TransferHomology

noncomputable section

/-- **The homology-level transfer** `tr_* : Hₙ(ℝP³;ℤ) → Hₙ(S³;ℤ)` of the antipodal double cover,
induced by the integral chain transfer (`Hmap` of `transferChainInt`). -/
def transferHml (n : ℕ) :
    Hml (chainBoundary RP3top) n →ₗ[ℤ] Hml (chainBoundary S3top) n :=
  Hmap (f := transferChainInt) chainBoundary_transferChainInt n

/-- The covering projection `p_*` in engine (`Hml`) form. -/
def projHml (n : ℕ) :
    Hml (chainBoundary S3top) n →ₗ[ℤ] Hml (chainBoundary RP3top) n :=
  Hmap (f := fun k => mapChainInt mkRP3C k) (fun _k x => chainBoundary_mapChainInt mkRP3C x) n

/-- **`p_* ∘ tr_* = 2` on `Hₙ(ℝP³;ℤ)`** (engine form) — the transfer relation of the antipodal
double cover: the composite is the map induced by the single chain map `p_# ∘ tr`
(`Hmap_comp`), whose values are uniformly `2 • x` (`mapChainInt_transferChainInt`). -/
theorem projHml_transferHml (n : ℕ) (x : Hml (chainBoundary RP3top) n) :
    projHml n (transferHml n x) = (2 : ℤ) • x := by
  have hcomp := Hmap_comp (dP := chainBoundary RP3top)
    chainBoundary_transferChainInt (fun _k x => chainBoundary_mapChainInt mkRP3C x)
    (fun k x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, chainBoundary_mapChainInt,
        chainBoundary_transferChainInt])
    n x
  refine hcomp.trans ?_
  refine Hmap_eq_smul_of_forall _ (fun k c => ?_) n x
  rw [LinearMap.comp_apply, mapChainInt_transferChainInt, two_smul, two_smul]

/-- **`p_* ∘ tr_* = 2` on the banked `Homology` carrier** — the transfer relation tied to the
banked covering-projection `projHomRP3`. -/
theorem projHomRP3_transferHml (n : ℕ) (h : Homology RP3top n) :
    projHomRP3 n (transferHml n h) = (2 : ℤ) • h := by
  have hbr : ∀ w : Hml (chainBoundary S3top) n, projHomRP3 n w = projHml n w := by
    intro w
    obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary S3top) n w
    show Homology.mapInt mkRP3C n (SKEFTHawking.SingularHomologyInt.Homology.mk S3top n z) = _
    rw [SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk]
    rfl
  rw [hbr]
  exact projHml_transferHml n h

end

end SKEFTHawking.KummerRP3TransferHomology
