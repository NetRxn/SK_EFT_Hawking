import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder

/-!
# Phase 5q.H — THE CLOPEN-PIECE CYLINDER HOMEOMORPHISM `↥(C ×ˢ univ) ≃ₜ cylW ↥C` (route (b) step 2)

A clopen `C ⊆ M` gives the clopen cylinder piece `U = C ×ˢ univ ⊆ cylW M = M × [0,1]`. Its subspace
`↥U` is homeomorphic to the genuine cylinder `cylW ↥C = ↥C × [0,1]` over the component base `↥C` — the
transport carrier for importing the CONNECTED cylinder fundamental class of `↥C` back to the ambient
piece. Built from Mathlib's `Homeomorph.Set.prod` (`↥(s ×ˢ t) ≃ₜ ↥s × ↥t`) and `Homeomorph.Set.univ`
(`↥(univ : Set α) ≃ₜ α`) on the interval factor.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom.
-/

open SKEFTHawking.PoincareLefschetzRelFundClassCylinder

namespace SKEFTHawking.PinPlusCylComponentHomeo

variable {M : Type} [TopologicalSpace M]

/-- **The clopen-piece cylinder homeomorphism** `↥(C ×ˢ univ) ≃ₜ cylW ↥C`. The piece subspace `↥U`
(`U = C ×ˢ univ ⊆ M × [0,1]`) is the genuine cylinder over the component base `↥C`. -/
def pieceHomeo (C : Set M) :
    ↥(C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) ≃ₜ cylW ↥C :=
  (Homeomorph.Set.prod C (Set.univ : Set (Set.Icc (0 : ℝ) 1))).trans
    ((Homeomorph.refl ↥C).prodCongr (Homeomorph.Set.univ (Set.Icc (0 : ℝ) 1)))

@[simp] theorem pieceHomeo_apply (C : Set M)
    (p : ↥(C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))) :
    pieceHomeo C p = (⟨(p : M × Set.Icc (0 : ℝ) 1).1, p.2.1⟩, (p : M × Set.Icc (0 : ℝ) 1).2) := rfl

@[simp] theorem pieceHomeo_symm_apply (C : Set M) (q : cylW ↥C) :
    (pieceHomeo C).symm q = ⟨((q.1 : M), q.2), ⟨q.1.2, Set.mem_univ _⟩⟩ := rfl

end SKEFTHawking.PinPlusCylComponentHomeo
