/-
# Phase 5q.H — the integral finite disjoint-union homology tool

`Hₙ(Fin m × Y; ℤ) ≅ ⊕_{Fin m} Hₙ(Y; ℤ)` for any space `Y` — a finite product-with-discrete `Fin m × Y`
is `m` disjoint copies of `Y`, and integral homology is additive over a finite disjoint union.

Built by iterating the two-piece integral clopen split `SingularClopenSplitInt.splitHIntEquiv`
(`Hₙ(X;ℤ) ≅ Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ)` for clopen `U`): peel the clopen fibre `{0} ×ˢ univ ≃ₜ Y` off
`Fin (m+1) × Y`, leaving `{i ≠ 0} × Y ≃ₜ Fin m × Y`, and recurse.

The homeomorphism-transport of integral homology reuses the banked
`SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all` (same recipe as
`KummerK7Opener.seamHomologyEquivInt`).

Consumer: the K7 seam is `16 × ℝP³` (`KummerK7Opener.seamHomologyEquivInt` reduces `Hₙ(seam)` to
`Hₙ(EIndex × ℝP³)`); this module's `eIndexProdHnEquivInt` then splits it into the 16 copies, so
`Hₙ(seam) ≅ ⊕₁₆ Hₙ(ℝP³)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularClopenSplitInt
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.KummerWeld

namespace SKEFTHawking.SingularFiniteProdDiscreteHnInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularClopenSplitInt (splitHIntEquiv)

noncomputable section

/-- **Transport integral homology across a homeomorphism of carriers.** The homeomorphism `h`
gives a continuous map both ways whose composites are the identity, so `Homology.mapInt` is
bijective (`SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all`). Same recipe as
`KummerK7Opener.seamHomologyEquivInt`. -/
def homologyCongrInt {X Y : TopCat} (h : (↑X : Type) ≃ₜ (↑Y : Type)) (n : ℕ) :
    Homology X n ≃ₗ[ℤ] Homology Y n :=
  LinearEquiv.ofBijective (Homology.mapInt (X := X) (Y := Y) ⟨h, h.continuous⟩ n)
    (SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all
      (X := X) (Y := Y) ⟨h, h.continuous⟩ ⟨h.symm, h.symm.continuous⟩
      (ContinuousMap.ext fun x => h.symm_apply_apply x)
      (ContinuousMap.ext fun y => h.apply_symm_apply y) n)

variable (Y : TopCat)

/-- The clopen fibre over `0 : Fin (m+1)` inside `Fin (m+1) × Y`. -/
def fibre0 (m : ℕ) : Set (Fin (m + 1) × (↑Y : Type)) := {p | p.1 = 0}

theorem isClopen_fibre0 (m : ℕ) : IsClopen (fibre0 Y m) :=
  (isClopen_discrete ({0} : Set (Fin (m + 1)))).preimage continuous_fst

/-- The clopen fibre `{0} ×ˢ Y` is homeomorphic to `Y` (project to the second coordinate). -/
def peelHomeoU (m : ℕ) : (fibre0 Y m) ≃ₜ (↑Y : Type) where
  toFun p := p.1.2
  invFun y := ⟨(0, y), rfl⟩
  left_inv := by
    rintro ⟨⟨i, y⟩, h⟩
    simp only [fibre0, Set.mem_setOf_eq] at h
    exact Subtype.ext (Prod.ext h.symm rfl)
  right_inv := fun y => rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (continuous_const.prodMk continuous_id) _

/-- `{i : Fin (m+1) // i ≠ 0} ≃ Fin m` via `Fin.pred` / `Fin.succ`. -/
def idxEquiv (m : ℕ) : {i : Fin (m + 1) // i ≠ 0} ≃ Fin m where
  toFun p := p.1.pred p.2
  invFun j := ⟨j.succ, Fin.succ_ne_zero j⟩
  left_inv := fun p => by simp
  right_inv := fun j => by simp

/-- The index equiv as a homeomorphism (both sides discrete). -/
def idxHomeo (m : ℕ) : {i : Fin (m + 1) // i ≠ 0} ≃ₜ Fin m :=
  { idxEquiv m with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- The complement of the `0`-fibre. -/
abbrev cofibre0 (m : ℕ) : Set (Fin (m + 1) × (↑Y : Type)) := (fibre0 Y m)ᶜ

/-- The complement of the `0`-fibre splits as `{i ≠ 0} × Y`. -/
def splitHomeo (m : ℕ) :
    (cofibre0 Y m) ≃ₜ ({i : Fin (m + 1) // i ≠ 0} × (↑Y : Type)) where
  toFun p := (⟨p.1.1, fun hc => p.2 hc⟩, p.1.2)
  invFun q := (⟨(q.1.1, q.2), fun hc => q.1.2 hc⟩ : cofibre0 Y m)
  left_inv := fun p => by ext <;> rfl
  right_inv := fun q => by ext <;> rfl
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) _

/-- The complement `Fin (m+1) × Y ∖ ({0} ×ˢ Y)` is homeomorphic to `Fin m × Y`. -/
def peelHomeoUc (m : ℕ) : (cofibre0 Y m) ≃ₜ (Fin m × (↑Y : Type)) :=
  (splitHomeo Y m).trans ((idxHomeo m).prodCongr (Homeomorph.refl (↑Y : Type)))

/-- `M × (Fin m → M) ≃ₗ (Fin (m+1) → M)` via `Fin.cons` — the pi-additivity of the peel. -/
def piFinSuccEquivInt (M : Type) [AddCommGroup M] [Module ℤ M] (m : ℕ) :
    (M × (Fin m → M)) ≃ₗ[ℤ] (Fin (m + 1) → M) where
  toFun q := Fin.cons q.1 q.2
  map_add' a b := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r a := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  invFun f := (f 0, Fin.tail f)
  left_inv q := by simp
  right_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

attribute [local irreducible] homologyCongrInt piFinSuccEquivInt peelHomeoU peelHomeoUc
  SKEFTHawking.SingularClopenSplitInt.splitHIntEquiv

/-- **The integral finite disjoint-union homology tool** (nonempty index):
`Hₙ(Fin (m+1) × Y; ℤ) ≅ (Fin (m+1) → Hₙ(Y; ℤ))` — `Fin (m+1) × Y` is `m+1` disjoint copies of `Y`,
and integral homology is additive over a finite disjoint union. Built by iterating the two-piece
integral clopen split `SingularClopenSplitInt.splitHIntEquiv`. -/
def finProdHnEquivInt (n : ℕ) :
    (m : ℕ) → Homology (TopCat.of (Fin (m + 1) × (↑Y : Type))) n ≃ₗ[ℤ] (Fin (m + 1) → Homology Y n)
  | 0 =>
    (homologyCongrInt (X := TopCat.of (Fin 1 × (↑Y : Type))) (Y := Y)
        (Homeomorph.uniqueProd (Fin 1) (↑Y : Type)) n).trans
      (LinearEquiv.funUnique (Fin 1) ℤ (Homology Y n)).symm
  | m + 1 =>
    (splitHIntEquiv (X := TopCat.of (Fin (m + 1 + 1) × (↑Y : Type)))
          (isClopen_fibre0 Y (m + 1)) n).symm.trans
      (((homologyCongrInt (peelHomeoU Y (m + 1)) n).prodCongr
            ((homologyCongrInt (peelHomeoUc Y (m + 1)) n).trans (finProdHnEquivInt n m))).trans
        (piFinSuccEquivInt (Homology Y n) (m + 1)))

/-! ## §2. The K7 seam specialisation — `Hₙ(16 × ℝP³; ℤ) ≅ ⊕₁₆ Hₙ(ℝP³; ℤ)` -/

open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerResolutionPiece (RP3)

/-- `EIndex ≃ Fin 16` from the 16-element count (`KummerWeld.eIndex_card`). -/
def eIndexEquivFin : EIndex ≃ Fin 16 := Fintype.equivFinOfCardEq KummerWeld.eIndex_card

/-- `EIndex × ℝP³ ≃ₜ Fin 16 × ℝP³` — the index reindexed (`EIndex` is finite hence discrete via
`Finite.instDiscreteTopology`, so the reindexing bijection is a homeomorphism). -/
def seamProdHomeo : (EIndex × RP3) ≃ₜ (Fin 16 × RP3) :=
  { toEquiv := eIndexEquivFin.prodCongr (Equiv.refl RP3)
    continuous_toFun := continuous_of_discreteTopology.prodMap continuous_id
    continuous_invFun := continuous_of_discreteTopology.prodMap continuous_id }

/-- **The K7 seam disjoint-union decomposition** `Hₙ(EIndex × ℝP³; ℤ) ≅ (EIndex → Hₙ(ℝP³; ℤ))` —
the 16 disjoint `ℝP³` seam copies split integral homology additively. Composed with
`KummerK7Opener.seamHomologyEquivInt` (which reduces `Hₙ(seam)` to `Hₙ(EIndex × ℝP³)`), this gives
`Hₙ(seam) ≅ ⊕₁₆ Hₙ(ℝP³)`, the seam feeder for the K7 Mayer–Vietoris `b₂` accounting. -/
def eIndexProdHnEquivInt (n : ℕ) :
    Homology (TopCat.of (EIndex × RP3)) n ≃ₗ[ℤ] (EIndex → Homology (TopCat.of RP3) n) :=
  (homologyCongrInt (X := TopCat.of (EIndex × RP3)) (Y := TopCat.of (Fin 16 × RP3))
      seamProdHomeo n).trans
    ((finProdHnEquivInt (TopCat.of RP3) n 15).trans
      (LinearEquiv.funCongrLeft ℤ (Homology (TopCat.of RP3) n) eIndexEquivFin))

end

end SKEFTHawking.SingularFiniteProdDiscreteHnInt
