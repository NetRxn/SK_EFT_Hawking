import Mathlib
import SKEFTHawking.SingularRelativeClopenSplitInt
import SKEFTHawking.SingularFiniteProdDiscreteHnInt
import SKEFTHawking.SingularRelativeFunctorialityInt

/-!
# The integral **relative** finite disjoint-union tool: `Hₙ(Fin m × Y, S; ℤ) ≅ ∏ᵢ Hₙ(Y, Sᵢ; ℤ)`

`SingularFiniteProdDiscreteHnInt.finProdHnEquivInt` splits **absolute** integral homology over a
finite disjoint union `Fin m × Y`. This module is its **relative** mirror: for an *arbitrary*
subspace `S ⊆ Fin m × Y`,

`Hₙ(Fin m × Y, S; ℤ) ≅ (∀ i : Fin m, Hₙ(Y, Sᵢ; ℤ))`,  `Sᵢ := {y | (i, y) ∈ S}`,

built by iterating the new two-piece engine
`SingularRelativeClopenSplitInt.relSplitHnIntEquiv` over exactly the peel of
`SingularFiniteProdDiscreteHnInt` (whose fibre/cofibre homeomorphisms `peelHomeoU` / `peelHomeoUc`
and clopen-ness `isClopen_fibre0` are reused verbatim — only the *homology* layer changes).

The subspace is genuinely arbitrary: it is **not** assumed to be a product, nor to meet every
fibre. That is what the consumer needs — the collar of the Kummer exceptional set is a subspace of
`16 × ResE` with no product structure, so the absolute split cannot see it and the mod-2 relative
split (`SingularRelativeDisjointUnionHn`) cannot see its ℤ-summands.

Contents:
* `relHomologyCongrInt` — transport integral **relative** homology across a homeomorphism of pairs
  (the relative mirror of `SingularFiniteProdDiscreteHnInt.homologyCongrInt`); reusable everywhere.
* `piFinSuccDepEquivInt` — the *dependent* `Fin.cons` linear equivalence
  `M 0 × (∀ j : Fin m, M j.succ) ≃ₗ (∀ i : Fin (m+1), M i)`. The absolute development only needed
  the constant-family version, because there the summands are all `Hₙ(Y)`; here the `i`-th summand
  is `Hₙ(Y, Sᵢ)` and **depends on `i`**.
* `finProdRelHnEquivInt` — the splitting.
* `finProdRelHnEquivInt_indexed` — the `EIndex`-indexed form (`EIndex ≃ Fin 16`), the shape the
  Kummer pair transport `(ESub, CollarInE) → 16 × (ResE, collar)` consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularRelativeClopenSplitInt (relSplitHnIntEquiv)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (fibre0 isClopen_fibre0 peelHomeoU peelHomeoUc
  cofibre0)

namespace SKEFTHawking.SingularRelativeFiniteProdSplitInt

noncomputable section

/-! ## §1. Transport of relative homology across a homeomorphism of pairs -/

/-- **Transport integral relative homology across a homeomorphism of pairs.** The relative mirror of
`SingularFiniteProdDiscreteHnInt.homologyCongrInt`: `h` gives continuous maps of pairs both ways
whose composites are the identity, so `RelHomologyInt.map` is bijective. -/
def relHomologyCongrInt {X Y : TopCat} (h : (↑X : Type) ≃ₜ (↑Y : Type)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : ∀ x : ↑X, h x ∈ B ↔ x ∈ A) (n : ℕ) :
    RelHomologyInt A n ≃ₗ[ℤ] RelHomologyInt B n :=
  LinearEquiv.ofBijective
    (RelHomologyInt.map (⟨h, h.continuous⟩ : C(↑X, ↑Y)) (fun x hx => (hAB x).mpr hx) n)
    (RelHomologyInt.map_bijective_of_comp_id (⟨h, h.continuous⟩ : C(↑X, ↑Y))
      (⟨h.symm, h.symm.continuous⟩ : C(↑Y, ↑X)) (fun x hx => (hAB x).mpr hx)
      (fun y hy => (hAB (h.symm y)).mp (by rw [h.apply_symm_apply]; exact hy))
      (ContinuousMap.ext fun x => h.symm_apply_apply x)
      (ContinuousMap.ext fun y => h.apply_symm_apply y) n)

/-! ## §2. The dependent `Fin.cons` assembly -/

/-- **The dependent `Fin.cons` linear equivalence** `M 0 × (∀ j : Fin m, M j.succ) ≃ₗ ∀ i, M i`.
The absolute development only needed the constant-family version (`piFinSuccEquivInt`); the relative
splitting's `i`-th summand is `Hₙ(Y, Sᵢ)` and genuinely depends on `i`. -/
def piFinSuccDepEquivInt (m : ℕ) (M : Fin (m + 1) → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℤ (M i)] : (M 0 × (∀ j : Fin m, M j.succ)) ≃ₗ[ℤ] (∀ i : Fin (m + 1), M i) where
  toFun q := Fin.cons q.1 q.2
  map_add' a b := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r a := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  invFun f := (f 0, fun j => f j.succ)
  left_inv q := by
    refine Prod.ext ?_ ?_
    · simp
    · funext j; simp
  right_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-! ## §3. The relative splitting -/

variable (Y : TopCat)

/-- The `i`-th fibre slice of a subspace of `Fin m × Y`. -/
def slice {m : ℕ} (S : Set (Fin m × (↑Y : Type))) (i : Fin m) : Set (↑Y : Type) :=
  {y | (i, y) ∈ S}

/-- The subspace pushed down one index level, for the recursion. -/
def shift {m : ℕ} (S : Set (Fin (m + 1 + 1) × (↑Y : Type))) :
    Set (Fin (m + 1) × (↑Y : Type)) := {q | (q.1.succ, q.2) ∈ S}

theorem slice_shift {m : ℕ} (S : Set (Fin (m + 1 + 1) × (↑Y : Type))) (j : Fin (m + 1)) :
    slice Y (shift Y S) j = slice Y S j.succ := rfl

/-- Compatibility of the `0`-fibre chart with the subspace. -/
theorem peelHomeoU_compat {m : ℕ} (S : Set (Fin (m + 1) × (↑Y : Type)))
    (p : ↑(sub (fibre0 Y m))) :
    peelHomeoU Y m p ∈ slice Y S 0
      ↔ p ∈ restr (X := TopCat.of (Fin (m + 1) × (↑Y : Type))) S (fibre0 Y m) := by
  obtain ⟨⟨i, y⟩, hi⟩ := p
  have hi0 : i = 0 := hi
  subst hi0
  exact Iff.rfl

/-- Compatibility of the cofibre chart with the shifted subspace. -/
theorem peelHomeoUc_compat {m : ℕ} (S : Set (Fin (m + 1 + 1) × (↑Y : Type)))
    (p : ↑(sub (cofibre0 Y (m + 1)))) :
    peelHomeoUc Y (m + 1) p ∈ shift Y S
      ↔ p ∈ restr (X := TopCat.of (Fin (m + 1 + 1) × (↑Y : Type))) S (cofibre0 Y (m + 1)) := by
  obtain ⟨⟨i, y⟩, hi⟩ := p
  have hine : i ≠ 0 := hi
  show ((i.pred hine).succ, y) ∈ S ↔ (i, y) ∈ S
  rw [Fin.succ_pred]

/-- Compatibility of the `Fin 1`-collapse with the subspace. -/
theorem uniqueProd_compat (S : Set (Fin 1 × (↑Y : Type))) (p : Fin 1 × (↑Y : Type)) :
    Homeomorph.uniqueProd (Fin 1) (↑Y : Type) p ∈ slice Y S 0 ↔ p ∈ S := by
  obtain ⟨i, y⟩ := p
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact Iff.rfl

/-- **The integral relative finite disjoint-union splitting**
`Hₙ(Fin (m+1) × Y, S; ℤ) ≅ (∀ i, Hₙ(Y, Sᵢ; ℤ))` for an arbitrary subspace `S`. Peels the clopen
`0`-fibre with `SingularRelativeClopenSplitInt.relSplitHnIntEquiv`, transports each piece across the
banked chart homeomorphisms, and recurses. -/
def finProdRelHnEquivInt (n : ℕ) :
    (m : ℕ) → (S : Set (Fin (m + 1) × (↑Y : Type))) →
      RelHomologyInt (X := TopCat.of (Fin (m + 1) × (↑Y : Type))) S n
        ≃ₗ[ℤ] (∀ i : Fin (m + 1), RelHomologyInt (X := Y) (slice Y S i) n)
  | 0, S =>
    (relHomologyCongrInt (X := TopCat.of (Fin 1 × (↑Y : Type))) (Y := Y)
        (Homeomorph.uniqueProd (Fin 1) (↑Y : Type)) (uniqueProd_compat Y S) n).trans
      (LinearEquiv.piUnique (R := ℤ)
        (fun i : Fin 1 => RelHomologyInt (X := Y) (slice Y S i) n)).symm
  | m + 1, S =>
    ((relSplitHnIntEquiv (X := TopCat.of (Fin (m + 1 + 1) × (↑Y : Type)))
          (isClopen_fibre0 Y (m + 1)) S n).symm.trans
        ((relHomologyCongrInt (peelHomeoU Y (m + 1)) (peelHomeoU_compat Y S) n).prodCongr
          ((relHomologyCongrInt (peelHomeoUc Y (m + 1)) (peelHomeoUc_compat Y S) n).trans
            (finProdRelHnEquivInt n m (shift Y S))))).trans
      (piFinSuccDepEquivInt (m + 1)
        (fun i => RelHomologyInt (X := Y) (slice Y S i) n))

/-! ## §4. The `EIndex`-indexed form — the shape the Kummer pair transport consumes -/

open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (eIndexEquivFin)

/-- `EIndex × Y ≃ₜ Fin 16 × Y` (both index types finite hence discrete). -/
def eIndexProdHomeo : (EIndex × (↑Y : Type)) ≃ₜ (Fin 16 × (↑Y : Type)) where
  toEquiv := eIndexEquivFin.prodCongr (Equiv.refl (↑Y : Type))
  continuous_toFun := continuous_of_discreteTopology.prodMap continuous_id
  continuous_invFun := continuous_of_discreteTopology.prodMap continuous_id

/-- **The `EIndex`-indexed integral relative splitting**
`Hₙ(EIndex × Y, S; ℤ) ≅ (∀ i : EIndex, Hₙ(Y, Sᵢ; ℤ))`.

This is exactly the shape of the Kummer pair-level transport `(ESub, CollarInE) → 16 × (ResE,
collar)`: `ESub ≃ₜ EIndex × ResE` (`KummerK7MVAssembly.eImageHomeo`) and `CollarInE` is an arbitrary
subspace of it, so the absolute split (`eIndexProdHnEquivInt`) cannot see it, and the mod-2 relative
split cannot see its ℤ-summands. Composed with `relHomologyCongrInt` along `eImageHomeo`, it turns a
statement about `H₂(ESub, CollarInE; ℤ)` into sixteen statements about `H₂(ResE, collarᵢ; ℤ)` — the
form `KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable` reduces the `b₂` target to. -/
def eIndexProdRelHnEquivInt (S : Set (EIndex × (↑Y : Type))) (n : ℕ) :
    RelHomologyInt (X := TopCat.of (EIndex × (↑Y : Type))) S n
      ≃ₗ[ℤ] (∀ i : EIndex, RelHomologyInt (X := Y) {y | (i, y) ∈ S} n) :=
  (relHomologyCongrInt (X := TopCat.of (EIndex × (↑Y : Type)))
      (Y := TopCat.of (Fin 16 × (↑Y : Type))) (eIndexProdHomeo Y)
      (B := {q : Fin 16 × (↑Y : Type) | (eIndexEquivFin.symm q.1, q.2) ∈ S})
      (fun p => by
        show (eIndexEquivFin.symm (eIndexEquivFin p.1), p.2) ∈ S ↔ p ∈ S
        rw [Equiv.symm_apply_apply]) n).trans
    ((finProdRelHnEquivInt Y n 15 {q : Fin 16 × (↑Y : Type) | (eIndexEquivFin.symm q.1, q.2) ∈ S}).trans
      (LinearEquiv.piCongrLeft' ℤ
        (fun i : EIndex => RelHomologyInt (X := Y) {y | (i, y) ∈ S} n) eIndexEquivFin).symm)

end

end SKEFTHawking.SingularRelativeFiniteProdSplitInt
