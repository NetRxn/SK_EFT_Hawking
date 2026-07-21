/-
# Phase 5q.H — single-copy evaluation of the finite disjoint-union homology splitting

The evaluation rule the δ₁-image analysis needs on top of
`SingularFiniteProdDiscreteHnInt`: pushing a class `y ∈ Hₙ(Y;ℤ)` into the `i`-th copy of
`Fin (m+1) × Y` and splitting lands exactly on `Pi.single i y`:

* `splitHIntEquiv_apply` / `splitHIntEquiv_symm_inl` / `splitHIntEquiv_symm_inr` — the clopen
  additivity equiv evaluated (uniformly in the degree);
* `finProdHnEquivInt_mapInt_single` — the peel-induction evaluation
  `finProdHnEquivInt (ι_i)_* y = Pi.single i y`;
* `eIndexProdHnEquivInt_mapInt_single` — the K7 seam specialisation on `EIndex × ℝP³`
  (`DecidableEq EIndex` is a hypothesis — discharge classically at the use site).

Consumer: `KummerK7Delta1Image` — identifies the 16 abstract generators of
`H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` with the concrete per-seam `ℝP³` generator classes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFiniteProdDiscreteHnInt
import SKEFTHawking.SingularMayerVietorisLESInt

namespace SKEFTHawking.SingularFiniteProdSingleInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp
  Homology.mapInt_id)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularClopenSplitInt (splitHIntEquiv splitHInt splitHInt_zero)
open SKEFTHawking.SingularLineMinusPointInt (splitH0Int)
open SKEFTHawking.SingularRelHomologyInt (homIncl)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt (Homology.mapInt_ambIncl)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt

noncomputable section

/-! ## §1. The clopen additivity equiv, evaluated -/

/-- The forward map of `splitHIntEquiv` IS the inclusion sum, in every degree. -/
theorem splitHIntEquiv_apply {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ)
    (p : Homology (sub U) n × Homology (sub Uᶜ) n) :
    splitHIntEquiv hU n p = homIncl U n p.1 + homIncl Uᶜ n p.2 :=
  match n with
  | 0 => rfl
  | _ + 1 => rfl

/-- The splitting sends a `U`-supported class to its first coordinate. -/
theorem splitHIntEquiv_symm_inl {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ)
    (u : Homology (sub U) n) :
    (splitHIntEquiv hU n).symm (homIncl U n u) = (u, 0) := by
  rw [LinearEquiv.symm_apply_eq, splitHIntEquiv_apply]
  simp

/-- The splitting sends a `Uᶜ`-supported class to its second coordinate. -/
theorem splitHIntEquiv_symm_inr {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ)
    (uc : Homology (sub Uᶜ) n) :
    (splitHIntEquiv hU n).symm (homIncl Uᶜ n uc) = (0, uc) := by
  rw [LinearEquiv.symm_apply_eq, splitHIntEquiv_apply]
  simp

/-- `homologyCongrInt` applied is the transported `mapInt` (definitional). -/
theorem homologyCongrInt_apply {X Y : TopCat} (h : (↑X : Type) ≃ₜ (↑Y : Type)) (n : ℕ)
    (x : Homology X n) :
    homologyCongrInt h n x = Homology.mapInt (X := X) (Y := Y) ⟨h, h.continuous⟩ n x := rfl

/-- `piFinSuccEquivInt` applied is `Fin.cons` (definitional). -/
theorem piFinSuccEquivInt_apply (M : Type) [AddCommGroup M] [Module ℤ M] (m : ℕ)
    (q : M × (Fin m → M)) :
    piFinSuccEquivInt M m q = Fin.cons q.1 q.2 := rfl

/-! ## §2. The copy inclusions -/

variable (Y : TopCat)

/-- The `i`-th copy inclusion `Y → Fin (m+1) × Y`. -/
def finInclC (m : ℕ) (i : Fin (m + 1)) : C(↑Y, Fin (m + 1) × ↑Y) :=
  ⟨fun p => (i, p), continuous_const.prodMk continuous_id⟩

/-- The corestriction of the `0`-th copy inclusion onto the clopen `0`-fibre. -/
def toFibre0C (m : ℕ) :
    C(↑Y, ↑(sub (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (fibre0 Y (m + 1)))) :=
  ⟨fun y => ⟨((0 : Fin (m + 1 + 1)), y), rfl⟩,
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) _⟩

/-- The corestriction of the `j.succ`-th copy inclusion into the cofibre. -/
def toCofibreC (m : ℕ) (j : Fin (m + 1)) :
    C(↑Y, ↑(sub (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (cofibre0 Y (m + 1)))) :=
  ⟨fun y => ⟨(j.succ, y), fun hc => Fin.succ_ne_zero j hc⟩,
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) _⟩

theorem ambIncl_comp_toFibre0C (m : ℕ) :
    (ambIncl (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (fibre0 Y (m + 1))).comp (toFibre0C Y m)
      = finInclC Y (m + 1) 0 :=
  ContinuousMap.ext fun _ => rfl

theorem ambIncl_comp_toCofibreC (m : ℕ) (j : Fin (m + 1)) :
    (ambIncl (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (cofibre0 Y (m + 1))).comp
        (toCofibreC Y m j)
      = finInclC Y (m + 1) j.succ :=
  ContinuousMap.ext fun _ => rfl

/-- The `0`-fibre peel undoes the corestricted inclusion. -/
theorem peelU_comp_toFibre0C (m : ℕ) :
    (⟨peelHomeoU Y (m + 1), (peelHomeoU Y (m + 1)).continuous⟩ :
        C(↑(sub (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (fibre0 Y (m + 1))), ↑Y)).comp
        (toFibre0C Y m)
      = ContinuousMap.id ↑Y :=
  ContinuousMap.ext fun _ => rfl

/-- The cofibre peel carries the corestricted `j.succ`-th inclusion to the `j`-th inclusion. -/
theorem peelUc_comp_toCofibreC (m : ℕ) (j : Fin (m + 1)) :
    (⟨peelHomeoUc Y (m + 1), (peelHomeoUc Y (m + 1)).continuous⟩ :
        C(↑(sub (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (cofibre0 Y (m + 1))),
          Fin (m + 1) × ↑Y)).comp (toCofibreC Y m j)
      = finInclC Y m j := by
  refine ContinuousMap.ext fun y => Prod.ext ?_ rfl
  show (j.succ.pred (Fin.succ_ne_zero j)) = j
  exact Fin.pred_succ j

/-! ## §3. The peel-induction evaluation -/

/-- The `0`-fibre transport: `H(peelU)_* ∘ (toFibre0)_* = id`. -/
theorem congr_peelU_mapInt (n m : ℕ) (y : Homology Y n) :
    (homologyCongrInt (peelHomeoU Y (m + 1)) n) (Homology.mapInt (toFibre0C Y m) n y) = y := by
  rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    peelU_comp_toFibre0C, Homology.mapInt_id, LinearMap.id_apply]

/-- The cofibre transport: `H(peelUc)_* ∘ (toCofibre j)_* = (ι_j)_*`. -/
theorem congr_peelUc_mapInt (n m : ℕ) (j : Fin (m + 1)) (y : Homology Y n) :
    (homologyCongrInt (peelHomeoUc Y (m + 1)) n) (Homology.mapInt (toCofibreC Y m j) n y)
      = Homology.mapInt (Y := TopCat.of (Fin (m + 1) × (↑Y : Type))) (finInclC Y m j) n y := by
  rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    peelUc_comp_toCofibreC]

/-- `Fin.cons` at a `0`-slot value is `Pi.single 0`. -/
theorem fin_cons_zero_single {M : Type} [AddCommGroup M] (m : ℕ) (y : M) :
    (Fin.cons y (0 : Fin m → M) : Fin (m + 1) → M) = Pi.single 0 y := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · rw [Fin.cons_zero, Pi.single_eq_same]
  · rw [Fin.cons_succ, Pi.zero_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero l)]

/-- `Fin.cons 0 (Pi.single j y) = Pi.single j.succ y`. -/
theorem fin_cons_succ_single {M : Type} [AddCommGroup M] (m : ℕ) (j : Fin m) (y : M) :
    (Fin.cons 0 (Pi.single j y) : Fin (m + 1) → M) = Pi.single j.succ y := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · rw [Fin.cons_zero, Pi.single_eq_of_ne (Fin.succ_ne_zero j).symm]
  · rw [Fin.cons_succ]
    rcases eq_or_ne l j with rfl | hne
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hne,
        Pi.single_eq_of_ne (fun h => hne (Fin.succ_injective _ h))]

/-- **Push a class into a copy and split: `Pi.single`.** The core peel induction. -/
theorem finProdHnEquivInt_mapInt_single (n : ℕ) :
    ∀ (m : ℕ) (i : Fin (m + 1)) (y : Homology Y n),
      finProdHnEquivInt Y n m (Homology.mapInt (finInclC Y m i) n y) = Pi.single i y
  | 0, i, y => by
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    simp only [finProdHnEquivInt, LinearEquiv.trans_apply]
    have h1 : (homologyCongrInt (X := TopCat.of (Fin 1 × (↑Y : Type))) (Y := Y)
        (Homeomorph.uniqueProd (Fin 1) (↑Y : Type)) n)
          (Homology.mapInt (finInclC Y 0 0) n y) = y := by
      rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
        show (⟨Homeomorph.uniqueProd (Fin 1) (↑Y : Type),
            (Homeomorph.uniqueProd (Fin 1) (↑Y : Type)).continuous⟩ :
              C(Fin 1 × (↑Y : Type), ↑Y)).comp (finInclC Y 0 0) = ContinuousMap.id ↑Y from
          ContinuousMap.ext fun _ => rfl,
        Homology.mapInt_id, LinearMap.id_apply]
    rw [h1]
    funext j
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    show y = (Pi.single (0 : Fin 1) y : Fin 1 → Homology Y n) 0
    rw [Pi.single_eq_same]
  | m + 1, i, y => by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · -- the 0-fibre case
      have hξ : Homology.mapInt (finInclC Y (m + 1) 0) n y
          = homIncl (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (fibre0 Y (m + 1)) n
              (Homology.mapInt (toFibre0C Y m) n y) := by
        rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
          ambIncl_comp_toFibre0C]
      simp only [finProdHnEquivInt, LinearEquiv.trans_apply]
      rw [hξ, splitHIntEquiv_symm_inl, LinearEquiv.prodCongr_apply]
      dsimp only
      rw [congr_peelU_mapInt Y n m y, map_zero, piFinSuccEquivInt_apply]
      exact fin_cons_zero_single (m + 1) y
    · -- the cofibre case
      have hξ : Homology.mapInt (finInclC Y (m + 1) j.succ) n y
          = homIncl (X := TopCat.of (Fin (m + 1 + 1) × ↑Y)) (cofibre0 Y (m + 1)) n
              (Homology.mapInt (toCofibreC Y m j) n y) := by
        rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
          ambIncl_comp_toCofibreC]
      simp only [finProdHnEquivInt, LinearEquiv.trans_apply]
      rw [hξ, splitHIntEquiv_symm_inr, LinearEquiv.prodCongr_apply]
      dsimp only
      rw [map_zero, LinearEquiv.trans_apply, congr_peelUc_mapInt Y n m j y,
        finProdHnEquivInt_mapInt_single n m j y, piFinSuccEquivInt_apply]
      exact fin_cons_succ_single (m + 1) j y

/-! ## §4. The K7 seam specialisation -/

open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerResolutionPiece (RP3)

/-- The `c`-th seam-copy inclusion `ℝP³ → EIndex × ℝP³`. -/
def eInclC (c : EIndex) : C(RP3, EIndex × RP3) :=
  ⟨fun r => (c, r), continuous_const.prodMk continuous_id⟩

/-- The reindexing carries the `c`-th copy inclusion to the `eIndexEquivFin c`-th one. -/
theorem seamProdHomeo_comp_eInclC (c : EIndex) :
    (⟨seamProdHomeo, seamProdHomeo.continuous⟩ :
        C(EIndex × RP3, Fin 16 × RP3)).comp (eInclC c)
      = finInclC (TopCat.of RP3) 15 (eIndexEquivFin c) :=
  ContinuousMap.ext fun _ => rfl

/-- **The seam single-copy evaluation**: pushing `y ∈ Hₙ(ℝP³;ℤ)` into the `c`-th seam copy and
splitting gives `Pi.single c y`. -/
theorem eIndexProdHnEquivInt_mapInt_single [DecidableEq EIndex] (n : ℕ) (c : EIndex)
    (y : Homology (TopCat.of RP3) n) :
    eIndexProdHnEquivInt n
        (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
          (eInclC c) n y)
      = Pi.single c y := by
  rw [eIndexProdHnEquivInt, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  have h1 : (homologyCongrInt (X := TopCat.of (EIndex × RP3)) (Y := TopCat.of (Fin 16 × RP3))
      seamProdHomeo n)
        (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3)) (eInclC c) n y)
      = Homology.mapInt (finInclC (TopCat.of RP3) 15 (eIndexEquivFin c)) n y := by
    rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
      seamProdHomeo_comp_eInclC]
  rw [h1, finProdHnEquivInt_mapInt_single]
  funext d
  show (Pi.single (eIndexEquivFin c) y : Fin 16 → Homology (TopCat.of RP3) n) (eIndexEquivFin d)
    = (Pi.single c y : EIndex → Homology (TopCat.of RP3) n) d
  rcases eq_or_ne d c with rfl | hne
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (fun h => hne (eIndexEquivFin.injective h)),
      Pi.single_eq_of_ne hne]

end

end SKEFTHawking.SingularFiniteProdSingleInt
