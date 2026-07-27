/-
# The transfer exact sequence of `T⁴° → Q`, and `ker t` in degree 3 identified with `H₅(Q;ℤ)`

`KummerQuotientH3Descent` reduced the whole `orientInput` residual to **one** property of one banked
map: `Function.Injective (transferH 3)` (equivalently, `H₃(Q;ℤ)` is 2-torsion-free). This module
supplies the missing structural link that turns that property into a *long-exact-sequence* question,
and then reads the answer off the sequence.

## §1. The missing identification: `A ≅ C(Q)`, hence `Hₙ(A;ℤ) ≅ Hₙ(Q;ℤ)` and `ι_A = t`

The SES-I mono leg `ι_A : Hₙ(A) → Hₙ(T⁴°)` of `KummerQuotientSmithSES` was, until now, a map out of
an *anonymous* Smith subcomplex `A = N·C(T⁴°)`. It is not anonymous: for a **free** involution the
integral transfer `tr : C(Q) → C(T⁴°)` is injective with `im tr = im N = A`
(`KummerQuotientTransferInt.transferChainInt_injective`,
`KummerQuotientTransferInt.range_transferChainInt_eq_range_normChain`) and is a chain map
(`chainBoundary_transferChainInt`). So `tr` corestricts to a levelwise **isomorphism**
`C(Q) ≅ A`, giving

    `qHmlEquivA n : Hₙ(Q;ℤ) ≅ Hₙ(A;ℤ)`   with   `ι_A ∘ qHmlEquivA = t`   (`inclAH_qHmlEquivA`).

This is the exact `Q`-side mirror of the banked `KummerRP3HomologyTop.rHmlEquivAHml` /
`trA_bijective` engine on the `S³ → ℝP³` lane, and it is what makes SES-I a statement about
`H_*(Q;ℤ)` rather than about an unnamed subcomplex.

## §2. The transfer (Gysin) exact sequence

Transporting the two SES-I exactness statements across `qHmlEquivA` gives the classical long exact
sequence of a free double cover, now banked on this project's carriers:

    ⋯ → Hₙ₊₁(B;ℤ) --δ_Q--> Hₙ(Q;ℤ) --t--> Hₙ(T⁴°;ℤ) --D̄--> Hₙ(B;ℤ) → ⋯

(`exact_deltaQ_transferH`, `exact_transferH_diffH`), where `B = D·C(T⁴°)` is the Smith difference
subcomplex — the twisted-coefficient complex of the covering.

## §3. The residual, squeezed between two top-degree vanishings

Exactness at `Hₙ(Q;ℤ)` says `ker t = im δ_Q`, so `t` is injective as soon as `Hₙ₊₁(B;ℤ) = 0`
(`transferH_injective_of_hmlB_succ_eq_zero`). And SES-III exactness at `Hₙ(B)` squeezes `Hₙ(B;ℤ)`
between `Hₙ₊₁(Q;ℤ)` and `Hₙ(T⁴°;ℤ)` (`hmlB_eq_zero_of_squeeze`). In degree 3 this reads

    `H₅(Q;ℤ) = 0`  and  `H₄(T⁴°;ℤ) = 0`   ⟹   `t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)` is injective
                                          ⟹   `H₃(Q;ℤ)` is 2-torsion-free
                                          ⟹   (with even descent) `H₃(K3;ℤ) = 0` and `orientInput`.

Both inputs are **top-degree vanishing statements for 4-dimensional carriers** — `Q` is a
4-manifold, `T⁴°` an *open* 4-manifold — i.e. the residual is no longer a torsion question at all.

## §4. Sharp form: the residual **is** `H₅(Q;ℤ)`

With the (strictly weaker, `Q`-free) pair of `T⁴°` inputs `H₄(T⁴°;ℤ) = H₅(T⁴°;ℤ) = 0`, both SES
connecting maps collapse to isomorphisms and

    `h5QEquivTransferKer : H₅(Q;ℤ) ≅ ker (t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)) = H₃(Q;ℤ)[2]`.

So — *modulo two `T⁴°`-side statements that involve no quotient at all* — the entire remaining
`orientInput` residual equals the fifth integral homology of `Q`. That is a strictly sharper
statement than §3's implication: it is an equivalence, so it also says a nonzero `H₅(Q;ℤ)` would
*produce* 2-torsion in `H₃(Q;ℤ)`. (`transferH_three_injective_iff_h5Q_eq_zero`.)

## Vacuity attack (run, and it fails)

* The conclusion `Function.Injective (transferH 3)` is **equivalent** to the open statement
  "`H₃(Q;ℤ)` is 2-torsion-free" (banked `twoTorsionFree_iff_transferH_three_injective`), which by
  `KummerK3H3SeamWindow.qSeamCoord3_surjective_iff_h3K3_eq_zero` feeds an open computation — so no
  hypothesis-free proof of it can live in this window, and none is claimed.
* The hypotheses are not free either, and §4 proves it: under the two `T⁴°` inputs the conclusion is
  *equivalent* to `H₅(Q;ℤ) = 0`, so any hypothesis-free discharge would in particular compute
  `H₅(Q;ℤ)`. A hypothesis whose removal would compute a homology group of `Q` is not a tautology.
* `qHmlEquivA` itself is not a repackaging of a definition: it rests on the **freeness** of the
  involution through `transferChainInt_injective` and `range_transferChainInt_eq_range_normChain`
  (which in turn rest on `mapSimplex_tauC_ne`, "no simplex is its own `τ`-translate"). For a
  non-free involution `A = N·C` is strictly larger than `im tr` and the statement is false.

## ⛔ Not re-attempted

The degree-1/2 Smith walk (`KummerQuotientH2Solve`) is **not** used and does not lift: its engine is
`X_H1_fixed_eq_zero` (`τ_* = −1` on `H₁`), and one degree up `τ_* = +1` — see the fence recorded in
`KummerQuotientH3Descent`. Nothing here asserts `projH 3` surjective; the route taken is orthogonal
(SES-I via the transfer identification, not SES-III surjectivity).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerQuotientH3Descent

namespace SKEFTHawking.KummerQuotientTransferSequence

open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop tauC qmkC)
open SKEFTHawking.KummerRP3Covering (normChain diffChain)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerQuotientTransferInt (transferChainInt transferChainInt_injective
  range_transferChainInt_eq_range_normChain chainBoundary_transferChainInt)
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3)

noncomputable section

/-! ## §1. The transfer chain isomorphism `C(Q) ≅ A` -/

/-- The integral transfer, corestricted to its range `A = N·C(T⁴°)`: a levelwise linear map
`C(Q) → A`. Well-defined by `range_transferChainInt_eq_range_normChain`, which is where the
**freeness** of the involution enters. -/
def qTrA (n : ℕ) : SingularChainInt Qtop n →ₗ[ℤ] Ac n :=
  (transferChainInt n).codRestrict (Amod n) (fun c => by
    have h : transferChainInt n c ∈ LinearMap.range (transferChainInt n) := ⟨c, rfl⟩
    rwa [range_transferChainInt_eq_range_normChain] at h)

/-- `tr : C(Q) → A` is a chain map. -/
theorem qTrA_chain (n : ℕ) (x : SingularChainInt Qtop (n + 1)) :
    dA n (qTrA (n + 1) x) = qTrA n (chainBoundary Qtop n x) :=
  Subtype.ext (chainBoundary_transferChainInt n x)

/-- `tr : C(Q) → A` is a levelwise isomorphism: injective (`transferChainInt_injective`, from the
free action) and onto `A` (`range tr = range N`). -/
theorem qTrA_bijective (n : ℕ) : Function.Bijective (qTrA n) := by
  constructor
  · intro a b hab
    exact transferChainInt_injective n (congrArg Subtype.val hab)
  · rintro ⟨y, hy⟩
    rw [Amod, ← range_transferChainInt_eq_range_normChain] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩

/-- **`Hₙ(Q;ℤ) ≅ Hₙ(A;ℤ)` in every degree** — the Smith norm subcomplex `A = N·C(T⁴°)` of the free
double cover *is* the chain complex of the quotient, so its homology is `H_*(Q;ℤ)`. This is the
`Q`-side mirror of the banked `KummerRP3HomologyTop.rHmlEquivAHml`. -/
def qHmlEquivA (n : ℕ) : Hml (chainBoundary Qtop) n ≃ₗ[ℤ] Hml dA n :=
  LinearEquiv.ofBijective (Hmap qTrA_chain n)
    (Hmap_bijective_of_bijective qTrA_chain qTrA_bijective n)

/-- **THE IDENTIFICATION: the SES-I mono leg is the transfer.** `ι_A ∘ qHmlEquivA = t`, so every
statement the SES-I long exact sequence makes about `Hₙ(A)` is a statement about `Hₙ(Q;ℤ)` and the
transfer. -/
theorem inclAH_qHmlEquivA (n : ℕ) (y : Hml (chainBoundary Qtop) n) :
    inclAH n (qHmlEquivA n y) = transferH n y := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary Qtop) n y
  rfl

/-- `t = ι_A ∘ qHmlEquivA` as functions. -/
theorem transferH_eq_comp (n : ℕ) :
    ⇑(transferH n) = ⇑(inclAH n) ∘ ⇑(qHmlEquivA n) :=
  funext fun y => (inclAH_qHmlEquivA n y).symm

/-- Transfer-injectivity **is** SES-I mono-leg injectivity. -/
theorem injective_transferH_iff_injective_inclAH (n : ℕ) :
    Function.Injective (transferH n) ↔ Function.Injective (inclAH n) := by
  constructor
  · intro h a b hab
    obtain ⟨y, rfl⟩ := (qHmlEquivA n).surjective a
    obtain ⟨y', rfl⟩ := (qHmlEquivA n).surjective b
    rw [inclAH_qHmlEquivA, inclAH_qHmlEquivA] at hab
    exact congrArg (qHmlEquivA n) (h hab)
  · intro h y y' hyy'
    rw [← inclAH_qHmlEquivA, ← inclAH_qHmlEquivA] at hyy'
    exact (qHmlEquivA n).injective (h hyy')

/-! ## §2. The transfer (Gysin) exact sequence of the free double cover -/

/-- SES-I LES exactness at `Hₙ(T⁴°)`: `ker D̄ = im ι_A` (engine `exact_Hmap_Hmap`). -/
theorem exact_inclAH_diffH (n : ℕ) : Function.Exact (inclAH n) (diffH n) :=
  exact_Hmap_Hmap hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-- The SES-I connecting map read on the quotient: `δ_Q : Hₙ₊₁(B;ℤ) → Hₙ(Q;ℤ)`. -/
def deltaQ (n : ℕ) : Hml dB (n + 1) →ₗ[ℤ] Hml (chainBoundary Qtop) n :=
  (qHmlEquivA n).symm.toLinearMap ∘ₗ deltaI n

/-- `ι_A ∘ δ' = t ∘ δ_Q`: the two readings of the SES-I connecting map agree. -/
theorem transferH_deltaQ (n : ℕ) (b : Hml dB (n + 1)) :
    transferH n (deltaQ n b) = inclAH n (deltaI n b) := by
  rw [← inclAH_qHmlEquivA]
  exact congrArg (inclAH n) ((qHmlEquivA n).apply_symm_apply (deltaI n b))

/-- **Transfer sequence, exactness at `Hₙ(Q;ℤ)`**: `ker (t) = im (δ_Q)`. -/
theorem exact_deltaQ_transferH (n : ℕ) : Function.Exact (deltaQ n) (transferH n) := by
  intro y
  rw [← inclAH_qHmlEquivA]
  constructor
  · intro hy
    obtain ⟨w, hw⟩ := (exact_deltaI_inclAH n (qHmlEquivA n y)).mp hy
    refine ⟨w, ?_⟩
    show (qHmlEquivA n).symm (deltaI n w) = y
    rw [hw, (qHmlEquivA n).symm_apply_apply]
  · rintro ⟨w, rfl⟩
    rw [show qHmlEquivA n (deltaQ n w) = deltaI n w from
      (qHmlEquivA n).apply_symm_apply (deltaI n w)]
    exact (exact_deltaI_inclAH n (deltaI n w)).mpr ⟨w, rfl⟩

/-- **Transfer sequence, exactness at `Hₙ(T⁴°;ℤ)`**: `ker (D̄) = im (t)`. -/
theorem exact_transferH_diffH (n : ℕ) : Function.Exact (transferH n) (diffH n) := by
  intro x
  rw [exact_inclAH_diffH n x]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(qHmlEquivA n).symm a, by rw [← inclAH_qHmlEquivA, (qHmlEquivA n).apply_symm_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨qHmlEquivA n y, inclAH_qHmlEquivA n y⟩

/-! ## §3. The residual squeezed between two top-degree vanishings -/

/-- **`Hₙ₊₁(B;ℤ) = 0 ⟹ t` injective in degree `n`** — exactness at `Hₙ(Q;ℤ)` of the transfer
sequence. -/
theorem transferH_injective_of_hmlB_succ_eq_zero (n : ℕ) (hB : ∀ b : Hml dB (n + 1), b = 0) :
    Function.Injective (transferH n) := by
  rw [injective_transferH_iff_injective_inclAH, injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨w, hw⟩ := (exact_deltaI_inclAH n a).mp ha
  rw [← hw, hB w, map_zero]

/-- **The SES-III squeeze**: `Hₙ(B;ℤ)` is trapped between `Hₙ₊₁(Q;ℤ)` and `Hₙ(T⁴°;ℤ)`, so it
vanishes when both do. -/
theorem hmlB_eq_zero_of_squeeze (n : ℕ)
    (hQ : ∀ x : Hml (chainBoundary Qtop) (n + 1), x = 0)
    (hPT : ∀ x : Hml (chainBoundary PTtop) n, x = 0) (b : Hml dB n) : b = 0 := by
  obtain ⟨z, hz⟩ := (exact_deltaIII_inclBH n b).mp (hPT (inclBH n b))
  rw [← hz, hQ z, map_zero]

/-- **THE REDUCTION.** `H₅(Q;ℤ) = 0` together with `H₄(T⁴°;ℤ) = 0` makes the degree-3 transfer
injective. Both are top-degree vanishing statements for 4-dimensional carriers. -/
theorem transferH_three_injective_of_top_vanishing
    (h5Q : ∀ x : Homology Qtop 5, x = 0) (h4PT : ∀ x : Homology PTtop 4, x = 0) :
    Function.Injective (transferH 3) :=
  transferH_injective_of_hmlB_succ_eq_zero 3 (hmlB_eq_zero_of_squeeze 4 h5Q h4PT)

/-- `H₃(Q;ℤ)` is 2-torsion-free from the two top-degree vanishings, through the banked
`KummerQuotientH3Descent.twoTorsionFree_iff_transferH_three_injective`. -/
theorem twoTorsionFree_of_top_vanishing
    (h5Q : ∀ x : Homology Qtop 5, x = 0) (h4PT : ∀ x : Homology PTtop 4, x = 0)
    (y : Homology (TopCat.of FreeQuotient) 3) (hy : (2 : ℤ) • y = 0) : y = 0 :=
  KummerQuotientH3Descent.twoTorsionFree_iff_transferH_three_injective.mpr
    (transferH_three_injective_of_top_vanishing h5Q h4PT) y hy

/-- **`H₃(K3;ℤ) = 0` from the two top-degree vanishings plus even descent.** Chains the reduction
into `KummerQuotientH3Descent.h3K3_eq_zero_of_twoTorsionFree_of_evenDescent`. -/
theorem h3K3_eq_zero_of_top_vanishing_of_evenDescent
    (h5Q : ∀ x : Homology Qtop 5, x = 0) (h4PT : ∀ x : Homology PTtop 4, x = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v)
    (x : Homology KummerK3top 3) : x = 0 :=
  KummerQuotientH3Descent.h3K3_eq_zero_of_twoTorsionFree_of_evenDescent
    (twoTorsionFree_of_top_vanishing h5Q h4PT) hd x

open scoped SKEFTHawking.KummerK3E1Package in
/-- **The `orientInput` atom** from the two top-degree vanishings plus even descent. -/
theorem nonempty_intOrientation_of_top_vanishing_of_evenDescent
    (h5Q : ∀ x : Homology Qtop 5, x = 0) (h4PT : ∀ x : Homology PTtop 4, x = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Nonempty (SingularHomologyInt.IntOrientation SKEFTHawking.KummerWeld.KummerK3) :=
  KummerQuotientH3Descent.nonempty_intOrientation_of_twoTorsionFree_of_evenDescent
    (twoTorsionFree_of_top_vanishing h5Q h4PT) hd

/-! ## §4. Sharp form: the residual **is** `H₅(Q;ℤ)` -/

/-- `δ³₄ : H₅(Q;ℤ) → H₄(B;ℤ)` is bijective once `H₄(T⁴°;ℤ) = H₅(T⁴°;ℤ) = 0`: surjective because
`ι_B` lands in `H₄(T⁴°) = 0`, injective because `ker δ³₄ = im p̄₅` and `H₅(T⁴°) = 0`. -/
theorem deltaIII_four_bijective (h4PT : ∀ x : Hml (chainBoundary PTtop) 4, x = 0)
    (h5PT : ∀ x : Hml (chainBoundary PTtop) 5, x = 0) : Function.Bijective (deltaIII 4) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨w, hw⟩ := (exact_projH_deltaIII 4 a).mp ha
    rw [← hw, h5PT w, map_zero]
  · intro b
    exact (exact_deltaIII_inclBH 4 b).mp (h4PT (inclBH 4 b))

/-- `δ_Q : H₄(B;ℤ) → H₃(Q;ℤ)` is injective once `H₄(T⁴°;ℤ) = 0`: `ker δ' = im D̄₄` and `D̄₄` starts
from `H₄(T⁴°) = 0`. -/
theorem deltaQ_three_injective (h4PT : ∀ x : Hml (chainBoundary PTtop) 4, x = 0) :
    Function.Injective (deltaQ 3) := by
  rw [deltaQ, LinearMap.coe_comp]
  refine Function.Injective.comp (qHmlEquivA 3).symm.injective ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨w, hw⟩ := (exact_diffH_deltaI 3 a).mp ha
  rw [← hw, h4PT w, map_zero]

/-- **THE SHARP FORM.** Modulo the two `T⁴°`-side vanishings — statements in which the quotient `Q`
does not appear at all — the degree-3 transfer kernel is *exactly* `H₅(Q;ℤ)`:

    `H₅(Q;ℤ) ≅ ker (t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)) = H₃(Q;ℤ)[2]`

(the second equality is the banked `KummerQuotientH3Descent.transferH_three_eq_zero_iff`). The whole
remaining `orientInput` residual is therefore the fifth integral homology of the 4-manifold `Q`. -/
def h5QEquivTransferKer (h4PT : ∀ x : Hml (chainBoundary PTtop) 4, x = 0)
    (h5PT : ∀ x : Hml (chainBoundary PTtop) 5, x = 0) :
    Hml (chainBoundary Qtop) 5 ≃ₗ[ℤ] LinearMap.ker (transferH 3) :=
  (LinearEquiv.ofBijective (deltaIII 4) (deltaIII_four_bijective h4PT h5PT)).trans
    ((LinearEquiv.ofInjective (deltaQ 3) (deltaQ_three_injective h4PT)).trans
      (LinearEquiv.ofEq _ _ (exact_deltaQ_transferH 3).linearMap_ker_eq.symm))

/-- **The residual, as an iff.** Under the two `T⁴°`-side vanishings, `t` is injective in degree 3
**iff** `H₅(Q;ℤ) = 0` — so the hypotheses of §3 are not merely sufficient, they are (given the
`T⁴°` inputs) exactly the residual. In particular no hypothesis-free proof of transfer-injectivity
can be extracted from this window without computing `H₅(Q;ℤ)`. -/
theorem transferH_three_injective_iff_h5Q_eq_zero
    (h4PT : ∀ x : Hml (chainBoundary PTtop) 4, x = 0)
    (h5PT : ∀ x : Hml (chainBoundary PTtop) 5, x = 0) :
    Function.Injective (transferH 3) ↔ ∀ x : Hml (chainBoundary Qtop) 5, x = 0 := by
  constructor
  · intro h x
    have hker : (h5QEquivTransferKer h4PT h5PT x : Hml (chainBoundary Qtop) 3) = 0 := by
      have := (h5QEquivTransferKer h4PT h5PT x).2
      rw [LinearMap.mem_ker] at this
      exact h (this.trans (map_zero (transferH 3)).symm)
    have h0 : h5QEquivTransferKer h4PT h5PT x = 0 := Subtype.ext hker
    have := congrArg (h5QEquivTransferKer h4PT h5PT).symm h0
    rwa [(h5QEquivTransferKer h4PT h5PT).symm_apply_apply, map_zero] at this
  · intro h
    exact transferH_three_injective_of_top_vanishing h (fun x => h4PT x)

end

end SKEFTHawking.KummerQuotientTransferSequence
