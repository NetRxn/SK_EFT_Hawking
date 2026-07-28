/-
# Phase 5q.H — `heven` is NOT a separate ledger item: the geometric datum already carries it

The welded Kummer `K3`'s E1 residual ledger stood at three inputs
(`KummerK3CapDualFamily.nonempty_kummerK3E1Atoms_of_stable_of_geoData`):

    hstable  —  StableNegRank16Two          (pure lattice theory, wt1's Eichler lane)
    heven    —  ∀ o a, 2 ∣ ⟨a ∪ a, [K3]_o⟩  (Wu / `w₂(K3) = 0`)
    hgeo     —  one cap-dual, cap-spanning geometric datum

`KummerK3EvenFromSpinWu` reduced `heven` to a `SingularCohomologyInt.SpinWuDatum`, i.e. to
`w₂(K3) = 0` plus the ℤ→ℤ/2 fundamental-class compatibility. **That reduction is not the cheapest
route, and this module retires it**: `heven` is a *consequence of `hgeo`* once `hgeo` is asked for one
extra number per class, namely the parity of its own self-pairing.

## The mechanism (§1)

`interFormInt` is a symmetric ℤ-bilinear form, so its diagonal is a quadratic form:

    ⟨x+y, x+y⟩ = ⟨x,x⟩ + ⟨y,y⟩ + 2⟨x,y⟩,        ⟨n·x, n·x⟩ = n²⟨x,x⟩.

Both correction terms are even. Hence **evenness of the diagonal propagates from a family to its
whole ℤ-span** (`interFormInt_diag_even_of_mem_span`), and a family that *generates* `H²(X;ℤ)` with
even self-pairings forces evenness everywhere (`interFormInt_diag_even_of_span_top`). No Wu relation,
no `Sq²`, no mod-2 substrate, no characteristic class.

## Why `hgeo` already supplies the generation (§2)

`hgeo` asks its cap-duals `c = a ⌢ [K3]` to **generate `H₂(K3;ℤ)`**, not its classes `a` to generate
`H²(K3;ℤ)`. The two are the same demand, because `hgeo` *also* delivers integral Poincaré duality
(`KummerK3CapDualFamily.nonempty_intPD_of_capDual_span`), and PD makes `· ⌢ [K3]` **injective**
(`capHInt_injective_of_intPD`: `a ⌢ [M] = 0` kills the whole row `⟨a ∪ ·, [M]⟩`, so `a = 0` by
nondegeneracy). An injective linear map reflects `span = ⊤` (`span_eq_top_of_capSpan`).

So the classes `a` of the datum span `H²(K3;ℤ)` for free, and §3 turns the extra parity input

    hdiag : ∀ i, 2 ∣ ⟨a i, c i⟩

— stated in the datum's own Kronecker language, one integer per class — into `heven`.

## The ledger (§4)

`nonempty_kummerK3E1Atoms_of_stable_of_geoDataEven` is the K3 headline with `heven` **deleted** and
`hdiag` added inside `hgeo`. Residual ledger: `hstable` + ONE geometric datum.

## This is neither a strengthening nor a weakening (§5)

`capDual_even_iff_heven`: given the rest of the datum, `hdiag` **is** `heven`. `→` is §3; `←` is the
cap–cup adjunction at `i`. So the trade is exact — the obligation was not hidden elsewhere, and the
Wu/`w₂ = 0` route is not owed anything it did not already owe. What changed is the *language*: the
residue now lives in the same Kronecker table the rest of `hgeo` is tabulated in, instead of in a
mod-2 Steenrod substrate the weld has no access to.

## Non-vacuity (§6)

`exists_odd_offDiag_of_capDual_even_span`: the datum forces the welded `K3`'s intersection matrix to
have an **odd off-diagonal** entry. (Even diagonal by §3; unimodular by PD; a unimodular matrix has an
odd entry, `KummerK3EvenFromSpinWu.exists_odd_entry_of_isUnimodular` — which therefore cannot be a
diagonal one.) So the datum is not satisfiable by a pairwise-orthogonal — "all `⟨aᵢ, cⱼ⟩ = 0` for
`i ≠ j`" — family, i.e. it asserts genuine linking between the geometric classes, and cannot be met
by any diagonal-Gram bookkeeping witness.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3CapDualFamily
import SKEFTHawking.KummerK3EvenFromSpinWu

namespace SKEFTHawking.KummerK3EvenFromSpanningFamily

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.KummerK3GeometricFamily
open SKEFTHawking.KummerK3CapDualFamily

noncomputable section

variable {X : TopCat}

/-! ## §1. Evenness of the diagonal propagates along the ℤ-span -/

/-- **If every member of a family has even self-intersection, so does every element of its span.**

The two span-generating steps each contribute an even correction: `⟨x+y,x+y⟩ − ⟨x,x⟩ − ⟨y,y⟩ = 2⟨x,y⟩`
(symmetry of `interFormInt`) and `⟨n·x,n·x⟩ = n²⟨x,x⟩`. This is the whole content of the "even
intersection form" conjunct on a *generated* lattice — it needs no Wu relation and no mod-2 substrate,
only that `interFormInt` is symmetric bilinear. -/
theorem interFormInt_diag_even_of_mem_span (fc : IntFundamentalClass X) {ι : Type*}
    (v : ι → Cohomology X 2) (hdiag : ∀ i, (2 : ℤ) ∣ interFormInt fc (v i) (v i))
    (a : Cohomology X 2) (ha : a ∈ Submodule.span ℤ (Set.range v)) :
    (2 : ℤ) ∣ interFormInt fc a a := by
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hdiag i
  | zero => simp
  | add x y _ _ ihx ihy =>
    have hexp : interFormInt fc (x + y) (x + y)
        = interFormInt fc x x + interFormInt fc y y + 2 * interFormInt fc x y := by
      simp only [map_add, LinearMap.add_apply, interFormInt_symm fc y x]
      ring
    rw [hexp]
    exact dvd_add (dvd_add ihx ihy) ⟨_, rfl⟩
  | smul c x _ ihx =>
    have hexp : interFormInt fc (c • x) (c • x) = (c * c) * interFormInt fc x x := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hexp]
    exact Dvd.dvd.mul_left ihx _

/-- **`heven`, from an even-diagonal GENERATING family.** The `span = ⊤` specialisation of the
previous lemma: a family of classes that generates `H²(X;ℤ)` and whose members have even
self-intersection makes the whole intersection form even. -/
theorem interFormInt_diag_even_of_span_top (fc : IntFundamentalClass X) {ι : Type*}
    (v : ι → Cohomology X 2) (hspan : Submodule.span ℤ (Set.range v) = ⊤)
    (hdiag : ∀ i, (2 : ℤ) ∣ interFormInt fc (v i) (v i)) (a : Cohomology X 2) :
    (2 : ℤ) ∣ interFormInt fc a a :=
  interFormInt_diag_even_of_mem_span fc v hdiag a (hspan ▸ Submodule.mem_top)

/-! ## §2. Under integral PD, cap-spanning upgrades to cohomological spanning -/

/-- **Integral Poincaré duality makes `· ⌢ [M] : H²(M;ℤ) → H₂(M;ℤ)` injective.**

If `a ⌢ [M] = 0` then the cap–cup adjunction `⟨a ∪ b, [M]⟩ = ⟨b, a ⌢ [M]⟩` kills the entire row of
`a` in the intersection form, so `PD.toDualEquiv a = 0` and `a = 0` by injectivity of the duality
equivalence. (Only injectivity of `toDualEquiv` is used — this is nondegeneracy, not the full perfect
pairing.) -/
theorem capHInt_injective_of_intPD (zM : Homology X 4)
    (PD : IntPoincareDuality (intFundamentalClassOfHomology zM)) :
    Function.Injective (fun a : Cohomology X 2 => capHInt 2 1 a zM) := by
  intro a a' h
  simp only at h
  have hzero : PD.toDualEquiv (a - a') = 0 := by
    ext b
    rw [PD.toDualEquiv_apply, interFormInt_eq_kroneckerHInt_capHInt, map_sub,
      LinearMap.sub_apply, h, sub_self, map_zero]
    rfl
  have := PD.toDualEquiv.map_eq_zero_iff.mp hzero
  exact sub_eq_zero.mp this

/-- **Cap-duals generating `H₂(M;ℤ)` ⟹ the classes themselves generate `H²(M;ℤ)`** (under integral
PD). The image of a span is the span of the image, so `span (range c) = ⊤` says the injective map
`· ⌢ [M]` carries `span (range a)` onto everything; an injective map reflects that
(`comap_map_eq_self` at `ker = ⊥`). This is what lets §3 apply §1 to the `hgeo` datum without adding
a spanning hypothesis in cohomology — `hgeo` already pays for it in homology. -/
theorem span_eq_top_of_capSpan {ι : Type*} (zM : Homology X 4)
    (PD : IntPoincareDuality (intFundamentalClassOfHomology zM))
    (a : ι → Cohomology X 2) (c : ι → Homology X 2)
    (hcap : ∀ i, capHInt 2 1 (a i) zM = c i) (hspan : Submodule.span ℤ (Set.range c) = ⊤) :
    Submodule.span ℤ (Set.range a) = ⊤ := by
  set f : Cohomology X 2 →ₗ[ℤ] Homology X 2 := (capHInt 2 1).flip zM with hf
  have hfa : ∀ i, f (a i) = c i := hcap
  have hinj : Function.Injective f := capHInt_injective_of_intPD zM PD
  have himg : Submodule.map f (Submodule.span ℤ (Set.range a)) = ⊤ := by
    rw [Submodule.map_span, ← hspan]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (hfa i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨a i, ⟨i, rfl⟩, hfa i⟩
  have := congrArg (Submodule.comap f) himg
  rwa [Submodule.comap_map_eq_self (by rw [LinearMap.ker_eq_bot.mpr hinj]; exact bot_le),
    Submodule.comap_top] at this

/-! ## §3. `heven` from a cap-dual family with even Kronecker diagonal -/

/-- **`heven` from a cap-dual, cap-spanning family with even Kronecker diagonal.** §1 + §2 + the
cap–cup adjunction: `⟨aᵢ ∪ aᵢ, [M]⟩ = ⟨aᵢ, cᵢ⟩`, so the parity input is one integer per class, read
off the same Kronecker table the rest of the geometric datum is tabulated in. -/
theorem heven_of_capDual_even_span {ι : Type*} (zM : Homology X 4)
    (PD : IntPoincareDuality (intFundamentalClassOfHomology zM))
    (a : ι → Cohomology X 2) (c : ι → Homology X 2)
    (hcap : ∀ i, capHInt 2 1 (a i) zM = c i) (hspan : Submodule.span ℤ (Set.range c) = ⊤)
    (hdiag : ∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i)) (x : Cohomology X 2) :
    (2 : ℤ) ∣ interFormInt (intFundamentalClassOfHomology zM) x x := by
  refine interFormInt_diag_even_of_span_top _ a
    (span_eq_top_of_capSpan zM PD a c hcap hspan) (fun i => ?_) x
  rw [interFormInt_eq_kroneckerHInt_capHInt, hcap]
  exact hdiag i

/-- **The same at the welded `K3`**, where the integral-PD input is not a hypothesis but is itself
produced by the datum (`KummerK3CapDualFamily.nonempty_intPD_of_capDual_span`). So the only thing the
`heven` conjunct of the K3 ledger ever needed, beyond what `hgeo` already supplies, is the parity of
the 22+ diagonal Kronecker numbers. -/
theorem kummerK3_heven_of_capDual_even_span {ι : Type*} (o : IntOrientation KummerK3)
    (a : ι → Cohomology KummerK3top 2) (c : ι → Homology KummerK3top 2)
    (hcap : ∀ i, capHInt 2 1 (a i) o.fundClass = c i)
    (hspan : Submodule.span ℤ (Set.range c) = ⊤)
    (hdiag : ∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i)) (x : Cohomology KummerK3top 2) :
    (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) x x := by
  obtain ⟨PD⟩ := nonempty_intPD_of_capDual_span o a c hcap hspan
  exact heven_of_capDual_even_span o.fundClass PD a c hcap hspan hdiag x

/-! ## §4. THE HEADLINE — the E1 ledger without `heven` -/

/-- **THE WELDED `K3`'s E1 ATOMS FROM TWO INPUTS — `heven` deleted from the ledger.**

Compared with `KummerK3CapDualFamily.nonempty_kummerK3E1Atoms_of_stable_of_geoData`, the separate
`heven` hypothesis (`∀ o a, 2 ∣ ⟨a ∪ a, [K3]_o⟩` — the Wu / `w₂(K3) = 0` input, and the only input
of the ledger that lived outside the geometric language) is **gone**. In its place, `hgeo` carries one
extra conjunct

    ∀ i, 2 ∣ ⟨a i, c i⟩

— the parity of each class's own Kronecker self-pairing, in the same table as the rest of the datum.
§5 shows the trade is exact, so this is a change of *language*, not of *strength*: the residual E1
ledger of the welded Kummer `K3` is now

    hstable  (pure lattice theory)   +   ONE geometric datum. -/
theorem nonempty_kummerK3E1Atoms_of_stable_of_geoDataEven (hstable : StableNegRank16Two)
    (hgeo : ∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤
          ∧ (∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i))
          ∧ ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms := by
  refine nonempty_kummerK3E1Atoms_of_stable_of_geoData hstable (fun o x => ?_) (fun o => ?_)
  · obtain ⟨ι, a, c, _, hcap, hspan, hdiag, _⟩ := hgeo o
    exact kummerK3_heven_of_capDual_even_span o a c hcap hspan hdiag x
  · obtain ⟨ι, a, c, sel, hcap, hspan, _, hkron⟩ := hgeo o
    exact ⟨ι, a, c, sel, hcap, hspan, hkron⟩

/-! ## §5. The new conjunct is EXACTLY `heven` restricted — no strengthening -/

/-- **The converse direction: `heven` gives the datum's parity conjunct.** One instance of the
cap–cup adjunction. Trivial, and stated so that §5's `iff` is honest in both directions rather than a
one-sided reduction dressed as an equivalence. -/
theorem capDual_even_of_heven {ι : Type*} (zM : Homology X 4)
    (a : ι → Cohomology X 2) (c : ι → Homology X 2)
    (hcap : ∀ i, capHInt 2 1 (a i) zM = c i)
    (heven : ∀ x : Cohomology X 2, (2 : ℤ) ∣ interFormInt (intFundamentalClassOfHomology zM) x x)
    (i : ι) : (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i) := by
  have := heven (a i)
  rwa [interFormInt_eq_kroneckerHInt_capHInt, hcap] at this

/-- **THE EXACTNESS OF THE TRADE.** Given a cap-dual, cap-spanning family under integral PD, the
datum's parity conjunct and `heven` are *the same hypothesis*. So §4's ledger reduction neither
smuggles the obligation elsewhere (`←`) nor demands anything new (`→`); it relocates it from the
mod-2 Steenrod substrate — where the weld has no `Sq²`, no ℤ/2 fundamental class and no tangent
bundle — into the Kronecker table the geometric lane already computes in. -/
theorem capDual_even_iff_heven {ι : Type*} (zM : Homology X 4)
    (PD : IntPoincareDuality (intFundamentalClassOfHomology zM))
    (a : ι → Cohomology X 2) (c : ι → Homology X 2)
    (hcap : ∀ i, capHInt 2 1 (a i) zM = c i) (hspan : Submodule.span ℤ (Set.range c) = ⊤) :
    (∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i))
      ↔ ∀ x : Cohomology X 2, (2 : ℤ) ∣ interFormInt (intFundamentalClassOfHomology zM) x x :=
  ⟨fun hdiag => heven_of_capDual_even_span zM PD a c hcap hspan hdiag,
    fun heven i => capDual_even_of_heven zM a c hcap heven i⟩

/-! ## §6. Non-vacuity: the datum forces an ODD OFF-DIAGONAL intersection number -/

/-- **THE ZERO-GEOMETRIC-INPUT ATTACK ON §4's DATUM.**

Could the datum's new parity conjunct be satisfied by a degenerate, "diagonal" witness — a family
whose classes pair to zero with each other? No. The conjunct plus `hspan` makes every *diagonal*
entry of the welded `K3`'s intersection matrix even, while `hspan` also forces integral PD, hence
unimodularity, hence (`KummerK3EvenFromSpinWu.exists_odd_entry_of_isUnimodular`) an **odd** entry
somewhere. An odd entry cannot be diagonal, so the datum asserts a genuine odd *linking number*
between two basis classes of `H²(K3;ℤ)`.

This is the analogue, for the parity conjunct, of `KummerK3EvenFromSpinWu.spinWu_mu2_ne_zero` for the
`SpinWuDatum`'s `μ₂`: the hypothesis carries content about the manifold, not bookkeeping. -/
theorem exists_odd_offDiag_of_capDual_even_span {ι : Type*} (o : IntOrientation KummerK3)
    (a : ι → Cohomology KummerK3top 2) (c : ι → Homology KummerK3top 2)
    (hcap : ∀ i, capHInt 2 1 (a i) o.fundClass = c i)
    (hspan : Submodule.span ℤ (Set.range c) = ⊤)
    (hdiag : ∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i)) :
    ∃ i j : Fin kummerK3IntH2Basis.rank, i ≠ j ∧
      ¬ (2 : ℤ) ∣ interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis i j := by
  obtain ⟨PD⟩ := nonempty_intPD_of_capDual_span o a c hcap hspan
  have huni : IsUnimodular (interMatrix (intFundamentalClassOfIntOrientation o)
      kummerK3IntH2Basis) := interMatrix_isUnimodular_of_intPD _ _ PD
  obtain ⟨i, j, hij⟩ := SKEFTHawking.KummerK3EvenFromSpinWu.exists_odd_entry_of_isUnimodular
    (by rw [kummerK3IntH2Basis_rank]; norm_num) _ huni
  refine ⟨i, j, ?_, hij⟩
  rintro rfl
  exact hij (by
    rw [interMatrix_apply]
    exact kummerK3_heven_of_capDual_even_span o a c hcap hspan hdiag _)

end

end SKEFTHawking.KummerK3EvenFromSpanningFamily
