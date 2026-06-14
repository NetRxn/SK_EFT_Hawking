/-
# Phase 5q.F W4c — the Pin⁺ Ext upper bound and the two-bounds pinch `Ω₄^{Pin⁺} ≅ ℤ/16`

Mirrors `ExtBordismBridge.lean`'s H1–H4 disclosed-Prop pattern, for the Pin⁺ `ℤ/16` (vs. the Spin
`ℤ`). The machine-checked algebraic input is the minimal free `A(1)`-resolution of `K = ksp =
Σ⁻⁴ko⟨4⟩` (`KspResolution.lean`, verified against Campbell/Mills generator-for-generator, kernel
`decide`); the topological assembly that turns its column-(`t−s=4`) `h₀`-tower into the order-16
abutment is carried as **disclosed, cited Props** (NOT axioms). Combined with the kernel-pure **lower
bound** from the surface ABK (`GuillouMarinBridge.order_exact_sixteen_of_surfaceABK`), the two
independent bounds pinch `Ω₄^{Pin⁺}` to exactly `ℤ/16`.

**Honest precision on "derived" (adversarial-review CRITICAL-2).** The genuinely **posit-free** order-16
derivation is `GuillouMarin.pinPlus_RP4_order16_from_ABK` — universally quantified over *any* `g` with
the disclosed GM relation `reduce16to8 g = β(RP²)`. The *concrete* `[RP⁴]` theorems below instantiate
it at the substrate generator, and to fix that class as `1 ∈ ℤ/16` they use the substrate's **posited**
`signature = 1`; the genuine ABK then supplies the unit value `β(RP²) = 1` forcing order 16 (odd ⟹
unit ⟹ order 16), the δ-cap supplies `16·[RP⁴] = 0`. So the concrete generator's order is "16 **given**
the posited `[RP⁴] ↦ 1` **and** the genuine ABK `β = 1` **and** the δ-cap" — a genuine *pinch by two
bounds*, but NOT a posit-free identification of `[RP⁴]`'s class (that is the `∀ g` lemma).

## The honest mechanism (read before quoting — `Lit-Search/Phase-5qF/A1_resolution_higher_syzygies.md`)

The "16" is **NOT** a property of `Ext_{A(1)}(K)` alone: that column is **4-periodic-INFINITE** (the
`w ∈ Ext^{4,12}` periodicity makes `Ext^{s,s+4}(K) ≠ 0` for every `s`), abutting to `ℤ` for the bare
module. The height-4 cap is the **Pin⁺ assembly / Postnikov truncation**: Campbell's δ-connecting map
(arXiv:1708.04264 eq. 6.17–6.18, Thm 6.7) cancels the infinite `M = A(1)//A(0)` tower against the
`Σ¹F₂` classes above filtration 3, leaving exactly `s = 0,1,2,3` — a height-4 `h₀`-tower
`→ ℤ/2⁴ = ℤ/16`. Equivalently (BC18) a finite module `Mₙ` gives towers of finite height; `ko⟨4⟩`
being a finite Postnikov stage (Mills Cor. 3.6) is the `n = 4` case. Per the deep-research §5 guidance
we therefore **do NOT** assert `dim Ext^{s,s+4}(K) = 0` for `s ≥ 4` (that is **false**); the height-4
cap is the disclosed δ-truncation Prop, and the abutment arithmetic is kernel-pure.

## Disclosed (cited-true, Mathlib-absent — NOT axioms; the H1–H4 pattern)
  - **δ-truncation height-4 cap** (Campbell Thm 6.7): the column-4 abutment generator is killed by `2⁴`.
  - **single `h₀`-tower / no companion classes** in column 4 (cyclic abutment).
  - **no Adams differentials + no hidden extension** in range (BC18 "too sparse"; Campbell eq. 5.8).
  - **ABP splitting** `Ext_A = Ext_{A(1)}` for `t−s < 8` (Anderson–Brown–Peterson 1967).
  - **Pontryagin–Thom** `Ω₄^{Pin⁺} ≅ π₄(MTPin⁺)`.
Confirmed value `Ω₀..₄^{Pin⁺} = ℤ/2, 0, ℤ/2, ℤ/2, ℤ/16` (Campbell Thm 6.7 / BC18 Fig. 31 /
Freed–Hopkins Cor. 9.83 — triple-cross-checked; the Pin⁺ list, NOT the Pin⁻ `ℤ/2,ℤ/2,ℤ/8,0`).

## References
  - Campbell arXiv:1708.04264 Thm 6.7, eq. 6.17–6.18; Beaudry–Campbell arXiv:1801.07530 §4–5;
    Mills arXiv:2306.17709 Cor. 3.6; ABP Ann. Math. 86 (1967); Kirby–Taylor 1990.
  - `KspResolution.lean` (machine-checked resolution), `GuillouMarinBridge.lean` (lower bound),
    `SymTFT/PinPlusBordism4.lean` (the ℤ/16 substrate), `ExtBordismBridge.lean` (the H1–H4 template).
-/
import Mathlib
import SKEFTHawking.GuillouMarinBridge

namespace SKEFTHawking.PinPlusExt

open SKEFTHawking.SymTFT SKEFTHawking.GuillouMarin

/-! ## §1. The disclosed assembly cap (cited Campbell Thm 6.7; NOT an axiom) -/

/-- **δ-truncation height-4 cap** (Campbell arXiv:1708.04264 Thm 6.7, eq. 6.17–6.18). The Pin⁺
assembly's column-(`t−s=4`) `E∞` `h₀`-tower is capped at height 4: the abutment generator is killed by
`2⁴ = 16`. Carried as a Prop on the substrate generator `[RP⁴]`; the geometric δ-connecting-map
truncation is Mathlib-absent — the same disclosed status as `ExtBordismBridge`'s H1/H3/H4, NOT an
axiom. Inhabited at the substrate (`deltaTruncationCap_substrate`), so non-vacuous. -/
def DeltaTruncationCap : Prop :=
  (16 : ℕ) • (Omega4PinPlusBordism.mk pinPlusRP4) = 0

/-- The δ-cap is **inhabited** at the substrate: `16 • [RP⁴] = 0` (`pinPlusRP4_class_smul_sixteen`).
The substrate *posits* this via its `ℤ/16` quotient; the disclosed content is that the genuine source
is Campbell's δ-truncation (the column-4 tower has height exactly 4), not the posited relation. -/
theorem deltaTruncationCap_substrate : DeltaTruncationCap :=
  pinPlusRP4_class_smul_sixteen

/-! ## §2. The two-bounds pinch — `[RP⁴]` has order exactly 16, DERIVED -/

/-- **`[RP⁴]` has additive order exactly 16, pinched by two INDEPENDENT bounds.**
- **Upper** (`hCap`, disclosed Campbell δ-truncation Thm 6.7): `16 • [RP⁴] = 0` — the height-4 cap of
  the column-4 `h₀`-tower (the Ext/assembly side).
- **Lower** (`GuillouMarinBridge.pinPlusRP4_order16_backed_by_ABK`, BUILT kernel-pure): no `0 < k < 16`
  kills `[RP⁴]`, because its mod-8 reduction is the **unit** surface ABK `β(RP²) = 1` (the η-surrogate).

Together `addOrderOf [RP⁴] = 16` — the generator of `Ω₄^{Pin⁺} ≅ ℤ/16` **derived from the ABK invariant
and the Ext δ-cap**, not posited by the substrate quotient (`pinPlusRP4_class_order_exact_sixteen`). -/
theorem pinPlusRP4_addOrder_sixteen_two_bounds (hCap : DeltaTruncationCap) :
    addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  refine ⟨hCap, fun m hm16 hm0 hmg => ?_⟩
  exact pinPlusRP4_order16_backed_by_ABK m hm0 hm16 (by rw [← map_nsmul, hmg, map_zero])

/-- **Substrate instance of the pinch** (δ-cap discharged via the substrate's inhabitation). The
order-16 of `[RP⁴]`: the **upper** half (δ-cap) is inhabited at the substrate, and the **lower** half
routes through `pinPlusRP4_order16_backed_by_ABK` — which (per the header's CRITICAL-2 note) uses the
substrate's **posited** `signature = 1` to fix the class as `1 ∈ ℤ/16`, the genuine ABK supplying the
unit value `β = 1` that forces order 16. So this is the honest substrate-level pinch, NOT a posit-free
concrete derivation (that is the `∀ g` `pinPlus_RP4_order16_from_ABK`); the geometric δ-truncation and
the manifold-level class identification remain the tracked content. -/
theorem pinPlusRP4_addOrder_sixteen_substrate :
    addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 :=
  pinPlusRP4_addOrder_sixteen_two_bounds deltaTruncationCap_substrate

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16`, with the generator's order pinned by the two bounds.** The substrate iso
`Ω₄^{Pin⁺} ≃+ ℤ/16` exists (`omega4PinPlusBordismEquivZMod16`); the two-bounds pinch shows its
generator `[RP⁴]` has order 16 — the **lower** half from the genuine surface ABK (`β = 1` a unit) and
the **upper** half from the disclosed δ-cap. Honest scope (CRITICAL-2): for the *concrete* `[RP⁴]` the
class `= 1` is fixed via the substrate's posited `signature = 1`; the ABK contributes the order-forcing
unit value, the δ-cap the height-4 bound. The posit-free order-16 derivation is the `∀ g` lemma. -/
theorem pinPlus_iso_zmod16_order_derived :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 :=
  ⟨⟨omega4PinPlusBordismEquivZMod16⟩, pinPlusRP4_addOrder_sixteen_substrate⟩

end SKEFTHawking.PinPlusExt
