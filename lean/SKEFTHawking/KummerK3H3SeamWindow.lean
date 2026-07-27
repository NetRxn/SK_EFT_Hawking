/-
# The `H₃(K3;ℤ)` orientation residual as ONE `Q`-side statement: the 16 seam classes are 2-saturated

`KummerK3E1Package.KummerK3H3TwoTorsionFree` (`orientInput`, the `H₃(K3;ℤ)` 2-torsion-freeness that
fires `nonempty_intOrientation_kummerK3`) was reduced in `KummerK3H3Reduction` to a 2-saturation of
`im Δ₃` inside `H₃(qThick) ⊕ H₃(eImage)`. That form still mentions the `E`-side summand and the
abstract MV diagonal. This module removes both, landing the residual on a single **concrete
sixteen-generator map into `Q`-side degree-3 homology**:

    qSeamCoord3 : ℤ¹⁶ = (EIndex → ℤ) →ₗ[ℤ] H₃(Q;ℤ)

(`Q = FreeQuotient`, the free `ℤ/2` quotient of the punctured torus; `ℤ¹⁶ ≅ H₃(collar;ℤ)` by the
banked `interH3EquivInt`, the sixteen boundary `ℝP³`s of `Q`). The headline is an **`↔`**, so nothing
is given away:

    KummerK3H3TwoTorsionFree  ↔  `im qSeamCoord3` is 2-saturated in `H₃(Q;ℤ)`.

Geometrically that is exactly "**the sixteen boundary `ℝP³` classes of `∂Q` span a 2-saturated
subgroup of `H₃(Q;ℤ)`**" — Lefschetz-dually, `H¹(Q;ℤ)` carrying no 2-torsion obstruction.

## Why the `E`-side and the abstract diagonal can be dropped

`H₃(eImage;ℤ) = 0` (`eImageH3_eq_zero`: each resolution piece retracts to `S²`), so the second
component of `Δ₃ = (i_*, j_*)` is identically zero and `(u, v) ∈ im Δ₃ ↔ u ∈ im i_*` (§2). The
collar `qThick ∩ eImage` retracts to the seam and `H₃(collar;ℤ) ≅ ℤ¹⁶` (`interH3EquivInt`), while
`H₃(qThick;ℤ) ≅ H₃(Q;ℤ)` (`qThickHnEquivInt 2`); both are **isomorphisms**, so 2-saturation
transports across them verbatim (§1's transport algebra).

## The sharper reading: surjectivity IS `H₃(K3;ℤ) = 0`

§4 records `Function.Surjective qSeamCoord3 ↔ ∀ x : H₃(K3;ℤ), x = 0`. So the sufficient criterion
"the sixteen seam classes generate `H₃(Q;ℤ)`" is *exactly* the vanishing of `H₃(K3;ℤ)`, i.e. it is
neither vacuous nor an over-approximation: it is the strongest form of the residual, and the
2-saturation `↔` is the weakest. Both are stated, so a future `Q`-side solve may discharge whichever
it lands on.

## The complete degree-4/3 MV window in those coordinates

§4b assembles the whole window UNCONDITIONALLY (`exact_k7Sum4_k7Delta3Coord`,
`exact_k7Delta3Coord_qSeamCoord3`, `qSeamCoord3_surjective_iff_h3K3_eq_zero`):

    H₄(qThick;ℤ) ⊕ H₄(eImage;ℤ) --Σ₄--> H₄(K3;ℤ) --∂₄--> ℤ¹⁶ --qSeamCoord3--> H₃(Q;ℤ) ↠ H₃(K3;ℤ) → 0

with `Σ₄` injective (`k7Sum4_injective`). So `ker qSeamCoord3 = im ∂₄` is pinned too: the only objects
in the whole degree-3 window still uncomputed are `H₃(Q;ℤ)` and `H₄(K3;ℤ)`.

## ⛔ What this module deliberately does NOT do — the free-quotient descent trap

`KummerPunctureH3Mod2.thickA_H3_twoTorsionFree` is UNCONDITIONAL: `H₃(T⁴°;ℤ)` has no 2-torsion. It
does **not** transport to `Q`. `T⁴° → Q` is a *free* `ℤ/2` quotient, and free `ℤ/2` quotients
**create** 2-torsion (`H₁(S³) = 0` but `H₁(ℝP³) = ℤ/2` — the in-tree `KummerRP3SmithSES` /
`KummerRP3HomologyUnconditional` computation of exactly that). Any argument of the shape
"`T⁴°` has no 2-torsion, hence `Q` has none" is FALSE, and no theorem here asserts it. §5 records the
one thing the covering *does* give unconditionally — that the descent defect is 2-torsion, via
`p_# ∘ tr = 2` (`KummerQuotientTransferInt.mapChainInt_transferChainInt`) — which is a statement
about `im p_*`, not about torsion-freeness of `H₃(Q;ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3H3Reduction
import SKEFTHawking.KummerQuotientSmithSES

namespace SKEFTHawking.KummerK3H3SeamWindow

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (eImage EIndex)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.KummerK3H3Reduction (delta3)

noncomputable section

/-! ## §1. Transport algebra for 2-saturation -/

/-- Membership in the range of `e ∘ f` is membership of the `e`-preimage in the range of `f`. -/
theorem mem_range_comp_equiv {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P) (v : P) :
    v ∈ Set.range (e.toLinearMap ∘ₗ f) ↔ e.symm v ∈ Set.range f := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by simp⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by simp [hm]⟩

/-- **2-saturation is invariant under a linear equivalence of the ambient module.** The transport
step that lets the residual be restated in `H₃(Q;ℤ)` coordinates without weakening it. -/
theorem two_saturated_congr {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] N) (e : N ≃ₗ[ℤ] P) :
    (∀ u : N, (2 : ℤ) • u ∈ Set.range f → u ∈ Set.range f) ↔
      ∀ v : P, (2 : ℤ) • v ∈ Set.range (e.toLinearMap ∘ₗ f) →
        v ∈ Set.range (e.toLinearMap ∘ₗ f) := by
  constructor
  · intro h v hv
    rw [mem_range_comp_equiv] at hv ⊢
    rw [map_smul] at hv
    exact h _ hv
  · intro h u hu
    have hev : (2 : ℤ) • e u ∈ Set.range (e.toLinearMap ∘ₗ f) := by
      rw [mem_range_comp_equiv, map_smul, e.symm_apply_apply]
      exact hu
    have := h (e u) hev
    rw [mem_range_comp_equiv, e.symm_apply_apply] at this
    exact this

/-- Precomposing with a surjection does not change the range. -/
theorem range_comp_surjective {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : N →ₗ[ℤ] P) (g : M →ₗ[ℤ] N) (hg : Function.Surjective g) :
    Set.range (f ∘ₗ g) = Set.range f := by
  ext p
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨g m, rfl⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨m, rfl⟩ := hg n
    exact ⟨m, rfl⟩

/-! ## §2. Dropping the dead `E`-side summand -/

/-- **The live half of the degree-3 MV diagonal**: `i_* : H₃(collar;ℤ) → H₃(qThick;ℤ)`, the first
component of `Δ₃`. -/
abbrev collarToQThick3 :
    Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 3 →ₗ[ℤ]
      Homology (sub (X := KummerK3top) qThick) 3 :=
  Homology.mapInt (subIncl (Set.inter_subset_left (s := qThick) (t := eImage))) 3

/-- **`im Δ₃` is `im i_* × 0`.** The second component of `Δ₃` lands in `H₃(eImage;ℤ) = 0`
(`eImageH3_eq_zero`), so membership in `im Δ₃` is decided by the `qThick` component alone. -/
theorem mem_range_delta3_iff
    (p : Homology (sub (X := KummerK3top) qThick) 3 ×
      Homology (sub (X := KummerK3top) eImage) 3) :
    p ∈ Set.range delta3 ↔ p.1 ∈ Set.range collarToQThick3 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Prod.ext hw ((eImageH3_eq_zero _).trans (eImageH3_eq_zero _).symm)⟩

/-- **The residual with the `E`-side removed**: `H₃(K3;ℤ)` is 2-torsion-free **iff** the image of the
collar inclusion `i_* : H₃(collar;ℤ) → H₃(qThick;ℤ)` is 2-saturated. Lossless (`↔`), by §2's
component characterisation of `im Δ₃` on top of
`KummerK3H3Reduction.kummerK3H3TwoTorsionFree_iff_delta3_two_saturated`. -/
theorem kummerK3H3TwoTorsionFree_iff_collar_two_saturated :
    KummerK3E1Package.KummerK3H3TwoTorsionFree ↔
      ∀ u, (2 : ℤ) • u ∈ Set.range collarToQThick3 → u ∈ Set.range collarToQThick3 := by
  rw [KummerK3H3Reduction.kummerK3H3TwoTorsionFree_iff_delta3_two_saturated]
  constructor
  · intro h u hu
    have h2 : (2 : ℤ) • (u, (0 : Homology (sub (X := KummerK3top) eImage) 3)) ∈
        Set.range delta3 := by
      rw [mem_range_delta3_iff]
      exact hu
    have := h _ h2
    rw [mem_range_delta3_iff] at this
    exact this
  · intro h p hp
    rw [mem_range_delta3_iff] at hp ⊢
    exact h p.1 hp

/-! ## §3. The residual in `H₃(Q;ℤ)` coordinates -/

/-- **THE `Q`-SIDE SEAM MAP** `ℤ¹⁶ → H₃(Q;ℤ)`: the sixteen boundary-`ℝP³` classes of `∂Q`, read
through the banked isomorphisms `interH3EquivInt : H₃(collar;ℤ) ≅ (EIndex → ℤ)` and
`qThickHnEquivInt 2 : H₃(qThick;ℤ) ≅ H₃(Q;ℤ)`. Every remaining piece of the `H₃(K3;ℤ)` orientation
residual is a statement about THIS map. -/
abbrev qSeamCoord3 : (EIndex → ℤ) →ₗ[ℤ] Homology (TopCat.of FreeQuotient) 3 :=
  ((qThickHnEquivInt 2).toLinearMap ∘ₗ collarToQThick3) ∘ₗ interH3EquivInt.symm.toLinearMap

/-- Coordinatising the collar does not move the image. -/
theorem range_qSeamCoord3 :
    Set.range qSeamCoord3 = Set.range ((qThickHnEquivInt 2).toLinearMap ∘ₗ collarToQThick3) :=
  range_comp_surjective _ _ interH3EquivInt.symm.surjective

/-- **THE RESIDUAL, in `Q`-side coordinates (the usable form).** `H₃(K3;ℤ)` is 2-torsion-free —
hence `KummerK3E1Package.nonempty_intOrientation_kummerK3` fires — **iff** the subgroup of `H₃(Q;ℤ)`
generated by the sixteen boundary-`ℝP³` classes is 2-saturated. No `H₃(K3)`, no product summand, no
abstract MV map: only the free-quotient's degree-3 homology and sixteen named classes in it. -/
theorem kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated :
    KummerK3E1Package.KummerK3H3TwoTorsionFree ↔
      ∀ u : Homology (TopCat.of FreeQuotient) 3,
        (2 : ℤ) • u ∈ Set.range qSeamCoord3 → u ∈ Set.range qSeamCoord3 := by
  rw [kummerK3H3TwoTorsionFree_iff_collar_two_saturated,
    two_saturated_congr collarToQThick3 (qThickHnEquivInt 2)]
  simp only [range_qSeamCoord3]

/-! ## §4. The strongest form: surjectivity IS `H₃(K3;ℤ) = 0` -/

/-- **`Δ₃` surjective ⟺ `H₃(K3;ℤ) = 0`.** `Σ₃` is surjective (`k7Sum3_surjective`) and kills
`im Δ₃` (`mvHomSumInt_mvHomDiagInt`), so a surjective `Δ₃` forces `H₃(K3;ℤ) = 0`; conversely
`ker Σ₃ = im Δ₃` (`k7_exact_middle`) makes every pair land in `im Δ₃` once `H₃(K3;ℤ)` vanishes. -/
theorem delta3_surjective_iff_h3K3_eq_zero :
    Function.Surjective delta3 ↔ ∀ x : Homology KummerK3top 3, x = 0 := by
  constructor
  · intro hsurj x
    obtain ⟨p, hp⟩ := k7Sum3_surjective x
    obtain ⟨w, rfl⟩ := hsurj p
    rw [← hp]
    exact mvHomSumInt_mvHomDiagInt (X := KummerK3top) qThick eImage 3 w
  · intro hzero p
    exact (k7_exact_middle 2 p).mp (hzero _)

/-- Surjectivity of the live half of `Δ₃` is surjectivity of `Δ₃`. -/
theorem collarToQThick3_surjective_iff :
    Function.Surjective collarToQThick3 ↔ Function.Surjective delta3 := by
  constructor
  · intro h p
    obtain ⟨w, hw⟩ := h p.1
    exact (mem_range_delta3_iff p).mpr ⟨w, hw⟩
  · intro h u
    obtain ⟨w, hw⟩ := h (u, 0)
    exact ⟨w, congrArg Prod.fst hw⟩

/-- **The sixteen seam classes generate `H₃(Q;ℤ)` ⟺ `H₃(K3;ℤ) = 0`.** The sharpest reading of the
residual: the strongest sufficient criterion available in §3's coordinates is exactly the vanishing
of `H₃(K3;ℤ)`, so it is neither vacuous nor a strengthening artefact. -/
theorem qSeamCoord3_surjective_iff_h3K3_eq_zero :
    Function.Surjective qSeamCoord3 ↔ ∀ x : Homology KummerK3top 3, x = 0 := by
  rw [← delta3_surjective_iff_h3K3_eq_zero, ← collarToQThick3_surjective_iff]
  constructor
  · intro h u
    obtain ⟨v, hv⟩ := h (qThickHnEquivInt 2 u)
    refine ⟨interH3EquivInt.symm v, ?_⟩
    have := congrArg (qThickHnEquivInt 2).symm hv
    simpa using this
  · intro h u
    obtain ⟨w, hw⟩ := h ((qThickHnEquivInt 2).symm u)
    refine ⟨interH3EquivInt w, ?_⟩
    show (qThickHnEquivInt 2) (collarToQThick3 (interH3EquivInt.symm (interH3EquivInt w))) = u
    rw [interH3EquivInt.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]

/-- **Sufficiency, in the form a future `Q`-side solve consumes.** If the sixteen boundary-`ℝP³`
classes generate `H₃(Q;ℤ)`, the orientation atom of the `K3` E1 package exists. -/
theorem kummerK3H3TwoTorsionFree_of_qSeamCoord3_surjective
    (h : Function.Surjective qSeamCoord3) : KummerK3E1Package.KummerK3H3TwoTorsionFree :=
  kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated.mpr fun u _ => h u

open scoped SKEFTHawking.KummerK3E1Package in
/-- **The orientation atom of the welded `K3`, from the `Q`-side criterion.** Chains §3/§4 into
`KummerK3E1Package.nonempty_intOrientation_kummerK3`: the sixteen seam classes generating `H₃(Q;ℤ)`
is enough to produce `Nonempty (IntOrientation KummerK3)`. -/
theorem nonempty_intOrientation_of_qSeamCoord3_surjective
    (h : Function.Surjective qSeamCoord3) :
    Nonempty (SingularHomologyInt.IntOrientation SKEFTHawking.KummerWeld.KummerK3) :=
  KummerK3E1Package.nonempty_intOrientation_kummerK3
    (kummerK3H3TwoTorsionFree_of_qSeamCoord3_surjective h)

/-! ## §4b. The kernel of the seam map: the whole degree-3 window in `Q`-side coordinates -/

/-- The degree-3 MV connecting map in the same `ℤ¹⁶` coordinates as `qSeamCoord3`:
`∂₄ : H₄(K3;ℤ) → H₃(collar;ℤ) ≅ ℤ¹⁶`. -/
abbrev k7Delta3Coord : Homology KummerK3top 4 →ₗ[ℤ] (EIndex → ℤ) :=
  interH3EquivInt.toLinearMap ∘ₗ k7Delta 3

theorem k7Delta3Coord_apply (a : Homology KummerK3top 4) :
    k7Delta3Coord a = interH3EquivInt (k7Delta 3 a) := by
  simp only [k7Delta3Coord, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]

/-- Vanishing of `Δ₃` is vanishing of its live half (the `E`-side component is always `0`). -/
theorem delta3_eq_zero_iff (w : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 3) :
    delta3 w = 0 ↔ collarToQThick3 w = 0 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    exact Prod.ext h (eImageH3_eq_zero _)

/-- **THE DEGREE-3 WINDOW, fully in `Q`-side coordinates (UNCONDITIONAL).**

    H₄(K3;ℤ) --∂₄--> ℤ¹⁶ --qSeamCoord3--> H₃(Q;ℤ)

is exact. Together with `qSeamCoord3_surjective_iff_h3K3_eq_zero` (the cokernel is `H₃(K3;ℤ)`) this
pins the entire MV degree-3 window of the weld on a single ℤ-linear diagram whose only unknown
object is `H₃(Q;ℤ)`: `im qSeamCoord3 ≅ ℤ¹⁶ / im ∂₄`, and `H₃(K3;ℤ) ≅ H₃(Q;ℤ) / im qSeamCoord3`. -/
theorem exact_k7Delta3Coord_qSeamCoord3 : Function.Exact k7Delta3Coord qSeamCoord3 := by
  intro v
  have hker : qSeamCoord3 v = 0 ↔ collarToQThick3 (interH3EquivInt.symm v) = 0 := by
    constructor
    · intro h
      have := congrArg (qThickHnEquivInt 2).symm h
      simpa using this
    · intro h
      show (qThickHnEquivInt 2) (collarToQThick3 (interH3EquivInt.symm v)) = 0
      rw [h, map_zero]
  rw [hker, ← delta3_eq_zero_iff, k7_exact_inter 3 (interH3EquivInt.symm v)]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [k7Delta3Coord_apply, ha, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha, k7Delta3Coord_apply, LinearEquiv.symm_apply_apply]

/-- **The window extends one step left**: `ker ∂₄ = im Σ₄`. With
`exact_k7Delta3Coord_qSeamCoord3` and `qSeamCoord3_surjective_iff_h3K3_eq_zero` this is the complete
degree-4/3 MV window of the weld,

    H₄(qThick;ℤ) ⊕ H₄(eImage;ℤ) --Σ₄--> H₄(K3;ℤ) --∂₄--> ℤ¹⁶ --qSeamCoord3--> H₃(Q;ℤ) ↠ H₃(K3;ℤ) → 0,

with `Σ₄` injective (`k7Sum4_injective`) — every object but `H₃(Q;ℤ)` and `H₄(K3;ℤ)` is banked. -/
theorem exact_k7Sum4_k7Delta3Coord :
    Function.Exact (mvHomSumInt (X := KummerK3top) qThick eImage 4) k7Delta3Coord := by
  intro b
  have h : k7Delta3Coord b = 0 ↔ k7Delta 3 b = 0 := by
    rw [k7Delta3Coord_apply]
    exact LinearEquiv.map_eq_zero_iff interH3EquivInt
  rw [h]
  exact k7_exact_ambient 3 b

/-! ## §5. The free-quotient descent: what the covering DOES give (and what it does NOT)

`H₃(qThick;ℤ) ≅ H₃(Q;ℤ)` and `Q = T⁴°/τ` is a **free** `ℤ/2` quotient of the punctured torus, whose
`H₃(·;ℤ)` is 2-torsion-free UNCONDITIONALLY (`KummerPunctureH3Mod2.thickA_H3_twoTorsionFree`). That
does **not** descend: free `ℤ/2` quotients create 2-torsion (`H₁(S³;ℤ) = 0`, `H₁(ℝP³;ℤ) = ℤ/2` — the
in-tree `KummerRP3HomologyUnconditional` computation). The covering's honest unconditional content in
every degree is the transfer identity below: the *descent defect* `H_n(Q;ℤ)/im p_*` is killed by 2 —
a statement about the image of `p_*`, NOT about torsion in `H_n(Q;ℤ)`.
-/

section Descent

open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC)
open SKEFTHawking.KummerQuotientTransferInt (transferChainInt mapChainInt_transferChainInt)
open SKEFTHawking.KummerQuotientSmithSES (projH transferH)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.SingularHomologyInt (chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt)

/-- **`p̄ ∘ t = 2` on `Hₙ(Q;ℤ)`** — the transfer identity dual to
`KummerQuotientSmithSES.transferH_projH` (`t ∘ p̄ = 1 + τ_*`), descending the chain-level
`p_# ∘ tr = 2` (`KummerQuotientTransferInt.mapChainInt_transferChainInt`) to homology. -/
theorem projH_transferH (n : ℕ) (y : Hml (chainBoundary Qtop) n) :
    projH n (transferH n y) = (2 : ℤ) • y := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary Qtop) n y
  rw [show ((2 : ℤ) • Hml.mk (chainBoundary Qtop) n z)
      = Hml.mk (chainBoundary Qtop) n ((2 : ℤ) • z) from
    ((Hml.mkHom (chainBoundary Qtop) n).map_smul (2 : ℤ) z).symm]
  show Hml.mk (chainBoundary Qtop) n _ = _
  refine congrArg (Hml.mk (chainBoundary Qtop) n) (Subtype.ext ?_)
  show mapChainInt qmkC n (transferChainInt n (z : _)) = ((2 : ℤ) • z : _)
  rw [mapChainInt_transferChainInt]
  rfl

/-- **Every doubled `Q`-class lifts to the punctured torus**: `2 · Hₙ(Q;ℤ) ⊆ im p_*`. This — and
only this — is what the free double cover gives unconditionally. It bounds the *cokernel* of `p_*`
by exponent 2; it says nothing about 2-torsion inside `Hₙ(Q;ℤ)`, which is precisely why
`thickA_H3_twoTorsionFree` cannot be transported to the `Q` side. -/
theorem two_smul_mem_range_projH (n : ℕ) (y : Hml (chainBoundary Qtop) n) :
    (2 : ℤ) • y ∈ Set.range (projH n) :=
  ⟨transferH n y, projH_transferH n y⟩

/-- The Smith-engine projection IS the project's induced map at positive degree (same chain map,
definitionally equal carriers) — the `projH` analogue of
`KummerQuotientH2Solve.tauH_eq_mapInt`. -/
theorem projH_eq_mapInt (n : ℕ) (x : Hml (chainBoundary PTtop) (n + 1)) :
    projH (n + 1) x = Homology.mapInt qmkC (n + 1) x := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary PTtop) (n + 1) x
  rfl

/-- **`2 · Hₙ₊₁(Q;ℤ) ⊆ im (p_* : Hₙ₊₁(T⁴°;ℤ) → Hₙ₊₁(Q;ℤ))`**, in the project's
`Homology.mapInt` idiom. At `n + 1 = 3` this is the exact — and only — unconditional bridge the
covering supplies between the banked `H₃(T⁴°;ℤ)` facts and the open `H₃(Q;ℤ)` residual of §3. -/
theorem two_smul_mem_range_mapInt_qmkC (n : ℕ) (y : Homology Qtop (n + 1)) :
    (2 : ℤ) • y ∈ Set.range (Homology.mapInt qmkC (n + 1)) := by
  obtain ⟨x, hx⟩ := two_smul_mem_range_projH (n + 1) y
  exact ⟨x, by rw [← projH_eq_mapInt]; exact hx⟩

/-! ### §5b. The collapse: one descent containment removes the weak form of the residual

The hypothesis below — "the punctured-torus classes descend into the seam span" — is a *genuine*
geometric containment, not a tautology: it fails for any `p_*`-image escaping the sixteen seam
classes, and nothing here discharges it. Under it, §5's `2 · H₃(Q;ℤ) ⊆ im p_*` forces the seam
cokernel to have exponent 2, so the 2-saturation `↔` of §3 and the surjectivity `↔` of §4 become the
SAME statement: the residual then has no weaker form than `H₃(K3;ℤ) = 0`.
-/

/-- Under the descent containment, every doubled `H₃(Q;ℤ)` class is already in the seam span —
i.e. `H₃(K3;ℤ) = coker qSeamCoord3` has exponent 2. -/
theorem two_smul_mem_range_qSeamCoord3_of_descent
    (h : Set.range (Homology.mapInt qmkC 3) ⊆ Set.range qSeamCoord3)
    (u : Homology (TopCat.of FreeQuotient) 3) : (2 : ℤ) • u ∈ Set.range qSeamCoord3 :=
  h (two_smul_mem_range_mapInt_qmkC 2 u)

/-- **The residual collapses to a single statement under the descent containment.** With
`im (p_* : H₃(T⁴°;ℤ) → H₃(Q;ℤ)) ⊆ im qSeamCoord3`, the weak (2-saturation) and strong (surjectivity)
forms of the `H₃(K3;ℤ)` orientation residual coincide — so a future `Q`-side solve gains nothing by
aiming at the weaker one. Makes §5's transfer identity load-bearing rather than decorative. -/
theorem twoTorsionFree_iff_qSeamCoord3_surjective_of_descent
    (h : Set.range (Homology.mapInt qmkC 3) ⊆ Set.range qSeamCoord3) :
    KummerK3E1Package.KummerK3H3TwoTorsionFree ↔ Function.Surjective qSeamCoord3 := by
  constructor
  · intro h3 u
    exact kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated.mp h3 u
      (two_smul_mem_range_qSeamCoord3_of_descent h u)
  · exact kummerK3H3TwoTorsionFree_of_qSeamCoord3_surjective

end Descent

end

end SKEFTHawking.KummerK3H3SeamWindow
