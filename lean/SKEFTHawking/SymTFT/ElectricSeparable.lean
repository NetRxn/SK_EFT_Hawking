/-
# SymTFT S2 — the NORMALIZED (separable) Frobenius structure on `1 ⊕ e`

`ElectricComonoid` landed the two Frobenius compatibility laws (`electricFrobenius_left` /
`electricFrobenius_right`) and computed the composite `Δ ≫ μ = 𝟙 + 𝟙` on the toric electric
Lagrangian object `unitPlusElectricObj k = 1 ⊕ e`.

**`Δ ≫ μ = 𝟙 + 𝟙` is NOT separability.** `SymTFT/FrobeniusAlgebra.lean` defines
`IsSeparableAlgebra X` as Kock 2004 §2.4 — the comultiplication is a right *section* of the
multiplication, `Δ ≫ μ = 𝟙 X` — the identity, not twice it. The composite `𝟙 + 𝟙` is the
FPdim-2 value of the *unnormalized* structure; separability is one rescaling away.

This module ships the rescaling and the genuine predicates:

* **`electricComulNorm = ⅟2 • Δ`, `electricCounitNorm = 2 • ε`** under `[Invertible (2 : k)]`
  — the two-sided normalization (halving `Δ` alone would break the counit laws; doubling `ε`
  restores them).
* **`electricComonObjNorm`** — the normalized structure is still a `ComonObj`
  (counit laws + coassociativity all survive, each verified, not assumed).
* **`electric_isFrobeniusAlgebra_norm`** — a genuine `IsFrobeniusAlgebra` for
  `(electricMonObj, electricComonObjNorm)`. (The *unnormalized* pair is also a genuine
  Frobenius algebra — `electric_isFrobeniusAlgebra`, unconditional — since both compatibility
  laws are scale-free in the sense that both sides carry the same power of the scalar.)
* **`electricComulNorm_comp_electricMul : Δ′ ≫ μ = 𝟙`** — the honest separability equation,
  and **`electric_isSeparableAlgebra_norm`**, the genuine `IsSeparableAlgebra` it packages.

**Characteristic 2 is genuinely excluded, not merely inconvenient.** `electricComul_comp_mul_eq_two_smul`
identifies the unnormalized composite as `(2 : k) • 𝟙`; in characteristic 2 that is `0`
(`electricComul_comp_electricMul_char_two`), so *no* scalar rescaling `c • Δ` can be a section
of `μ` unless the object is degenerate (`no_smul_separability_of_char_two`). The
`[Invertible (2 : k)]` hypothesis is therefore sharp for this route.

The scalar action itself is supplied by `SymTFT/VecGLinear.lean` (`Linear` +
`MonoidalLinear` on `VecG_Cat k G`) and `SymTFT/CenterLinear.lean` (their descent to
`Center C`) — `Preadditive` alone gives only `ℤ`-scalars and cannot halve.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.

## References

- Kock, *Frobenius Algebras and 2D TQFTs*, Cambridge 2004, §2.4 (separability = `Δ ≫ μ = 𝟙`;
  a Frobenius algebra with invertible `dim` is normalizable to a separable one).
- Davydov–Müger–Nikshych–Ostrik, arXiv:1009.2117 (étale = commutative + separable).
-/
import Mathlib
import SKEFTHawking.SymTFT.ElectricComonoid
import SKEFTHawking.SymTFT.FrobeniusAlgebra
import SKEFTHawking.SymTFT.VecGLinear
import SKEFTHawking.SymTFT.CenterLinear

namespace SKEFTHawking.SymTFT.ElectricSeparable

open CategoryTheory MonoidalCategory Limits
open SKEFTHawking SKEFTHawking.CenterFunctorZ2 SKEFTHawking.CenterFunctorZ2Equiv
open SKEFTHawking.SymTFT
open SKEFTHawking.SymTFT.A5VacuumPlusElectric
open SKEFTHawking.SymTFT.ElectricAlgebraObject
open SKEFTHawking.SymTFT.ElectricComonoid

variable (k : Type) [CommRing k]

/-! ## §1. The unnormalized pair IS a Frobenius algebra (unconditional) -/

/-- **`1 ⊕ e` is a genuine Frobenius algebra** in `Center (VecG_Cat k G2)`, for the landed
`electricMonObj` / `electricComonObj` structures: this is exactly the `IsFrobeniusAlgebra`
predicate of `SymTFT/FrobeniusAlgebra.lean`, whose two conjuncts are the two laws proved in
`ElectricComonoid` (`electricFrobenius_right` is the left-whiskered conjunct,
`electricFrobenius_left` the right-whiskered one). No hypothesis on `k`.

Note this says nothing about separability: `IsFrobeniusAlgebra` is the bimodule-map condition
only. -/
theorem electric_isFrobeniusAlgebra : IsFrobeniusAlgebra (unitPlusElectricObj k) :=
  ⟨electricFrobenius_right k, electricFrobenius_left k⟩

/-! ## §2. The unnormalized composite as a scalar multiple of the identity -/

/-- **`Δ ≫ μ = (2 : k) • 𝟙`** — the `k`-scalar form of `electricComul_comp_electricMul`
(`Δ ≫ μ = 𝟙 + 𝟙`). This is the FPdim-2 value of the *unnormalized* Frobenius structure;
it is what makes the normalization of §3 possible exactly when `2` is invertible in `k`. -/
theorem electricComul_comp_mul_eq_two_smul :
    electricComul k ≫ electricMul k = (2 : k) • 𝟙 (unitPlusElectricObj k) := by
  rw [electricComul_comp_electricMul, two_smul]

/-! ## §3. The normalized (separable) structure, under `[Invertible (2 : k)]` -/

section Normalized

variable [Invertible (2 : k)]

/-- **The normalized comultiplication** `Δ′ = ½ • Δ`. Halving `Δ` turns the FPdim-2 composite
`Δ ≫ μ = 2 • 𝟙` into the separability identity `Δ′ ≫ μ = 𝟙`. -/
noncomputable def electricComulNorm :
    unitPlusElectricObj k ⟶ unitPlusElectricObj k ⊗ unitPlusElectricObj k :=
  (⅟(2 : k)) • electricComul k

/-- **The normalized counit** `ε′ = 2 • ε`. The doubling is forced: the counit laws pair `Δ`
with `ε` linearly, so halving `Δ` must be compensated on the counit for
`Δ′ ≫ (ε′ ▷ X) = λ⁻¹` to survive. -/
noncomputable def electricCounitNorm :
    unitPlusElectricObj k ⟶ 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) :=
  (2 : k) • unitPlusElectric_counit k

/-- The scalar `½ · 2 = 1` bookkeeping used by both counit laws. -/
private theorem invOf_two_mul_two : (⅟(2 : k)) * (2 : k) = 1 := invOf_mul_self (2 : k)

/-- **Left counit law for the normalized structure**: `Δ′ ≫ (ε′ ▷ X) = (λ_ X).inv`. The two
rescalings cancel exactly. -/
theorem electricComulNorm_counit_comul :
    electricComulNorm k ≫ (electricCounitNorm k ▷ unitPlusElectricObj k) =
      (λ_ (unitPlusElectricObj k)).inv := by
  rw [electricComulNorm, electricCounitNorm, MonoidalLinear.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul, smul_smul, invOf_two_mul_two, one_smul,
    electricComul_counit_comul]

/-- **Right counit law for the normalized structure**: `Δ′ ≫ (X ◁ ε′) = (ρ_ X).inv`. -/
theorem electricComulNorm_comul_counit :
    electricComulNorm k ≫ (unitPlusElectricObj k ◁ electricCounitNorm k) =
      (ρ_ (unitPlusElectricObj k)).inv := by
  rw [electricComulNorm, electricCounitNorm, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, invOf_two_mul_two, one_smul,
    electricComul_comul_counit]

/-- **Coassociativity of the normalized comultiplication**. Both sides pick up the same
factor `(½)²`, so this is `electricComul_assoc` rescaled. -/
theorem electricComulNorm_assoc :
    electricComulNorm k ≫ (unitPlusElectricObj k ◁ electricComulNorm k) =
      electricComulNorm k ≫ (electricComulNorm k ▷ unitPlusElectricObj k) ≫
        (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom := by
  simp only [electricComulNorm, MonoidalLinear.whiskerLeft_smul,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [electricComul_assoc]

/-- **The normalized comonoid structure on `1 ⊕ e`** — the same object, with `Δ′ = ½ • Δ` and
`ε′ = 2 • ε`. Shipped as a `def` (not an `instance`) so it does not collide with the
unconditional `electricComonObj`; downstream statements name it explicitly. -/
@[reducible] noncomputable def electricComonObjNorm :
    CategoryTheory.ComonObj (unitPlusElectricObj k) where
  counit := electricCounitNorm k
  comul := electricComulNorm k
  counit_comul := electricComulNorm_counit_comul k
  comul_counit := electricComulNorm_comul_counit k
  comul_assoc := electricComulNorm_assoc k

/-! ### §3.1 Separability — the honest `Δ′ ≫ μ = 𝟙` -/

/-- **THE SEPARABILITY EQUATION**: `Δ′ ≫ μ = 𝟙` on the toric electric Lagrangian object.
This — not `Δ ≫ μ = 𝟙 + 𝟙` — is Kock 2004 §2.4 separability: the normalized comultiplication
is a genuine right section of the multiplication. Proof: `Δ′ ≫ μ = ½ • (Δ ≫ μ) = ½ • (2 • 𝟙)`
and `½ · 2 = 1`. -/
theorem electricComulNorm_comp_electricMul :
    electricComulNorm k ≫ electricMul k = 𝟙 (unitPlusElectricObj k) := by
  rw [electricComulNorm, Linear.smul_comp, electricComul_comp_mul_eq_two_smul, smul_smul,
    invOf_two_mul_two, one_smul]

/-- **`IsSeparableAlgebra` for the normalized structure** — the packaged form of
`electricComulNorm_comp_electricMul` against the project predicate of
`SymTFT/FrobeniusAlgebra.lean`. Instance arguments are given explicitly because
`electricComonObjNorm` is deliberately not registered as an instance. -/
theorem electric_isSeparableAlgebra_norm :
    @IsSeparableAlgebra (CategoryTheory.Center (VecG_Cat k G2)) _ _
      (unitPlusElectricObj k) (electricMonObj k) (electricComonObjNorm k) :=
  electricComulNorm_comp_electricMul k

/-- **`IsFrobeniusAlgebra` for the normalized structure** — the Frobenius compatibility laws
survive the rescaling (both sides of each law are homogeneous of degree one in `Δ`), so this
is `electric_isFrobeniusAlgebra` transported through `½ •`. Together with
`electric_isSeparableAlgebra_norm` this is a genuine *separable* Frobenius algebra. -/
theorem electric_isFrobeniusAlgebra_norm :
    @IsFrobeniusAlgebra (CategoryTheory.Center (VecG_Cat k G2)) _ _
      (unitPlusElectricObj k) (electricMonObj k) (electricComonObjNorm k) := by
  constructor
  · show (unitPlusElectricObj k ◁ electricComulNorm k) ≫
        (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).inv ≫
        (electricMul k ▷ unitPlusElectricObj k) =
      electricMul k ≫ electricComulNorm k
    simp only [electricComulNorm, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp,
      Linear.comp_smul]
    rw [electricFrobenius_right]
  · show (electricComulNorm k ▷ unitPlusElectricObj k) ≫
        (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom ≫
        (unitPlusElectricObj k ◁ electricMul k) =
      electricMul k ≫ electricComulNorm k
    simp only [electricComulNorm, MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
      Linear.comp_smul]
    rw [electricFrobenius_left]

end Normalized

/-! ## §4. Characteristic 2 is genuinely excluded -/

/-- In characteristic 2 the unnormalized Frobenius composite **vanishes**:
`Δ ≫ μ = (2 : k) • 𝟙 = 0`. -/
theorem electricComul_comp_electricMul_char_two (h2 : (2 : k) = 0) :
    electricComul k ≫ electricMul k = 0 := by
  rw [electricComul_comp_mul_eq_two_smul, h2, zero_smul]

/-- **No scalar rescaling can separate the algebra in characteristic 2.** If `(2 : k) = 0` and
some `c • Δ` were a right section of `μ`, then the identity of `1 ⊕ e` would be zero — i.e.
the object degenerates. So `[Invertible (2 : k)]` is not a convenience hypothesis: it is sharp
for the rescaling route. -/
theorem no_smul_separability_of_char_two (h2 : (2 : k) = 0) (c : k)
    (hsep : (c • electricComul k) ≫ electricMul k = 𝟙 (unitPlusElectricObj k)) :
    𝟙 (unitPlusElectricObj k) = 0 := by
  rw [Linear.smul_comp, electricComul_comp_electricMul_char_two k h2, smul_zero] at hsep
  exact hsep.symm

/-! ### §4.1 The object is non-degenerate, so the char-2 exclusion is an outright refutation -/

/-- **The electric anyon is not a zero object** for nontrivial `k`: its identity is nonzero,
because at the flux sector `eAdd` the underlying `VecG_Cat` component is the free line
`ModuleCat.of k k`, on which `𝟙 = 0` would force `(1 : k) = 0`. -/
theorem id_electricAnyon_ne_zero [Nontrivial k] :
    𝟙 (electricAnyon k) ≠ (0 : electricAnyon k ⟶ electricAnyon k) := by
  intro h
  have he : (𝟙 ((electricAnyon k).1 eAdd)) = 0 := by
    -- `.f` needs the ascription: field notation does not fire on the raw `𝟙` (its type shows as
    -- `CategoryStruct.toQuiver.1 …`, not a constant application).
    have hf : (𝟙 (electricAnyon k) : electricAnyon k ⟶ electricAnyon k).f = 0 := by rw [h]; rfl
    exact congrFun hf eAdd
  have h1 : (1 : k) = 0 := by
    have hev := congrArg
      (fun f : (ModuleCat.of k k) ⟶ (ModuleCat.of k k) => f.hom (1 : k)) he
    -- NB: a bare `simpa using hev` fails — `simp` closes the GOAL `(1 : k) = 0` to `False`
    -- via `one_ne_zero`, so the simplified hypothesis no longer matches. Rewrite the
    -- hypothesis only.
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_coe, id_eq] at hev
    exact hev
  exact one_ne_zero h1

/-- **The toric electric Lagrangian object `1 ⊕ e` is not a zero object** for nontrivial `k`:
the electric summand splits off (`electricInj ≫ electricProj = 𝟙`), so `𝟙 (1 ⊕ e) = 0` would
collapse the electric anyon. -/
theorem id_unitPlusElectricObj_ne_zero [Nontrivial k] :
    𝟙 (unitPlusElectricObj k) ≠ (0 : unitPlusElectricObj k ⟶ unitPlusElectricObj k) := by
  intro h
  refine id_electricAnyon_ne_zero k ?_
  calc 𝟙 (electricAnyon k)
      = electricInj k ≫ electricProj k := (electricInj_comp_electricProj k).symm
    _ = (electricInj k ≫ 𝟙 (unitPlusElectricObj k)) ≫ electricProj k := by
        rw [Category.comp_id]
    _ = 0 := by rw [h, Limits.comp_zero, Limits.zero_comp]

/-- **CHARACTERISTIC 2 IS REFUTED, not merely excluded.** For nontrivial `k` of
characteristic 2, **no** scalar rescaling `c • Δ` of the electric comultiplication is a right
section of `μ` — i.e. `IsSeparableAlgebra` is unattainable on this object along the rescaling
route. Hence the `[Invertible (2 : k)]` hypothesis of §3 is sharp. -/
theorem no_smul_separability_of_char_two' [Nontrivial k] (h2 : (2 : k) = 0) (c : k) :
    (c • electricComul k) ≫ electricMul k ≠ 𝟙 (unitPlusElectricObj k) := fun hsep =>
  id_unitPlusElectricObj_ne_zero k (no_smul_separability_of_char_two k h2 c hsep)

end SKEFTHawking.SymTFT.ElectricSeparable
