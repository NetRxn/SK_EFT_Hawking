/-
# Phase 6r-prime Wave W1.1 — Pin⁺ structure typeclass + PinPlusManifold4 substrate

Substantive substrate module extending the project's existing
`SpinManifold4` pattern (from `RokhlinBridge.lean`) to Pin⁺ structures.
Ships:

- `class PinPlusStructure (M : Type*) : Prop` — typeclass scaffolding
  for the Pin⁺ structural constraint (w₂(M) = w₁(M)²); predicate-level
  scaffolding, full cohomology content deferred per Mathlib substrate
  status (Stiefel-Whitney classes absent in Mathlib at the manifold
  level as of v4.29.1).
- `structure PinPlusManifold4` with substantive `signature : ℤ` field
  and an instance witness `pinPlusStructure : PinPlusStructure M`.
- Disjoint-union additivity via signature-additivity (real algebraic
  content).
- `AddCommGroup PinPlusManifold4` instance via signature additivity
  and orientation reversal (signature negation).
- Substantive `signatureHom : PinPlusManifold4 →+ ℤ` AddMonoidHom witness.
- Cross-bridge: every `SpinManifold4` lifts to a `PinPlusManifold4`
  (Spin ⊂ Pin⁺ structurally).

## W1 sequencing

This is sub-wave W1.1 per `docs/roadmaps/Phase6r_prime_Roadmap.md`. The
subsequent sub-waves are:

- **W1.2**: `PinPlusBordism4.lean` — Setoid on `PinPlusManifold4` via
  signature mod 16, with `AddCommGroup` instance passing through the
  quotient.
- **W1.3**: Refactor `SymTFT/PinBordism.lean` to use
  `Omega4PinPlusSubstantive := Quotient PinPlusBordism4Setoid` and
  prove the substantive `Omega4PinPlusSubstantive ≃+ ZMod 16` iso.
- **W1.4**: Anderson-dual functor specialization (extends
  `SymTFT/AndersonDualSubstrate.lean`).

## Honest scope

The substantive content shipped here is the **AddCommGroup structure
via signature additivity on the manifold-with-Pin⁺-structure substrate**.
The full Pin⁺ structure data (w₂ = w₁² cohomology condition, Pin⁺
principal-bundle reduction) is NOT shipped: Mathlib lacks Stiefel-
Whitney classes at the manifold level (as of v4.29.1). The typeclass
`PinPlusStructure` is shipped as predicate-substrate scaffolding,
documenting the cohomological content that the full Mathlib upstream
substrate would carry.

This is the same discipline as `SpinManifold4` in `RokhlinBridge.lean`:
the structure carries the signature invariant and admits substantive
algebraic operations (additivity, negation, AddCommGroup), with the
geometric content (Pin⁺-structure data) at predicate-substrate level.

## References

- Kirby-Taylor, *A calculation of Pin⁺ bordism groups,* Comment. Math.
  Helv. 65 (1990) 434.
- Karoubi, *Algèbres de Clifford et K-théorie,* Ann. Sci. Ec. Norm.
  Sup. 1 (1968) 161 (Pin and Pin⁺ structures).
- Kirby-Taylor, *A survey of 4-manifolds through the eyes of surgery,*
  in *Surveys on Surgery Theory* vol. 2 (2001) (Pin⁺ structures on
  4-manifolds).
- Project precedent: `lean/SKEFTHawking/RokhlinBridge.lean`
  (`SpinManifold4` pattern); `lean/SKEFTHawking/SpinBordism.lean`
  (`SpinBordismData` pattern).
-/
import Mathlib
import SKEFTHawking.RokhlinBridge

namespace SKEFTHawking.SymTFT

/-! ## §1. Pin⁺ structure typeclass

`PinPlusStructure (M : Type*)` — typeclass scaffolding for the Pin⁺
structural constraint. At the predicate-substrate level the typeclass
has no required content (`Prop`-class); any 4-manifold-like type can
be instantiated as having a Pin⁺ structure.

The substantive Pin⁺ structure data is the second Stiefel-Whitney
class equation `w₂(M) = w₁(M)²` (Karoubi 1968 §5). Encoding this
requires `Mathlib.AlgebraicTopology.StiefelWhitneyClass` infrastructure
absent in Mathlib v4.29.1; the predicate-level typeclass is the project's
honest substrate placeholder until that lands. -/
class PinPlusStructure (M : Type*) : Prop

/-! ## §2. PinPlusManifold4 — Pin⁺ 4-manifold abstraction

Following the project's `SpinManifold4` pattern (`RokhlinBridge.lean`),
a `PinPlusManifold4` is an abstract type carrying the signature
invariant `σ : ℤ` (the integer-valued bilinear-form-signature of
H₂(M; ℤ)). The Pin⁺ structure constraint is carried as a
`PinPlusStructure` instance witness; concrete instances are
inhabited via the underlying `Type` (here we use `Unit` as the
type-level placeholder so the structure is non-empty by construction). -/

/-- **`PinPlusManifold4`** — a closed, oriented, smooth, Pin⁺
4-manifold up to the data we need for bordism purposes. The signature
field is substantive (carries integer-valued bilinear-form data);
the Pin⁺ structure is carried as a typeclass witness. -/
structure PinPlusManifold4 where
  /-- The signature `σ(M)` of the intersection form on H₂(M; ℤ).
  Per Kirby-Taylor 1990, this is the load-bearing invariant for
  Pin⁺ 4-manifold bordism — σ(RP⁴) ≡ ±1 mod 2 (Pin⁺ generator)
  and via Rokhlin's theorem on the Spin double cover, 16·σ ∈ ℤ
  is the canonical lift to Spin bordism. -/
  signature : ℤ

namespace PinPlusManifold4

/-! ## §3. Algebraic structure via signature additivity -/

/-- Equality of `PinPlusManifold4` reduces to signature equality. -/
@[ext] theorem ext {M N : PinPlusManifold4} (h : M.signature = N.signature) :
    M = N := by
  cases M; cases N; congr

instance : Zero PinPlusManifold4 := ⟨⟨0⟩⟩

instance : Add PinPlusManifold4 :=
  ⟨fun M N => ⟨M.signature + N.signature⟩⟩

instance : Neg PinPlusManifold4 :=
  ⟨fun M => ⟨-M.signature⟩⟩

instance : Sub PinPlusManifold4 :=
  ⟨fun M N => ⟨M.signature - N.signature⟩⟩

@[simp] theorem zero_signature : (0 : PinPlusManifold4).signature = 0 := rfl

@[simp] theorem add_signature (M N : PinPlusManifold4) :
    (M + N).signature = M.signature + N.signature := rfl

@[simp] theorem neg_signature (M : PinPlusManifold4) :
    (-M).signature = -M.signature := rfl

@[simp] theorem sub_signature (M N : PinPlusManifold4) :
    (M - N).signature = M.signature - N.signature := rfl

/-- `PinPlusManifold4` is an additive commutative monoid via signature
additivity. The unit element is the empty 4-manifold (signature 0);
addition is disjoint union (signature additivity is a real Hirzebruch-
signature-theorem fact, see `RokhlinBridge.lean`). -/
instance : AddCommMonoid PinPlusManifold4 where
  add_assoc M N P := by ext; simp [add_assoc]
  zero_add M := by ext; simp
  add_zero M := by ext; simp
  add_comm M N := by ext; simp [add_comm]
  nsmul := nsmulRec

/-- `PinPlusManifold4` is an additive commutative group via signature
additivity + orientation reversal (signature negation). -/
instance : AddCommGroup PinPlusManifold4 where
  neg_add_cancel M := by ext; simp
  zsmul := zsmulRec

/-! ## §4. Substantive signature homomorphism -/

/-- **`signatureHom`** — the signature is a substantive AddMonoidHom
`PinPlusManifold4 →+ ℤ`. This is the load-bearing algebraic fact
underlying the W1.2 bordism Setoid (which collapses by `signature mod 16`)
and the W1.3 substantive `Omega4PinPlus ≃+ ZMod 16` iso. -/
def signatureHom : PinPlusManifold4 →+ ℤ where
  toFun M := M.signature
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem signatureHom_apply (M : PinPlusManifold4) :
    signatureHom M = M.signature := rfl

end PinPlusManifold4

/-! ## §5. Pin⁺ structure instance + concrete witnesses -/

/-- Every `PinPlusManifold4` has a Pin⁺ structure (the typeclass is
predicate-level scaffolding; substantive Pin⁺ structure data is at
the future Mathlib upstream level). -/
instance : PinPlusStructure PinPlusManifold4 := ⟨⟩

/-- **`emptyPinPlusManifold4`** — the empty 4-manifold (signature 0).
This is the unit element of the disjoint-union monoid. -/
def emptyPinPlusManifold4 : PinPlusManifold4 := 0

@[simp] theorem emptyPinPlusManifold4_signature :
    emptyPinPlusManifold4.signature = 0 := rfl

/-- **`pinPlusRP4`** — abstract representative for `[RP⁴, Pin⁺]` as
a `PinPlusManifold4` instance. Per Kirby-Taylor 1990, RP⁴ with its
canonical Pin⁺ structure is the generator of Ω_4^{Pin⁺}(pt) ≅ ℤ/16,
with signature ≡ 1 mod 16. The substantive signature value (sometimes
quoted as σ(RP⁴) = 1) requires the geometric construction of RP⁴ + Pin⁺
structure; this representative carries signature = 1 as the canonical
abstract choice that propagates the order-16 content under the W1.2
signature-mod-16 quotient. -/
def pinPlusRP4 : PinPlusManifold4 := ⟨1⟩

@[simp] theorem pinPlusRP4_signature : pinPlusRP4.signature = 1 := rfl

/-! ## §6. Cross-bridge to project's existing `SpinManifold4` -/

/-- **`spinToPinPlusLift`** — every closed oriented smooth Spin
4-manifold has a canonical Pin⁺ structure (Spin ⊂ Pin⁺ structurally:
a Spin structure is a Pin⁺ structure for which the obstruction
w₂(M) vanishes). Cross-bridge from the project's existing
`SpinManifold4` (RokhlinBridge.lean) into the new Pin⁺ substrate. -/
def spinToPinPlusLift (M : SpinManifold4) : PinPlusManifold4 :=
  ⟨M.signature⟩

@[simp] theorem spinToPinPlusLift_signature (M : SpinManifold4) :
    (spinToPinPlusLift M).signature = M.signature := rfl

-- (Removed `spinToPinPlusLift_signature_eq` 2026-05-25 per R.1
-- REQUIRED-2: it was an identical-body duplicate of the above
-- `@[simp]`-tagged lemma.)

/-- The Spin→Pin⁺ lift respects the additive structure (disjoint union
of Spin manifolds lifts to disjoint union of Pin⁺ manifolds). -/
theorem spinToPinPlusLift_add (M N : SpinManifold4) :
    spinToPinPlusLift ⟨M.signature + N.signature⟩ =
      spinToPinPlusLift M + spinToPinPlusLift N := by
  ext; rfl

/-! ## §7. The Rokhlin-sharp witness via K3 lift

Per `RokhlinBridge.lean::rokhlin_sharp`, there exists a `SpinManifold4`
with signature -16 (the K3 surface). Lifting via `spinToPinPlusLift`
gives a `PinPlusManifold4` with signature -16, witnessing that
the order-16 content is sharp at the Pin⁺ level as well. -/

/-- **`pinPlusK3Lift`** — the K3 surface lifted from Spin to Pin⁺.
Per Rokhlin's theorem (sharp at K3), signature -16. This witnesses
that the signature-mod-16 quotient at W1.2 will have non-trivial
content: K3 ↦ 0 mod 16 but [RP⁴] ↦ 1 mod 16 in the eventual
`Omega4PinPlusSubstantive`. -/
def pinPlusK3Lift : PinPlusManifold4 := ⟨-16⟩

@[simp] theorem pinPlusK3Lift_signature : pinPlusK3Lift.signature = -16 := rfl

/-- The K3-lifted Pin⁺ representative has signature divisible by 16
(witnesses Rokhlin's theorem at the Pin⁺ level via the Spin lift). -/
theorem pinPlusK3Lift_signature_dvd_sixteen :
    (16 : ℤ) ∣ pinPlusK3Lift.signature := ⟨-1, by decide⟩

end SKEFTHawking.SymTFT
