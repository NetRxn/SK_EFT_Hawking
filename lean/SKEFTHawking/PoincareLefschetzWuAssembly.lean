/-
# Phase 5q.H (W-A.1e) — the generic dual-class layer + the datum-assembly seam

The GENERIC datum-level layer over the merged Lefschetz–Wu tower (`PoincareLefschetzWu5`) and the
relative fundamental-class datum (`PoincareLefschetzRelFundClass`): bounded linear algebra over the
merged towers, no new geometry.

## §1. The generic dual-class extraction

For a `LefschetzWuDatum X S k nk n` and a class `w : H^k(X)`, the **dual functional**
`dualFunctional P w : H^{nk}(X,S) → ℤ/2`, `y ↦ μ(w ⌣ y)`, is literally `pairing P w` (the datum's own
perfect pairing evaluated at `w`) — the FUNCTIONAL-level generic dual-class extraction (the honest
statement: Mathlib has no relative cap product to build the HOMOLOGY class `[Q_w]` directly, so the
extraction lives at the functional level, matching how the Wu class itself is built via `wuFunctional`).

When the relative Kronecker pairing (`SingularRelativePairing.relKroneckerH`) against `H_{nk}(X,S)` is
**representationally perfect** (`RelKroneckerSurjective`, a UCT-flavored hypothesis field — bundled per
the house pattern, NOT proved: the genuinely-open half of relative universal coefficients, since the
project's in-tree `SingularRelativeUC` facts already give the INJECTIVE half for free), this functional
is represented by an honest relative-homology class `[Q_w] ∈ H_{nk}(X,S)` (`RepresentedBy`), unique
whenever it exists — uniqueness needs NO extra hypothesis, it follows already from
`SingularRelativeUC.relHomology_eq_zero_of_relKroneckerH`.

Specialized to the `n = 5` tower's two characteristic classes:
* `dualW2` — the dual functional of `w₂(W) = wuW2 P₁₄ P₂₃` (the `(2,3)` leg). VERIFIED against the
  merged `PinPlusCharPairData` carrier: Bor's admissibility field (`WAdm.hwu`/`CharPairBor.hwu`) is
  literally `wuW2 P₁₄ P₂₃ = 0` — the FULL `v₂ + v₁²` Stiefel–Whitney sum, with **no further `+ v₁²`**
  summed on top. `wuW2_add_cupSquare_wuW1_eq_wuClassW2` below computes what the further-summed
  quantity `w₂(W) + w₁(W)²` collapses to (bare `v₂`, char-2 cancellation) — settling the item's open
  arithmetic question: that quantity is a DIFFERENT, NOT-needed class; `dualW2` correctly targets
  plain `wuW2`.
* `dualW1` — the dual functional of `w₁(W) = wuW1 P₁₄` (the `(1,4)` leg) — the odd-bit `V` of the KT §5
  `ψ` story.

## §2. The datum-assembly seam `LefschetzWuDatum.ofRelFund14` / `.ofRelFund23`

Assembles a full `LefschetzWuDatum X S k nk 5` from a `RelFundClassDatum (m := 3) S` (the deep `μ`
input, `PoincareLefschetzRelFundClass`) with the `cup` and `sqOp` fields wired CONCRETE — `relCupH14` /
`relCupH23` (`SingularRelativeCup`) and `relSq1` / `relSq2` (`SingularRelativeBockstein` /
`SingularRelativeSteenrodSq2`) — leaving EXACTLY the finite-dimensionality / non-degeneracy / Betti-
equality trio (`findimAbs`, `findimRel`, `nondeg`, `dimeq`) as the named residual obligation for a
genuine compact 5-manifold-with-boundary `W` (1d's discharge target). Every other field of the `n = 5`
Wu tower is now concrete.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzWu5
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.SingularRelativeCup
import SKEFTHawking.SingularRelativeSteenrodSq2
import SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.PoincareLefschetzWuAssembly

open SKEFTHawking.PoincareLefschetzWu5 SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2 SKEFTHawking.SingularRelativeUC
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2

variable {X : TopCat} {S : Set X} {k nk n : ℕ}

/-! ## §1. The generic dual-class extraction -/

/-- **The dual functional** of `w : H^k(X)`: `y ↦ μ(w ⌣ y)` on `H^{nk}(X,S)` — literally the datum's
own Lefschetz pairing evaluated at `w`. The FUNCTIONAL-level generic dual-class extraction. -/
noncomputable def dualFunctional (P : LefschetzWuDatum X S k nk n) (w : Cohomology X k) :
    RelativeCohomology S nk →ₗ[ZMod 2] ZMod 2 :=
  pairing P w

@[simp] theorem dualFunctional_apply (P : LefschetzWuDatum X S k nk n) (w : Cohomology X k)
    (y : RelativeCohomology S nk) : dualFunctional P w y = P.mu (P.cup w y) := rfl

/-- `dualFunctional` is additive in `w`. -/
theorem dualFunctional_add (P : LefschetzWuDatum X S k nk n) (w w' : Cohomology X k) :
    dualFunctional P (w + w') = dualFunctional P w + dualFunctional P w' :=
  map_add (pairing P) w w'

/-- `dualFunctional` sends `0` to `0`. -/
theorem dualFunctional_zero (P : LefschetzWuDatum X S k nk n) : dualFunctional P 0 = 0 :=
  map_zero (pairing P)

/-- **Naturality against the Wu class itself**: at `w = v_k := wuClass P`, `dualFunctional` recovers the
Wu functional `x ↦ μ(Sq^k x)` — connecting the generic extraction back to the tower's own Wu class. -/
theorem dualFunctional_wuClass (P : LefschetzWuDatum X S k nk n) :
    dualFunctional P (wuClass P) = wuFunctional P := by
  ext x
  rw [dualFunctional_apply, wuFunctional, LinearMap.comp_apply, ← wu_relation P x]

/-- **A relative-homology class represents a functional** on `H^{N+1}(X,S)` via the relative Kronecker
pairing: `⟨·, z⟩ = φ`. -/
def RepresentedBy {N : ℕ} (S : Set X) (φ : RelativeCohomology S (N + 1) →ₗ[ZMod 2] ZMod 2)
    (z : RelativeHomology S (N + 1)) : Prop :=
  (relKroneckerH S).flip z = φ

/-- **Uniqueness of the representative** — no extra hypothesis needed: it is exactly the injectivity of
`(relKroneckerH S).flip`, which `SingularRelativeUC.relHomology_eq_zero_of_relKroneckerH` already proves
in-tree. -/
theorem RepresentedBy.unique {N : ℕ} {φ : RelativeCohomology S (N + 1) →ₗ[ZMod 2] ZMod 2}
    {z z' : RelativeHomology S (N + 1)} (hz : RepresentedBy S φ z) (hz' : RepresentedBy S φ z') :
    z = z' := by
  have heq : (relKroneckerH S).flip z = (relKroneckerH S).flip z' := hz.trans hz'.symm
  have hsub : (relKroneckerH S).flip (z - z') = 0 := by rw [map_sub, heq, sub_self]
  have hz0 : z - z' = 0 := by
    apply relHomology_eq_zero_of_relKroneckerH S
    intro ω
    have hcon := congrFun (congrArg DFunLike.coe hsub) ω
    simpa using hcon
  exact sub_eq_zero.mp hz0

/-- **Representationally perfect at degree `N+1`**: `(relKroneckerH S).flip` is surjective onto the
full linear dual of `H^{N+1}(X,S)` — the genuinely-open UCT-flavored half of relative universal
coefficients (the injective half is free, see `RepresentedBy.unique`). Bundled as an explicit
hypothesis (house pattern: bundle-don't-posit), never a new axiom. -/
def RelKroneckerSurjective (S : Set X) (N : ℕ) : Prop :=
  Function.Surjective ⇑((relKroneckerH (X := X) S (N := N)).flip)

/-- **Existence of the representing class**, given the bundled perfectness hypothesis. -/
theorem exists_representative {N : ℕ} (hsurj : RelKroneckerSurjective S N)
    (φ : RelativeCohomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :
    ∃ z : RelativeHomology S (N + 1), RepresentedBy S φ z :=
  hsurj φ

/-! ### The `n = 5` specializations -/

/-- **The dual functional of `w₂(W)`** (the `(2,3)` leg): `dualFunctional P₂₃ (wuW2 P₁₄ P₂₃)`. This is
literally the class Bor's admissibility hypothesis names (`PinPlusCharPairData.WAdm.hwu` /
`CharPairBor.hwu` : `wuW2 P₁₄ P₂₃ = 0`), the FULL `v₂ + v₁²` sum — no further `+ v₁²`. -/
noncomputable def dualW2 (P₁₄ : LefschetzWuDatum X S 1 4 5) (P₂₃ : LefschetzWuDatum X S 2 3 5) :
    RelativeCohomology S 3 →ₗ[ZMod 2] ZMod 2 :=
  dualFunctional P₂₃ (wuW2 P₁₄ P₂₃)

@[simp] theorem dualW2_apply (P₁₄ : LefschetzWuDatum X S 1 4 5) (P₂₃ : LefschetzWuDatum X S 2 3 5)
    (y : RelativeCohomology S 3) : dualW2 P₁₄ P₂₃ y = P₂₃.mu (P₂₃.cup (wuW2 P₁₄ P₂₃) y) := rfl

/-- **The dual functional of `w₁(W) = v₁`** (the `(1,4)` leg) — the odd-bit `V` of the KT §5 `ψ`
story. -/
noncomputable def dualW1 (P₁₄ : LefschetzWuDatum X S 1 4 5) :
    RelativeCohomology S 4 →ₗ[ZMod 2] ZMod 2 :=
  dualFunctional P₁₄ (wuW1 P₁₄)

@[simp] theorem dualW1_apply (P₁₄ : LefschetzWuDatum X S 1 4 5) (y : RelativeCohomology S 4) :
    dualW1 P₁₄ y = P₁₄.mu (P₁₄.cup (wuW1 P₁₄) y) := rfl

/-- **Verification of the mission's open arithmetic question**: `w₂(W) + w₁(W)²` collapses (char 2) to
BARE `v₂` (`wuClassW2 P₂₃`) — a DIFFERENT quantity from `wuW2` itself. Since the merged carrier's `hwu`
field is literally `wuW2 P₁₄ P₂₃ = 0` (checked directly against `PinPlusCharPairData.WAdm` /
`CharPairBor`), NOT `wuW2 + w₁² = 0`, this further-summed quantity is NOT what `dualW2` should target
— settling the verification in favor of the plain `wuW2` form. -/
theorem wuW2_add_cupSquare_wuW1_eq_wuClassW2 (P₁₄ : LefschetzWuDatum X S 1 4 5)
    (P₂₃ : LefschetzWuDatum X S 2 3 5) :
    wuW2 P₁₄ P₂₃ + PoincareDualityWuFormula.cupSquareₗ (wuW1 P₁₄) = wuClassW2 P₂₃ := by
  rw [wuW2, show wuW1 P₁₄ = wuClassW1 P₁₄ from rfl, add_assoc, ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]

/-! ## §2. The datum-assembly seam -/

/-- **The `(1,4)` Lefschetz–Wu datum assembled from a relative fundamental-class datum**, with the
`cup` and `Sq¹` fields wired CONCRETE (`relCupH14`, `relSq1`). The named residual obligation (1d's
discharge target for a genuine compact 5-manifold-with-boundary `W`): `findimAbs`, `findimRel`,
`nondeg`, `dimeq`. -/
noncomputable def LefschetzWuDatum.ofRelFund14 (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 1))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (nondeg : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 1)
           = Module.finrank (ZMod 2) (RelativeCohomology S 4)) :
    LefschetzWuDatum X S 1 4 5 :=
  D.toLefschetzWuDatum relCupH14 (relSq1 (n := 3)) findimAbs findimRel nondeg dimeq

/-- **The `(2,3)` Lefschetz–Wu datum assembled from a relative fundamental-class datum**, with the
`cup` and `Sq²` fields wired CONCRETE (`relCupH23`, `relSq2`). Same named residual obligation as the
`(1,4)` leg, at the `(2,3)` finite-dimensionality/non-degeneracy/Betti-equality shape. -/
noncomputable def LefschetzWuDatum.ofRelFund23 (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 2))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (nondeg : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 2)
           = Module.finrank (ZMod 2) (RelativeCohomology S 3)) :
    LefschetzWuDatum X S 2 3 5 :=
  D.toLefschetzWuDatum relCupH23 relSq2 findimAbs findimRel nondeg dimeq

/-- The `(1,4)` assembled datum's `mu` field is exactly the relative fundamental-class functional. -/
theorem LefschetzWuDatum.ofRelFund14_mu (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 1))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (nondeg : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 1)
           = Module.finrank (ZMod 2) (RelativeCohomology S 4)) :
    (LefschetzWuDatum.ofRelFund14 D findimAbs findimRel nondeg dimeq).mu = D.mu := rfl

/-- The `(2,3)` assembled datum's `mu` field is exactly the relative fundamental-class functional. -/
theorem LefschetzWuDatum.ofRelFund23_mu (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 2))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (nondeg : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 2)
           = Module.finrank (ZMod 2) (RelativeCohomology S 3)) :
    (LefschetzWuDatum.ofRelFund23 D findimAbs findimRel nondeg dimeq).mu = D.mu := rfl

end SKEFTHawking.PoincareLefschetzWuAssembly
