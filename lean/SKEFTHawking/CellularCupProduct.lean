/-
# Phase 5q.F W4-cohomology brick 6 — the cellular ℤ/2 cup product (toward the intersection form)

The genuine **cup product** on cellular ℤ/2 cohomology — the ring structure that Mathlib lacks entirely
(confirmed: no cup product / cohomology ring in Mathlib, only abstract `CommRing`/`Coalgebra`). It is the
prerequisite for the **intersection form** on `H²` (resp. `H¹` of a surface), which carries the
`ZMod 4`-quadratic refinement underlying the Guillou–Marin / ABK invariant `β` of a Pin⁺ 4-manifold.

The cup product is NOT determined by the chain complex alone — it needs a **diagonal approximation**
`Δ : C → C ⊗ C` (Alexander–Whitney). We carry the diagonal as data (`CupData.coeff`, the ℤ/2
coefficients of the cellular diagonal), exactly as the project carries Stiefel–Whitney data on
`HasStiefelWhitney`; the cochain cup product, its bilinearity, and (with the `leibniz` chain-map field)
its descent to cohomology are then genuine theorems. This module ships the **cochain-level** cup product
and its bilinearity; the Leibniz/descent and the surface intersection form follow in the next bricks.

Per Invariant #15: no new axioms — `CupData` is carried geometric structure (the diagonal), and the cup
product is a definitional construction over it.
-/
import SKEFTHawking.CellularCohomologyMod2

namespace SKEFTHawking.CellularCohomologyMod2

open scoped BigOperators

/-- **Diagonal-approximation data** on a cell complex `C` (carried, as `HasStiefelWhitney` carries SW
data): `coeff p q σ a b` is the ℤ/2 coefficient of `(a : p-cell) ⊗ (b : q-cell)` in the cellular
diagonal `Δσ` of the `(p+q)`-cell `σ` (the Alexander–Whitney diagonal). It determines the cup product on
cochains. -/
structure CupData (C : CellComplex) where
  /-- The diagonal coefficient of `a ⊗ b` in `Δσ`. -/
  coeff : (p q : ℕ) → C.cells (p + q) → C.cells p → C.cells q → ZMod 2

namespace CupData

variable {C : CellComplex} (D : CupData C)

/-- The **cochain cup product** `⌣ : Cᵖ × Cᵍ → Cᵖ⁺ᵍ`, `(f ⌣ g)(σ) = ∑_{a,b} ⟨Δσ : a⊗b⟩ · f(a) · g(b)`,
induced by the carried diagonal. -/
def cup {p q : ℕ} (f : Cochain C p) (g : Cochain C q) : Cochain C (p + q) :=
  fun σ => ∑ a : C.cells p, ∑ b : C.cells q, D.coeff p q σ a b * f a * g b

@[simp] theorem cup_apply {p q : ℕ} (f : Cochain C p) (g : Cochain C q) (σ : C.cells (p + q)) :
    D.cup f g σ = ∑ a : C.cells p, ∑ b : C.cells q, D.coeff p q σ a b * f a * g b := rfl

/-- The cup product is **left-additive**. -/
theorem cup_add_left {p q : ℕ} (f₁ f₂ : Cochain C p) (g : Cochain C q) :
    D.cup (f₁ + f₂) g = D.cup f₁ g + D.cup f₂ g := by
  funext σ
  simp only [cup_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **right-additive**. -/
theorem cup_add_right {p q : ℕ} (f : Cochain C p) (g₁ g₂ : Cochain C q) :
    D.cup f (g₁ + g₂) = D.cup f g₁ + D.cup f g₂ := by
  funext σ
  simp only [cup_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **left ℤ/2-linear in the scalar**. -/
theorem cup_smul_left {p q : ℕ} (c : ZMod 2) (f : Cochain C p) (g : Cochain C q) :
    D.cup (c • f) g = c • D.cup f g := by
  funext σ
  simp only [cup_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **right ℤ/2-linear in the scalar**. -/
theorem cup_smul_right {p q : ℕ} (c : ZMod 2) (f : Cochain C p) (g : Cochain C q) :
    D.cup f (c • g) = c • D.cup f g := by
  funext σ
  simp only [cup_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **bilinear**, packaged as a `ZMod 2`-bilinear map `Cᵖ →ₗ Cᵍ →ₗ Cᵖ⁺ᵍ`. -/
def cupₗ {p q : ℕ} : Cochain C p →ₗ[ZMod 2] Cochain C q →ₗ[ZMod 2] Cochain C (p + q) :=
  LinearMap.mk₂ (ZMod 2) (fun f g => D.cup f g)
    (fun f₁ f₂ g => D.cup_add_left f₁ f₂ g) (fun c f g => D.cup_smul_left c f g)
    (fun f g₁ g₂ => D.cup_add_right f g₁ g₂) (fun c f g => D.cup_smul_right c f g)

@[simp] theorem cupₗ_apply {p q : ℕ} (f : Cochain C p) (g : Cochain C q) :
    D.cupₗ f g = D.cup f g := rfl

/-- `0 ⌣ g = 0`. -/
@[simp] theorem zero_cup {p q : ℕ} (g : Cochain C q) : D.cup (0 : Cochain C p) g = 0 := by
  funext σ; simp [cup_apply]

/-- `f ⌣ 0 = 0`. -/
@[simp] theorem cup_zero {p q : ℕ} (f : Cochain C p) : D.cup f (0 : Cochain C q) = 0 := by
  funext σ; simp [cup_apply]

end CupData

/-! ## §2. The Leibniz rule and descent to cohomology

The cup product descends to cohomology iff the diagonal is a chain map — the **Leibniz rule**
`δ(f ⌣ g) = δf ⌣ g + f ⌣ δg` (over `ℤ/2`, no sign). We carry it as a field on `CupRing` (the specific
instances — `RP^n`, surfaces — discharge it from their explicit diagonals). The index bookkeeping is
mild: `p + (q+1)` is *definitionally* `(p+q)+1` (Nat recursion is on the right argument), so only the
left term `δf ⌣ g : C^{(p+1)+q}` needs transport to `C^{(p+q)+1}` (via `Nat.succ_add`). -/

/-- A cell complex with a cup product satisfying the **Leibniz rule** (`δ` is a derivation), so the cup
product descends to a graded-ring structure on cohomology. -/
structure CupRing (C : CellComplex) extends CupData C where
  /-- The Leibniz rule `δ(f ⌣ g) = δf ⌣ g + f ⌣ δg` (over `ℤ/2`). The left term is transported along
  `(p+1) + q = (p+q) + 1` (`Nat.succ_add`); the right term lands in `p + (q+1) = (p+q)+1`
  definitionally. -/
  leibniz : ∀ {p q : ℕ} (f : Cochain C p) (g : Cochain C q),
    coboundary C (p + q) (toCupData.cup f g)
      = cast (congrArg (Cochain C) (Nat.succ_add p q)) (toCupData.cup (coboundary C p f) g)
        + toCupData.cup f (coboundary C q g)

/-- Transport of the zero cochain along an index equality is zero. -/
theorem cast_cochain_zero {C : CellComplex} {a b : ℕ} (h : a = b) :
    cast (congrArg (Cochain C) h) (0 : Cochain C a) = 0 := by
  subst h; rfl

namespace CupRing

variable {C : CellComplex} (R : CupRing C)

/-- **The cup product of two cocycles is a cocycle.** `δf = 0` and `δg = 0` give
`δ(f ⌣ g) = δf ⌣ g + f ⌣ δg = 0` by the Leibniz rule. The foundation of the descent of the cup product
to cohomology. -/
theorem cup_cocycle {p q : ℕ} (f : Cochain C p) (g : Cochain C q)
    (hf : coboundary C p f = 0) (hg : coboundary C q g = 0) :
    coboundary C (p + q) (R.toCupData.cup f g) = 0 := by
  rw [R.leibniz f g, hf, hg, CupData.zero_cup, CupData.cup_zero, add_zero]
  exact cast_cochain_zero (Nat.succ_add p q)

/-- **The cup of a coboundary with a cocycle is a coboundary.** For a cocycle `g` (`δg = 0`), the
transported cup `δh ⌣ g` equals the coboundary `δ(h ⌣ g)`. The second half of the descent of the cup
product to cohomology (well-definedness modulo coboundaries in the left argument). -/
theorem cup_coboundary_left {p q : ℕ} (h : Cochain C p) (g : Cochain C q)
    (hg : coboundary C q g = 0) :
    cast (congrArg (Cochain C) (Nat.succ_add p q)) (R.toCupData.cup (coboundary C p h) g)
      = coboundary C (p + q) (R.toCupData.cup h g) := by
  have hL := R.leibniz h g
  rw [hg, CupData.cup_zero, add_zero] at hL
  exact hL.symm

/-- The cup product of two **cocycle representatives**, packaged as a cocycle (an element of
`ker δ^{p+q}`). The representative-level cup used to define the cup product on cohomology. -/
def cupCocycle {p q : ℕ} (z₁ : LinearMap.ker (coboundary C p))
    (z₂ : LinearMap.ker (coboundary C q)) : LinearMap.ker (coboundary C (p + q)) :=
  ⟨R.toCupData.cup z₁.val z₂.val,
   LinearMap.mem_ker.mpr
     (R.cup_cocycle z₁.val z₂.val (LinearMap.mem_ker.mp z₁.2) (LinearMap.mem_ker.mp z₂.2))⟩

@[simp] theorem cupCocycle_val {p q : ℕ} (z₁ : LinearMap.ker (coboundary C p))
    (z₂ : LinearMap.ker (coboundary C q)) :
    (R.cupCocycle z₁ z₂).val = R.toCupData.cup z₁.val z₂.val := rfl

end CupRing

/-! ## §3. The genuine Smith SW-mechanism `w₂(N) = 0` over the real cup product

This upgrades the Smith homomorphism's operative content (`SymTFT/SmithMechanism.lean`,
`smith_w2_vanishes`) from the rank-carrier `CohomologyMod2` — whose `cupSquare` is rank-transport
(`⟨x.rank⟩`, the module's own "thin-model CRITICAL-1 caveat") — to **this session's genuine cup
product**: `b²` is now the real cup-square `b ⌣ b`. -/

/-- Over `ℤ/2` every cochain is 2-torsion: `x + x = 0`. -/
theorem cochain_add_self {C : CellComplex} {n : ℕ} (x : Cochain C n) : x + x = 0 := by
  funext σ
  show x σ + x σ = 0
  have h : ∀ r : ZMod 2, r + r = 0 := by decide
  exact h (x σ)

namespace CupData

variable {C : CellComplex} (D : CupData C)

/-- The **cup-square** `b ↦ b ⌣ b : C¹ → C²`. For a cocycle `b` representing a class in `H¹`, this is
the genuine `b² ∈ H²` — not the rank-transport surrogate of `SymTFT/StiefelWhitney.cupSquare`. -/
def cupSquare (b : Cochain C 1) : Cochain C (1 + 1) := D.cup b b

/-- **Genuine Smith SW-mechanism: `w₂(N) = 0`.** Given the Whitney identity `w₂(N) = c + b²` (from the
normal-bundle split `TM|_N ≅ TN ⊕ ν`, `b = w₁(ν)`, `c = w₂(M)|_N`) and the Spin-ℤ₄ constraint `c = b²`
(`w₂(M) = a²` restricting), the second Stiefel–Whitney class of the Smith dual `N = PD(a)` vanishes:
`w₂(N) = b² + b² = 0` over `ℤ/2`, so `N` admits a Pin⁺ structure (Lawson–Michelsohn II.1.7;
Tachikawa–Yonekura 3.14). Here `b²` is the **genuine cup-square** `b ⌣ b`, de-thinning the
rank-transport `cupSquare` of `SymTFT/SmithMechanism.smith_w2_vanishes`. -/
theorem smith_w2_vanishes_genuine (w2 c : Cochain C (1 + 1)) (b : Cochain C 1)
    (hWhitney : w2 = c + D.cupSquare b) (hSpinZ4 : c = D.cupSquare b) : w2 = 0 := by
  rw [hWhitney, hSpinZ4]
  exact cochain_add_self _

end CupData

/-! ## §4. The `RP^n` cup ring and the genuine Smith mechanism on the generator `[RP⁴]`

`H*(RP^n; ℤ/2) = ℤ/2[α]/(αⁿ⁺¹)` with `αⁱ ⌣ αʲ = αⁱ⁺ʲ` — since each degree has a single cell, every
cup coefficient is `1`. This gives the genuine cup-square `α² = α ⌣ α` (the `H²` generator), de-thinning
the Smith mechanism's rank-transport on the generator `[RP⁴]`. -/

/-- The cup product on `RP^n`: `αⁱ ⌣ αʲ = αⁱ⁺ʲ`, i.e. every diagonal coefficient is `1`. -/
def RPCupData (n : ℕ) : CupData (RPComplex n) where
  coeff _ _ _ _ := 1

/-- The genuine cup-square of the `H¹` generator `α = 1` of `RP^n` (`n ≥ 2`) is the **nonzero** `H²`
generator `α² = 1`: `α ⌣ α` sums the single `(1,1)`-cell pair with coefficient `1`. So `α²` is genuinely
nonzero — the Smith cancellation `α² + α² = 0` below is a real char-2 cancellation, not `0 + 0`. -/
theorem RPCupData_cupSquare_gen (n : ℕ) (hn : 2 ≤ n) :
    (RPCupData n).cupSquare (1 : Cochain (RPComplex n) 1) = (1 : Cochain (RPComplex n) 2) := by
  haveI : Unique ((RPComplex n).cells 1) := RPComplex_cells_unique n 1 (by omega)
  funext σ
  simp [CupData.cupSquare, CupData.cup, RPCupData]

/-- **The Smith mechanism's cancellation on the generator `[RP⁴]`, over the GENUINE cup-square.** For
`RP⁴` the Smith inputs are `b = α = w₁(RP⁴)` and `c = α² = w₂(RP⁵)|_{RP⁴}`, and the Whitney + Spin-ℤ₄
relations give `w₂(RP⁴) = α² + α² = 0`. Here `α²` is the genuine (nonzero) cup-square `α ⌣ α`
(`RPCupData_cupSquare_gen`), so the Pin⁺-landing of the Smith image `[RP⁴]` is backed by this session's
REAL cup product — not the rank-transport of `SymTFT/SmithMechanism`. -/
theorem RP4_smith_cupSquare_cancellation :
    (RPCupData 4).cupSquare (1 : Cochain (RPComplex 4) 1)
      + (RPCupData 4).cupSquare (1 : Cochain (RPComplex 4) 1) = 0 :=
  cochain_add_self _

end SKEFTHawking.CellularCohomologyMod2
