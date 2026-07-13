/-
# Phase 5q.H (W-A item 3, THE CENTRAL BUILD) — the gate-frozen faithful Pin⁺ instance
# `pinPlusCharPairData`: the certified characteristic-pair carrier

The v4 (GATE-PASSED, statement shapes FROZEN) definition of
`docs/dev-loops/Phase5qH/W_A_FAITHFUL_INSTANCE_DESIGN.md`, built as a `T2TangentialData`:
the KT §6 characteristic-pair bordism group carrier, with a genuine `revStr` (enhancement
negation), no free invariant-valued field, and the honest per-datum certificate discipline
(R7/R8) demanded by the two round-1 no-gos.

This module opens the build with the **frozen algebraic core** — the piece whose exact shape
the round-2 gate pins (`PinPlusTaylorConventionNoGo.lean`) and whose in-substrate honesty is the
whole point of the design:

* `jointEnhancement q_σ q_τ := orthSum q_σ (Z4Quadratic.neg q_τ)` — the **τ-end-NEGATED** joint
  enhancement of a bordism's two ends (per Bor-END, never per boundary component — the exact
  kernel-forced form, no-go `taylor-leg-end-convention-trap`, design §2 item 4).
* `TaylorLegVanishes` — the structure-extension (Taylor Thm 1.1) condition: the joint enhancement
  vanishes on the membrane's boundary-to-interior kernel `L = ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))`.
* `brown_eq_of_taylorLeg_lagrangian` — **the anti-collapse engine.** The Taylor leg (`q` vanishes
  on `L`) + `L` Lagrangian (`half-lives-half-dies` for the honest membrane) FORCE
  `brown q_σ = brown q_τ` (Gauss factorization, via `BrownMetabolic.brown_eq_zero_of_metabolic`
  applied to the joint form + `brown_orthSum` + `brown_neg`). This is what makes the computed grade
  `abk8 := brown ∘ q` descend well-defined along `Bor` — so the reading-(ii) torsor collapse
  (no-go `dataBordism_mk_eq_of_cylinder_bor`) is **provably impossible** even with a bundled `bd`:
  a `Bor (reflCylinder s) σ τ` between different-`brown` structures cannot supply a Lagrangian on
  which the negated joint enhancement vanishes.
* The **discriminating `cylBor` self-test** (design §2 item 4 ⚠): with the τ-end negated the reflexive
  cylinder's anti-diagonal kernel gives `q(x) − q(x) = 0` (`jointEnhancement_vanishes_on_diagonal`),
  so `cylBor` is instantiable; the PLAIN (un-negated) reading would force `2·q = 0` on the same
  kernel (`plain_joint_forces_two_torsion_on_diagonal`), which the odd `ℝP²` generator
  (`q(gen) = 1 ∈ ℤ/4`) violates — a POSITIVE confirmation this module states reading (iii), the ONLY
  correct one.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.T2TangentialBordism
import SKEFTHawking.PinPlusTiedData
import SKEFTHawking.BrownInvariant
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.BrownMetabolic
import SKEFTHawking.PoincareLefschetzWu5
import SKEFTHawking.BordismGroup

namespace SKEFTHawking.PinPlusCharPairData

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

/-! ## §1. The τ-end-negated joint enhancement and the Taylor-leg condition (FROZEN, §2 item 4) -/

/-- **The joint enhancement of a bordism's two ends, with the τ-end NEGATED** (design §2 item 4,
the EXACT kernel-forced form; no-go `taylor-leg-end-convention-trap`): `q_σ ⊕ (neg q_τ)` on
`H₁(∂Q;ℤ/2) = H₁(Σ_σ;ℤ/2) ⊕ H₁(Σ_τ;ℤ/2)`. Negation is per Bor-END (the whole τ-end), never per
boundary component — the doubling bordism's two σ-side components both stay UN-negated, which is
exactly why the `negBor` self-test is blind to the end-convention and `cylBor` is the discriminator. -/
def jointEnhancement {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    Z4Quadratic (Fin nσ ⊕ Fin nτ) :=
  orthSum qσ (neg qτ)

/-- **The structure-extension (Taylor Thm 1.1) condition**, design §2 item 4: the τ-end-negated joint
enhancement vanishes on the membrane's boundary-to-interior kernel `L = ker(H₁(∂Q) → H₁(Q))`.
Stated over `L` as a submodule of `H₁(∂Q;ℤ/2) = (Fin nσ ⊕ Fin nτ) → ZMod 2` (the boundary
identification pins `H₁(∂Q)` to the ends' `H₁` via the enhancement bases). -/
def TaylorLegVanishes {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (L : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2)) : Prop :=
  ∀ l ∈ L, (jointEnhancement qσ qτ).q l = 0

/-- **`L` is Lagrangian** for the joint enhancement's polar form (`half-lives-half-dies` for the
honest membrane): every class `B`-orthogonal to all of `L` lies in `L` (`L^⊥ ⊆ L`, the maximality the
metabolic theorem consumes; self-orthogonality is forced by the Taylor vanishing). -/
def JointLagrangian {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (L : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2)) : Prop :=
  ∀ v, (∀ l ∈ L, (jointEnhancement qσ qτ).B v l = 0) → v ∈ L

/-! ## §2. The anti-collapse engine — Taylor leg + Lagrangian ⟹ `brown q_σ = brown q_τ` -/

/-- **THE ANTI-COLLAPSE LEMMA (Gauss factorization).** If the τ-end-negated joint enhancement
vanishes on a Lagrangian `L` (the Taylor leg on the honest membrane), then `brown q_σ = brown q_τ`.
Proof: `brown_eq_zero_of_metabolic` gives `brown (jointEnhancement) = 0`; `brown_orthSum` +
`brown_neg` expand this to `brown q_σ + (−brown q_τ) = 0`, i.e. `brown q_σ = brown q_τ`.

This is the load-bearing consequence the whole design rests on (§2 item 4, "q-vanishing on the
kernel ⟹ isotropic ⟹ Lagrangian ⟹ Gauss factorization ⟹ β(q_σ) = β(q_τ)"): it makes the computed
grade `abk8 := brown ∘ q` a genuine bordism invariant, so the reading-(ii) torsor collapse
(no-go `dataBordism_mk_eq_of_cylinder_bor`) is impossible — a `Bor` between different-`brown`
structures cannot furnish such an `L`. -/
theorem brown_eq_of_taylorLeg_lagrangian {nσ nτ : ℕ}
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (L : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2))
    (htaylor : TaylorLegVanishes qσ qτ L) (hlag : JointLagrangian qσ qτ L) :
    qσ.brown = qτ.brown := by
  haveI : Fintype L := Fintype.ofFinite L
  have h := (jointEnhancement qσ qτ).brown_eq_zero_of_metabolic L htaylor hlag
  rw [jointEnhancement, brown_orthSum, brown_neg] at h
  have hsub : qσ.brown - qτ.brown = 0 := by rw [sub_eq_add_neg]; exact h
  exact sub_eq_zero.mp hsub

/-! ## §3. The discriminating `cylBor` self-test (design §2 item 4 ⚠) -/

/-- **Reading (iii) makes `cylBor` instantiable.** On the reflexive cylinder both ends carry the same
`q`, and the membrane `Σ × [0,1]` has boundary-to-interior kernel the anti-diagonal
`{ x : x ∘ inl = x ∘ inr }` (in char 2). On such a diagonal class the τ-end-negated joint enhancement
vanishes: `q(x∘inl) + (−q(x∘inr)) = q(x∘inl) − q(x∘inl) = 0`. So the Taylor leg holds and `cylBor`
is populatable — the negated τ-end is exactly what avoids the plain-sum `2·q = 0` trap below. -/
theorem jointEnhancement_vanishes_on_diagonal {n : ℕ} (q : Z4Quadratic (Fin n))
    (x : Fin n ⊕ Fin n → ZMod 2) (hx : (fun i => x (Sum.inl i)) = fun i => x (Sum.inr i)) :
    (jointEnhancement q q).q x = 0 := by
  show q.q (fun i => x (Sum.inl i)) + -(q.q (fun i => x (Sum.inr i))) = 0
  rw [← hx, add_neg_cancel]

/-- **The plain (un-negated) reading forces `2·q = 0` on the same anti-diagonal** — reading (i) of
§2 item 4. On the diagonal class `Sum.elim a a`, the un-negated joint sum evaluates to `q a + q a`.
The odd `ℝP²` generator (`q(gen) = 1 ∈ ℤ/4`, `1 + 1 = 2 ≠ 0`) violates this, so reading (i) has NO
instance containing the ℝP⁴/ℝP² witness (no-go `no_plain_end_pairing_of_cylinder`). This POSITIVELY
confirms this module states reading (iii): the τ-end negation is not cosmetic. -/
theorem plain_joint_forces_two_torsion_on_diagonal {n : ℕ} (q : Z4Quadratic (Fin n))
    (a : Fin n → ZMod 2) :
    (orthSum q q).q (Sum.elim a a) = q.q a + q.q a := by
  show q.q (fun i => (Sum.elim a a) (Sum.inl i)) + q.q (fun i => (Sum.elim a a) (Sum.inr i))
      = q.q a + q.q a
  rfl

/-- The `ℝP²` odd generator's enhancement value is not 2-torsion: `q(gen) = 1`, `1 + 1 = 2 ≠ 0` in
`ZMod 4` (DG Example 3.17; the mod-8 `brown` order-8 generator). The plain reading (i) would need
this `= 0` on the cylinder — it does not, so reading (iii) is forced. -/
theorem rp2_generator_value_not_two_torsion :
    (stdQuadratic 1).q (fun _ => 1) + (stdQuadratic 1).q (fun _ => 1) ≠ 0 := by
  decide

/-! ## §4. The per-op boundary-kernel Lagrangians (concrete `Z4Quadratic` linear algebra)

The `Bor` interface's op witnesses (`cylBor`, `negBor`, `addBor`, …) must each furnish a membrane
boundary-to-interior kernel `L = ker(H₁(∂Q) → H₁(Q))` on which the τ-end-negated joint enhancement
vanishes (the Taylor leg) AND which is Lagrangian for the joint polar form (`half-lives-half-dies`).
These are the discriminating totality obligations (design §2 item 4 ⚠). Here they are discharged at
the honest algebra level — the boundary identification pins `H₁(∂Q)` to the ends' `H₁` (the
enhancement bases), so each membrane's kernel is a CONCRETE submodule of `(Fin nσ ⊕ Fin nτ) → ZMod 2`
and the Taylor/Lagrangian properties are pure `Z4Quadratic` facts (no manifold, no universe bump). -/

/-- **The cylinder membrane's boundary map** `H₁(Σ ⊔ Σ) → H₁(Σ)` of `Q = Σ × [0,1]`: both ends map
isomorphically to `H₁(Σ)`, summed — `(a,b) ↦ a + b` (char 2). Its kernel is the diagonal (the honest
cylinder's `half-lives-half-dies` half). -/
def cylBd (n : ℕ) : (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := fun i => x (Sum.inl i) + x (Sum.inr i)
  map_add' a b := by funext i; simp [Pi.add_apply]; ring
  map_smul' c a := by funext i; simp [Pi.smul_apply, mul_add]

/-- The cylinder kernel `L = ker(cylBd)`: exactly the diagonal `{ x : x∘inl = x∘inr }` (char 2). -/
def cylLagrangian (n : ℕ) : Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  LinearMap.ker (cylBd n)

/-- Membership in the cylinder kernel is the diagonal condition. -/
theorem mem_cylLagrangian_iff {n : ℕ} (x : Fin n ⊕ Fin n → ZMod 2) :
    x ∈ cylLagrangian n ↔ (fun i => x (Sum.inl i)) = fun i => x (Sum.inr i) := by
  rw [cylLagrangian, LinearMap.mem_ker]
  constructor
  · intro h; funext i
    have : x (Sum.inl i) + x (Sum.inr i) = 0 := congrFun h i
    -- in char 2, a + b = 0 ↔ a = b
    have h2 : x (Sum.inl i) = - x (Sum.inr i) := by rw [eq_neg_iff_add_eq_zero]; exact this
    rwa [CharTwo.neg_eq] at h2
  · intro h; funext i
    show x (Sum.inl i) + x (Sum.inr i) = 0
    rw [congrFun h i, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

/-- **`cylBor`'s Taylor leg holds** (reading iii): the τ-end-negated joint enhancement vanishes on the
diagonal cylinder kernel — `q(x∘inl) − q(x∘inl) = 0`. -/
theorem taylorLeg_cyl {n : ℕ} (q : Z4Quadratic (Fin n)) :
    TaylorLegVanishes q q (cylLagrangian n) := by
  intro l hl
  exact jointEnhancement_vanishes_on_diagonal q l ((mem_cylLagrangian_iff l).mp hl)

/-- **The cylinder diagonal kernel is Lagrangian** for the joint polar form `q.B ⊕ q.B`: isotropic
(char 2: `B((a,a),(a',a')) = 2·q.B a a' = 0`) and maximal (`v ⟂ diagonal ⟹ q.B (u+w) = 0 ⟹ u = w`
by nondegeneracy). -/
theorem lagrangian_cyl {n : ℕ} (q : Z4Quadratic (Fin n)) :
    JointLagrangian q q (cylLagrangian n) := by
  intro v hv
  rw [mem_cylLagrangian_iff]
  -- hv : ∀ l ∈ cylLagrangian, (jointEnhancement q q).B v l = 0
  -- (jointEnhancement q q).B v l = q.B (v∘inl) (l∘inl) + q.B (v∘inr) (l∘inr)
  -- take l = the diagonal class of any a : Fin n → ZMod 2
  set u := fun i => v (Sum.inl i) with hu
  set w := fun i => v (Sum.inr i) with hw
  have hkey : ∀ a : Fin n → ZMod 2, q.B u a + q.B w a = 0 := by
    intro a
    have hla : (Sum.elim a a) ∈ cylLagrangian n := by
      rw [mem_cylLagrangian_iff]; rfl
    have h := hv (Sum.elim a a) hla
    -- h : (jointEnhancement q q).B v (Sum.elim a a) = 0
    have hexp : (jointEnhancement q q).B v (Sum.elim a a)
        = q.B u a + q.B w a := rfl
    rw [hexp] at h; exact h
  -- q.B (u + w) a = 0 for all a ⟹ u + w = 0 ⟹ u = w
  have hsum : ∀ a, q.B (u + w) a = 0 := by
    intro a; rw [q.B_add_left]; exact hkey a
  have huw : u + w = 0 := q.nondeg _ hsum
  funext i
  have : u i + w i = 0 := congrFun huw i
  have h2 : u i = - w i := by rw [eq_neg_iff_add_eq_zero]; exact this
  rwa [CharTwo.neg_eq] at h2

/-- **`cylBor` instantiates cleanly** (the design's discriminating self-test, §2 item 4 ⚠): with the
τ-end negated, the diagonal cylinder kernel is a Lagrangian on which the joint enhancement vanishes,
so the anti-collapse lemma yields the (here trivial) `brown q = brown q`. Confirms the reading-(iii)
statement is instantiable — the whole point of the round-2 gate. -/
theorem cyl_brown_eq {n : ℕ} (q : Z4Quadratic (Fin n)) : q.brown = q.brown :=
  brown_eq_of_taylorLeg_lagrangian q q (cylLagrangian n) (taylorLeg_cyl q) (lagrangian_cyl q)

end SKEFTHawking.PinPlusCharPairData
