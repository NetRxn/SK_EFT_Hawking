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

/-! ## §4.5. The general metabolic-Lagrangian transport engine (reusable for every op witness)

Each op's boundary-to-interior kernel `L` is the diagonal/graph Lagrangian transported through the
`reindex`/`orthSum`/`neg` operations that `sumStr`/`revStr` apply to the enhancements. These purely
algebraic lemmas do the `half-lives-half-dies` maximality lifting ONCE, generically, so the twelve op
witnesses reduce to naming the right transport. `IsMetabolic (jointEnhancement qσ qτ) L` unfolds
definitionally to `TaylorLegVanishes qσ qτ L ∧ JointLagrangian qσ qτ L`. -/

/-- **`L` is metabolic for a `ZMod 4`-quadratic form `Q`**: `Q` vanishes on `L` (isotropic Taylor leg)
and `L` is maximal isotropic for its polar form (`half-lives-half-dies`). The two anti-collapse-engine
conditions, stated for a general form so the `reindex`/`orthSum`/`neg` transports apply. -/
def IsMetabolic {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (L : Submodule (ZMod 2) (ι → ZMod 2)) : Prop :=
  (∀ l ∈ L, Q.q l = 0) ∧ (∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L)

/-- The jointEnhancement metabolic condition IS the pair the `CharPairBor` fields need. -/
theorem taylorLeg_of_isMetabolic {nσ nτ : ℕ} {qσ : Z4Quadratic (Fin nσ)} {qτ : Z4Quadratic (Fin nτ)}
    {L : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2)}
    (h : IsMetabolic (jointEnhancement qσ qτ) L) : TaylorLegVanishes qσ qτ L := h.1

theorem jointLagrangian_of_isMetabolic {nσ nτ : ℕ} {qσ : Z4Quadratic (Fin nσ)}
    {qτ : Z4Quadratic (Fin nτ)} {L : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2)}
    (h : IsMetabolic (jointEnhancement qσ qτ) L) : JointLagrangian qσ qτ L := h.2

/-- **Extensionality for `Z4Quadratic`** — a form is determined by `q` and `B` (the axioms are
proof-irrelevant). Lets the op witnesses rewrite one enhancement into a `reindex`/`neg`/`orthSum` of
another and pull the metabolic Lagrangian across via the §4.5 engine. -/
theorem z4_ext {ι : Type*} [Fintype ι] [DecidableEq ι] {Q₁ Q₂ : Z4Quadratic ι}
    (hq : Q₁.q = Q₂.q) (hB : Q₁.B = Q₂.B) : Q₁ = Q₂ := by
  cases Q₁; cases Q₂; cases hq; cases hB; rfl

/-- **Metabolic transports along `reindex`.** `x ↦ x ∘ e` is a linear bijection, so the preimage of a
metabolic `L` is metabolic for `Q.reindex e`. -/
theorem IsMetabolic.reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Q : Z4Quadratic ι} {L : Submodule (ZMod 2) (ι → ZMod 2)} (h : IsMetabolic Q L) (e : ι ≃ κ) :
    IsMetabolic (Q.reindex e) (L.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) e)) := by
  obtain ⟨htaylor, hlag⟩ := h
  refine ⟨fun l hl => ?_, fun v hv => ?_⟩
  · rw [Submodule.mem_comap] at hl
    exact htaylor _ hl
  · rw [Submodule.mem_comap]
    refine hlag _ (fun l' hl' => ?_)
    show Q.B (fun i => v (e i)) l' = 0
    have hx : (LinearMap.funLeft (ZMod 2) (ZMod 2) e) (fun k => l' (e.symm k)) = l' := by
      funext i; simp [LinearMap.funLeft_apply, Equiv.symm_apply_apply]
    have hb := hv (fun k => l' (e.symm k)) (by rw [Submodule.mem_comap, hx]; exact hl')
    simpa [Z4Quadratic.reindex, Equiv.symm_apply_apply] using hb

/-- **Metabolic transports along `neg`.** `neg Q` has the same polar form `B` and negates `q`, so the
same `L` stays metabolic (`-(0) = 0`). -/
theorem IsMetabolic.neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Z4Quadratic ι} {L : Submodule (ZMod 2) (ι → ZMod 2)} (h : IsMetabolic Q L) :
    IsMetabolic (Z4Quadratic.neg Q) L := by
  obtain ⟨htaylor, hlag⟩ := h
  refine ⟨fun l hl => ?_, hlag⟩
  show -(Q.q l) = 0
  rw [htaylor l hl, neg_zero]

/-- The block submodule `L₁ ⊞ L₂` inside `ι₁ ⊕ ι₂ → ZMod 2`: the `inl`-restriction lies in `L₁` and the
`inr`-restriction lies in `L₂`. -/
def blockSub {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (L₁ : Submodule (ZMod 2) (ι₁ → ZMod 2)) (L₂ : Submodule (ZMod 2) (ι₂ → ZMod 2)) :
    Submodule (ZMod 2) (ι₁ ⊕ ι₂ → ZMod 2) :=
  L₁.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inl : ι₁ → ι₁ ⊕ ι₂)) ⊓
    L₂.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : ι₂ → ι₁ ⊕ ι₂))

theorem mem_blockSub {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {L₁ : Submodule (ZMod 2) (ι₁ → ZMod 2)} {L₂ : Submodule (ZMod 2) (ι₂ → ZMod 2)}
    (x : ι₁ ⊕ ι₂ → ZMod 2) :
    x ∈ blockSub L₁ L₂ ↔ (fun i => x (Sum.inl i)) ∈ L₁ ∧ (fun i => x (Sum.inr i)) ∈ L₂ := by
  rw [blockSub, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap]
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h1, h2⟩)

/-- **Metabolic transports along `orthSum`** (block-diagonal): a metabolic `L₁` for `Q₁` and `L₂` for
`Q₂` give the block Lagrangian `L₁ ⊞ L₂` for `orthSum Q₁ Q₂`. -/
theorem IsMetabolic.orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {Q₁ : Z4Quadratic ι₁} {Q₂ : Z4Quadratic ι₂}
    {L₁ : Submodule (ZMod 2) (ι₁ → ZMod 2)} {L₂ : Submodule (ZMod 2) (ι₂ → ZMod 2)}
    (h₁ : IsMetabolic Q₁ L₁) (h₂ : IsMetabolic Q₂ L₂) :
    IsMetabolic (Z4Quadratic.orthSum Q₁ Q₂) (blockSub L₁ L₂) := by
  obtain ⟨ht1, hl1⟩ := h₁
  obtain ⟨ht2, hl2⟩ := h₂
  refine ⟨fun l hl => ?_, fun v hv => ?_⟩
  · rw [mem_blockSub] at hl
    show Q₁.q _ + Q₂.q _ = 0
    rw [ht1 _ hl.1, ht2 _ hl.2, add_zero]
  · rw [mem_blockSub]
    refine ⟨hl1 _ (fun a ha => ?_), hl2 _ (fun a ha => ?_)⟩
    · have hmem : Sum.elim a (0 : ι₂ → ZMod 2) ∈ blockSub L₁ L₂ := by
        rw [mem_blockSub]; exact ⟨ha, L₂.zero_mem⟩
      have hb := hv _ hmem
      have hexp : (Z4Quadratic.orthSum Q₁ Q₂).B v (Sum.elim a (0 : ι₂ → ZMod 2))
          = Q₁.B (fun i => v (Sum.inl i)) a + Q₂.B (fun i => v (Sum.inr i)) 0 := rfl
      rw [hexp, show Q₂.B (fun i => v (Sum.inr i)) 0 = 0 from by
        rw [Q₂.B_symm]; exact Q₂.B_zero_left _, add_zero] at hb
      exact hb
    · have hmem : Sum.elim (0 : ι₁ → ZMod 2) a ∈ blockSub L₁ L₂ := by
        rw [mem_blockSub]; exact ⟨L₁.zero_mem, ha⟩
      have hb := hv _ hmem
      have hexp : (Z4Quadratic.orthSum Q₁ Q₂).B v (Sum.elim (0 : ι₁ → ZMod 2) a)
          = Q₁.B (fun i => v (Sum.inl i)) 0 + Q₂.B (fun i => v (Sum.inr i)) a := rfl
      rw [hexp, show Q₁.B (fun i => v (Sum.inl i)) 0 = 0 from by
        rw [Q₁.B_symm]; exact Q₁.B_zero_left _, zero_add] at hb
      exact hb

/-- **The diagonal is metabolic for a `±`-doubling `orthSum Q₁ Q₂`** — when `Q₁.q a + Q₂.q a = 0` and
`Q₁.B = Q₂.B` (`Q₂ = ± Q₁` on the same polar form). The `half-lives-half-dies` core generalizing
`taylorLeg_cyl`/`lagrangian_cyl`: cylinder (`Q₂ = neg Q₁`) and doubling (`Q₁ = neg Q₂`) both fit. -/
theorem diag_metabolic {n : ℕ} (Q₁ Q₂ : Z4Quadratic (Fin n))
    (hq : ∀ a, Q₁.q a + Q₂.q a = 0) (hB : Q₁.B = Q₂.B) :
    IsMetabolic (Z4Quadratic.orthSum Q₁ Q₂) (cylLagrangian n) := by
  refine ⟨fun l hl => ?_, fun v hv => ?_⟩
  · have hdiag := (mem_cylLagrangian_iff l).mp hl
    show Q₁.q (fun i => l (Sum.inl i)) + Q₂.q (fun i => l (Sum.inr i)) = 0
    rw [← hdiag]; exact hq _
  · rw [mem_cylLagrangian_iff]
    set u := fun i => v (Sum.inl i) with hu
    set w := fun i => v (Sum.inr i) with hw
    have hkey : ∀ a : Fin n → ZMod 2, Q₁.B u a + Q₁.B w a = 0 := by
      intro a
      have hla : (Sum.elim a a) ∈ cylLagrangian n := by rw [mem_cylLagrangian_iff]; rfl
      have hb := hv (Sum.elim a a) hla
      have hexp : (Z4Quadratic.orthSum Q₁ Q₂).B v (Sum.elim a a) = Q₁.B u a + Q₂.B w a := rfl
      rw [hexp, ← hB] at hb
      exact hb
    have hsum : ∀ a, Q₁.B (u + w) a = 0 := fun a => by rw [Q₁.B_add_left]; exact hkey a
    have huw : u + w = 0 := Q₁.nondeg _ hsum
    funext i
    have h2 : u i = - w i := by rw [eq_neg_iff_add_eq_zero]; exact congrFun huw i
    rwa [CharTwo.neg_eq] at h2

/-- The **graph submodule** of a `ZMod 2`-linear isometry `φ` between the two ends' `H₁`: classes whose
`τ`-part is `φ` of their `σ`-part. This is the boundary-to-interior kernel of a reparametrized-cylinder
membrane (`cylBor`/`commBor`/`assocBor`/`unitBor`). -/
def graphSub {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (φ : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (ι₂ → ZMod 2)) :
    Submodule (ZMod 2) (ι₁ ⊕ ι₂ → ZMod 2) :=
  LinearMap.ker (φ.toLinearMap ∘ₗ
      LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inl : ι₁ → ι₁ ⊕ ι₂)
    - LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : ι₂ → ι₁ ⊕ ι₂))

theorem mem_graphSub {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (φ : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (ι₂ → ZMod 2)) (x : ι₁ ⊕ ι₂ → ZMod 2) :
    x ∈ graphSub φ ↔ (fun i => x (Sum.inr i)) = φ (fun i => x (Sum.inl i)) := by
  rw [graphSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero]
  exact eq_comm

/-- **The graph of a `q`-isometry is metabolic** for the τ-end-negated joint form `orthSum qσ (neg qτ)`:
the Taylor leg holds (`qσ − qτ∘φ = 0`) and the graph is its own polar (nondegeneracy of `qσ` + the
`B`-isometry). Stated over arbitrary indices (the `sumStr` blocks are `Sum` types); on `Fin` indices
`orthSum qσ (neg qτ)` is `jointEnhancement qσ qτ`. Reusable engine for the reparametrized-cylinder ops. -/
theorem graphSub_metabolic {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {qσ : Z4Quadratic ι₁} {qτ : Z4Quadratic ι₂}
    (φ : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (ι₂ → ZMod 2))
    (hq : ∀ a, qτ.q (φ a) = qσ.q a) (hB : ∀ a a', qτ.B (φ a) (φ a') = qσ.B a a') :
    IsMetabolic (Z4Quadratic.orthSum qσ (Z4Quadratic.neg qτ)) (graphSub φ) := by
  refine ⟨fun l hl => ?_, fun v hv => ?_⟩
  · rw [mem_graphSub] at hl
    show qσ.q (fun i => l (Sum.inl i)) + -(qτ.q (fun i => l (Sum.inr i))) = 0
    rw [hl, hq, add_neg_cancel]
  · rw [mem_graphSub]
    set u := fun i => v (Sum.inl i) with hu
    set w := fun i => v (Sum.inr i) with hw
    have hkey : ∀ a, qσ.B u a + qσ.B (φ.symm w) a = 0 := by
      intro a
      have hla : (Sum.elim a (φ a)) ∈ graphSub φ := by rw [mem_graphSub]; rfl
      have hb := hv (Sum.elim a (φ a)) hla
      have hexp : (Z4Quadratic.orthSum qσ (Z4Quadratic.neg qτ)).B v (Sum.elim a (φ a))
          = qσ.B u a + qτ.B w (φ a) := rfl
      rw [hexp, show qτ.B w (φ a) = qσ.B (φ.symm w) a from by
        rw [← hB]; congr 1; exact (φ.apply_symm_apply w).symm] at hb
      exact hb
    have hsum : ∀ a, qσ.B (u + φ.symm w) a = 0 := fun a => by rw [qσ.B_add_left]; exact hkey a
    have huw : u + φ.symm w = 0 := qσ.nondeg _ hsum
    have hu_eq : u = φ.symm w := by
      funext i
      have hi : u i + (φ.symm w) i = 0 := congrFun huw i
      have h2 : u i = -((φ.symm w) i) := by rw [eq_neg_iff_add_eq_zero]; exact hi
      rwa [CharTwo.neg_eq] at h2
    rw [hu_eq, φ.apply_symm_apply]

/-! ### Reindex algebra — the `sumStr` enhancement identities the graph op witnesses consume.
`sumStr` composes by `orthSum` then `reindex`es to `Fin (m+n)`; these lemmas let `commBor`/`assocBor`/
`unitBor` rewrite one end's enhancement as a `reindex` of the other's, keeping every `finSumFinEquiv`
ABSTRACT (only `sumCongr`/`sumComm`/`sumAssoc`/`sumEmpty` are reduced). -/

/-- Reindexing along the identity is a no-op. -/
theorem reindex_refl {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι) :
    Q.reindex (Equiv.refl ι) = Q := by
  apply z4_ext <;> rfl

/-- Reindexing composes: `(Q.reindex e₁).reindex e₂ = Q.reindex (e₁.trans e₂)`. -/
theorem reindex_trans {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] [DecidableEq ρ] (Q : Z4Quadratic ι) (e₁ : ι ≃ κ) (e₂ : κ ≃ ρ) :
    (Q.reindex e₁).reindex e₂ = Q.reindex (e₁.trans e₂) := by
  apply z4_ext <;> rfl

/-- Negation commutes with reindexing (both keep `B`, both negate `q`). -/
theorem neg_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    Z4Quadratic.neg (Q.reindex e) = (Z4Quadratic.neg Q).reindex e := by
  apply z4_ext <;> rfl

/-- Reindexing distributes over `orthSum` via `Equiv.sumCongr`. -/
theorem orthSum_reindex {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) (e₁ : ι₁ ≃ κ₁) (e₂ : ι₂ ≃ κ₂) :
    Z4Quadratic.orthSum (Q₁.reindex e₁) (Q₂.reindex e₂)
      = (Z4Quadratic.orthSum Q₁ Q₂).reindex (Equiv.sumCongr e₁ e₂) := by
  apply z4_ext
  · funext x
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr]
  · funext x y
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr]

/-- `orthSum` commutes up to the `Sum`-swap reindex. -/
theorem orthSum_comm_eq {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    Z4Quadratic.orthSum Q₂ Q₁ = (Z4Quadratic.orthSum Q₁ Q₂).reindex (Equiv.sumComm ι₁ ι₂) := by
  apply z4_ext
  · funext x
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumComm_apply, Sum.swap_inl,
      Sum.swap_inr, add_comm]
  · funext x y
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumComm_apply, Sum.swap_inl,
      Sum.swap_inr, add_comm]

/-- `orthSum` associates up to the `Sum`-assoc reindex. -/
theorem orthSum_assoc_eq {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) (Q₃ : Z4Quadratic ι₃) :
    Z4Quadratic.orthSum Q₁ (Z4Quadratic.orthSum Q₂ Q₃)
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum Q₁ Q₂) Q₃).reindex
          (Equiv.sumAssoc ι₁ ι₂ ι₃) := by
  apply z4_ext
  · funext x
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumAssoc_apply_inl_inl,
      Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr, add_assoc]
  · funext x y
    simp only [Z4Quadratic.orthSum, Z4Quadratic.reindex, Equiv.sumAssoc_apply_inl_inl,
      Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr, add_assoc]

/-- `orthSum` with a rank-0 right summand is the left summand, reindexed away the empty block. -/
theorem orthSum_stdZero_eq {n : ℕ} (Q : Z4Quadratic (Fin n)) :
    Z4Quadratic.orthSum Q (stdQuadratic 0)
      = Q.reindex (Equiv.sumEmpty (Fin n) (Fin 0)).symm := by
  apply z4_ext
  · funext x
    show Q.q (fun i => x (Sum.inl i)) + (stdQuadratic 0).q (fun i => x (Sum.inr i))
        = Q.q (fun i => x ((Equiv.sumEmpty (Fin n) (Fin 0)).symm i))
    rw [show (stdQuadratic 0).q (fun i => x (Sum.inr i)) = 0 from
      (stdQuadratic 0).q_zero ▸ congrArg _ (Subsingleton.elim _ _), add_zero]
    rfl
  · funext x y
    show Q.B (fun i => x (Sum.inl i)) (fun i => y (Sum.inl i))
          + (stdQuadratic 0).B (fun i => x (Sum.inr i)) (fun i => y (Sum.inr i))
        = Q.B (fun i => x ((Equiv.sumEmpty (Fin n) (Fin 0)).symm i))
            (fun i => y ((Equiv.sumEmpty (Fin n) (Fin 0)).symm i))
    rw [show (stdQuadratic 0).B (fun i => x (Sum.inr i)) (fun i => y (Sum.inr i)) = 0 from by
      rw [Subsingleton.elim (fun i => x (Sum.inr i)) 0]; exact (stdQuadratic 0).B_zero_left _,
      add_zero]
    rfl

/-- The τ-end-negated joint enhancement distributes over `reindex` via `Equiv.sumCongr`. -/
theorem jointEnhancement_reindex {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) (e₁ : ι₁ ≃ κ₁) (e₂ : ι₂ ≃ κ₂) :
    Z4Quadratic.orthSum (Q₁.reindex e₁) (Z4Quadratic.neg (Q₂.reindex e₂))
      = (Z4Quadratic.orthSum Q₁ (Z4Quadratic.neg Q₂)).reindex (Equiv.sumCongr e₁ e₂) := by
  rw [neg_reindex, orthSum_reindex]

/-- **The graph of a reindex-isometry is metabolic** for `orthSum Q (neg (Q.reindex g))`: the two ends
are the SAME form indexed differently, so the graph of the reparametrization `funCongrLeft g.symm` is a
metabolic Lagrangian (the reparametrized-cylinder membrane kernel of `commBor`/`assocBor`/`unitBor`). -/
theorem reindexGraph_metabolic {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : Z4Quadratic ι) (g : ι ≃ κ) :
    IsMetabolic (Z4Quadratic.orthSum Q (Z4Quadratic.neg (Q.reindex g)))
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm)) := by
  have key : ∀ b : ι → ZMod 2,
      (fun i => (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm b) (g i)) = b := by
    intro b; funext i
    simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply]
  apply graphSub_metabolic
  · intro a
    show Q.q (fun i => (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm a) (g i)) = Q.q a
    rw [key a]
  · intro a a'
    show Q.B (fun i => (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm a) (g i))
          (fun i => (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g.symm a') (g i)) = Q.B a a'
    rw [key a, key a']

/-- **Two reindexes of a common form are joint-metabolic** — `orthSum (A.reindex e₁) (neg (A.reindex e₂))`
has the graph of `funCongrLeft (e₁.symm.trans e₂).symm` as a metabolic Lagrangian. This is the uniform
engine for `commBor`/`assocBor`/`unitBor`: each end's `sumStr` enhancement is a reindex of one flattened
`orthSum` form, and the membrane is the reparametrizing cylinder between them. -/
theorem commonReindex_metabolic {ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ₁]
    [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (A : Z4Quadratic ι) (e₁ : ι ≃ κ₁) (e₂ : ι ≃ κ₂) :
    IsMetabolic (Z4Quadratic.orthSum (A.reindex e₁) (Z4Quadratic.neg (A.reindex e₂)))
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (e₁.symm.trans e₂).symm)) := by
  have h : A.reindex e₂ = (A.reindex e₁).reindex (e₁.symm.trans e₂) := by
    rw [reindex_trans]; congr 1; ext x
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [h]
  exact reindexGraph_metabolic (A.reindex e₁) (e₁.symm.trans e₂)

/-! ## §5. The frozen structure shapes `CharPairStr` (Mfd) and `CharPairBor` (Bor)

⚠ **UNIVERSE FRICTION (reported, not silently worked around).** The frozen v4 §2 `Mfd` table lists
BOTH `cert : PinPlusCertK I s` AND `surf : SingularManifold PUnit k (𝓡 2)`. `PinPlusCertK` (and the
`swTotalNe`/`swNumberW14`/`poincareDual4*` 5q.G substrate it consumes) is **monomorphic at carrier
universe 0** (`SingularSWNumber`/`SingularPD4Instances` pin `M : Type`), so any `Mfd s` carrying
`cert` must be `Type 0`; but a bundled `surf : SingularManifold …` is `Type 1` (it bundles a `Type 0`
carrier), and the `T2TangentialData` interface binds `Mfd s : Type u ⟺ s : SingularManifold.{u}`.
Hence `cert` and a bundled-manifold `surf` **cannot coexist in one `Type 0` `Mfd s`** against the
current substrate. This is a substrate universe gap, NOT a mathematical weakening. Per the design's
own authorization (§2 "if the canonical `[Σ]` machinery isn't merged … bundle abstractly"), the
surface's MANIFOLD content — `surf`, `surfT2`, `emb`, `embSmooth`, `embInj`, and the `hchar`/`hpolar`
ties + the `H₁(Σ) ≃ₗ Fin n` basis equiv — is **deferred to wt2's 2-dim PD tower**; its ALGEBRAIC
shadow `(n, q)` (all the Taylor leg / anti-collapse consume) is carried concretely here.
RESOLUTION for the lead: universe-poly-fy the 5q.G SW/PD4 substrate (`M : Type` → `M : Type*`) to
carry a concrete `surf`, OR keep the deferral. The algebraic honesty (grade well-definedness) does
not depend on this choice — it rides on `brown_eq_of_taylorLeg_lagrangian`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5

/-- **A certified characteristic-pair structure on `s`** (design v4 §2 `Mfd` table, `Type 0` form).
Carries the concrete algebraic + admissibility content; the surface MANIFOLD (`surf`/`emb`/`hchar`/
`hpolar`/basis-equiv) is deferred to wt2 (see the §5 universe-friction note). -/
structure CharPairStr (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))) [I.Boundaryless]
    (s : SingularManifold PUnit k I) : Type where
  /-- leg 1: the carrier is Hausdorff (feeds `t2Str`). -/
  t2 : T2Space s.M
  /-- the `w₂ = 0` admissibility certificate (EXISTS, 5q.G; `k`-generic). -/
  cert : SKEFTHawking.PinPlusTiedData.PinPlusCertK I s
  /-- ▲A-5: the enhancement rank `n = dim H₁(Σ;ℤ/2)` (the surface's `H₁`; wt2 supplies the basis
  equiv `H₁(Σ) ≃ₗ (Fin n → ZMod 2)`). -/
  n : ℕ
  /-- the `ZMod 4`-quadratic enhancement `q : Z4Quadratic (Fin n)` — the algebraic shadow of the
  characteristic surface. `hpolar` (`q.B` = Σ's mod-2 intersection form) is wt2's discharge. -/
  q : Z4Quadratic (Fin n)

/-- **A certified characteristic-pair bordism datum** (design v4 §2 `Bor` items 0–4). Carries the
frozen load-bearing content: item 0 (`hWT2`), item 1's W-admissibility SHAPE (the two Lefschetz–Wu
data + `w₂(W) = 0`), the membrane's boundary-to-interior kernel `L` (item 2's algebraic content),
item 4's EXACT τ-end-negated Taylor leg, and the `half-lives-half-dies` Lagrangian property `hlag`
— from which `brown σ.q = brown τ.q` is FORCED (`brown_eq_of_taylorLeg_lagrangian`), so the computed
grade descends and the reading-(ii) collapse is impossible. Item 2's geometric membrane `Q` and item
3's relative characteristic condition need wt3's relative-Lefschetz/rel-PD tower and are deferred
(documented obligations), exactly as the design authorizes ("abstract-bundled if the rel-PD machinery
is not yet merged"). -/
structure CharPairBor {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) (σ : CharPairStr I s) (τ : CharPairStr I t) : Type where
  /-- item 0 (▲A-2): the bordism carrier is Hausdorff (the T2-refined relation). -/
  hWT2 : T2Space b.W
  /-- item 1 (▲A-3): the `(1,4)` Lefschetz–Wu datum of the compact 5-manifold-with-boundary `(W,∂W)`
  (supplies `v₁ = w₁(W)`). -/
  P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5
  /-- item 1: the `(2,3)` Lefschetz–Wu datum (supplies `v₂`). -/
  P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5
  /-- item 1: **W-admissibility** `w₂(W) = 0` (`⟺ Pin⁺ exists on W`), in the Wu-formula form
  `v₂ = v₁²`, stated against the canonical Lefschetz-dual classes. -/
  hwu : wuW2 P14 P23 = 0
  /-- item 2 (algebraic content of the certified membrane `Q`): its boundary-to-interior kernel
  `L = ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))`, a submodule of `H₁(∂Q) = (Fin σ.n ⊕ Fin τ.n) → ZMod 2` (the
  boundary identification pins `∂Q = Σ_σ ⊔ Σ_τ` to the ends' `H₁` via the enhancement bases). -/
  L : Submodule (ZMod 2) (Fin σ.n ⊕ Fin τ.n → ZMod 2)
  /-- item 4 (▲A-1, the EXACT kernel-forced form): the τ-end-NEGATED joint enhancement vanishes on
  `L`. Per Bor-END, never per boundary component (no-go `taylor-leg-end-convention-trap`). -/
  htaylor : TaylorLegVanishes σ.q τ.q L
  /-- `L` is Lagrangian for the joint polar form (`half-lives-half-dies` for the honest membrane) —
  the property that, with `htaylor`, FORCES `brown σ.q = brown τ.q` (the anti-collapse). -/
  hlag : JointLagrangian σ.q τ.q L

/-- **The frozen `Bor` FORCES grade equality of the ends** — the honesty guarantee. From any
`CharPairBor b σ τ`, the exact Taylor leg + Lagrangian give `brown σ.q = brown τ.q` via the
anti-collapse engine, so the computed grade `abk8 := brown ∘ q` is a genuine bordism invariant and no
reading-(ii) torsor collapse (`dataBordism_mk_eq_of_cylinder_bor`) is possible. -/
theorem CharPairBor.brown_eq {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBor b σ τ) : σ.q.brown = τ.q.brown :=
  brown_eq_of_taylorLeg_lagrangian σ.q τ.q β.L β.htaylor β.hlag

/-! ## §6. The Mfd-level op witnesses (`emptyStr`, `sumStr`, `revStr` — no W-tower needed) -/

open SKEFTHawking.PinPlusTiedData in
/-- `emptyStr`: the char-pair structure on the empty manifold (rank-0 enhancement). -/
noncomputable def charPairEmptyStr : CharPairStr I (emptySM : SingularManifold PUnit k I) where
  t2 := ⟨fun x => x.elim⟩
  cert := pinPlusCertK_empty
  n := 0
  q := stdQuadratic 0

open SKEFTHawking.PinPlusTiedData in
/-- `sumStr`: disjoint union of char-pair structures — ranks add, enhancements `orthSum`+reindex (the
GM pattern), cert via `PinPlusCertK.sum`, T2 via `t2_sum`. -/
noncomputable def charPairSumStr {s t : SingularManifold PUnit k I}
    (σ : CharPairStr I s) (τ : CharPairStr I t) : CharPairStr I (s.sum t) where
  t2 := t2_sum σ.t2 τ.t2
  cert := PinPlusCertK.sum σ.cert τ.cert
  n := σ.n + τ.n
  q := (orthSum σ.q τ.q).reindex finSumFinEquiv

/-- `revStr`: structure reversal = enhancement negation ALONE (design A4 `revStr`; `β ↦ −β`), same
carrier / cert / rank. -/
noncomputable def charPairRevStr {s : SingularManifold PUnit k I} (σ : CharPairStr I s) :
    CharPairStr I s where
  t2 := σ.t2
  cert := σ.cert
  n := σ.n
  q := neg σ.q

@[simp] theorem charPairRevStr_q {s : SingularManifold PUnit k I} (σ : CharPairStr I s) :
    (charPairRevStr σ).q = neg σ.q := rfl

@[simp] theorem charPairSumStr_q {s t : SingularManifold PUnit k I}
    (σ : CharPairStr I s) (τ : CharPairStr I t) :
    (charPairSumStr σ τ).q = (orthSum σ.q τ.q).reindex finSumFinEquiv := rfl

/-! ## §7. The W-admissibility provider (the un-merged wt3 relative-Lefschetz/Wu tower, bundled)

Item 1's W-admissibility datum (`LefschetzWuDatum` for each op's bordism `W` + `w₂(W) = 0`) needs
wt3's **relative Poincaré–Lefschetz/Wu tower on compact 5-manifolds-with-boundary** — the
route-independent critical-path tower the design's New-build list item 1 names, NOT yet merged. Per
the 5q.G discharge-later pattern it is consumed as an explicit PARAMETER: a single universally-
quantified admissibility function. This is a HYPOTHESIS (no axiom); wt3's tower discharges it by
producing `WAdm b` for every bordism `b`. The op witnesses draw item 1 from it and construct
everything else (T2 of `W`, the Lagrangian, the exact Taylor leg) concretely. -/

/-- The W-admissibility datum of a single bordism: the two Lefschetz–Wu data + `w₂(W) = 0`. -/
structure WAdm {s t : SingularManifold PUnit k I} (b : Bordism (I.prod (𝓡∂ 1)) s t) : Type where
  /-- the `(1,4)` Lefschetz–Wu datum. -/
  P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5
  /-- the `(2,3)` Lefschetz–Wu datum. -/
  P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5
  /-- W-admissibility: `w₂(W) = 0` (Wu form `v₂ = v₁²`). -/
  hwu : wuW2 P14 P23 = 0

/-- **The W-admissibility provider** (wt3's relative-Lefschetz/Wu tower, bundled as a hypothesis):
supplies `WAdm b` for every bordism `b`. Discharge obligation: wt3's rel-PD/Wu tower on compact
5-manifolds-with-boundary. (Manifold universe pinned to `0`, the datum's universe.) -/
structure CharPairWProvider (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] (k : WithTop ℕ∞) : Type (u_1 + 1) where
  /-- admissibility for every bordism between closed 4-manifolds. -/
  wadm : ∀ {s t : SingularManifold.{0} PUnit.{1} k I} (b : Bordism.{0} (I.prod (𝓡∂ 1)) s t), WAdm b

/-- Assemble a `CharPairBor` from the concretely-buildable data (T2 of `W`, the membrane kernel `L`,
the exact Taylor leg, the Lagrangian) + item 1 drawn from the provider. -/
def mkCharPairBor (prov : CharPairWProvider I k) {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) {σ : CharPairStr I s} {τ : CharPairStr I t}
    (hWT2 : T2Space b.W) (L : Submodule (ZMod 2) (Fin σ.n ⊕ Fin τ.n → ZMod 2))
    (htaylor : TaylorLegVanishes σ.q τ.q L) (hlag : JointLagrangian σ.q τ.q L) :
    CharPairBor b σ τ where
  hWT2 := hWT2
  P14 := (prov.wadm b).P14
  P23 := (prov.wadm b).P23
  hwu := (prov.wadm b).hwu
  L := L
  htaylor := htaylor
  hlag := hlag

/-! ## §8. `cylBor` — the discriminating op, instantiated end-to-end through the provider -/

/-- **`cylBor` instantiates** (design §2 item 4 ⚠, the discriminator): the reflexive cylinder over `s`
carries the char-pair structure `σ` to itself, with the diagonal membrane kernel (Lagrangian, Taylor
leg holds via `q − q = 0`) and W-admissibility from the provider. This is the op whose totality the
round-2 gate turns on — and it goes through under the τ-end-negated reading (iii). -/
noncomputable def charPairCylBor (prov : CharPairWProvider I k) {s : SingularManifold PUnit k I}
    (σ : CharPairStr I s) : CharPairBor (reflCylinder s) σ σ :=
  mkCharPairBor prov (reflCylinder s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    (cylLagrangian σ.n) (taylorLeg_cyl σ.q) (lagrangian_cyl σ.q)

/-! ## §9. `revBor` — end-reversal transport (clean: no reindexing) and `negBor` consistency -/

/-- Under end-reversal the joint enhancement's quadratic value NEGATES: `neg` on both ends sends
`q_σ ⊕ (neg q_τ)` to its pointwise negation. So a class killed by the Taylor leg stays killed. -/
theorem jointEnhancement_neg_q {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (jointEnhancement (neg qσ) (neg qτ)).q x = -((jointEnhancement qσ qτ).q x) := by
  show -(qσ.q (fun i => x (Sum.inl i))) + -(-(qτ.q (fun i => x (Sum.inr i))))
      = -(qσ.q (fun i => x (Sum.inl i)) + -(qτ.q (fun i => x (Sum.inr i))))
  ring

/-- Under end-reversal the joint enhancement's POLAR form is UNCHANGED (`neg` keeps `B`). -/
theorem jointEnhancement_neg_B {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    (jointEnhancement (neg qσ) (neg qτ)).B = (jointEnhancement qσ qτ).B := rfl

/-- **`revBor` instantiates** — end-reversal (`revStr` on both ends) transports a `CharPairBor` with
the SAME membrane kernel `L`: the Taylor leg survives (the joint value negates, `−0 = 0`,
`jointEnhancement_neg_q`) and the Lagrangian is literally unchanged (`jointEnhancement_neg_B`). No
reindexing — the cleanest op after `cylBor`. -/
def charPairRevBor {s t : SingularManifold PUnit k I} {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStr I s} {τ : CharPairStr I t} (β : CharPairBor b σ τ) :
    CharPairBor b (charPairRevStr σ) (charPairRevStr τ) where
  hWT2 := β.hWT2
  P14 := β.P14
  P23 := β.P23
  hwu := β.hwu
  L := β.L
  htaylor := by
    intro l hl
    show (jointEnhancement (neg σ.q) (neg τ.q)).q l = 0
    rw [jointEnhancement_neg_q]
    rw [β.htaylor l hl, neg_zero]
  hlag := by
    intro v hv
    refine β.hlag v (fun l hl => ?_)
    have := hv l hl
    rwa [show (jointEnhancement (charPairRevStr σ).q (charPairRevStr τ).q).B
        = (jointEnhancement σ.q τ.q).B from jointEnhancement_neg_B σ.q τ.q] at this

/-- **`negBor` consistency**: the doubling's ⊔-end enhancement `neg q ⊕ q` has Brown invariant `0`
(`brown_orthSum` + `brown_neg`: `−β + β = 0`) — matching the empty end (`brown 0 = 0`). So the
doubling `(M,σ̄) ⊔ (M,σ)` bounds at the invariant level (the inverse law `−[M,σ] + [M,σ] = 0`), the
content of `negBor`. The full `CharPairBor` witness supplies the anti-diagonal Lagrangian of
`orthSum (neg q) q` reindexed by `finSumFinEquiv` (a mechanical transport of `lagrangian_cyl`). -/
theorem neg_doubling_brown_zero {n : ℕ} (q : Z4Quadratic (Fin n)) :
    (orthSum (neg q) q).brown = 0 := by
  rw [brown_orthSum, brown_neg, neg_add_cancel]

/-! ## §9.5. The remaining `Bor` op witnesses (symm / neg / add / comm / assoc / unit)

Each transports the §4.5 metabolic engine through the `reindex`/`neg`/`orthSum` that `sumStr`/`revStr`
apply to the enhancements, then draws item 1 (`P14`/`P23`/`hwu`) either from `β` (same `W`) or from the
provider (a new `W`). `symmBor` reuses `b`'s W-datum (`b.symm.W = b.W`). -/

/-- **`symmBor` instantiates** — a bordism reversal swaps the two ends. The membrane kernel is `β.L`
pulled back along the `Sum.swap` regrouping: the τ-end-negated joint form of the swapped ends is the
`Equiv.sumComm`-reindex of the NEGATED original joint form (`z4_ext`), so metabolicity transports via
`IsMetabolic.neg`+`IsMetabolic.reindex`. `b.symm.W = b.W`, so item 1 is inherited from `β`. -/
def charPairSymmBor {s t : SingularManifold PUnit k I} {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStr I s} {τ : CharPairStr I t} (β : CharPairBor b σ τ) :
    CharPairBor b.symm τ σ :=
  have hmeta : IsMetabolic (jointEnhancement τ.q σ.q)
      (β.L.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumComm (Fin σ.n) (Fin τ.n)))) := by
    have hform : jointEnhancement τ.q σ.q
        = (Z4Quadratic.neg (jointEnhancement σ.q τ.q)).reindex (Equiv.sumComm (Fin σ.n) (Fin τ.n)) := by
      apply z4_ext
      · funext y
        show (τ.q).q (fun i => y (Sum.inl i)) + -((σ.q).q (fun i => y (Sum.inr i)))
            = -((jointEnhancement σ.q τ.q).q (fun i => y (Equiv.sumComm (Fin σ.n) (Fin τ.n) i)))
        simp only [jointEnhancement, Z4Quadratic.orthSum, Z4Quadratic.neg, Equiv.sumComm_apply,
          Sum.swap_inl, Sum.swap_inr]
        ring
      · funext y y'
        show (τ.q).B (fun i => y (Sum.inl i)) (fun i => y' (Sum.inl i))
              + (σ.q).B (fun i => y (Sum.inr i)) (fun i => y' (Sum.inr i))
            = (jointEnhancement σ.q τ.q).B (fun i => y (Equiv.sumComm (Fin σ.n) (Fin τ.n) i))
                (fun i => y' (Equiv.sumComm (Fin σ.n) (Fin τ.n) i))
        simp only [jointEnhancement, Z4Quadratic.orthSum, Z4Quadratic.neg, Equiv.sumComm_apply,
          Sum.swap_inl, Sum.swap_inr]
        ring
    rw [hform]
    exact (IsMetabolic.neg ⟨β.htaylor, β.hlag⟩).reindex (Equiv.sumComm (Fin σ.n) (Fin τ.n))
  { hWT2 := β.hWT2
    P14 := β.P14
    P23 := β.P23
    hwu := β.hwu
    L := β.L.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumComm (Fin σ.n) (Fin τ.n)))
    htaylor := hmeta.1
    hlag := hmeta.2 }

/-- **`negBor` instantiates** — the doubling `(M,σ̄) ⊔ (M,σ)` bounds `Σ × [0,1]`. Its σ-side end
`orthSum (neg σ.q) σ.q` has the anti-diagonal (`cylLagrangian`) as a metabolic Lagrangian
(`diag_metabolic`, both copies UN-negated on the σ-end per the no-go), transported through the
`finSumFinEquiv` reindex and block-summed with the (trivially metabolic) empty τ-end `⊤`. Item 1 from
the provider on `doublingBordism s`. -/
noncomputable def charPairNegBor (prov : CharPairWProvider I k) {s : SingularManifold PUnit k I}
    (σ : CharPairStr I s) :
    CharPairBor (doublingBordism s) (charPairSumStr (charPairRevStr σ) σ) charPairEmptyStr :=
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr (charPairRevStr σ) σ).q
      ((cylLagrangian σ.n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    (diag_metabolic (neg σ.q) σ.q (fun a => neg_add_cancel _) rfl).reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBor prov (doublingBordism s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    (blockSub ((cylLagrangian σ.n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)))
    hmeta.1 hmeta.2

/-- **`commBor` instantiates** — disjoint-union commutativity. The two ends carry `orthSum σ.q τ.q`
and `orthSum τ.q σ.q`, isometric via the block swap; the membrane is the swap-reparametrized cylinder,
whose kernel is the reindex-isometry graph (`reindexGraph_metabolic` on `orthSum_comm_eq`, transported
through the `finSumFinEquiv` reindex by `jointEnhancement_reindex`). Item 1 from the provider. -/
noncomputable def charPairCommBor (prov : CharPairWProvider I k)
    {s t : SingularManifold PUnit k I} (σ : CharPairStr I s) (τ : CharPairStr I t) :
    CharPairBor (mapCylinder (Diffeomorph.sumComm I s.M k t.M)
      (by funext z; rcases z with z | z <;> rfl)) (charPairSumStr σ τ) (charPairSumStr τ σ) :=
  have hbase : IsMetabolic
      (Z4Quadratic.orthSum (orthSum σ.q τ.q) (Z4Quadratic.neg (orthSum τ.q σ.q)))
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
        (Equiv.sumComm (Fin σ.n) (Fin τ.n)).symm)) := by
    rw [orthSum_comm_eq σ.q τ.q]
    exact reindexGraph_metabolic (orthSum σ.q τ.q) (Equiv.sumComm (Fin σ.n) (Fin τ.n))
  have hform : jointEnhancement (charPairSumStr σ τ).q (charPairSumStr τ σ).q
      = (Z4Quadratic.orthSum (orthSum σ.q τ.q) (Z4Quadratic.neg (orthSum τ.q σ.q))).reindex
          (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    jointEnhancement_reindex (orthSum σ.q τ.q) (orthSum τ.q σ.q) finSumFinEquiv finSumFinEquiv
  have hmeta : IsMetabolic (jointEnhancement (charPairSumStr σ τ).q (charPairSumStr τ σ).q)
      ((graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
        (Equiv.sumComm (Fin σ.n) (Fin τ.n)).symm)).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))) := by
    rw [hform]; exact hbase.reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
  mkCharPairBor prov _
    (by haveI := σ.t2; haveI := τ.t2
        exact inferInstanceAs (T2Space ((s.M ⊕ t.M) × Set.Icc (0 : ℝ) 1)))
    _ hmeta.1 hmeta.2

/-- **`unitBor` instantiates** — the disjoint-union unit law `σ ⊔ ∅ ~ σ`. The source enhancement
`orthSum σ.q (stdQuadratic 0)` is `σ.q` reindexed away the empty block (`orthSum_stdZero_eq`); the
membrane is the padding-cylinder, whose kernel is the reindex-isometry graph (`commonReindex_metabolic`
with the identity on the target end). Item 1 from the provider. -/
noncomputable def charPairUnitBor (prov : CharPairWProvider I k) {s : SingularManifold PUnit k I}
    (σ : CharPairStr I s) :
    CharPairBor (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
      (charPairSumStr σ charPairEmptyStr) σ :=
  have hqS : (charPairSumStr σ charPairEmptyStr).q
      = σ.q.reindex ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum σ.q (stdQuadratic 0)).reindex finSumFinEquiv = _
    rw [orthSum_stdZero_eq, reindex_trans]
  have hmeta : IsMetabolic (jointEnhancement (charPairSumStr σ charPairEmptyStr).q σ.q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
        ((((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv).symm.trans
          (Equiv.refl (Fin σ.n))).symm))) := by
    rw [hqS]
    exact commonReindex_metabolic σ.q ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv)
      (Equiv.refl (Fin σ.n))
  mkCharPairBor prov _
    (by haveI := σ.t2
        haveI : T2Space (emptySM (X := PUnit) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
        exact inferInstanceAs (T2Space ((s.M ⊕ emptySM.M) × Set.Icc (0 : ℝ) 1)))
    _ hmeta.1 hmeta.2

/-- **`assocBor` instantiates** — disjoint-union associativity. Both ends' enhancements are reindexes of
the common flattened form `A = orthSum (orthSum σ.q τ.q) ρ.q` (via `orthSum_reindex` for the inner
`sumStr` reindex and `orthSum_assoc_eq` for the reassociation); the membrane is the sumAssoc-cylinder,
whose kernel is the reindex-isometry graph (`commonReindex_metabolic`). Item 1 from the provider. -/
noncomputable def charPairAssocBor (prov : CharPairWProvider I k)
    {s t u : SingularManifold PUnit k I} (σ : CharPairStr I s) (τ : CharPairStr I t)
    (ρ : CharPairStr I u) :
    CharPairBor (mapCylinder (Diffeomorph.sumAssoc I s.M k t.M u.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
      (charPairSumStr (charPairSumStr σ τ) ρ) (charPairSumStr σ (charPairSumStr τ ρ)) := by
  have hqS : (charPairSumStr (charPairSumStr σ τ) ρ).q
      = (Z4Quadratic.orthSum (orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum ((orthSum σ.q τ.q).reindex finSumFinEquiv) ρ.q).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl ρ.q]
    rw [orthSum_reindex, reindex_trans]
  have hqT : (charPairSumStr σ (charPairSumStr τ ρ)).q
      = (Z4Quadratic.orthSum (orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
            ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv)) := by
    show (Z4Quadratic.orthSum σ.q ((orthSum τ.q ρ.q).reindex finSumFinEquiv)).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl σ.q]
    rw [orthSum_reindex, reindex_trans, orthSum_assoc_eq, reindex_trans]
  have hmeta := commonReindex_metabolic (Z4Quadratic.orthSum (orthSum σ.q τ.q) ρ.q)
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv)
    ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv))
  rw [← hqS, ← hqT] at hmeta
  exact mkCharPairBor prov _
    (by haveI := σ.t2; haveI := τ.t2; haveI := ρ.t2
        exact inferInstanceAs (T2Space (((s.M ⊕ t.M) ⊕ u.M) × Set.Icc (0 : ℝ) 1)))
    _ hmeta.1 hmeta.2

/-! ## §10. THE UNIVERSE-UNBLOCK PROOF-OF-CONCEPT (the payoff of the `TangentialData.{u,v}` generalization)

The §5 friction, resolved. The frozen v4 `Mfd` table lists BOTH `cert : PinPlusCertK I s`
(carrier-universe-0-monomorphic — the 5q.G SW/PD4 substrate pins `s.M : Type`) AND a bundled
`surf : SingularManifold …` (which is `Type 1`, bundling a `Type 0` carrier). Under the OLD
`TangentialData.{u}` interface (`Mfd : SingularManifold.{u} X k I → Type u`) these could NOT coexist in
one `Mfd s`: `cert` forces `s` — hence `Mfd s` — to universe 0, but a bundled `surf` needs `Type 1`. The
generalized `TangentialData.{u, v}` interface (`Mfd : SingularManifold.{u} X k I → Type v`) decouples the
structure universe `v` from the carrier universe `u`, so an `Mfd s` may sit at `Type 1` (carrying the
concrete surface) while its carrier `s` stays at universe 0 (still certified). This section demonstrates
the unblock CONCRETELY — the surface MANIFOLD content is now carriable in-substrate; only the `hchar`/
`hpolar` anchors (wt2's 2-dim PD tower) remain abstract. -/

/-- **The bundled characteristic-pair structure** — `CharPairStr` (the `Type 0` algebraic + certificate
core) PLUS the concrete characteristic surface `surf` (a closed, universe-0 2-manifold), its Hausdorff
certificate `surfT2`, and its smooth injective embedding `emb`/`embSmooth`/`embInj` into the 4-manifold
carrier `s.M`. Because `surf : SingularManifold.{0} …` is `Type 1`, so is `CharPairStrBundled` — while the
carrier `s` and the retained `cert : PinPlusCertK I s` keep `s` at universe 0. This is exactly the
`Type 1` `Mfd`-value / universe-0 certified carrier pairing the OLD interface forbade. -/
structure CharPairStrBundled (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))) [I.Boundaryless]
    (s : SingularManifold PUnit k I) extends CharPairStr I s where
  /-- the concrete characteristic surface — a closed, **universe-0** 2-manifold (`Type 1` when bundled). -/
  surf : SingularManifold.{0} (PUnit.{1}) k (𝓡 2)
  /-- the surface carrier is Hausdorff. -/
  surfT2 : T2Space surf.M
  /-- the surface embeds into the 4-manifold carrier `s.M`. -/
  emb : surf.M → s.M
  /-- the embedding is smooth. -/
  embSmooth : ContMDiff (𝓡 2) I k emb
  /-- the embedding is injective. -/
  embInj : Function.Injective emb

/-- **The unblock, as a type.** `charPairBundledMfd` is a legitimate `Mfd`-family for a carrier at
universe 0 landing in `Type 1` — precisely the `SingularManifold.{0} X k I → Type 1` shape the generalized
`TangentialData.{0, 1}.Mfd` field now admits (`v = 1 ≠ u = 0`). Under the pre-generalization
`Mfd : SingularManifold.{u} → Type u` this very definition was a universe error (`Type 1 ≠ Type 0`); it now
type-checks, which IS the resolution of the §5 friction. -/
def charPairBundledMfd : SingularManifold.{0} PUnit k I → Type 1 :=
  fun s => CharPairStrBundled (k := k) I s

/-- **The anti-collapse engine still applies to the bundled variant.** Any `CharPairBor` between the
underlying char-pair structures of two BUNDLED data forces their Brown invariants equal
(`brown_eq_of_taylorLeg_lagrangian` via `CharPairBor.brown_eq`) — the computed grade `abk8 := brown ∘ q`
descends exactly as for the un-bundled `CharPairStr`, so carrying the concrete surface costs nothing in
honesty and the reading-(ii) torsor collapse remains provably impossible. -/
theorem charPairBundled_brown_eq {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBor b σ.toCharPairStr τ.toCharPairStr) :
    σ.q.brown = τ.q.brown :=
  β.brown_eq

open SKEFTHawking.PinPlusTiedData in
/-- **A concrete inhabitant** (non-vacuity of the `Type 1` bundle): the empty carrier with the empty
characteristic surface, RETAINING the `w₂ = 0` certificate `pinPlusCertK_empty`. Witnesses that the
`Type 1` bundle is genuinely inhabitable with the certificate present and the carrier at universe 0 — the
concrete realization of the §5 resolution. -/
noncomputable def charPairBundledEmpty :
    CharPairStrBundled I (emptySM : SingularManifold PUnit k I) where
  toCharPairStr := charPairEmptyStr
  surf := emptySM
  surfT2 := ⟨fun x => x.elim⟩
  emb := fun x => x.elim
  embSmooth := contMDiff_of_subsingleton
  embInj := fun x => x.elim

end SKEFTHawking.PinPlusCharPairData
