/-
# Phase 5q.E W6 — the Ω₅^{Spin-ℤ₄} bordism substrate + the CONSTRUCTED Smith homomorphism

This module builds the **Spin-ℤ₄ side** of the "16 convergence" anomaly-inflow chain (the SM
Dai–Freed anomaly's home group), and the **Smith homomorphism** `Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` as a
**constructed substrate map** — moving the Smith map from a *hypothesis* (`CommonOrigin.SmithInflow`)
to a *construction*. With this, `CommonOrigin`'s common-origin theorem can be stated
**unconditionally at the substrate level** (`sixteen_convergence_common_origin_unconditional`):
the SM Dai–Freed anomaly lives in a genuine `Ω₅` bordism `Quotient`, is sent by the constructed
`smithHom` into the Pin⁺ bordism ℤ₁₆, and the chain SM → Ω₅ → Smith → Ω₄ is fully built.

## Honest scope (identical discipline to the accepted Pin⁺ substrate)

This is the **exact analog** of `SymTFT/PinPlusBordism4.lean` (Phase 6r, reviewed/accepted): a
**thin** manifold structure `SpinZ4Manifold5` carrying a ℤ-valued invariant `daiFreed : ℤ` (the
ℤ-lift of the Dai–Freed/η class, `16·η ∈ ℤ`), quotiented by `16 ∣ Δ(daiFreed)` to give a genuine
`Omega5SpinZ4Bordism ≃+ ZMod 16`. Just as the Pin⁺ substrate **assigns** `signature` (e.g.
`pinPlusRP4 := ⟨1⟩`) rather than computing it from geometry, this substrate **assigns** `daiFreed`;
the geometric Spin-ℤ₄ structure and the genuine η-invariant are the **tracked** content.

**Honest caveat — the faithfulness gap here is LARGER than on the Pin⁺ side (do not flatten this).**
Two same-day records (the `smith_inflow_z16` HYPOTHESIS_REGISTRY entry and the Phase 5q.E roadmap)
reasoned that the real Dai–Freed invariant is **intrinsically ℤ₁₆** (η/16 mod 1 ∈ ℝ/ℤ), with no
*natural* ℤ-lift. So while this Lean `Quotient` is a genuine, kernel-pure `≃+ ZMod 16` (it is NOT
"vacuous" — that earlier wording overstated the other way), the act of carrying `daiFreed : ℤ` and
reducing mod 16 is a **less-faithful** stand-in than the Pin⁺ signature is for `Ω₄^{Pin⁺}`: the
Pin⁺ side's tracked content is "this ℤ-valued signature is the bordism invariant," whereas this
side *additionally* tracks "the invariant takes ℤ values at all," which the geometric η does not.
The `APSEta.wittenYonekuraToZ16` η-map is a placeholder, so the *computed* η is unavailable.

**What W6 changes vs. the W5 `SmithInflow` hypothesis (scoped honestly):** the Smith map is now a
**constructed** `AddEquiv` between two genuine bordism `Quotient`s (`smithHom`), not an abstract
`ZMod 16 ≃+ Ω₄` hypothesis. So `CommonOrigin`'s ℤ₁₆-level chain SM → Ω₅ → Smith → Ω₄ is built with
**no abstract Lean hypothesis** (`smithInflowOfSmithHom` realizes the W5 `SmithInflow` from
`smithHom`). This is a **hypothesis-level** change only — NOT a faithfulness-level one: the geometric
**construction** of `Ω₅^{Spin-ℤ₄}` from manifolds + the η-invariant, and the faithfulness of these
thin substrates, remain the Mathlib-absent landmark (a *larger* tracked gap than the Pin⁺ side, per
the caveat above). This is its honest substrate stand-in, not a discharge of the geometry.

## References
  - García-Etxebarria–Montero, JHEP 08 (2019) 003 [arXiv:1808.00009] — `Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆`, the SM
    ℤ₁₆ Dai–Freed anomaly.
  - Wang (2024) — the Smith homomorphism / string-bordism program.
  - `SymTFT/PinPlusBordism4.lean` (the Pin⁺ substrate this mirrors), Kirby–Taylor 1990.
-/

import Mathlib
import SKEFTHawking.SymTFT.PinPlusBordism4

namespace SKEFTHawking.SymTFT

/-! ## §1. SpinZ4Manifold5 — thin Spin-ℤ₄ 5-manifold (à la PinPlusManifold4) -/

/-- A closed Spin-ℤ₄ 5-manifold, reduced to the data needed for bordism: a ℤ-lift of its
Dai–Freed/η anomaly class. Thin substrate (the geometric Spin-ℤ₄ structure + η-invariant are
tracked, mirroring `PinPlusManifold4`'s `signature` field — but see the header caveat: the η
invariant is ℤ₁₆-native, so this ℤ-lift is a *less*-faithful stand-in than the Pin⁺ signature). -/
structure SpinZ4Manifold5 where
  /-- ℤ-lift of the Dai–Freed anomaly class (`16·η ∈ ℤ`); the `Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` invariant. -/
  daiFreed : ℤ

namespace SpinZ4Manifold5

@[ext] theorem ext {M N : SpinZ4Manifold5} (h : M.daiFreed = N.daiFreed) : M = N := by
  cases M; cases N; congr

instance : Zero SpinZ4Manifold5 := ⟨⟨0⟩⟩
instance : Add SpinZ4Manifold5 := ⟨fun M N => ⟨M.daiFreed + N.daiFreed⟩⟩
instance : Neg SpinZ4Manifold5 := ⟨fun M => ⟨-M.daiFreed⟩⟩

@[simp] theorem zero_daiFreed : (0 : SpinZ4Manifold5).daiFreed = 0 := rfl
@[simp] theorem add_daiFreed (M N : SpinZ4Manifold5) :
    (M + N).daiFreed = M.daiFreed + N.daiFreed := rfl
@[simp] theorem neg_daiFreed (M : SpinZ4Manifold5) : (-M).daiFreed = -M.daiFreed := rfl

instance : AddCommGroup SpinZ4Manifold5 where
  add_assoc M N P := by ext; simp [add_assoc]
  zero_add M := by ext; simp
  add_zero M := by ext; simp
  add_comm M N := by ext; simp [add_comm]
  neg_add_cancel M := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

end SpinZ4Manifold5

/-- The generator of `Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` (the `ν=1` Spin-ℤ₄ 5-manifold), with `daiFreed = 1`. -/
def spinZ4Gen : SpinZ4Manifold5 := ⟨1⟩

/-- The SM Dai–Freed anomaly representative for `N_f` complete generations: `daiFreed = 16·N_f`
(`16` Weyl per generation), anomaly-free since `16·N_f ≡ 0 mod 16`. -/
def smSpinZ4Class (N_f : ℕ) : SpinZ4Manifold5 := ⟨16 * N_f⟩

/-- A non-generator, non-trivial witness exercising the quotient beyond `{0, gen}` (the analog of
the Pin⁺ side's `pinPlusK3Lift := ⟨-16⟩`, which the Pin⁺ substrate uses to witness its quotient is
not collapsed): `daiFreed = 3` is neither `0`, `1`, nor `16·k`, so its class is the non-trivial
`3 ∈ ZMod 16`. Witnesses that `Omega5SpinZ4Bordism` is a genuine 16-element quotient, not just
`{0, [gen]}`. -/
def spinZ4NonTrivial : SpinZ4Manifold5 := ⟨3⟩

/-! ## §2. The Ω₅^{Spin-ℤ₄} bordism quotient (à la Omega4PinPlusBordism) -/

/-- Bordism Setoid: `M ~ N ↔ 16 ∣ (Δ daiFreed)`. -/
def SpinZ4Bordism5Setoid : Setoid SpinZ4Manifold5 where
  r M N := (16 : ℤ) ∣ (M.daiFreed - N.daiFreed)
  iseqv :=
    { refl := fun M => by simp
      symm := fun {M N} h => by
        have : N.daiFreed - M.daiFreed = -(M.daiFreed - N.daiFreed) := by ring
        rw [this]; exact h.neg_right
      trans := fun {M N P} h₁ h₂ => by
        have : M.daiFreed - P.daiFreed =
            (M.daiFreed - N.daiFreed) + (N.daiFreed - P.daiFreed) := by ring
        rw [this]; exact dvd_add h₁ h₂ }

/-- **`Omega5SpinZ4Bordism`** — the genuine Spin-ℤ₄ 5-manifold bordism `Quotient` (`≅ ZMod 16`,
GEM 2018). The SM Dai–Freed anomaly lives here. -/
def Omega5SpinZ4Bordism : Type := Quotient SpinZ4Bordism5Setoid

namespace Omega5SpinZ4Bordism

/-- Canonical projection. -/
def mk (M : SpinZ4Manifold5) : Omega5SpinZ4Bordism := Quotient.mk _ M

/-- The Dai–Freed class mod 16 is well-defined on the quotient. -/
def daiFreedMod16 : Omega5SpinZ4Bordism → ZMod 16 :=
  Quotient.lift (fun M => (M.daiFreed : ZMod 16)) (fun M N h => by
    have hcast : ((M.daiFreed - N.daiFreed : ℤ) : ZMod 16) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have : (M.daiFreed : ZMod 16) - (N.daiFreed : ZMod 16) = 0 := by push_cast at hcast; exact hcast
    exact sub_eq_zero.mp this)

@[simp] theorem daiFreedMod16_mk (M : SpinZ4Manifold5) :
    daiFreedMod16 (mk M) = (M.daiFreed : ZMod 16) := rfl

end Omega5SpinZ4Bordism

open Omega5SpinZ4Bordism

instance : Zero Omega5SpinZ4Bordism := ⟨mk 0⟩

instance : Add Omega5SpinZ4Bordism :=
  ⟨Quotient.lift₂ (fun M N => mk (M + N)) (fun M₁ N₁ M₂ N₂ h₁ h₂ => by
    apply Quotient.sound
    show (16 : ℤ) ∣ ((M₁ + N₁).daiFreed - (M₂ + N₂).daiFreed)
    have : (M₁ + N₁).daiFreed - (M₂ + N₂).daiFreed =
        (M₁.daiFreed - M₂.daiFreed) + (N₁.daiFreed - N₂.daiFreed) := by simp; ring
    rw [this]; exact dvd_add h₁ h₂)⟩

instance : Neg Omega5SpinZ4Bordism :=
  ⟨Quotient.lift (fun M => mk (-M)) (fun M N h => by
    apply Quotient.sound
    show (16 : ℤ) ∣ ((-M).daiFreed - (-N).daiFreed)
    have : (-M).daiFreed - (-N).daiFreed = -(M.daiFreed - N.daiFreed) := by simp; ring
    rw [this]; exact h.neg_right)⟩

@[simp] theorem omega5_add_mk (M N : SpinZ4Manifold5) :
    (mk M : Omega5SpinZ4Bordism) + mk N = mk (M + N) := rfl

instance : AddCommGroup Omega5SpinZ4Bordism where
  add_assoc x y z := by
    induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
    induction z using Quotient.inductionOn with | _ P =>
    show mk (M + N + P) = mk (M + (N + P)); congr 1; ext; simp [add_assoc]
  zero_add x := by
    induction x using Quotient.inductionOn with | _ M => show mk (0 + M) = mk M; congr 1; ext; simp
  add_zero x := by
    induction x using Quotient.inductionOn with | _ M => show mk (M + 0) = mk M; congr 1; ext; simp
  add_comm x y := by
    induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
    show mk (M + N) = mk (N + M); congr 1; ext; simp [add_comm]
  neg_add_cancel x := by
    induction x using Quotient.inductionOn with | _ M => show mk (-M + M) = mk 0; congr 1; ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The Dai–Freed-class-mod-16 homomorphism `Ω₅^{Spin-ℤ₄} →+ ZMod 16`. -/
def omega5ToZMod16 : Omega5SpinZ4Bordism →+ ZMod 16 where
  toFun := daiFreedMod16
  map_zero' := by show daiFreedMod16 (mk 0) = 0; simp
  map_add' x y := by
    induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
    show ((M + N).daiFreed : ZMod 16) = (M.daiFreed : ZMod 16) + (N.daiFreed : ZMod 16)
    simp

/-- Inverse map. -/
def omega5OfZMod16 (n : ZMod 16) : Omega5SpinZ4Bordism := mk ⟨n.val⟩

/-- **`omega5SpinZ4BordismEquivZMod16`** — `Ω₅^{Spin-ℤ₄} ≃+ ZMod 16` (GEM 2018, at the substrate
level). -/
noncomputable def omega5SpinZ4BordismEquivZMod16 : Omega5SpinZ4Bordism ≃+ ZMod 16 where
  toFun := omega5ToZMod16
  invFun := omega5OfZMod16
  left_inv x := by
    induction x using Quotient.inductionOn with | _ M =>
    apply Quotient.sound
    show (16 : ℤ) ∣ (((M.daiFreed : ZMod 16).val : ℤ) - M.daiFreed)
    have h : ((((M.daiFreed : ZMod 16).val : ℤ) - M.daiFreed : ℤ) : ZMod 16) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp h
  right_inv n := by
    show ((((⟨n.val⟩ : SpinZ4Manifold5).daiFreed : ZMod 16))) = n
    show ((n.val : ℤ) : ZMod 16) = n
    push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
  map_add' := omega5ToZMod16.map_add'

@[simp] theorem omega5_gen_class : omega5SpinZ4BordismEquivZMod16 (mk spinZ4Gen) = 1 := by
  show daiFreedMod16 (mk spinZ4Gen) = 1
  show ((spinZ4Gen.daiFreed : ZMod 16)) = 1
  show ((1 : ℤ) : ZMod 16) = 1
  decide

@[simp] theorem omega5_sm_class (N_f : ℕ) :
    omega5SpinZ4BordismEquivZMod16 (mk (smSpinZ4Class N_f)) = 16 * (N_f : ZMod 16) := by
  show daiFreedMod16 (mk (smSpinZ4Class N_f)) = 16 * (N_f : ZMod 16)
  show (((smSpinZ4Class N_f).daiFreed : ZMod 16)) = 16 * (N_f : ZMod 16)
  show (((16 * N_f : ℤ)) : ZMod 16) = 16 * (N_f : ZMod 16)
  push_cast; ring

/-- The non-generator witness has the non-trivial class `3 ∈ ZMod 16` — the quotient is a genuine
16-element group (not collapsed to `{0, [gen]}`), mirroring the Pin⁺ side's non-trivial witnesses. -/
theorem omega5_nontrivial_class :
    omega5SpinZ4BordismEquivZMod16 (mk spinZ4NonTrivial) = 3 := by
  show daiFreedMod16 (mk spinZ4NonTrivial) = 3
  show ((spinZ4NonTrivial.daiFreed : ZMod 16)) = 3
  show ((3 : ℤ) : ZMod 16) = 3
  decide

/-! ## §3. The constructed Smith homomorphism Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺} -/

/-- **`smithHom`** — the Smith homomorphism `Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}`, **constructed** (not
hypothesized) as the canonical generator-preserving iso between the two genuine bordism `Quotient`s.
Its ℤ₁₆-level behaviour is the cited-true Smith content (GEM 2018 / Wang 2024); the geometric
dimension-shifting bordism construction is the tracked/absent part. This is the substrate-level
discharge of the W5 `CommonOrigin.SmithInflow` hypothesis. -/
noncomputable def smithHom : Omega5SpinZ4Bordism ≃+ Omega4PinPlusBordism :=
  omega5SpinZ4BordismEquivZMod16.trans omega4PinPlusBordismEquivZMod16.symm

/-- The Smith homomorphism sends the Ω₅ generator to the Pin⁺ generator `[RP⁴]`. -/
theorem smithHom_gen : smithHom (mk spinZ4Gen) = Omega4PinPlusBordism.mk pinPlusRP4 := by
  show omega4PinPlusBordismEquivZMod16.symm (omega5SpinZ4BordismEquivZMod16 (mk spinZ4Gen)) = _
  rw [omega5_gen_class, ← pinPlusRP4_class_to_zmod16]
  exact omega4PinPlusBordismEquivZMod16.symm_apply_apply _

/-- The Smith homomorphism sends the SM Dai–Freed anomaly class (`16·N_f`) to the **trivial** Pin⁺
bordism class — the anomaly-free SM lands at `0 ∈ Ω₄^{Pin⁺}`, now via a *constructed* map. -/
theorem smithHom_sm_trivial (N_f : ℕ) : smithHom (mk (smSpinZ4Class N_f)) = 0 := by
  show omega4PinPlusBordismEquivZMod16.symm (omega5SpinZ4BordismEquivZMod16 (mk (smSpinZ4Class N_f))) = 0
  rw [omega5_sm_class, show (16 : ZMod 16) * (N_f : ZMod 16) = 0 from by
    rw [show (16 : ZMod 16) = 0 from by decide]; ring, map_zero]

/-- **ℤ₁₆-level consistency of the constructed Smith map.** For every Ω₅ class, the Rokhlin
signature reading of its Pin⁺ image under `smithHom` equals its own Dai–Freed class
(`signatureMod16 ∘ smithHom = daiFreedMod16`). This holds **by construction** of `smithHom` (it was
defined as the composite of the two `≃+ ZMod 16` isos), so it carries no geometric Rokhlin/Dai–Freed
content — that dimension-shifting identification is the tracked, Mathlib-absent part. -/
theorem signatureMod16_smithHom (x : Omega5SpinZ4Bordism) :
    Omega4PinPlusBordism.signatureMod16 (smithHom x) = omega5SpinZ4BordismEquivZMod16 x := by
  show omega4PinPlusBordismToZMod16 (omega4PinPlusBordismEquivZMod16.symm
    (omega5SpinZ4BordismEquivZMod16 x)) = omega5SpinZ4BordismEquivZMod16 x
  exact omega4PinPlusBordismEquivZMod16.apply_symm_apply _

end SKEFTHawking.SymTFT
