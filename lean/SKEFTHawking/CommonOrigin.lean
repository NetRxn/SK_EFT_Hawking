/-
# Phase 5q.E Wave 5 — the "16 convergence" as a genuine COMMON ORIGIN (conditional)

This is the capstone the goal actually asks for (roadmap E.1–E.5): **replace the bare
enumeration** `RokhlinBridge.sixteen_convergence_full` ("the numeral 16 appears in four
contexts") **with a map-composition** in which the four 16s are images of **one genuine ℤ₁₆**
— the Pin⁺ bordism group `Ω₄^{Pin⁺}` (`SymTFT.Omega4PinPlusBordism`, a real `Quotient`, with
`≃+ ZMod 16` and `[RP⁴]` of *exact* order 16, Kirby–Taylor 1990) — **under explicit maps**.

## The honest status of this theorem (read before quoting it anywhere)

This is a **CONDITIONAL** common origin, and the conditionality is the whole honesty story:

- The genuine geometric **Smith homomorphism** `Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` (the dimension-
  shifting bordism map that physically *ties* the SM Dai–Freed anomaly group to the Pin⁺ group)
  is **Mathlib-absent** — there is no `Ω₅^{Spin-ℤ₄}` bordism group in the library at all
  (verified 2026-06-14; Phase 5q.E roadmap §Mathlib status). So it is carried as a **disclosed
  tracked input**, the structure `SmithInflow` — an iso `ZMod 16 ≃+ Ω₄^{Pin⁺}` pinned to the
  generator. It is a *hypothesis*, **NOT an axiom**, and it is **inhabited** at the substrate
  level (`substrateSmithInflow`), so the conditional is not vacuously false.
- Two distinct claims, with distinct warrants: (i) that the Smith hom is an **isomorphism**
  `ℤ₁₆ ≅ ℤ₁₆` is the **cited-true** fact (García-Etxebarria–Montero 2018 arXiv:1808.00009; Wang
  2024 Smith-homomorphism); (ii) the *specific* pin `smith 1 = [RP⁴]` is a **normalization
  convention** (an iso of ℤ₁₆ is determined only up to a unit; we fix the canonical Kirby–Taylor
  generator) — NOT itself a cited theorem; the true Smith hom agrees up to a generator
  relabeling. This is the crucial contrast with the Arf no-go (`RokhlinArfNoGo.lean`), which died
  because a claimed lattice identity was *false*; here the cited fact (iso-ness) is *true* and
  only its geometric *construction* — and the convention-free generator choice — are absent.

So this theorem says: **GIVEN the Smith inflow** (iso cited-true; generator pin conventional), the SM Dai–Freed
anomaly, the Rokhlin signature obstruction, and the Kitaev 16-fold phase are read by explicit
homomorphisms into *one* genuine ℤ₁₆, and **Rokhlin and Kitaev read it identically, pointwise**
(`rokhlin_reads_kitaev`). It does **NOT** construct the geometric Smith map or `Ω₅^{Spin-ℤ₄}`
(the Mathlib landmarks remain deferred), and — load-bearing — a shared ℤ₁₆ **constrains, it does
not derive** the SM: the SM is the *trivial* class among 16, `[RP⁴]` is the shared generator,
and many theories share this ℤ₁₆. The 3-generation headline is independent and imports none of this.

## W6 (2026-06-14): the Smith map is CONSTRUCTED — a hypothesis-level change, scoped honestly
The §4 additions replace the abstract `SmithInflow` hypothesis with a constructed substrate map:
`SpinZ4Bordism5.lean` builds the `Ω₅^{Spin-ℤ₄}` bordism group as a genuine, kernel-pure `Quotient`
and the Smith homomorphism `smithHom : Ω₅ → Ω₄^{Pin⁺}` as a **constructed** `AddEquiv`.
`sixteen_convergence_common_origin_via_constructed_smith` then states the common origin with **no
abstract Lean hypothesis**. **This is hypothesis-level, NOT a geometric discharge:** the Ω₅
substrate is thin like Pin⁺ but with a **larger** faithfulness gap (the Dai–Freed invariant is
ℤ₁₆-native — η/16 mod 1 — so the `daiFreed : ℤ` lift additionally tracks "the invariant takes ℤ
values at all," which the Pin⁺ signature does not). The geometric *construction* of `Ω₅` from
manifolds + the η-invariant, and the substrates' faithfulness, remain the Mathlib-absent landmark.
Do not quote "no hypothesis" as "unconditional" in the geometric sense.

## Why this is a real upgrade over `sixteen_convergence_full`
That theorem is an *unconditional conjunction with no maps between the four 16s*. This one
exhibits the **explicit maps** and proves they **cohere into one ℤ₁₆** (pointwise Rokhlin=Kitaev,
SM at the trivial class, `[RP⁴]` the order-16 generator) — the difference between "the number 16
recurs" and "these are images of one ℤ₁₆ invariant under explicit maps."

## References
  - Kirby–Taylor, Comment. Math. Helv. 65 (1990) 434 — `Ω₄^{Pin⁺} ≅ ℤ₁₆` (via `PinPlusBordism4`).
  - García-Etxebarria–Montero, JHEP 08 (2019) 003 [arXiv:1808.00009] — SM ℤ₁₆ Dai–Freed anomaly.
  - Wang (2024) — Smith homomorphism / string-bordism program.
  - `KitaevSixteenFold.lean` (the Kitaev reading), `SymTFT/PinPlusBordism4.lean` (the Pin⁺ ℤ₁₆),
    `RokhlinBridge.lean::sixteen_convergence_full` (the enumeration this upgrades).
  - `docs/SIXTEEN_CONVERGENCE_STATUS.md`, `docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md`.
-/

import Mathlib
import SKEFTHawking.SymTFT.PinPlusBordism4
import SKEFTHawking.SymTFT.SpinZ4Bordism5
import SKEFTHawking.KitaevSixteenFold
import SKEFTHawking.Spin10Sixteen

namespace SKEFTHawking.CommonOrigin

open SKEFTHawking SKEFTHawking.SymTFT

/-! ## §1. The disclosed Smith inflow (tracked hypothesis, NOT an axiom) -/

/-- **`SmithInflow`** — the disclosed geometric input tying the SM Dai–Freed group
`Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` to the Pin⁺ bordism group `Ω₄^{Pin⁺}` via the **Smith homomorphism**,
carried at the ℤ₁₆ level as a generator-preserving isomorphism. The geometric construction is
Mathlib-absent; its ℤ₁₆-level **iso-ness** is cited-true (GEM 2018; Wang 2024), while the
generator pin `smith 1 = [RP⁴]` is the canonical normalization (convention, not a cited theorem).
This is a *hypothesis*, not an axiom, and it is inhabited (`substrateSmithInflow`). -/
structure SmithInflow where
  /-- The Smith homomorphism at the ℤ₁₆ level: `Ω₅^{Spin-ℤ₄}(≅ ℤ₁₆) ≃+ Ω₄^{Pin⁺}`. -/
  smith : ZMod 16 ≃+ Omega4PinPlusBordism
  /-- Pinned to the canonical generator: the order-16 generator `1` maps to `[RP⁴]`. -/
  smith_gen : smith 1 = Omega4PinPlusBordism.mk pinPlusRP4

/-- **The `SmithInflow` hypothesis is satisfiable** (not vacuously false): the inverse of the
Kirby–Taylor iso `Ω₄^{Pin⁺} ≃+ ZMod 16` sends `1 ↦ [RP⁴]`. This is the substrate-level witness;
the geometric Smith map's interpretation onto it is the tracked content. -/
noncomputable def substrateSmithInflow : SmithInflow where
  smith := omega4PinPlusBordismEquivZMod16.symm
  smith_gen := by
    rw [← pinPlusRP4_class_to_zmod16]
    exact omega4PinPlusBordismEquivZMod16.symm_apply_apply _

/-- **The Smith inflow is canonical (unique), not an arbitrary choice.** Any two
generator-preserving inflows are equal — a `ℤ₁₆`-hom is determined by its value at `1`, and both
send `1 ↦ [RP⁴]`. So the common origin below does not depend on a choice of Smith map: the
generator pin *forces* the entire ℤ₁₆-level identification. (Only the geometric *reality* of this
unique map is tracked, not any selection among candidates.) -/
theorem smithInflow_smith_unique (S T : SmithInflow) : S.smith = T.smith := by
  have hkey : S.smith.toAddMonoidHom.comp (Int.castAddHom (ZMod 16))
      = T.smith.toAddMonoidHom.comp (Int.castAddHom (ZMod 16)) := by
    apply AddMonoidHom.ext_int
    show S.smith (((1 : ℤ)) : ZMod 16) = T.smith (((1 : ℤ)) : ZMod 16)
    have h1 : (((1 : ℤ)) : ZMod 16) = 1 := by norm_num
    rw [h1, S.smith_gen, T.smith_gen]
  ext n
  have := DFunLike.congr_fun hkey (n.val : ℤ)
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

/-! ## §2. The four facet-readings into the ONE ℤ₁₆ -/

/-- **Rokhlin reads Kitaev — pointwise.** For *every* Kitaev phase `ν`, the Rokhlin signature
class (`signatureMod16`) of its image in `Ω₄^{Pin⁺}` under the Smith inflow is exactly `ν`. So
the Kitaev 16-fold labels and the Rokhlin Pin⁺ signature classes are the **same ℤ₁₆, pointwise**
— the goal's literal "the Pin⁺ ℤ₁₆ that Rokhlin and the Kitaev 16-fold way both read." (The
composite `signatureMod16 ∘ smith : ℤ₁₆ →+ ℤ₁₆` sends `1 ↦ 1`, hence is the identity.) -/
theorem rokhlin_reads_kitaev (S : SmithInflow) (ν : ℤ) :
    Omega4PinPlusBordism.signatureMod16 (S.smith (Kitaev16.kitaevClass ν)) = (ν : ZMod 16) := by
  have key : ((omega4PinPlusBordismToZMod16.comp S.smith.toAddMonoidHom).comp
      (Int.castAddHom (ZMod 16))) = Int.castAddHom (ZMod 16) := by
    apply AddMonoidHom.ext_int
    show omega4PinPlusBordismToZMod16 (S.smith (((1 : ℤ)) : ZMod 16)) = (((1 : ℤ)) : ZMod 16)
    have h1 : (((1 : ℤ)) : ZMod 16) = 1 := by norm_num
    rw [h1, S.smith_gen]
    exact pinPlusRP4_class_signature
  simpa [Kitaev16.kitaevClass] using DFunLike.congr_fun key ν

/-- **The Kitaev generator IS the Pin⁺ bordism generator.** The Kitaev `ν=1` phase maps to
`[RP⁴]` under the Smith inflow — the non-vacuous heart of the unification (not a `0 = 0`). -/
theorem kitaev_generator_is_bordism_generator (S : SmithInflow) :
    S.smith (Kitaev16.kitaevClass 1) = Omega4PinPlusBordism.mk pinPlusRP4 := by
  have : Kitaev16.kitaevClass 1 = 1 := by unfold Kitaev16.kitaevClass; decide
  rw [this, S.smith_gen]

/-- **The SM Dai–Freed anomaly is the trivial bordism class** (anomaly-free): `N_f` complete
generations have anomaly class `16·N_f ≡ 0`, which the Smith inflow sends to `0 ∈ Ω₄^{Pin⁺}`. -/
theorem sm_anomaly_trivial_in_bordism (S : SmithInflow) (N_f : ℕ) :
    S.smith (16 * (N_f : ZMod 16)) = 0 := by
  have h16 : (16 : ZMod 16) * (N_f : ZMod 16) = 0 := by
    rw [show (16 : ZMod 16) = 0 from by decide]; ring
  rw [h16, map_zero]

/-- **Facet-1 → facet-2 → bordism — the chain from its actual start.** The goal's anomaly-inflow
chain begins with the SM 16-fermion content (the Spin(10) Weyl spinor). Here that "16" is the
`Spin10Sixteen` branching sum `dim(10)+dim(5̄)+dim(1)` (the even-binomial count `C(5,0)+C(5,2)+C(5,4)`,
NOT a literal), and `N_f` generations feed it through the Smith inflow to the trivial bordism class
— routing facet 1 (the Spin(10) count) explicitly into the common origin. -/
theorem sm_spin10_count_trivial_in_bordism (S : SmithInflow) (N_f : ℕ) :
    S.smith (((Spin10.su5dim .ten + Spin10.su5dim .fivebar + Spin10.su5dim .one : ℕ) : ZMod 16)
      * (N_f : ZMod 16)) = 0 := by
  have hcount : ((Spin10.su5dim .ten + Spin10.su5dim .fivebar + Spin10.su5dim .one : ℕ) : ZMod 16)
      = 0 := by decide
  rw [hcount, zero_mul, map_zero]

/-- **Rokhlin: a smooth-spin bulk is the trivial class.** The K3 spin 4-manifold's Pin⁺ lift has
`16 ∣ σ` (`σ = -16`), so its class in `Ω₄^{Pin⁺}` is `0` — Rokhlin's theorem at the bordism level. -/
theorem rokhlin_k3_trivial : Omega4PinPlusBordism.mk pinPlusK3Lift = 0 := by
  have h : omega4PinPlusBordismEquivZMod16 (Omega4PinPlusBordism.mk pinPlusK3Lift) = 0 :=
    pinPlusK3Lift_class_signature
  rwa [← map_zero omega4PinPlusBordismEquivZMod16,
    omega4PinPlusBordismEquivZMod16.injective.eq_iff] at h

/-! ## §3. The common-origin capstone -/

/-- **`sixteen_convergence_common_origin`** — the four 16s as images of ONE ℤ₁₆ under explicit
maps (conditional on the disclosed Smith inflow `S`). Bundles:
1. **SM (facets 1–2):** the Dai–Freed anomaly `16·N_f` is the trivial class (anomaly-free).
2. **Kitaev (facet 4):** the generator `ν=1` is the Pin⁺ bordism generator `[RP⁴]`.
3. **Rokhlin (facet 3):** `signatureMod16 [RP⁴] = 1` — Rokhlin reads `[RP⁴]` as the generator,
   *agreeing* with Kitaev (and pointwise for all phases, `rokhlin_reads_kitaev`).
4. **Rokhlin:** the smooth-spin K3 lift is the trivial class (`16 ∣ σ`).
5. **Genuineness:** `[RP⁴]` has *exact* order 16 — the shared ℤ₁₆ is real, not collapsed.

This is the genuine common-origin map-composition that supersedes `sixteen_convergence_full`'s
enumeration. **Conditional** on `S` (disclosed, inhabited; iso cited-true, generator pin
conventional); **constrains-not-derives**. -/
theorem sixteen_convergence_common_origin (S : SmithInflow) (N_f : ℕ) :
    S.smith (16 * (N_f : ZMod 16)) = 0 ∧
    S.smith (Kitaev16.kitaevClass 1) = Omega4PinPlusBordism.mk pinPlusRP4 ∧
    Omega4PinPlusBordism.signatureMod16 (Omega4PinPlusBordism.mk pinPlusRP4) = 1 ∧
    Omega4PinPlusBordism.mk pinPlusK3Lift = 0 ∧
    (∀ k : ℕ, 0 < k → k < 16 → (k : ℕ) • (Omega4PinPlusBordism.mk pinPlusRP4) ≠ 0) :=
  ⟨sm_anomaly_trivial_in_bordism S N_f,
   kitaev_generator_is_bordism_generator S,
   pinPlusRP4_class_signature,
   rokhlin_k3_trivial,
   pinPlusRP4_class_order_exact_sixteen⟩

/-- **Substrate instance.** The common origin instantiated at the inhabited `substrateSmithInflow`
— the unconditional substrate-level statement (the geometric Smith interpretation onto this
inflow is the tracked content per the module docstring). -/
theorem sixteen_convergence_common_origin_substrate (N_f : ℕ) :
    substrateSmithInflow.smith (16 * (N_f : ZMod 16)) = 0 ∧
    substrateSmithInflow.smith (Kitaev16.kitaevClass 1) = Omega4PinPlusBordism.mk pinPlusRP4 ∧
    Omega4PinPlusBordism.signatureMod16 (Omega4PinPlusBordism.mk pinPlusRP4) = 1 ∧
    Omega4PinPlusBordism.mk pinPlusK3Lift = 0 ∧
    (∀ k : ℕ, 0 < k → k < 16 → (k : ℕ) • (Omega4PinPlusBordism.mk pinPlusRP4) ≠ 0) :=
  sixteen_convergence_common_origin substrateSmithInflow N_f

/-! ## §4. W6 — replace the abstract `SmithInflow` with a constructed substrate Smith map

W6 (`SymTFT/SpinZ4Bordism5.lean`) builds the `Ω₅^{Spin-ℤ₄}` bordism group as a genuine, kernel-pure
`Quotient` (`≃+ ZMod 16`) and the Smith homomorphism `smithHom : Ω₅ → Ω₄^{Pin⁺}` as a **constructed**
`AddEquiv`. So at the **ℤ₁₆/Lean level** the chain `SM → Ω₅ → Smith → Ω₄` is built with no abstract
hypothesis — but this is a **hypothesis-level** change, NOT a geometric-faithfulness one.

**Honest scoping (read before quoting this as "unconditional"):** the Ω₅ substrate is *thin* like
the Pin⁺ one, but its faithfulness gap is **LARGER**, not "the same" — the geometric Dai–Freed
invariant is ℤ₁₆-native (η/16 mod 1), so carrying `daiFreed : ℤ` additionally tracks "the invariant
takes ℤ values at all," which the Pin⁺ signature does not need (see `SpinZ4Bordism5` header + the
`smith_inflow_z16` HYPOTHESIS_REGISTRY entry). So "the hypothesis is gone" means *no abstract Lean
binder*, and nothing about the geometry being proved; the geometric construction of `Ω₅` from
manifolds + the η-invariant, and the substrates' faithfulness, remain the Mathlib-absent landmark. -/

/-- **The `SmithInflow` is now realized from a constructed substrate map** (not merely from an
abstract `ZMod 16`-iso): `smithHom` precomposed with `Ω₅ ≃+ ZMod 16`. This replaces the abstract
existence-of-iso input with a map between two genuine bordism `Quotient`s — a *hypothesis-level*
improvement; the geometric faithfulness of those thin `Quotient`s is still tracked (and is a larger
gap than the Pin⁺ side, per §4 scoping). -/
noncomputable def smithInflowOfSmithHom : SmithInflow where
  smith := SymTFT.omega5SpinZ4BordismEquivZMod16.symm.trans SymTFT.smithHom
  smith_gen := by
    show SymTFT.smithHom (SymTFT.omega5SpinZ4BordismEquivZMod16.symm 1) = _
    have h : SymTFT.omega5SpinZ4BordismEquivZMod16.symm (1 : ZMod 16)
        = SymTFT.Omega5SpinZ4Bordism.mk SymTFT.spinZ4Gen := by
      rw [← SymTFT.omega5_gen_class]
      exact SymTFT.omega5SpinZ4BordismEquivZMod16.symm_apply_apply _
    rw [h, SymTFT.smithHom_gen]

/-- **`sixteen_convergence_common_origin_via_constructed_smith`** — the common origin with the Smith
map a **construction** rather than the abstract `SmithInflow` hypothesis (W6). Using the constructed
`smithHom`, the SM Dai–Freed anomaly (in the genuine `Ω₅^{Spin-ℤ₄}` bordism `Quotient`) is sent to
the trivial Pin⁺ class; the Ω₅ generator to `[RP⁴]`; Rokhlin reads that image as the generator `1`;
`[RP⁴]` has exact order 16.

**"No `SmithInflow` hypothesis" is hypothesis-level only — NOT "unconditional" in the geometric
sense.** The chain is built at the ℤ₁₆/Lean level; the *geometric faithfulness* of the thin Ω₅/Ω₄
substrates and the genuine η-invariant remain tracked — a **larger** gap than the Pin⁺ side (the
Dai–Freed invariant is ℤ₁₆-native, with no natural ℤ-lift; §4 scoping). Do **not** quote this as a
geometric discharge of the Smith map / Ω₅ bordism group. -/
theorem sixteen_convergence_common_origin_via_constructed_smith (N_f : ℕ) :
    SymTFT.smithHom (SymTFT.Omega5SpinZ4Bordism.mk (SymTFT.smSpinZ4Class N_f)) = 0 ∧
    SymTFT.smithHom (SymTFT.Omega5SpinZ4Bordism.mk SymTFT.spinZ4Gen)
      = Omega4PinPlusBordism.mk pinPlusRP4 ∧
    Omega4PinPlusBordism.signatureMod16
      (SymTFT.smithHom (SymTFT.Omega5SpinZ4Bordism.mk SymTFT.spinZ4Gen)) = 1 ∧
    (∀ k : ℕ, 0 < k → k < 16 → (k : ℕ) • (Omega4PinPlusBordism.mk pinPlusRP4) ≠ 0) := by
  refine ⟨SymTFT.smithHom_sm_trivial N_f, SymTFT.smithHom_gen, ?_,
    pinPlusRP4_class_order_exact_sixteen⟩
  rw [SymTFT.signatureMod16_smithHom, SymTFT.omega5_gen_class]

/-! ## §5. Module summary

The conditional common origin (roadmap E.1–E.5), superseding the enumeration:
  - `SmithInflow` — the disclosed tracked Smith hom (hypothesis, NOT axiom; inhabited by
    `substrateSmithInflow`; **canonical/unique** by `smithInflow_smith_unique` — the generator pin
    forces it, so the result is choice-free).
  - `rokhlin_reads_kitaev` — **pointwise** Rokhlin = Kitaev in the ONE ℤ₁₆ (the strong unification).
  - `kitaev_generator_is_bordism_generator` — Kitaev ν=1 = `[RP⁴]` (non-vacuous heart).
  - `sm_anomaly_trivial_in_bordism`, `rokhlin_k3_trivial` — SM / smooth-spin at the trivial class.
  - `sm_spin10_count_trivial_in_bordism` — facet 1 (the Spin(10) count = `su5dim` sum) routed
    into the chain from its actual start (SM 16-fermion content → anomaly → bordism).
  - `sixteen_convergence_common_origin` (+ `_substrate`) — the bundled four-facet capstone.
  - **W6**: `smithInflowOfSmithHom` (the `SmithInflow` realized from the Ω₅ substrate + `smithHom`)
    and `sixteen_convergence_common_origin_via_constructed_smith` (the chain SM → Ω₅ → Smith → Ω₄
    built with NO abstract Lean hypothesis — *hypothesis-level*, not a geometric discharge).

Walls still standing (the residual is NOT narrower in the geometric sense): the GEOMETRIC
construction of `Ω₅^{Spin-ℤ₄}` from manifolds + the η-invariant, and the geometric Smith/Dai–Freed
maps, remain Mathlib-absent. W6 builds *thin substrate* analogs; the ℤ₁₆/Lean chain is now
constructed (no abstract binder), but the substrates' *geometric faithfulness* is tracked — and for
Ω₅ that gap is **larger** than the Pin⁺ side (the η invariant is ℤ₁₆-native; `smith_inflow_z16`
registry). Kernel-pure; 0 axiom/0 sorry.
-/

end SKEFTHawking.CommonOrigin
