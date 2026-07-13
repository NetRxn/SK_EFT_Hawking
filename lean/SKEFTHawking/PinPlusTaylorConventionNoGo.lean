/-
# Phase 5q.H (W-A definition gate, re-gate round 2) — ⛔ kernel no-go: the Taylor-leg
END-CONVENTION trap in the v3 design (§2 item 4)

Adversarial RE-GATE findings (Fable vacuity re-attack, 2026-07-13) against
`docs/dev-loops/Phase5qH/W_A_FAITHFUL_INSTANCE_DESIGN.md` §2 (v3), made kernel-checkable.

## The finding — the v3 Taylor/structure-extension leg is convention-critical

v3 §2 item 4 states the structure-extension condition as "classes of `H₁(Σ;ℤ/2)` bounding in `Q`
have `q = 0`", and its self-test verifies only `negBor` (where the joint end-enhancement is
`q ⊕ (−q)` and the cylinder kernel is the anti-diagonal, so ANY sign convention passes). The
statement admits three readings, and the two unverified ones are fatal — BOTH through the honest
(T2, compact, charted) product cylinder itself, so no certificate hardening can block them:

* **Reading (i), plain joint sum** — the enhancement `q_σ ⊕ q_τ` on `H₁(∂Q;ℤ/2)` vanishes on
  `ker(H₁(∂Q) → H₁(Q))`. On the mandatory `cylBor σ : Bor (reflCylinder s) σ σ` every honest
  membrane `Q` with `∂Q = Σ ⊔ Σ` has Lagrangian kernel (half-lives-half-dies), and for the
  design's own headline `Σ = ℝP²` the UNIQUE Lagrangian of `⟨1⟩ ⊕ ⟨1⟩` is the (anti-)diagonal
  `span{(g,g)}`, forcing `q(g) + q(g) = 0` — i.e. `2·q = 0` on the kernel classes of EVERY
  structure (`no_plain_end_pairing_of_cylinder`). The headline enhancement `q(gen) = 1 ∈ ℤ/4`
  has `1 + 1 = 2 ≠ 0` (`odd_enhancement_value_not_two_torsion`), so under reading (i) `cylBor`
  is uninstantiable for every odd structure and the v3 datum admits NO instance containing the
  ℝP⁴/ℝP² witness — the v2 finding-2 (uninstantiable-op) pattern in a new coat.
* **Reading (ii), σ-side-only** — only classes of the σ-end's `H₁(Σ_σ)` that individually bound
  in `Q` are constrained. For every cylinder-like membrane the kernel meets `H₁(Σ_σ) ⊕ 0`
  trivially, so the condition is VACUOUS on `reflCylinder` witnesses: `Bor (reflCylinder s) σ τ`
  becomes inhabited for ARBITRARY `σ, τ` (the other legs inherit exactly as in the v3 self-test),
  and then `mk ⟨s,σ⟩ = mk ⟨s,τ⟩` (`dataBordism_mk_eq_of_cylinder_bor`) — the whole per-manifold
  structure torsor collapses and NO invariant separating same-manifold structures (the ℝP⁴
  `±1 ∈ ℤ/16`, mod-8 shadow `1 ≠ 7 ∈ ℤ/8`, `rp4_brown_values_distinct`) can descend
  (`not_cylinder_bor_of_invariant_ne`). Crucially the T2 fence does NOT block this: the
  collapsing `W` is the honest Hausdorff cylinder (`t2DataBordism_mk_eq_of_cylinder_bor`).
* **Reading (iii), the ONLY correct one** — the τ-end enhancement enters NEGATED: the joint
  enhancement `q_σ ⊕ (−q_τ)` on `H₁(∂Q;ℤ/2)` (per Bor-END, not per boundary component — the
  doubling bordism's two components both sit on the σ-end and stay un-negated, which is exactly
  why the v3 `negBor` self-test cannot distinguish the readings) vanishes on
  `ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))`. Under (iii): `cylBor` (kernel anti-diagonal, `q − q = 0`),
  `negBor` (`(−q) + q = 0`), `symmBor`/`commBor`/`assocBor`/`unitBor`/`addBor`/`revBor` all
  instantiate, and β-invariance of the computed `abk8` is forced (a form vanishing on a
  Lagrangian has Brown invariant 0, so `β(q_σ) − β(q_τ) = 0`).

AMENDMENT (the exact statement fix): v3 item 4 must read
  "the enhancement `q_σ ⊕ (Z4Quadratic.neg q_τ)`, transported to `H₁(∂Q;ℤ/2)` via the boundary
   identification, vanishes on `ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))`."

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/
maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.T2TangentialBordism

namespace SKEFTHawking.PinPlusTaylorConventionNoGo

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.T2TangentialBordism

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-! ## §1. Reading (i) — the plain-joint-sum trap dies on `cylBor` -/

/-- **⛔ No-go (i): a plain (un-negated) end-pairing consequence over the reflexive cylinder
forces every structure's enhancement values 2-torsion.** Let `f` extract any invariant-valued
coordinate of a structure (Design v3: `f σ = q_σ(x₀)` at a cylinder-kernel class `x₀`, e.g. the
`ℝP²` generator, where every honest membrane's kernel is the unique Lagrangian anti-diagonal).
If the datum's `Bor` over `reflCylinder` entails the plain-sum condition `f σ + f τ = 0` — as
v3 §2 item 4 under the plain joint-sum reading does — then the mandatory `cylBor σ₀` forces
`f σ₀ + f σ₀ = 0` for EVERY `σ₀`. -/
theorem no_plain_end_pairing_of_cylinder.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v} [Add A] [Zero A]
    (f : ξ.Mfd s → A)
    (hplain : ∀ σ τ : ξ.Mfd s, ξ.Bor (reflCylinder s) σ τ → f σ + f τ = 0)
    (σ₀ : ξ.Mfd s) : f σ₀ + f σ₀ = 0 :=
  hplain σ₀ σ₀ (ξ.cylBor σ₀)

/-- **⛔ No-go (i), falsifier form**: a datum carrying a structure with a non-2-torsion
enhancement value (the v3 headline: `q(gen) = 1 ∈ ℤ/4` on `Σ = ℝP²`) can have NO plain-sum
end-pairing condition over the reflexive cylinder — under reading (i) of v3 item 4 the design
admits no instance containing the ℝP⁴/ℝP² witness. -/
theorem not_cylinder_plain_pairing_of_odd_value.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v} [Add A] [Zero A]
    (f : ξ.Mfd s → A) {σ₀ : ξ.Mfd s} (hodd : f σ₀ + f σ₀ ≠ 0) :
    ¬ ∀ σ τ : ξ.Mfd s, ξ.Bor (reflCylinder s) σ τ → f σ + f τ = 0 :=
  fun hplain => hodd (no_plain_end_pairing_of_cylinder ξ f hplain σ₀)

/-- The v3 headline enhancement value is NOT 2-torsion: `1 + 1 = 2 ≠ 0` in `ℤ/4` (the odd
`Pin⁻` enhancement `q(gen) = 1` on `ℝP²`, Design v3 §3 item 4 / DG Example 3.17). -/
theorem odd_enhancement_value_not_two_torsion : (1 : ZMod 4) + 1 ≠ 0 := by decide

/-! ## §2. Reading (ii) — the σ-side-only (cylinder-vacuous) reading collapses the torsor
through the HONEST Hausdorff cylinder -/

/-- **⛔ No-go (ii), step 1: any inhabitant of `Bor` over the reflexive cylinder identifies the
two structures' classes.** If the Taylor leg is stated so that reflexive-cylinder witnesses
exist between DIFFERENT structures `σ ≠ τ` on the same manifold (as the σ-side-only reading
permits — the kernel of a cylinder-like membrane meets `H₁(Σ_σ) ⊕ 0` trivially, so the
condition is vacuous while every other v3 leg inherits exactly as in the design's own `negBor`
self-test), the per-manifold structure torsor collapses in the quotient. -/
theorem dataBordism_mk_eq_of_cylinder_bor.{u} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} (σ τ : ξ.Mfd s)
    (h : Nonempty (ξ.Bor (reflCylinder s) σ τ)) :
    DataBordismGrp.mk ξ ⟨s, σ⟩ = DataBordismGrp.mk ξ ⟨s, τ⟩ :=
  DataBordismGrp.mk_eq_of_bordant ξ ⟨reflCylinder s, h⟩

/-- **⛔ No-go (ii), step 2: the T2 fence does NOT block the collapse** — the collapsing bordism
manifold is the honest Hausdorff cylinder `s.M × [0,1]` (T2 whenever the structure certifies its
carrier T2), so the reading-(ii) vacuity survives every per-datum certificate of the v3 design:
only the exact statement of the Taylor leg carries the honesty. -/
theorem t2DataBordism_mk_eq_of_cylinder_bor.{u} (ξ : T2TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} (σ τ : ξ.Mfd s)
    (h : Nonempty (ξ.Bor (reflCylinder s) σ τ)) :
    T2DataBordismGrp.mk ξ ⟨s, σ⟩ = T2DataBordismGrp.mk ξ ⟨s, τ⟩ := by
  refine T2DataBordismGrp.mk_eq_of_bordant ξ ⟨reflCylinder s, ?_, h⟩
  haveI := ξ.t2Str σ
  exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))

/-- **⛔ No-go (ii), falsifier form**: a computed invariant separating two structures on the same
manifold (v3's `abk8` on ℝP⁴'s two `Pin⁺` structures: Brown values `±1 ∈ ℤ/8`) FORBIDS any
reflexive-cylinder `Bor` witness between them. Contrapositively, a Taylor-leg statement that is
vacuous on cylinder witnesses (reading (ii)) makes `abk8` ill-defined on the quotient. -/
theorem not_cylinder_bor_of_invariant_ne.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v}
    (g : DataBordismGrp ξ → A) {σ τ : ξ.Mfd s}
    (hne : g (DataBordismGrp.mk ξ ⟨s, σ⟩) ≠ g (DataBordismGrp.mk ξ ⟨s, τ⟩)) :
    ¬ Nonempty (ξ.Bor (reflCylinder s) σ τ) :=
  fun h => hne (congrArg g (dataBordism_mk_eq_of_cylinder_bor ξ σ τ h))

/-- The two ℝP⁴ `Pin⁺` mod-8 shadows are distinct: `β = 1 ≠ 7 = −1 ∈ ℤ/8` (Witten §2.5:
`P′ = P ⊗ ε` negates the ℤ/16 invariant; DG Example 3.17 for the `ℝP²` Brown values) — the
separation reading (ii) erases. -/
theorem rp4_brown_values_distinct : (1 : ZMod 8) ≠ -1 := by decide

end SKEFTHawking.PinPlusTaylorConventionNoGo
