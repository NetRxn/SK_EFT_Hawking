/-
# Phase 5q.H (W-A definition gate) — ⛔ kernel no-gos against the Design-A/C `comp`/`revStr` leg

Adversarial gate findings (Fable vacuity attack, 2026-07-13) against
`docs/dev-loops/Phase5qH/W_A_FAITHFUL_INSTANCE_DESIGN.md` §2 (Design A/C), made kernel-checkable.

## Finding 1 — the comp-twist / cylinder-rigidity trap (`no_comp_twist_of_doubling_rigid`)

Design A/C specifies simultaneously:
* (i) `sumStr` acts componentwise on the `comp`-coordinate of a disjoint union
  (`comp ∈ H¹(·;ℤ/2)`, and `H¹(M ⊔ N) = H¹(M) ⊕ H¹(N)` componentwise);
* (ii) `revStr` twists `comp ↦ comp + w₁(s.M)` (the `P ↦ P ⊗ ε` shadow, Witten §2.5) — a
  NON-trivial shift on non-orientable `s` (`w₁(ℝP⁴) ≠ 0`);
* (iii) `Bor b σ τ` requires the `comp`-coordinates to be **compatible under restriction
  `H¹(W) → H¹(∂-ends)`**. For every product-cylinder bordism (`reflCylinder`,
  `doublingBordism` — the interface's mandatory `cylBor`/`negBor` witnesses) the two boundary
  inclusions `M × {⊥}`, `M × {⊤}` are homotopic in `W = M × [0,1]`, so their `H¹`-restrictions
  are EQUAL maps: any `∃ x ∈ H¹(W)`-style compatibility forces the two end-`comp`s to agree
  ("doubling-rigidity").

These three are **jointly contradictory**: `negBor σ` is a mandatory field inhabiting
`Bor (doublingBordism s) (sumStr (revStr σ) σ) emptyStr`, whose end-components carry
`comp (revStr σ)` and `comp σ`; rigidity forces `comp (revStr σ) = comp σ`, i.e. the twist
vanishes — for EVERY structure, on EVERY manifold. So Design A/C (twist ≠ 0 on ℝP⁴) admits
**no instance**. The theorem is stated abstractly (any comp-projection `f`, any component-wise
`c₂`, any Bor whose doubling witnesses are component-rigid), so it fences every re-statement of
the same shape, not one encoding.

The dual trap (`no_uniform_comp_twist_of_cylinder_rigid`): if the builder instead twists the
compatibility condition itself uniformly (τ-end read off with a `+ δ` correction), the mandatory
`cylBor σ : Bor (reflCylinder s) σ σ` forces `δ = 0`. Between the two: an untwisted restriction
condition kills `negBor`-with-twisted-`revStr`; a uniformly twisted one kills `cylBor`. The only
escapes are (a) dropping the `comp`-twist from `revStr` (then `comp` decouples from conjugation
and becomes gauge, re-opening the mod-8 ceiling), or (b) a per-boundary-component collar/normal
co-orientation datum in `Bor` (NEW structure the design does not have — note the doubling
bordism's two ends are both on the `inl` side of `e`, so the `Sum`-marking CANNOT carry the
distinction).

## Finding 2 — the missing-T2 recursion at the membrane level (`qLevelTripleMembrane`)

Design A/C's `Bor` carries a 3-dimensional characteristic membrane `Q`, encoded (design §2)
"the same injection-onto-image pattern `BordismGroup.lean` uses for `∂W`, one dimension down" —
i.e. a `Bordism`-shaped structure. That pattern does **not** require `T2Space Q`; the
`tripleBordism` construction is dimension-generic, so instantiating it at a 2-dimensional model
(`I = 𝓡 2`) produces a compact charted non-Hausdorff 3-dimensional "membrane" whose boundary is
THREE copies of any closed surface Σ — the kernel-checked seed of Taylor-condition erasure
(the bug-eyed membranes let `H₁(∂Q) → H₁(Q)` kernels be chosen adversarially, so "classes that
bound in `Q` have `q = 0`" loses its teeth: enhancements with different Brown invariants become
Bor-related and the grade is no longer bordism-invariant). The T2 fence on `W`
(`IsT2DataBordant`) does NOT propagate to `Q`: every manifold-typed datum of the carrier needs
its own T2 certificate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/
maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.NonHausdorffBordismCollapse

namespace SKEFTHawking.PinPlusCompTorsorNoGo

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.NonHausdorffBordismCollapse

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-! ## §1. The comp-twist / cylinder-rigidity no-go -/

/-- **⛔ No-go 1a (the untwisted-rigidity trap).** Let `ξ` be ANY tangential datum with a
`comp`-style projection `f : ξ.Mfd s → A` whose disjoint-union behaviour is componentwise
(`c₂ (sumStr σ τ) = (f σ, f τ)`), and suppose the bordism data over the **doubling cylinder**
force the two end-components to agree (as any `∃ x ∈ H¹(W)`-restriction compatibility does,
since the two boundary inclusions of a product cylinder are homotopic). Then the structure
reversal CANNOT move `f`: `f (revStr σ) = f σ` for every `σ`. Applied to Design A/C
(`f = comp`, `A = H¹(s.M;ℤ/2)`, `revStr`-twist `= + w₁ ≠ 0` on ℝP⁴): the design admits no
instance — one of the three specification legs must be dropped. -/
theorem no_comp_twist_of_doubling_rigid.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v}
    (f : ξ.Mfd s → A) (c₂ : ξ.Mfd (s.sum s) → A × A)
    (hsum : ∀ σ τ : ξ.Mfd s, c₂ (ξ.sumStr σ τ) = (f σ, f τ))
    (hrigid : ∀ α : ξ.Mfd (s.sum s),
      ξ.Bor (doublingBordism s) α ξ.emptyStr → (c₂ α).1 = (c₂ α).2)
    (σ : ξ.Mfd s) : f (ξ.revStr σ) = f σ := by
  have h := hrigid _ (ξ.negBor σ)
  rw [hsum] at h
  exact h

/-- **⛔ No-go 1a, falsifier form**: a datum whose reversal genuinely twists a componentwise
`comp`-projection on some structure (Design A/C: `comp (revStr σ) = comp σ + w₁ ≠ comp σ` on
ℝP⁴) can have NO doubling-rigid bordism condition on that projection. -/
theorem not_doubling_rigid_of_comp_twist.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v}
    (f : ξ.Mfd s → A) (c₂ : ξ.Mfd (s.sum s) → A × A)
    (hsum : ∀ σ τ : ξ.Mfd s, c₂ (ξ.sumStr σ τ) = (f σ, f τ))
    {σ : ξ.Mfd s} (htwist : f (ξ.revStr σ) ≠ f σ) :
    ¬ ∀ α : ξ.Mfd (s.sum s),
        ξ.Bor (doublingBordism s) α ξ.emptyStr → (c₂ α).1 = (c₂ α).2 :=
  fun hrigid => htwist (no_comp_twist_of_doubling_rigid ξ f c₂ hsum hrigid σ)

/-- **⛔ No-go 1b (the uniformly-twisted-rigidity trap, the dual failure).** If the builder
instead bakes a uniform twist `δ` into the bordism condition itself (reading the τ-end off with
a `+ δ` correction, so that cylinder witnesses force `f σ = f τ + δ`), the mandatory reflexivity
witness `cylBor σ₀ : Bor (reflCylinder s) σ₀ σ₀` forces `δ = 0`. Combined with No-go 1a: neither
an untwisted nor a uniformly twisted `H¹`-restriction condition can coexist with the
`comp ↦ comp + w₁` reversal — only a per-boundary-component co-orientation datum (absent from
Design A/C, and not recoverable from the `Sum`-marking, since `doublingBordism`'s two ends both
sit on the `inl` side) could carry the twist. -/
theorem no_uniform_comp_twist_of_cylinder_rigid.{u, v} (ξ : TangentialData.{u} X k I)
    {s : SingularManifold.{u} X k I} {A : Type v} [AddGroup A]
    (f : ξ.Mfd s → A) (δ : A)
    (hrigid : ∀ σ τ : ξ.Mfd s, ξ.Bor (reflCylinder s) σ τ → f σ = f τ + δ)
    (σ₀ : ξ.Mfd s) : δ = 0 := by
  have h : f σ₀ + δ = f σ₀ + 0 := by rw [add_zero]; exact (hrigid σ₀ σ₀ (ξ.cylBor σ₀)).symm
  exact add_left_cancel h

/-! ## §2. The missing-T2 recursion at the membrane (`Q`) level -/

/-- **⛔ No-go 2 (the Q-level bug-eyed membrane).** The `Bordism`-shaped encoding proposed for
Design A/C's characteristic membrane `Q` ("the `∂W` injection-onto-image pattern, one dimension
down") admits, for EVERY closed surface-type datum `σ` (at `k = 0`, any 2-dimensional model),
a compact **non-Hausdorff** inhabitant whose boundary is THREE copies of `Σ` — the
`tripleBordism` pathology transported verbatim to the membrane dimension. A `T2Space W` field
on the ambient bordism does not fence this: `Q` is a separate manifold-typed datum and needs
its own `T2Space Q` certificate (and its own genuine fundamental-class anchoring), else the
Taylor-Theorem-1.1 leg of `Bor` is synthetically dischargeable. -/
noncomputable def qLevelTripleMembrane {X : Type*} [TopologicalSpace X]
    {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
    (σ : SingularManifold X 0 I₂) :
    Bordism (I₂.prod (𝓡∂ 1)) ((σ.sum σ).sum σ) emptySM :=
  SKEFTHawking.NonHausdorffBordismCollapse.tripleBordism σ

/-- The bug-eyed membrane is provably non-Hausdorff (for nonempty `Σ`) — the datum the missing
`T2Space Q` field would exclude. -/
theorem qLevelTripleMembrane_not_t2 {X : Type*} [TopologicalSpace X]
    {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
    (σ : SingularManifold X 0 I₂) (m₀ : σ.M) :
    ¬T2Space (qLevelTripleMembrane σ).W :=
  SKEFTHawking.NonHausdorffBordismCollapse.tripleBordism_not_t2 σ m₀

end SKEFTHawking.PinPlusCompTorsorNoGo
