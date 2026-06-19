import Mathlib
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.PoincareDualityWu

/-!
# Phase 5q.F (w₂-foundation, brick 72c-6) — constructing the Poincaré-duality datum from `[M]`

The `PoincareDualityWu.PoincareDual4Mid` datum (the precise Poincaré-duality requirement the Wu class
consumes) carries three fields: a fundamental-class functional `μ : H⁴ → ℤ/2`, finite-dimensionality of
`H²`, and the non-degeneracy of the middle cup pairing. This module discharges those fields from the
constructed fundamental class `[M]` (`SingularFundamentalClass.fundamentalClass`) and the closed-manifold
Poincaré duality being built in this phase.

**This brick builds `μ = ⟨·, [M]⟩`** — the fundamental-class functional, as the Kronecker pairing of a
top-degree cohomology class against `[M]` (`SingularHomologyMod2.kroneckerH`). The finite-dimensionality
and non-degeneracy fields are the subsequent bricks (the cap product `[M] ⌢ ·` and its Poincaré-duality
iso). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.SingularCapHomology

namespace SKEFTHawking.PoincareDualityConstruct

/-- **The fundamental-class functional `μ = ⟨·, [M]⟩ : Hᵐ⁺²(M;ℤ/2) → ℤ/2`** of a closed connected
charted manifold: the Kronecker pairing (`kroneckerH`) of a top-degree cohomology class against the
fundamental class `[M]` (`fundamentalClass`). This is the `PoincareDual4Mid.mu` field (`m = 2`,
`m+2 = 4`); a *constructed* functional, not a hypothesis. -/
noncomputable def fundamentalFunctional {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    Cohomology (TopCat.of M) (m + 2) →ₗ[ZMod 2] ZMod 2 :=
  (kroneckerH (X := TopCat.of M) (m + 2)).flip fundamentalClass

/-- **`μ ω = ⟨ω, [M]⟩`** — the fundamental-class functional evaluates a cohomology class by the
Kronecker pairing against `[M]`. -/
@[simp] theorem fundamentalFunctional_apply {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (ω : Cohomology (TopCat.of M) (m + 2)) :
    fundamentalFunctional (m := m) (M := M) ω
      = kroneckerH (X := TopCat.of M) (m + 2) ω fundamentalClass :=
  rfl

/-! ### The cap–cup adjunction (toward Poincaré-duality non-degeneracy of the cup pairing) -/

/-- **Cap–cup adjunction** `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (chain level): the Kronecker pairing of a cup
product against a chain equals the pairing of the right factor against the cap product. Both sides use
the same Alexander–Whitney front/back split (`a` evaluated on the front `k`-face, `b`/the chain on the
back `l`-face), so on a basis simplex both equal `a(frontₖσ) · b(backₗσ)`. This is the algebraic bridge
from the cup pairing `(a,b) ↦ ⟨a∪b, [M]⟩` to the cap-with-`[M]` duality map — the route to the
`PoincareDual4Mid.nondeg` field once cap descends to homology and `[M] ⌢ ·` is shown to be an iso. -/
theorem kronecker_cup_cap {X : TopCat} {k l : ℕ} (a : SingularCochain X k) (b : SingularCochain X l)
    (c : SingularChain X (k + l)) :
    kronecker (cup a b) c = kronecker b (cap a c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd =>
      rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [cap_single_smul, capBasis, kronecker_single, kronecker_smul_right, kronecker_smul_right,
        kronecker_single, cup_apply]
      simp only [smul_eq_mul]; ring

/-! ### Universal-coefficients fact (over ℤ/2): the Kronecker pairing is non-degenerate in homology -/

/-- **Every chain functional is `kronecker` of a cochain** (the dual of `Finsupp` is the full function
space): `φ = ⟨f, ·⟩` for `f σ = φ (single σ 1)`. -/
theorem exists_cochain_of_functional {X : TopCat} {n : ℕ}
    (φ : SingularChain X n →ₗ[ZMod 2] ZMod 2) :
    ∃ f : SingularCochain X n, ∀ c : SingularChain X n, kronecker f c = φ c := by
  refine ⟨fun σ => φ (Finsupp.single σ 1), fun c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp [kronecker_apply]
  | add c d hc hd => rw [kronecker_add_right, map_add, hc, hd]
  | single σ s =>
      rw [kronecker_single,
        show Finsupp.single σ s = s • Finsupp.single σ (1 : ZMod 2) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one],
        map_smul, smul_eq_mul]

/-- **The Kronecker pairing is non-degenerate in the homology argument** (universal coefficients over
the field `ℤ/2`): a homology class `β` pairing to `0` with every cohomology class is `0`. If `β = [z] ≠ 0`
then `z` is a cycle not a boundary, so (over a field, `Submodule.exists_le_ker_of_notMem`) a functional
`φ` separates `z` from the boundaries; `φ = ⟨f, ·⟩` for a cochain `f` (`exists_cochain_of_functional`),
and `f` is a cocycle (`δf σ = ⟨f, ∂σ⟩ = φ(∂σ) = 0`), giving `⟨[f], β⟩ = φ(z) ≠ 0` — a contradiction. The
route to `PoincareDual4Mid.nondeg`. -/
theorem homology_eq_zero_of_kroneckerH {X : TopCat} (n : ℕ) (β : Homology X n)
    (h : ∀ ω : Cohomology X n, kroneckerH (X := X) n ω β = 0) : β = 0 := by
  by_contra hβ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  have hznb : z.1 ∉ boundaries X n := by
    intro hz
    exact hβ ((Submodule.Quotient.mk_eq_zero _).mpr hz)
  obtain ⟨φ, hφv, hφker⟩ := Submodule.exists_le_ker_of_notMem hznb
  obtain ⟨f, hf⟩ := exists_cochain_of_functional φ
  -- `f` is a cocycle: `δf σ = ⟨f, ∂σ⟩ = φ(∂σ) = 0` (`∂σ ∈ boundaries ≤ ker φ`).
  have hfcocycle : coboundaryₗ X n f = 0 := by
    ext σ
    have hbb : boundaryBasis X n σ ∈ boundaries X n :=
      ⟨Finsupp.single σ 1, chainBoundary_single X n σ⟩
    show coboundary X n f σ = 0
    rw [← kronecker_boundaryBasis f σ, hf]
    exact LinearMap.mem_ker.mp (hφker hbb)
  -- contradiction: `⟨[f], β⟩ = φ(z) ≠ 0`.
  have hc := h (Submodule.Quotient.mk ⟨f, hfcocycle⟩)
  rw [kroneckerH_mk_mk, hf] at hc
  exact hφv hc

/-! ### The descended cap–cup adjunction with `[M]` -/

/-- **`cupH24` on representatives** `[fa] ∪ [gc] = [fa ⌣ gc]`. -/
theorem cupH24_mk_mk {X : TopCat} (fc gc : LinearMap.ker (coboundaryₗ X 2)) :
    cupH24 (Submodule.Quotient.mk fc) (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) :=
  cupRightH24_apply_mk fc gc

/-- **The descended cap–cup adjunction with `[M]`** (`m = 2`, 4-manifold): `μ(a ∪ b) = ⟨b, a ⌢ [M]⟩`,
the cohomology-level form of `kronecker_cup_cap` evaluated against the fundamental class. The bridge from
the cup pairing `(a,b) ↦ ⟨a∪b, [M]⟩` to the duality map `a ⌢ [M]` — the algebraic heart of
`PoincareDual4Mid.nondeg` (combined with the UC fact `homology_eq_zero_of_kroneckerH` and the PD-injectivity
of `a ↦ a ⌢ [M]`). -/
theorem fundamentalFunctional_cupH24 {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (a b : Cohomology (TopCat.of M) 2) :
    fundamentalFunctional (m := 2) (M := M) (cupH24 a b)
      = kroneckerH (X := TopCat.of M) 2 b
        (capH 2 1 a (fundamentalClass (m := 2) (M := M))) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zM, hzM⟩ := Submodule.Quotient.mk_surjective _ (fundamentalClass (m := 2) (M := M))
  rw [fundamentalFunctional_apply, ← hzM]
  simp only [cupH24_mk_mk, kroneckerH_mk_mk]
  exact kronecker_cup_cap fa.1 fb.1 zM.1

/-- **`PoincareDual4Mid.nondeg` reduces to PD-injectivity of the duality map** (`m = 2`): if
`a ↦ a ⌢ [M] : H² → H₂` is injective, the middle cup pairing `(a,b) ↦ ⟨a∪b, [M]⟩` is non-degenerate.
A class `a` with `⟨a∪b, [M]⟩ = 0` for all `b` has `⟨b, a⌢[M]⟩ = 0` for all `b` (adjunction
`fundamentalFunctional_cupH24`), so `a⌢[M] = 0` (universal coefficients `homology_eq_zero_of_kroneckerH`),
so `a = 0` (PD-injectivity). This isolates the remaining `PoincareDual4Mid.nondeg` obligation to exactly
the Poincaré-duality injectivity of `· ⌢ [M]` (the local-global cap-iso theorem). -/
theorem nondeg_of_duality_injective {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hPD : Function.Injective fun a : Cohomology (TopCat.of M) 2 =>
      capH 2 1 a (fundamentalClass (m := 2) (M := M))) :
    Function.Injective
      ⇑((cupH24 (X := TopCat.of M)).compr₂ (fundamentalFunctional (m := 2) (M := M))) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine hPD ?_
  show capH 2 1 a (fundamentalClass (m := 2) (M := M))
    = capH 2 1 0 (fundamentalClass (m := 2) (M := M))
  rw [map_zero, LinearMap.zero_apply]
  refine homology_eq_zero_of_kroneckerH 2 _ (fun ω => ?_)
  rw [← fundamentalFunctional_cupH24]
  exact LinearMap.congr_fun ha ω

end SKEFTHawking.PoincareDualityConstruct
