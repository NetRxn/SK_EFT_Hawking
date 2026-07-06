/-
# Phase 5q.H (E1 · integral PD tower) — the dual cochain operator (transpose of a chain map)

Reusable homological infrastructure for the small-chains cohomology surjectivity (`(B)`, the last node of
the integral relative-cohomology Mayer–Vietoris middle exactness): the **ℤ-transpose** `dualCochainInt T` of
an integral chain map `T : Cₙ → Cₘ`, characterised by the Kronecker adjunction
  `⟨dualCochainInt T f, c⟩ = ⟨f, T c⟩`.
It generalises the coboundary (`coboundary = dualCochainInt chainBoundary`, the on-main
`kronecker_coboundary_chainBoundary`), is additive and CONTRAVARIANT-functorial
(`dualCochainInt (S ∘ T) = dualCochainInt T ∘ dualCochainInt S`), and dualises the iterated-subdivision
chain homotopy `1 − Sdᵐ = ∂Dₘ + Dₘ∂` into a cochain homotopy — the mechanism that lifts a `Hom(Q)` cocycle
to `relCochainsInt (U ∪ V)`. Not specific to the MV chase — dualises ANY integral chain map.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.SingularExcisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSubdivisionInt

namespace SKEFTHawking.SingularDualCochainInt

variable {X : TopCat}

/-- The **dual cochain operator** of an integral chain map. For `T : Cₙ → Cₘ`, `dualCochainInt T` sends a
cochain `f ∈ Cochainᵐ` to the cochain `σ ↦ ⟨f, T (single σ 1)⟩ ∈ Cochainⁿ` — the ℤ-transpose of `T` under
the Kronecker pairing (`kronecker_dualCochainInt`). -/
noncomputable def dualCochainInt {n m : ℕ}
    (T : SingularChainInt X n →ₗ[ℤ] SingularChainInt X m) (f : SingularCochainInt X m) :
    SingularCochainInt X n :=
  fun σ => kronecker f (T (Finsupp.single σ 1))

/-- **The transpose adjunction** `⟨dualCochainInt T f, c⟩ = ⟨f, T c⟩` — the defining property. Proved by
`Finsupp` induction on `c`, using linearity of `T` and of the pairing in the chain slot. -/
theorem kronecker_dualCochainInt {n m : ℕ}
    (T : SingularChainInt X n →ₗ[ℤ] SingularChainInt X m) (f : SingularCochainInt X m)
    (c : SingularChainInt X n) :
    kronecker (dualCochainInt T f) c = kronecker f (T c) := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | single_add σ a c' _ _ ih =>
    rw [kronecker_add_right, kronecker_single, map_add, kronecker_add_right, ih,
      show (Finsupp.single σ a : SingularChainInt X n) = a • Finsupp.single σ 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, kronecker_smul_right, dualCochainInt, smul_eq_mul]

/-- **The coboundary is the transpose of the chain boundary**: `dualCochainInt (chainBoundary) = coboundary`
— identifying the on-main `coboundary` as a special case of the general transpose (via the adjunction
`kronecker_coboundary_chainBoundary`). The bridge that lets the dual homotopy speak in terms of `coboundary`. -/
theorem dualCochainInt_chainBoundary {n : ℕ} (f : SingularCochainInt X n) :
    dualCochainInt (chainBoundary X n) f = coboundary X n f := by
  funext σ
  rw [dualCochainInt, ← kronecker_coboundary_chainBoundary, kronecker_single, one_mul]

/-- **The transpose is additive in the cochain**: `dualCochainInt T (f + g) = dualCochainInt T f
+ dualCochainInt T g`. -/
theorem dualCochainInt_add {n m : ℕ}
    (T : SingularChainInt X n →ₗ[ℤ] SingularChainInt X m) (f g : SingularCochainInt X m) :
    dualCochainInt T (f + g) = dualCochainInt T f + dualCochainInt T g := by
  funext σ
  simp only [dualCochainInt, Pi.add_apply, kronecker_add_left]

/-- **The transpose is CONTRAVARIANT-functorial**: `dualCochainInt (T ∘ₗ S) = dualCochainInt S ∘
dualCochainInt T` (dualising a composite reverses order). The tool that dualises a composite chain map
(e.g. an iterated-subdivision / `ρ` chain map) one factor at a time. -/
theorem dualCochainInt_comp {a b c : ℕ} (S : SingularChainInt X a →ₗ[ℤ] SingularChainInt X b)
    (T : SingularChainInt X b →ₗ[ℤ] SingularChainInt X c) (f : SingularCochainInt X c) :
    dualCochainInt (T ∘ₗ S) f = dualCochainInt S (dualCochainInt T f) := by
  funext σ
  rw [dualCochainInt, LinearMap.comp_apply, dualCochainInt, kronecker_dualCochainInt]

/-- The **iterated subdivision homotopy `Dₘ` bundled as a `LinearMap`** — `∑_{i<m} Sdⁱ ∘ D`, a finite sum of
composites of linear maps (`singularDInt` is linear, `singularSdInt` powers are `Module.End`). Agrees with
the on-main function `iterHomotopyInt` (`iterHomotopyIntₗ_apply`), so `dualCochainInt` can transpose it. -/
noncomputable def iterHomotopyIntₗ (X : TopCat) (n m : ℕ) :
    SingularChainInt X n →ₗ[ℤ] SingularChainInt X (n + 1) :=
  ∑ i ∈ Finset.range m, ((singularSdInt X (n + 1)) ^ i) ∘ₗ singularDInt X n

@[simp] theorem iterHomotopyIntₗ_apply (X : TopCat) (n m : ℕ) (c : SingularChainInt X n) :
    iterHomotopyIntₗ X n m c = iterHomotopyInt X n m c := by
  rw [iterHomotopyIntₗ, iterHomotopyInt]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, Module.End.coe_pow]

/-- **The dual iterated-subdivision homotopy, on cocycles** — the mechanism of `(B)`. For a cocycle
`f ∈ Cochain^{n+1}`, `f` and its dual subdivision `(Sdᵐ)*f = dualCochainInt (singularSdInt^m) f` differ by a
coboundary: `f − (Sdᵐ)*f = δ((Dₘ)*f)`. Dualises `iterHomotopyInt_chainHomotopy` (`∂(D'ₘc) + Dₘ∂c = c − Sdᵐc`)
via the transpose adjunction — the `∂D'ₘ` term is killed by the cocycle condition (`⟨f, ∂w⟩ = ⟨δf, w⟩ = 0`).
Since `(Sdᵐ)*f` vanishes on any chain `Sdᵐ` makes small, this is the cohomologous small-representative that
lifts a `Hom(Q)` cocycle to `relCochainsInt (U ∪ V)`. -/
theorem sub_dualSdIterate_eq_coboundary {n : ℕ} (f : SingularCochainInt X (n + 1))
    (hf : coboundary X (n + 1) f = 0) (m : ℕ) :
    f - dualCochainInt ((singularSdInt X (n + 1)) ^ m) f
      = coboundary X n (dualCochainInt (iterHomotopyIntₗ X n m) f) := by
  funext σ
  have hL : (f - dualCochainInt ((singularSdInt X (n + 1)) ^ m) f) σ
      = kronecker f (Finsupp.single σ 1)
        - kronecker f ((⇑(singularSdInt X (n + 1)))^[m] (Finsupp.single σ 1)) := by
    rw [Pi.sub_apply, show f σ = kronecker f (Finsupp.single σ 1) from by rw [kronecker_single, one_mul],
      dualCochainInt, Module.End.coe_pow]
  have hR : coboundary X n (dualCochainInt (iterHomotopyIntₗ X n m) f) σ
      = kronecker f (iterHomotopyInt X n m (chainBoundary X n (Finsupp.single σ 1))) := by
    rw [← dualCochainInt_chainBoundary, dualCochainInt, kronecker_dualCochainInt, iterHomotopyIntₗ_apply]
  rw [hL, hR]
  have hcocy : kronecker f
      (chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m (Finsupp.single σ 1))) = 0 := by
    rw [← kronecker_coboundary_chainBoundary, hf]; simp [kronecker_apply]
  have hhom := iterHomotopyInt_chainHomotopy X m n (Finsupp.single σ 1)
  have hsub : kronecker f (Finsupp.single σ 1)
        - kronecker f ((⇑(singularSdInt X (n + 1)))^[m] (Finsupp.single σ 1))
      = kronecker f
          (Finsupp.single σ 1 - (⇑(singularSdInt X (n + 1)))^[m] (Finsupp.single σ 1)) := by
    simp only [kronecker_eq_linearCombination, map_sub]
  rw [hsub, ← hhom, kronecker_add_right, hcocy, zero_add]

end SKEFTHawking.SingularDualCochainInt
