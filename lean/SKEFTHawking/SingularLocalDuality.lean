import Mathlib
import SKEFTHawking.SingularH0
import SKEFTHawking.SingularRelativeDuality0
import SKEFTHawking.SingularRelativePairing

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4f-b) — the cap–augmentation identity (local PD core)

Toward the local Poincaré-duality isomorphism `D_x : Hⁿ(M|x) → H₀(M)` (`relativeDuality0` at the local
fundamental cycle): the key chain-level identity that linearizes the cap against the augmentation,
  `ε(a ⌢ z) = ⟨a, z⟩`,
for a `k`-cochain `a` and a `k`-chain `z` (the cap lands in `C₀`, `m = 0`). It holds because the front
`k`-face of a `k`-simplex is the simplex itself (`frontFace_zero`), so `capBasis a σ = a(σ)•[backFace σ]`
and the augmentation (coefficient sum) reads off `a(σ)`.

This identity makes the duality map `D_x` post-composed with the augmentation equal to the Kronecker
pairing against the local fundamental cycle — so `D_x`'s injectivity reduces to the relative-UC
injectivity already established (`SingularLocalCohomology`), with no point-class computation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing

namespace SKEFTHawking.SingularLocalDuality

/-- **The front `k`-face of a `k`-simplex is itself** (`q = 0`): `frontIncl k 0 = 𝟙 [k]`, so
`frontFace (q := 0) σ = σ`. The degenerate case of the Alexander–Whitney front face. -/
theorem frontFace_zero {X : TopCat} {k : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + 0)))) :
    frontFace (q := 0) σ = σ := by
  have hid : frontIncl k 0 = 𝟙 (SimplexCategory.mk k) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    rfl
  show (TopCat.toSSet.obj X).map (frontIncl k 0).op σ = σ
  rw [hid]
  simp

/-- **The cap–augmentation identity** `ε(a ⌢ z) = ⟨a, z⟩` for a `k`-cochain `a` and `k`-chain `z`
(the cap lands in `C₀`). On a basis `k`-simplex `σ`, `a ⌢ [σ] = a(frontₖ σ)•[backₒ σ] = a(σ)•[backₒ σ]`
(`frontFace_zero`), and `ε` reads off the coefficient `a(σ)`; summing gives `⟨a, z⟩`. The linearization
of the duality map by the augmentation. -/
theorem augmentation_cap {X : TopCat} {k : ℕ} (a : SingularCochain X k) (z : SingularChain X (k + 0)) :
    augmentation X (cap (m := 0) a z) = kronecker a z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact (map_zero (kroneckerₗ k a)).symm
  | add c d hc hd => rw [map_add, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [cap_single_smul, capBasis, frontFace_zero, map_smul, map_smul, augmentation_single,
        kronecker_single]
      simp only [smul_eq_mul, mul_one]

/-- **The duality–pairing bridge** (chain level): for a relative `(k+1)`-cocycle `a` and an absolute
chain `z` representing a relative cycle, the augmentation of `a ⌢ z` equals the relative Kronecker
pairing of `a` against `[z]`,
  `ε(a ⌢ z) = ⟨a, [z]⟩`.
By `augmentation_cap` (`ε(a ⌢ z) = ⟨a, z⟩` at the absolute-cochain level) and `relKronecker_mk`
(`⟨a, [z]⟩ = ⟨a.1, z⟩`). This identifies the augmentation of the degree-0 duality map
`SingularRelativeDuality0.relativeDuality0` with the relative pairing `relKronecker` — the link by which
`D_x`'s injectivity reduces to the relative-UC injectivity (`SingularLocalCohomology`). -/
theorem augmentation_cap_eq_relKronecker {X : TopCat} (S : Set X) {k : ℕ}
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) (z : SingularChain X (k + 1)) :
    augmentation X (cap (m := 0) a.1.1 z) = relKronecker S a.1 (RelativeChain.mk S (k + 1) z) := by
  rw [relKronecker_mk]
  exact augmentation_cap a.1.1 z

end SKEFTHawking.SingularLocalDuality
