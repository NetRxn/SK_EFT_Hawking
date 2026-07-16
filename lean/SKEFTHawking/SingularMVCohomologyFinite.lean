/-
# Phase 5q.H close-out — THE MV/LES COHOMOLOGY FINITE-DIMENSIONALITY OPENER (carrier-agnostic bricks)

The capstone `CapstoneAmbientSupply` row (`PinPlusTraceCapstoneInhabit.lean`) carries four
finite-dimensionality atoms — `findimAbs14`/`findimAbs23` (`H¹(W)`, `H²(W)` finite-dim) and
`findimRel14`/`findimRel23` (`H⁴(W,∂W)`, `H³(W,∂W)` finite-dim). This module banks the GENERAL,
carrier-agnostic exact-sequence bricks that reduce each of the four to piece-wise (co)homology
finiteness, ready to fire on the two-piece MV cover `W = B ∪ Ha` of any carrier.

## The four bricks (all kernel-pure, general in the carrier `X : TopCat`)

* **`finiteDimensional_of_exact`** — the middle `B` of a 3-term exact `A →f B →g C` is finite-dim as
  soon as `A` and `C` are (`ker g = im f` a quotient-image of `A`; `B ⧸ ker g ≅ im g ⊆ C`; then
  `Module.Finite.of_submodule_quotient`). The linear-algebra engine of the two sandwiches below.
* **`finiteDimensional_cohomology_of_homology`** — `Hᵏ(X)` finite-dim ⟸ `Hₖ(X)` finite-dim, via the
  absolute perfect Kronecker pairing `kroneckerHEquiv : Hᵏ(X) ≃ (Hₖ(X))^*` (mod-2 field UC, no
  finite-dim hypothesis on the pairing itself). The absolute-cohomology enabler for `findimAbs`.
* **`finiteDimensional_relativeCohomology_of_relativeHomology`** — `Hᵏ(X,S)` finite-dim ⟸ `Hₖ(X,S)`
  finite-dim, via `relKroneckerHEquiv` (the relative UC pairing). The relative-cohomology enabler for
  `findimRel` (reduces the deep relative-cohomology side to the tractable relative-HOMOLOGY side).
* **`finiteDimensional_homology_of_mv_cover`** — `Hₙ₊₁(X)` finite-dim from `Hₙ₊₁(A)`, `Hₙ₊₁(B)` and
  `Hₙ(A∩B)` finite-dim, for an interior-cover `A ∪ B` (`mv_exact_ambient` — exactness at `Hₙ₊₁(X)`
  of `Hₙ₊₁(A)⊕Hₙ₊₁(B) →(mvHomSum) Hₙ₊₁(X) →(mvDelta) Hₙ(A∩B)` — fed to `finiteDimensional_of_exact`).
  The two-piece-cover absolute-homology brick.
* **`finiteDimensional_relativeHomology_of_pair`** — `Hₙ₊₁(X,S)` finite-dim from `Hₙ₊₁(X)` and `Hₙ(S)`
  finite-dim (`exact_homProj_connecting` — exactness at `Hₙ₊₁(X,S)` of
  `Hₙ₊₁(X) →(j_*) Hₙ₊₁(X,S) →(δ) Hₙ(S)` — fed to `finiteDimensional_of_exact`). The pair-LES sandwich,
  general in `(X,S)`.

Composed (`findimAbs` = cohomology-of-homology ∘ mv-cover; `findimRel` = relCohomology-of-relHomology
∘ pair-sandwich ∘ mv-cover), these reduce the capstone's four cohomology-finiteness atoms to a
transparent row of piece-homology finiteness facts (`H_*(B)`, `H_*(Ha)`, `H_*(B∩Ha)`, `H_*(∂W)`) plus
the MV interior cover — the genuinely-geometric inputs (`B ≃ M` closed-manifold Betti, `Ha ≃ D⁵`
contractible, `B∩Ha ≃` seam). No carrier internals are touched: every brick is stated for a general
`X : TopCat`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularRelativeKroneckerEquiv
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularPairLES

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularRelativeKroneckerEquiv
open SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularMVCohomologyFinite

noncomputable section

variable {X : TopCat}

/-! ## §1. The linear-algebra engine — the middle of a 3-term exact sequence. -/

/-- **The middle of a 3-term exact sequence is finite-dimensional** when both ends are: for
`f : A →ₗ B`, `g : B →ₗ C` with `Function.Exact f g`, `A` and `C` finite-dimensional force `B`
finite-dimensional (`ker g = im f` is a quotient-image of `A`; `B ⧸ ker g ≅ im g ⊆ C`;
`Module.Finite.of_submodule_quotient`). The engine of both MV sandwiches below. -/
theorem finiteDimensional_of_exact {A B C : Type*}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup C] [Module (ZMod 2) C]
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) C]
    {f : A →ₗ[ZMod 2] B} {g : B →ₗ[ZMod 2] C} (hexact : Function.Exact f g) :
    FiniteDimensional (ZMod 2) B := by
  haveI hker : FiniteDimensional (ZMod 2) (LinearMap.ker g) := by
    rw [hexact.linearMap_ker_eq]
    exact (f.quotKerEquivRange).finiteDimensional
  haveI hquot : FiniteDimensional (ZMod 2) (B ⧸ LinearMap.ker g) :=
    (g.quotKerEquivRange).symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-! ## §2. The universal-coefficient enablers — cohomology finiteness from homology finiteness. -/

/-- **Absolute cohomology finite-dimensionality from absolute homology's** (mod-2 field UC): `Hᵏ(X)`
is finite-dimensional as soon as `Hₖ(X)` is, because the absolute perfect Kronecker pairing
`kroneckerHEquiv` identifies `Hᵏ(X)` with the (finite-dimensional) dual of `Hₖ(X)`. The
`findimAbs`-shrinking lemma: absolute cohomology → absolute homology. -/
theorem finiteDimensional_cohomology_of_homology (N : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology X (N + 1))) :
    FiniteDimensional (ZMod 2) (Cohomology X (N + 1)) := by
  haveI := h
  exact (kroneckerHEquiv (X := X) N).symm.finiteDimensional

/-- **Relative cohomology finite-dimensionality from relative homology's** (mod-2 field UC): `Hᵏ(X,S)`
is finite-dimensional as soon as `Hₖ(X,S)` is, via the relative Kronecker pairing `relKroneckerHEquiv`.
The `findimRel`-shrinking lemma: relative cohomology → relative homology. -/
theorem finiteDimensional_relativeCohomology_of_relativeHomology {S : Set ↑X} (N : ℕ)
    (h : FiniteDimensional (ZMod 2) (RelativeHomology (X := X) S (N + 1))) :
    FiniteDimensional (ZMod 2) (RelativeCohomology (X := X) S (N + 1)) := by
  haveI := h
  exact (relKroneckerHEquiv S N).symm.finiteDimensional

/-! ## §3. The two-piece MV cover — absolute homology finiteness. -/

/-- **The two-piece MV absolute-homology finiteness brick.** For an interior-cover `A ∪ B` of `X`
(`⋃ interior = univ`), `Hₙ₊₁(X)` is finite-dimensional from `Hₙ₊₁(A)`, `Hₙ₊₁(B)` and `Hₙ(A∩B)`
finite-dimensional, by exactness at `Hₙ₊₁(X)` of the Mayer–Vietoris LES
`Hₙ₊₁(A)⊕Hₙ₊₁(B) →(mvHomSum) Hₙ₊₁(X) →(mvDelta) Hₙ(A∩B)` (`mv_exact_ambient`) fed to
`finiteDimensional_of_exact`. -/
theorem finiteDimensional_homology_of_mv_cover (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (hA : FiniteDimensional (ZMod 2) (Homology (sub A) (n + 1)))
    (hB : FiniteDimensional (ZMod 2) (Homology (sub B) (n + 1)))
    (hAB : FiniteDimensional (ZMod 2) (Homology (sub (A ∩ B)) n)) :
    FiniteDimensional (ZMod 2) (Homology X (n + 1)) := by
  haveI := hA; haveI := hB; haveI := hAB
  exact finiteDimensional_of_exact (mv_exact_ambient A B n hcov)

/-! ## §4. The pair-LES sandwich — relative homology finiteness. -/

/-- **The pair-LES relative-homology finiteness brick.** `Hₙ₊₁(X,S)` is finite-dimensional from
`Hₙ₊₁(X)` and `Hₙ(S)` finite-dimensional, by exactness at `Hₙ₊₁(X,S)` of the pair LES
`Hₙ₊₁(X) →(j_*) Hₙ₊₁(X,S) →(δ) Hₙ(S)` (`exact_homProj_connecting`) fed to `finiteDimensional_of_exact`.
General in `(X,S)`. -/
theorem finiteDimensional_relativeHomology_of_pair (S : Set ↑X) (n : ℕ)
    (hW : FiniteDimensional (ZMod 2) (Homology X (n + 1)))
    (hBd : FiniteDimensional (ZMod 2) (Homology (sub S) n)) :
    FiniteDimensional (ZMod 2) (RelativeHomology (X := X) S (n + 1)) := by
  haveI := hW; haveI := hBd
  exact finiteDimensional_of_exact (exact_homProj_connecting S n)

end

end SKEFTHawking.SingularMVCohomologyFinite
