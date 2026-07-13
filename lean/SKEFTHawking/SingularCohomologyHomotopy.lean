/-
# Phase 5q.H (W-A.1e cyl-1) — homotopy invariance of singular `ℤ/2` COHOMOLOGY

The cohomology-side companion to `SingularHomotopyInvariance` (which proves homotopy invariance of
singular `ℤ/2` **homology** via the prism operator). The project's cohomology functor
(`SingularCohomologyFunctoriality.cohomologyPullback`) previously had functoriality + a
*homeomorphism*-level equivalence (`cohomologyHomeoEquiv`) only — nothing for a general homotopy
equivalence. This module supplies that missing piece, and it does so WITHOUT re-dualizing the prism:
it bootstraps directly off the already-proven homology homotopy invariance through the
Kronecker adjunction and mod-2 universal-coefficients non-degeneracy.

**The bootstrap.** For homotopic `f, g : X → Y` (the two ends of a homotopy `H`), the difference of
cohomology pullbacks `f* ω − g* ω ∈ Hⁿ⁺¹(X)` pairs to zero against every `β ∈ Hₙ₊₁(X)`: by the
Kronecker adjunction `⟨φ*ω, β⟩ = ⟨ω, φ_*β⟩` (`kroneckerH_cohomologyPullback`) the pairing becomes
`⟨ω, f_*β − g_*β⟩`, and `f_* = g_*` on homology (`Homology.map_slice_eq`, the prism theorem) makes it
vanish. Mod-2 universal coefficients (`cohomology_eq_zero_of_kroneckerH`, the injective half that is
free in-tree) then forces `f* ω − g* ω = 0`. No new geometry, no new prism dualization.

From that core equality (`cohomologyPullback_slice_eq`) the standard corollaries follow by pure
functoriality (`cohomologyPullback_comp` / `cohomologyPullback_id`): homotopic maps induce equal
pullbacks (`cohomologyPullback_eq_of_homotopic`), a homotopy equivalence induces a bijection
(`cohomologyPullback_bijective_of_homotopyEquiv`) / iso (`cohomologyHomotopyEquiv`), the identity-
composite special case (`cohomologyPullback_bijective_of_comp_id`), and finite-dimensionality
transfer across a homotopy equivalence (`finiteDimensional_cohomology_of_homotopyEquiv`) — the
absolute-side enabler for cylinders `W = Σ × [0,1]` (`H^{k}(Σ × I) ≅ H^{k}(Σ)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularProdContractibleInt

namespace SKEFTHawking.SingularCohomologyHomotopy

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularUniversalCoeff
open SKEFTHawking.SingularProdContractibleInt

/-- **The two slices of a homotopy induce equal cohomology pullbacks** (degree `≥ 1`). The
cohomology-side mirror of `Homology.map_slice_eq`, proved by pairing the difference against every
homology class: `⟨(slice H 1)*ω − (slice H 0)*ω, β⟩ = ⟨ω, (slice H 1)_*β − (slice H 0)_*β⟩`
(Kronecker adjunction), which vanishes because `(slice H 1)_* = (slice H 0)_*` on `Hₙ₊₁`
(`Homology.map_slice_eq`); mod-2 universal coefficients then forces the cohomology difference to
`0`. -/
theorem cohomologyPullback_slice_eq {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ) :
    cohomologyPullback (slice H 1) (n + 1) = cohomologyPullback (slice H 0) (n + 1) := by
  refine LinearMap.ext fun ω => ?_
  rw [← sub_eq_zero]
  refine cohomology_eq_zero_of_kroneckerH n _ (fun β => ?_)
  rw [map_sub, LinearMap.sub_apply, kroneckerH_cohomologyPullback, kroneckerH_cohomologyPullback,
    Homology.map_slice_eq]
  exact sub_self _

/-- **Homotopic maps induce equal maps on cohomology** (degree `≥ 1`): if `f` and `g` are the two
ends of a homotopy `H` then `Hⁿ⁺¹(f) = Hⁿ⁺¹(g)` (contravariant). The cohomology mirror of
`Homology.map_eq_of_homotopic`. -/
theorem cohomologyPullback_eq_of_homotopic {X Y : TopCat} {f g : C(↑X, ↑Y)}
    (H : C(↑X × unitInterval, ↑Y)) (h0 : slice H 0 = f) (h1 : slice H 1 = g) (n : ℕ) :
    cohomologyPullback f (n + 1) = cohomologyPullback g (n + 1) := by
  rw [← h0, ← h1]
  exact (cohomologyPullback_slice_eq H n).symm

/-- **A homotopy equivalence induces an isomorphism on cohomology** (degree `≥ 1`): given
`f : X → Y`, `g : Y → X` with `g ∘ f ≃ id_X` and `f ∘ g ≃ id_Y` (witnessed by homotopies), the
pullback `f* : Hⁿ⁺¹(Y) → Hⁿ⁺¹(X)` is bijective. The cohomology mirror of
`Homology.map_bijective_of_homotopyEquiv` (contravariant, so `g* = f*⁻¹`). -/
theorem cohomologyPullback_bijective_of_homotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (cohomologyPullback f (n + 1)) := by
  have hX : (cohomologyPullback f (n + 1)).comp (cohomologyPullback g (n + 1)) = LinearMap.id := by
    rw [← cohomologyPullback_comp, cohomologyPullback_eq_of_homotopic Hgf hgf0 hgf1,
      cohomologyPullback_id]
  have hY : (cohomologyPullback g (n + 1)).comp (cohomologyPullback f (n + 1)) = LinearMap.id := by
    rw [← cohomologyPullback_comp, cohomologyPullback_eq_of_homotopic Hfg hfg0 hfg1,
      cohomologyPullback_id]
  have hL : Function.LeftInverse (cohomologyPullback g (n + 1)) (cohomologyPullback f (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hY, LinearMap.id_apply]
  have hR : Function.RightInverse (cohomologyPullback g (n + 1)) (cohomologyPullback f (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hX, LinearMap.id_apply]
  exact ⟨hL.injective, hR.surjective⟩

/-- **A pair of maps with identity composites** (e.g. the two halves of a homeomorphism, or a
strong deformation retract with a strict section) induces an isomorphism on `Hⁿ⁺¹`. Special case of
`cohomologyPullback_bijective_of_homotopyEquiv` with the constant (projection) homotopies. -/
theorem cohomologyPullback_bijective_of_comp_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (cohomologyPullback f (n + 1)) :=
  cohomologyPullback_bijective_of_homotopyEquiv f g ⟨fun p => p.1, continuous_fst⟩
    (by rw [hgf]; exact ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
    ⟨fun p => p.1, continuous_fst⟩
    (by rw [hfg]; exact ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n

/-- **The cohomology iso of a homotopy equivalence** `Hⁿ⁺¹(Y) ≃ₗ Hⁿ⁺¹(X)` (contravariant),
packaged from `cohomologyPullback_bijective_of_homotopyEquiv`. -/
noncomputable def cohomologyHomotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Cohomology Y (n + 1) ≃ₗ[ZMod 2] Cohomology X (n + 1) :=
  LinearEquiv.ofBijective (cohomologyPullback f (n + 1))
    (cohomologyPullback_bijective_of_homotopyEquiv f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 n)

/-- **Finite-dimensionality transfers across a homotopy equivalence** (degree `≥ 1`): if
`Hⁿ⁺¹(Y)` is finite-dimensional and `f : X → Y` is a homotopy equivalence (witnessed by `g` and the
two homotopies), then `Hⁿ⁺¹(X)` is finite-dimensional. For the cylinder `W = Σ × [0,1]` with `f` the
projection `Σ × I → Σ` this is the absolute-side `findim` enabler `H^{k}(Σ × I) ≅ H^{k}(Σ)`. -/
theorem finiteDimensional_cohomology_of_homotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Cohomology Y (n + 1))) :
    FiniteDimensional (ZMod 2) (Cohomology X (n + 1)) :=
  haveI := h
  (cohomologyHomotopyEquiv f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 n).finiteDimensional

/-! ## §2. The contractible-factor collapse (the cylinder absolute cohomology)

The mod-2 cohomology mirror of the integral primitives
`SingularProdContractibleInt.prodFst_bijectiveInt` / `prodContractibleEquivInt`, reusing their
coefficient-agnostic projection/section/homotopy topology (`prodFst`, `prodSect`, `prodHomotopy`,
`constHomotopy` and their slice lemmas) and this module's homotopy invariance. For a cylinder
`W = M × [0,1]` (factor `C = TopCat.of unitInterval`, `unitInterval := Set.Icc (0:ℝ) 1` — the in-tree
bordism cylinder base), these give `H^{k}(M) ≅ H^{k}(M × I)` and its `findim` transfer — the concrete
absolute-side content of the cylinder trio's `findimAbs`, dimension-agnostic in `M`. -/

/-- **The first-factor projection is a cohomology isomorphism (bijective)** in every positive degree
when the factor `C` carries a contraction. Contravariant mirror of `prodFst_bijectiveInt` — it is
`prodFst*` (the pullback) that is bijective. -/
theorem prodFst_cohomology_bijective (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Function.Bijective (cohomologyPullback (prodFst Y C) (n + 1)) :=
  cohomologyPullback_bijective_of_homotopyEquiv (prodFst Y C) (prodSect Y C c₀)
    (prodHomotopy Y C H) (slice_prodHomotopy_zero Y C c₀ H h1) (slice_prodHomotopy_one Y C H h0)
    (constHomotopy Y) ((slice_constHomotopy Y 0).trans (prodFst_comp_prodSect Y C c₀).symm)
    (slice_constHomotopy Y 1) n

/-- **The contractible-factor cohomology collapse** `Hⁿ⁺¹(Y) ≃ₗ[ZMod 2] Hⁿ⁺¹(Y × C)` (contravariant
mirror of `prodContractibleEquivInt`). For a cylinder `W = M × [0,1]` this is `Hⁿ⁺¹(M) ≅ Hⁿ⁺¹(W)` —
the concrete absolute-side identification of mission step 1, dimension-agnostic in `M`. -/
noncomputable def prodContractibleCohomologyEquiv (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Cohomology Y (n + 1) ≃ₗ[ZMod 2] Cohomology (ProdSp Y C) (n + 1) :=
  LinearEquiv.ofBijective (cohomologyPullback (prodFst Y C) (n + 1))
    (prodFst_cohomology_bijective Y C c₀ H h0 h1 n)

/-- **Finite-dimensionality of the cylinder's absolute cohomology from the base**: if `Hⁿ⁺¹(Y)` is
finite-dimensional and the factor `C` is contractible, then `Hⁿ⁺¹(Y × C)` is finite-dimensional —
the `findimAbs` enabler for `W = M × [0,1]` (`findim H^{k}(M) ⟹ findim H^{k}(M × I)`). -/
theorem finiteDimensional_cohomology_prodContractible (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Cohomology Y (n + 1))) :
    FiniteDimensional (ZMod 2) (Cohomology (ProdSp Y C) (n + 1)) :=
  haveI := h
  (prodContractibleCohomologyEquiv Y C c₀ H h0 h1 n).finiteDimensional

end SKEFTHawking.SingularCohomologyHomotopy
