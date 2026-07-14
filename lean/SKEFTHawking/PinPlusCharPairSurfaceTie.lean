/-
# Phase 5q.H (W-A arm 4) — THE (n, q, surf) BASIS-TIE SUPPORT for `CharPairStrBundled`.

The W-A re-gate round-5 finding `realization-seam-basis-gauge-launders-e8` proved the topological
certificates of the realization seam are collectively gauge-blind: the seam's free enhancement bases
admit a gauge (`killerGauge`) that fixes all topology while mapping the honest anti-diagonal kernel
onto the e₈ kernel. The FIX (this arm) is the **basis tie**: the enhancement `(n, q)` must be DERIVED
from carrier-carried surface data — a genuine `H¹(Σ;ℤ/2)` basis `basis` plus the polar-form tie
`hpolar : q.B(basis a)(basis b) = ⟨a ∪ b, [Σ]⟩` — so gauging the basis forces gauging `q` covariantly
and kernel-vs-form alignment becomes gauge-invariant.

This module banks the two reusable ingredients the strengthened `CharPairStrBundled` witnesses need:

* **§1 — empty-space (co)homology vanishing.** For an `IsEmpty` carrier the singular simplex object is
  empty, so `SingularChain`/`SingularCochain` are subsingletons and `Homology`/`Cohomology` vanish.
  This is what makes the *empty-surface* witnesses (`charPairBundledEmpty`, and the fake-class shape)
  carry a genuine — degenerate but honest — `basis`/`surfClass`/`hpolar`.

* **§2 — the disjoint-union tie split.** `push_pair` reduces a cup-pairing against a pushed-forward
  class to a pairing on the summand via the Kronecker adjunction + cup naturality. `sumBasis` blocks the
  two summand `H¹` bases (through `cohomologyDisjointSumEquiv`) into a single `Fin (nσ + nτ)` basis,
  `sumSurfClass` sums the pushed-forward surface classes, and `sumHpolar` assembles the two component
  polar-form ties into the tie for the `sumStr` bundle `q = (orthSum qσ qτ).reindex finSumFinEquiv`.
  Crucially the whole split rides on FUNCTORIALITY of the pairing (no `Nonempty`/`CompactSpace`
  hypotheses on the surfaces), so it is robust to empty summands (the `σ ⊔ ∅` unit witness).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyDisjointSum
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.BrownInvariant
import SKEFTHawking.PinPlusGMData

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.PinPlusCharPairSurfaceTie

/-! ## §1. Empty-space (co)homology vanishing -/

/-- The singular `n`-simplex object of an `IsEmpty` space is empty (no map from the nonempty
standard simplex). -/
theorem isEmpty_simplex {M : Type} [TopologicalSpace M] [IsEmpty M] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n))) := by
  constructor
  rintro ⟨f⟩
  obtain ⟨x⟩ : Nonempty ↑(SimplexCategory.toTop.obj (SimplexCategory.mk n)) := inferInstance
  exact (‹IsEmpty M›).false (f.hom x)

/-- The mod-2 homology of an `IsEmpty` space vanishes (subsingleton) — the chains are trivial. -/
instance subsingleton_homology {M : Type} [TopologicalSpace M] [IsEmpty M] (n : ℕ) :
    Subsingleton (Homology (TopCat.of M) n) := by
  haveI := isEmpty_simplex (M := M) n
  haveI : Subsingleton (SingularChain (TopCat.of M) n) := inferInstance
  haveI : Subsingleton (cycles (TopCat.of M) n) := inferInstance
  exact (Submodule.Quotient.mk_surjective _).subsingleton

/-- The mod-2 cohomology of an `IsEmpty` space vanishes (subsingleton) — the cochains are trivial. -/
instance subsingleton_cohomology {M : Type} [TopologicalSpace M] [IsEmpty M] (n : ℕ) :
    Subsingleton (Cohomology (TopCat.of M) n) := by
  haveI := isEmpty_simplex (M := M) n
  haveI : Subsingleton (SingularCochain (TopCat.of M) n) := inferInstance
  haveI : Subsingleton (LinearMap.ker (coboundaryₗ (TopCat.of M) n)) := inferInstance
  exact (Submodule.Quotient.mk_surjective _).subsingleton

/-! ## §2. The disjoint-union tie split -/

/-- **The pushforward-pairing split** `⟨a ∪ b, φ₊ z⟩ = ⟨φ*a ∪ φ*b, z⟩` — the Kronecker adjunction
(`kroneckerH_cohomologyPullback`) plus cup naturality (`cohomologyPullback_cupH`). This is what lets
a cup-pairing against a *pushed-forward* surface class descend to a pairing on the summand. -/
theorem push_pair {X Y : TopCat} (φ : C(↑X, ↑Y)) (a b : Cohomology Y 1) (z : Homology X 2) :
    kroneckerH 2 (cupH a b) (Homology.map φ 2 z)
      = kroneckerH 2 (cupH (cohomologyPullback φ 1 a) (cohomologyPullback φ 1 b)) z := by
  rw [← kroneckerH_cohomologyPullback, cohomologyPullback_cupH]

variable {A B : TopCat} {nσ nτ : ℕ}

/-- **The blocked `H¹` basis of the disjoint union** — restrict `H¹(A ⊔ B)` to the two summands
(`cohomologyDisjointSumEquiv`), transport each by its enhancement basis, repackage as a
`Sum`-indexed function, and reindex to `Fin (nσ + nτ)`. -/
noncomputable def sumBasis
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    Cohomology (sumSpace A B) 1 ≃ₗ[ZMod 2] (Fin (nσ + nτ) → ZMod 2) :=
  (cohomologyDisjointSumEquiv A B 1).trans
    ((bσ.prodCongr bτ).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin nσ) (Fin nτ) (ZMod 2) (ZMod 2)).symm.trans
        (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm)))

/-- **The blocked surface class of the disjoint union** — the sum of the two pushed-forward surface
classes `inl₊ zσ + inr₊ zτ` (`0` on the missing summand: robust to empty summands). -/
noncomputable def sumSurfClass (zσ : Homology A 2) (zτ : Homology B 2) :
    Homology (sumSpace A B) 2 :=
  Homology.map (inlMap A B) 2 zσ + Homology.map (inrMap A B) 2 zτ

/-- The de-reindexed blocked basis IS the `Sum.elim` of the two summand-basis images — the
intertwining that makes the `orthSum`-block polar form see the two components. -/
theorem sumBasis_funLeft
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (a : Cohomology (sumSpace A B) 1) :
    LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv (sumBasis bσ bτ a)
      = Sum.elim (bσ (cohomologyPullback (inlMap A B) 1 a))
          (bτ (cohomologyPullback (inrMap A B) 1 a)) := by
  funext i
  rw [LinearMap.funLeft_apply]
  show (sumBasis bσ bτ a) (finSumFinEquiv i) = _
  unfold sumBasis
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply]
  cases i with
  | inl j => rfl
  | inr j => rfl

/-- **THE `sumStr` POLAR-FORM TIE** — the two component ties `hσ`/`hτ` assemble into the tie for the
disjoint-union bundle `q = (orthSum qσ qτ).reindex finSumFinEquiv`, with basis `sumBasis` and class
`sumSurfClass`. Pure functoriality: no `Nonempty`/compactness on the surfaces, so it survives an empty
summand (the unit witness `σ ⊔ ∅`). -/
theorem sumHpolar
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (zσ : Homology A 2) (zτ : Homology B 2)
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (hσ : ∀ a b, qσ.B (bσ a) (bσ b) = kroneckerH 2 (cupH a b) zσ)
    (hτ : ∀ a b, qτ.B (bτ a) (bτ b) = kroneckerH 2 (cupH a b) zτ)
    (a b : Cohomology (sumSpace A B) 1) :
    ((orthSum qσ qτ).reindex finSumFinEquiv).B (sumBasis bσ bτ a) (sumBasis bσ bτ b)
      = kroneckerH 2 (cupH a b) (sumSurfClass zσ zτ) := by
  show (orthSum qσ qτ).B
      (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv (sumBasis bσ bτ a))
      (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv (sumBasis bσ bτ b)) = _
  rw [sumBasis_funLeft, sumBasis_funLeft]
  show qσ.B (bσ (cohomologyPullback (inlMap A B) 1 a)) (bσ (cohomologyPullback (inlMap A B) 1 b))
      + qτ.B (bτ (cohomologyPullback (inrMap A B) 1 a))
          (bτ (cohomologyPullback (inrMap A B) 1 b)) = _
  rw [hσ, hτ, sumSurfClass, map_add, push_pair, push_pair]

/-! ### W-anchored variants — the output types are stated at an ambient `W` DEFEQ to `sumSpace A B`,
so the `charPairBundledSumStr` witness fields (typed at `TopCat.of (σ.surf.sum τ.surf).M`) match
SYNTACTICALLY. This routes the (cheap) TopCat-level `rfl` `W = sumSpace A B` through `▸` INSIDE the
helper, avoiding the expensive `Homology`/`Cohomology`-constructor `isDefEq` at distinct-but-defeq
TopCats that a direct assignment triggers. -/

/-- `sumBasis` re-anchored at an ambient `W = sumSpace A B`. -/
noncomputable def sumBasisW (W : TopCat) (hW : W = sumSpace A B)
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    Cohomology W 1 ≃ₗ[ZMod 2] (Fin (nσ + nτ) → ZMod 2) :=
  hW ▸ sumBasis bσ bτ

/-- `sumSurfClass` re-anchored at an ambient `W = sumSpace A B`. -/
noncomputable def sumSurfClassW (W : TopCat) (hW : W = sumSpace A B)
    (zσ : Homology A 2) (zτ : Homology B 2) : Homology W 2 :=
  hW ▸ sumSurfClass zσ zτ

/-- The `sumStr` polar-form tie re-anchored at an ambient `W = sumSpace A B`. -/
theorem sumHpolarW (W : TopCat) (hW : W = sumSpace A B)
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (zσ : Homology A 2) (zτ : Homology B 2)
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (hσ : ∀ a b, qσ.B (bσ a) (bσ b) = kroneckerH 2 (cupH a b) zσ)
    (hτ : ∀ a b, qτ.B (bτ a) (bτ b) = kroneckerH 2 (cupH a b) zτ)
    (a b : Cohomology W 1) :
    ((orthSum qσ qτ).reindex finSumFinEquiv).B (sumBasisW W hW bσ bτ a) (sumBasisW W hW bσ bτ b)
      = kroneckerH 2 (cupH a b) (sumSurfClassW W hW zσ zτ) := by
  subst hW
  exact sumHpolar bσ bτ zσ zτ qσ qτ hσ hτ a b

end SKEFTHawking.PinPlusCharPairSurfaceTie
