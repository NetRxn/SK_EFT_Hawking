/-
# Phase 5q.H — the integral orientation datum from FREE, NONTRIVIAL top integral homology

`IntOrientationMod2Lift` reduced `Nonempty (IntOrientation M)` to a single sharp condition
(`nonempty_intOrientation_iff_mem_range`): the mod-2 fundamental class `[M]₂` must lie in the range
of the reduction `redHomology M 4`. Its §1 sufficient criterion routed that through
2-torsion-freeness of `H₃(M;ℤ)` (which makes `redHomology` *surjective*). That is not the only
route, and for the welded `K3` carrier it is the wrong one — 2-torsion-freeness of `H₃` is exactly
the open `orientInput` residual.

This module supplies the **degree-4 route**, which needs nothing about `H₃` at all:

> `H₄(M;ℤ)` free and nontrivial  ⟹  `Nonempty (IntOrientation M)`

for a closed **connected** charted 4-manifold `M`. Three ambient-generic ingredients, none of them
about `M`'s middle homology:

* **§1** — a top class that is not 2-divisible has NONZERO mod-2 reduction. This is the
  contrapositive of the unconditional kernel bound
  `SphereProdHTwoMod2.exists_two_smul_of_redHomology_eq_zero` (`ker (redHomology (n+1)) ⊆ 2·Hₙ₊₁`).
  Note the direction: the *surjectivity* half of that module's rank-UCT core needs 2-torsion-freeness
  of `Hₙ`, but the *kernel* half — the half used here — is hypothesis-free.
* **§2** — a nontrivial free `ℤ`-module has a non-2-divisible element (a basis vector: its own
  coordinate would have to be `2k = 1`).
* **§3** — on a closed **connected** charted `(m+2)`-manifold, every NONZERO mod-2 top class **is**
  the fundamental class, because `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2` on the nose
  (`SingularFundamentalClass.localDegree_bijective`, Hatcher 3.26, already in tree) and `ℤ/2` has a
  unique nonzero element.

Chaining them (§4): a basis vector `c ∈ H₄(M;ℤ)` reduces to a nonzero class, which therefore IS
`[M]₂`, which therefore lies in the range of `redHomology`, which by
`nonempty_intOrientation_iff_mem_range` IS the orientation datum.

**Why this is the sharp shape.** The hypotheses are exactly the classical statement "a closed
connected 4-manifold is orientable iff `H₄ ≅ ℤ`": the theorem cannot be vacuous (§5 fires it at the
in-tree `S⁴` witness) and cannot be trivial (for a closed connected NON-orientable 4-manifold
`H₄(M;ℤ) = 0`, so `Nontrivial` fails — as it must, since `IntOrientation` is then empty by
`nonempty_intOrientation_iff_mem_range` together with `fundamentalClass_ne_zero`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationMod2Lift
import SKEFTHawking.SingularFundamentalClassExist

namespace SKEFTHawking.IntOrientationFreeTopHomology

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFundamentalClass (fundamentalClass localDegree localDegree_bijective
  localDegree_fundamentalClass)

/-! ## §1. A non-2-divisible integral class has nonzero mod-2 reduction -/

/-- **Non-2-divisible ⟹ nonzero mod 2.** The contrapositive of the *unconditional* half of the
rank-UCT core: `SphereProdHTwoMod2.exists_two_smul_of_redHomology_eq_zero` says the kernel of
`redHomology X (n+1)` is contained in `2 · Hₙ₊₁(X;ℤ)`, with no hypothesis on `Hₙ`. So any class that
is not twice something survives the reduction. -/
theorem redHomology_ne_zero_of_not_two_smul {X : TopCat} (n : ℕ) (c : Homology X (n + 1))
    (hc : ∀ d : Homology X (n + 1), c ≠ (2 : ℤ) • d) : redHomology X (n + 1) c ≠ 0 := by
  intro h
  obtain ⟨d, hd⟩ := SKEFTHawking.SphereProdHTwoMod2.exists_two_smul_of_redHomology_eq_zero n c h
  exact hc d hd

/-! ## §2. A nontrivial free `ℤ`-module has a non-2-divisible element -/

/-- **A basis vector of a nontrivial free `ℤ`-module is not 2-divisible.** If `b i = 2 • d` then
comparing `i`-th coordinates gives `1 = 2 * (b.repr d) i` in `ℤ`, impossible by parity. The index `i`
is produced from the support of the coordinate vector of any nonzero element, which exists by
`Nontrivial`. -/
theorem exists_not_two_smul {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Nontrivial N] :
    ∃ c : N, ∀ d : N, c ≠ (2 : ℤ) • d := by
  classical
  set b := Module.Free.chooseBasis ℤ N with hb
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hrx : b.repr x ≠ 0 := fun h => hx (by simpa using congrArg b.repr.symm h)
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrx
  refine ⟨b i, fun d hd => ?_⟩
  have hcoord := congrArg (fun y => (b.repr y) i) hd
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
    smul_eq_mul] at hcoord
  omega

/-! ## §3. On a closed connected manifold every nonzero mod-2 top class is `[M]₂` -/

/-- **`Hₘ₊₂(M;ℤ/2) ≅ ℤ/2` has a unique nonzero element, and it is the fundamental class.** The
local-degree map `Φ_{x₀}` is bijective on a closed connected charted manifold
(`SingularFundamentalClass.localDegree_bijective`, Hatcher 3.26), so a nonzero class has
`Φ_{x₀} a = 1 = Φ_{x₀} [M]₂` (`localDegree_fundamentalClass`) and injectivity closes it. This is the
uniqueness companion to `fundamentalClass_ne_zero`: existence of a nonzero top mod-2 class is
unconditional, but on a CONNECTED closed manifold there is only one. -/
theorem eq_fundamentalClass_of_ne_zero {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    {a : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of M) (m + 2)} (ha : a ≠ 0) :
    a = fundamentalClass (m := m) (M := M) := by
  classical
  set x₀ := Classical.arbitrary M with hx₀
  have hbij := localDegree_bijective (m := m) (M := M) x₀
  have hane : localDegree (m := m) x₀ a ≠ 0 := by
    intro h
    exact ha (hbij.injective (by rw [h, map_zero]))
  have ha1 : localDegree (m := m) x₀ a = 1 := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (localDegree (m := m) x₀ a) with h | h
    · exact absurd h hane
    · exact h
  exact hbij.injective (by rw [ha1, localDegree_fundamentalClass (m := m) x₀])

/-! ## §4. The orientation datum from free, nontrivial `H₄(M;ℤ)` -/

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **`[M]₂` lifts integrally as soon as `H₄(M;ℤ)` is free and nontrivial.** A basis vector `c` is
not 2-divisible (§2), so `redHomology 4 c ≠ 0` (§1), so `redHomology 4 c = [M]₂` (§3). -/
theorem mem_range_redHomology_of_free_nontrivial
    [Module.Free ℤ (Homology (TopCat.of M) 4)] [Nontrivial (Homology (TopCat.of M) 4)] :
    fundamentalClass (m := 2) (M := M) ∈ Set.range (redHomology (TopCat.of M) 4) := by
  obtain ⟨c, hc⟩ := exists_not_two_smul (N := Homology (TopCat.of M) 4)
  exact ⟨c, eq_fundamentalClass_of_ne_zero (m := 2)
    (redHomology_ne_zero_of_not_two_smul (X := TopCat.of M) 3 c hc)⟩

/-- **THE DEGREE-4 ORIENTATION CRITERION.** A closed connected charted 4-manifold whose fourth
integral homology is free and nontrivial carries the `IntOrientation` datum — the `orient` field of
`SpinSigmaAtomPkg`. Nothing about `H₃(M;ℤ)` is used: this is an independent route to the datum,
complementary to `IntOrientationMod2Lift.intOrientation_of_h3_twoTorsionFree`, and the one available
whenever the top integral homology has been *computed* rather than the middle one bounded. -/
theorem nonempty_intOrientation_of_free_nontrivial
    [Module.Free ℤ (Homology (TopCat.of M) 4)] [Nontrivial (Homology (TopCat.of M) 4)] :
    Nonempty (IntOrientation M) :=
  SKEFTHawking.IntOrientationMod2Lift.nonempty_intOrientation_iff_mem_range.mpr
    mem_range_redHomology_of_free_nontrivial

end SKEFTHawking.IntOrientationFreeTopHomology
