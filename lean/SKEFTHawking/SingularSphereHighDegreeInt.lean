import Mathlib
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SingularLocalHomologyInt

/-!
# Phase 5q.H (integral Substrate-G, E1) — high-degree vanishing of sphere homology `Hₚ(Sⁿ;ℤ) = 0` (`p > n`)

The **integer-coefficient** mirror of `SingularSphereHighDegree.sphere_homology_high`. The convex base
case of the fundamental-class compactness induction (`Hᵢ(M | K;ℤ) = 0` for `i > n`) reduces, via the
radial retract `ℝⁿ ∖ K ≃ ℝⁿ ∖ 0 ≃ Sⁿ⁻¹` and the acyclic-ambient connecting iso, to the **high-degree
vanishing of sphere homology**: `Hₚ(Sⁿ;ℤ) = 0` for `p ≥ n + 1`. Built by induction on the sphere
dimension `n`, using the integral suspension/dimension-reduction iso
`SingularSphereHomologyInt.dimReductionEquivInt : Hₖ₊₂(Sⁿ;ℤ) ≅ Hₖ₊₁(Sⁿ⁻¹;ℤ)`.

The base `Hₚ(S⁰;ℤ) = 0` (`p ≥ 1`) comes from the **clopen-split vanishing**: if `X` splits as a clopen
partition `U ⊔ Uᶜ` and both pieces are acyclic in degree `p`, then `Hₚ(X;ℤ) = 0` (`S⁰` is two points,
each homeomorphic to the acyclic `ℝ⁰`). Over ℤ the split argument is if anything cleaner than mod-2: the
`chainIncl U + chainIncl Uᶜ = 0` step is closed directly by submodule negation (no `x + x = 0` shortcut).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLineMinusPointInt SKEFTHawking.SingularLocalHomologyInt
open SKEFTHawking.SingularSphereHomologyInt
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularSphereHighDegreeInt

/-- The converse of `homology_trivial_of_acyclicInt`: if `Hₙ₊₁(X;ℤ) = 0` then every `(n+1)`-cycle is a
boundary. The ℤ mirror of `SingularLocalHomology.boundaries_of_homology_trivial`. -/
theorem boundaries_of_homology_trivialInt {X : TopCat} {n : ℕ}
    (h : ∀ x : Homology X (n + 1), x = 0) (z : SingularChainInt X (n + 1))
    (hz : chainBoundary X n z = 0) : z ∈ boundaries X (n + 1) :=
  Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp (h (Homology.mk X (n + 1) ⟨z, hz⟩)))

/-- **Clopen-split vanishing** (integral): if `U ⊆ X` is clopen and both `Hₖ₊₁(U;ℤ) = 0` and
`Hₖ₊₁(Uᶜ;ℤ) = 0`, then `Hₖ₊₁(X;ℤ) = 0`. The chain complex of `X` splits as `C(U) ⊕ C(Uᶜ)`
(`subspaceChainsInt_sup_compl_eq_top`, `subspaceChainsInt_inf_compl_eq_bot`), so any `(k+1)`-cycle is a
sum of a `U`-cycle and a `Uᶜ`-cycle, each a boundary by hypothesis. Mirror of
`SingularSphereHighDegree.homology_trivial_of_clopen_split`. -/
theorem homology_trivial_of_clopen_splitInt {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (k : ℕ)
    (hUtriv : ∀ x : Homology (sub U) (k + 1), x = 0)
    (hUctriv : ∀ x : Homology (sub Uᶜ) (k + 1), x = 0)
    (x : Homology X (k + 1)) : x = 0 := by
  refine homology_trivial_of_acyclicInt ?_ x
  intro z hz
  have hmem : z ∈ subspaceChainsInt (S := U) (k + 1) ⊔ subspaceChainsInt (S := Uᶜ) (k + 1) := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  set a' := (inclRangeEquiv U (k + 1)).symm ⟨a, ha⟩ with ha'
  set b' := (inclRangeEquiv Uᶜ (k + 1)).symm ⟨b, hb⟩ with hb'
  have hAeq : chainIncl U (k + 1) a' = a := chainIncl_inclRangeEquiv_symm U (k + 1) ⟨a, ha⟩
  have hBeq : chainIncl Uᶜ (k + 1) b' = b := chainIncl_inclRangeEquiv_symm Uᶜ (k + 1) ⟨b, hb⟩
  have hsum : chainIncl U k (chainBoundary (sub U) k a')
      + chainIncl Uᶜ k (chainBoundary (sub Uᶜ) k b') = 0 := by
    rw [chainIncl_chainBoundary, chainIncl_chainBoundary, hAeq, hBeq, ← map_add, hab, hz]
  -- `chainIncl U (∂a') = -chainIncl Uᶜ (∂b')` lies in both clopen subspaces, hence in `⊥ = 0`.
  have hneg : chainIncl U k (chainBoundary (sub U) k a')
      = -chainIncl Uᶜ k (chainBoundary (sub Uᶜ) k b') :=
    (neg_eq_of_add_eq_zero_left hsum).symm
  have hbotU : chainIncl U k (chainBoundary (sub U) k a') = 0 := by
    have hinf : chainIncl U k (chainBoundary (sub U) k a')
        ∈ subspaceChainsInt (S := U) k ⊓ subspaceChainsInt (S := Uᶜ) k :=
      ⟨⟨chainBoundary (sub U) k a', rfl⟩,
        hneg ▸ (subspaceChainsInt (S := Uᶜ) k).neg_mem ⟨chainBoundary (sub Uᶜ) k b', rfl⟩⟩
    rw [subspaceChainsInt_inf_compl_eq_bot, Submodule.mem_bot] at hinf
    exact hinf
  have hbotUc : chainIncl Uᶜ k (chainBoundary (sub Uᶜ) k b') = 0 := by
    have := hbotU.symm.trans hneg
    rwa [eq_comm, neg_eq_zero] at this
  have hcycA : chainBoundary (sub U) k a' = 0 :=
    chainIncl_injective U k (hbotU.trans (map_zero _).symm)
  have hcycB : chainBoundary (sub Uᶜ) k b' = 0 :=
    chainIncl_injective Uᶜ k (hbotUc.trans (map_zero _).symm)
  have haB : a ∈ boundaries X (k + 1) := by
    rw [← hAeq]
    exact chainIncl_mem_boundariesInt U (k + 1) a' (boundaries_of_homology_trivialInt hUtriv a' hcycA)
  have hbB : b ∈ boundaries X (k + 1) := by
    rw [← hBeq]
    exact chainIncl_mem_boundariesInt Uᶜ (k + 1) b'
      (boundaries_of_homology_trivialInt hUctriv b' hcycB)
  rw [← hab]
  exact Submodule.add_mem _ haB hbB

/-- **One-point acyclicity** (integral): a topological space with a unique point is acyclic in positive
degree, `Hₖ₊₁(X;ℤ) = 0`. Transported from `Hₖ₊₁(ℝ⁰;ℤ) = 0` (`eucl_homology_trivialInt`) along the
unique continuous maps `X → ℝ⁰` and `ℝ⁰ → X` (both compositions are the identity since both spaces are
subsingletons). Mirror of `SingularSphereHighDegree.homology_unique_trivial`. -/
theorem homology_unique_trivialInt {X : TopCat} [Unique ↑X] (k : ℕ) (x : Homology X (k + 1)) :
    x = 0 := by
  haveI hs : Subsingleton (EuclideanSpace ℝ (Fin 0)) := ⟨fun a b => by ext i; exact Fin.elim0 i⟩
  haveI : Subsingleton ↑(SingularEuclideanAcyclic.Eucl 0) := hs
  let f : C(↑X, ↑(SingularEuclideanAcyclic.Eucl 0)) := ⟨fun _ => 0, continuous_const⟩
  let g : C(↑(SingularEuclideanAcyclic.Eucl 0), ↑X) := ⟨fun _ => default, continuous_const⟩
  have hgf : g.comp f = ContinuousMap.id ↑X := ContinuousMap.ext fun z => Subsingleton.elim _ _
  have hfg : f.comp g = ContinuousMap.id ↑(SingularEuclideanAcyclic.Eucl 0) :=
    ContinuousMap.ext fun z => Subsingleton.elim _ _
  exact homology_trivial_of_bijectiveInt f
    (Homology.mapInt_bijective_of_comp_id_all f g hgf hfg (k + 1))
    (eucl_homology_trivialInt 0 k) x

/-- On `S⁰ = ` the unit sphere in `ℝ¹`, the single coordinate is `±1`. -/
theorem sphere0_coord (p : ↑(SingularSphereAcyclic.Sph 0)) :
    (↑p : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨ (↑p : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  have hn : ‖(↑p : EuclideanSpace ℝ (Fin 1))‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs] at hn
  exact abs_eq (by norm_num) |>.mp hn

/-- A vector in `ℝ¹` is determined by its single coordinate. -/
theorem eucl1_ext {v w : EuclideanSpace ℝ (Fin 1)} (h : v 0 = w 0) : v = w := by
  ext i; fin_cases i; exact h

/-- **`Hₚ(S⁰;ℤ) = 0` for `p ≥ 1`** — the base of the sphere-dimension induction (integral). `S⁰` (the
unit sphere in `ℝ¹`) is two points, split by the sign of the coordinate into clopen one-point pieces,
each acyclic. Mirror of `SingularSphereHighDegree.sphere0_homology_high`. -/
theorem sphere0_homology_high (k : ℕ) (x : Homology (SingularSphereAcyclic.Sph 0) (k + 1)) :
    x = 0 := by
  set c : ↑(SingularSphereAcyclic.Sph 0) → ℝ := fun p => (↑p : EuclideanSpace ℝ (Fin 1)) 0 with hc
  have hc_cont : Continuous c := by fun_prop
  have hcne : ∀ p, c p = 1 ∨ c p = -1 := sphere0_coord
  have hcoord1 : ∀ p, 0 < c p → c p = 1 := fun p hp =>
    (hcne p).resolve_right fun h => by rw [h] at hp; norm_num at hp
  have hcoordm1 : ∀ p, ¬ (0 < c p) → c p = -1 := fun p hp =>
    (hcne p).resolve_left fun h => hp (by rw [h]; norm_num)
  have hsingle : ∀ a : ℝ, (EuclideanSpace.single (0 : Fin 1) a) 0 = a := fun a => by simp
  have hmem : ∀ a : ℝ, |a| = 1 → (EuclideanSpace.single (0 : Fin 1) a) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    intro a ha; rw [mem_sphere_zero_iff_norm]; simp [ha]
  set U : Set ↑(SingularSphereAcyclic.Sph 0) := {p | 0 < c p} with hU
  have hopenU : IsOpen U := hc_cont.isOpen_preimage _ isOpen_Ioi
  have hUc_eq : Uᶜ = {p | c p < 0} := by
    ext p
    simp only [hU, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rcases hcne p with h | h <;> rw [h] <;> norm_num
  have hopenUc : IsOpen Uᶜ := by rw [hUc_eq]; exact hc_cont.isOpen_preimage _ isOpen_Iio
  have hclopen : IsClopen U := ⟨isOpen_compl_iff.mp hopenUc, hopenU⟩
  refine homology_trivial_of_clopen_splitInt hclopen k ?_ ?_ x
  · haveI : Inhabited ↥U :=
      ⟨⟨⟨EuclideanSpace.single 0 1, hmem 1 (by norm_num)⟩,
        show (0 : ℝ) < (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 by rw [hsingle]; norm_num⟩⟩
    haveI : Subsingleton ↥U := ⟨fun a b => by
      apply Subtype.ext; apply Subtype.ext; apply eucl1_ext
      change c ↑a = c ↑b; rw [hcoord1 _ a.2, hcoord1 _ b.2]⟩
    haveI : Unique ↥U := ⟨⟨default⟩, fun a => Subsingleton.elim a default⟩
    exact homology_unique_trivialInt k
  · haveI : Inhabited ↥Uᶜ :=
      ⟨⟨⟨EuclideanSpace.single 0 (-1), hmem (-1) (by norm_num)⟩,
        show ¬ (0 : ℝ) < (EuclideanSpace.single (0 : Fin 1) (-1 : ℝ)) 0 by rw [hsingle]; norm_num⟩⟩
    haveI : Subsingleton ↥Uᶜ := ⟨fun a b => by
      apply Subtype.ext; apply Subtype.ext; apply eucl1_ext
      change c ↑a = c ↑b; rw [hcoordm1 _ a.2, hcoordm1 _ b.2]⟩
    haveI : Unique ↥Uᶜ := ⟨⟨default⟩, fun a => Subsingleton.elim a default⟩
    exact homology_unique_trivialInt k

/-- **High-degree vanishing of sphere homology** (integral): `Hₚ(Sⁿ;ℤ) = 0` for every `p > n`. By
induction on the sphere dimension `n`: the base `n = 0` is `sphere0_homology_high`; the step transports
`Hₖ₊₂(Sⁿ⁺¹;ℤ) ≅ Hₖ₊₁(Sⁿ;ℤ)` (`SingularSphereHomologyInt.dimReductionEquivInt`, noting
`SingularPuncturedRetract.Sph (n+1) = SingularSphereAcyclic.Sph n` definitionally) and applies the
inductive hypothesis. Mirror of `SingularSphereHighDegree.sphere_homology_high`. -/
theorem sphere_homology_high :
    ∀ (n p : ℕ), n < p → ∀ x : Homology (SingularSphereAcyclic.Sph n) p, x = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp x
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
    exact sphere0_homology_high k x
  | succ n ih =>
    intro p hp x
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1 :=
      ⟨EuclideanSpace.single 0 1, by rw [mem_sphere_zero_iff_norm]; simp⟩
    have hequiv := SingularSphereHomologyInt.dimReductionEquivInt (n := n + 1) v k
    have hz : hequiv x = 0 := ih (k + 1) (by omega) (hequiv x)
    rw [← hequiv.symm_apply_apply x, hz, map_zero]

end SKEFTHawking.SingularSphereHighDegreeInt
