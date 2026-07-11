/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, Brick J (integral, the double-support δφ-kill)

The foundational engine of the mod-2 **Route B** (chain-safe, double-support) close of the PD connecting
square (`SingularConnSquareCloseNC.subHomConnecting_openDuality`), ported to ℤ. Route B closes `hcoreG`
(`subHomConnectingInt(legW K g) = openDuality(legδ K g)`) WITHOUT the `relCohomMvConnecting`/`absCohomConn`
class lift (the mod-2 DISCARDED CrossReal route); its key locality is that the connecting cochain vanishes
on BOTH cover legs SEPARATELY (`a ∈ relCochains A` AND `a ∈ relCochains B`), never needing a `(U∪V)`
union-membership.

* `exists_iterate_cover_split_ambInt` — ambient cover-split (ℤ analog of mod-2 `exists_iterate_cover_split_amb`),
  a repackaging of `SingularCoverFineSplitInt.exists_cover_fine_split_of_boundaryInt` with the two legs as
  ambient subspace chains. Used 3× below and downstream.
* `cap_relCochains_pair_double_support_eq_boundaryInt` — **Brick J**: for a cocycle `a` vanishing on the
  `A`- and `B`-simplices separately, and a `P`-supported `c` that is ambient-null-homologous
  (`c = ∂D + ρ`, `ρ ∈ C(A∪B)`) with `∂c = chainIncl_A u' + chainIncl_B w'`, the cap `capInt a c` is the
  boundary of a `P`-supported chain — the ambient `D` dissolves via small-`D` over the total cover.

Signs (the ℤ vs char-2 delta): the chain homotopy `∂Dₘ + Dₘ∂ = 1 − Sdᵐ` is signed, and the cocycle
cap-map carries `(-1)ᵏ` (`capInt_cocycle_chainMap`); both are absorbed into the witness `E`, so the
`∃E` conclusion mirrors mod-2 exactly. Every char-2 `abel_nf; simp [two_smul, add_self]` collapse becomes
a plain `abel`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.

NOTE for downstream Route-B bricks: (1) the cocycle-vanishing hypotheses are typed `∀ τ, a (simplexIncl A k τ) = 0`
(the direct form `capInt_subspaceChainInt_eq_zero` consumes); a consumer holding `a ∈ relCochainsInt A k`
bridges by evaluating on `chainIncl A k (single τ 1)`. (2) Always pass `(m := …)` explicitly on
`capInt_subspaceChainInt_eq_zero`/`capInt_mem_subspaceChainsInt`/`capInt_cocycle_chainMap` — leaving `m`
implicit forces `k+m =?= (k+n)+1` unification that explodes the heartbeat budget.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularCoverFineSplitInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularDualCochainInt
import SKEFTHawking.SingularSubdivisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt iterHomotopyInt_chainHomotopy)
open SKEFTHawking.SingularDualCochainInt (iterHomotopyIntₗ iterHomotopyIntₗ_apply)
open SKEFTHawking.SingularEuclideanCapIsoInt (capInt_subspaceChainInt_eq_zero)
open SKEFTHawking.SingularCapSupportInt (capInt_mem_subspaceChainsInt)
open SKEFTHawking.SingularExcisionIsoInt (iterHomotopyInt_mem_subspaceChainsInt
  mem_subspaceChainsInt_of_support subspaceChainsInt_inf)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularCoverFineSplitInt (exists_cover_fine_split_of_boundaryInt)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Ambient cover-split (integral)** — the ℤ analog of the mod-2 `exists_iterate_cover_split_amb`,
built from `exists_cover_fine_split_of_boundaryInt` by repackaging the two `sub`-typed legs as ambient
subspace chains. -/
theorem exists_iterate_cover_split_ambInt {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (f : SingularChainInt X n) (hf : f ∈ subspaceChainsInt (U ∪ V) n) :
    ∃ (μ : ℕ) (fA fB : SingularChainInt X n),
      fA ∈ subspaceChainsInt U n ∧ fB ∈ subspaceChainsInt V n
      ∧ (⇑(singularSdInt X n))^[μ] f = fA + fB := by
  obtain ⟨i, pU, pV, hsplit⟩ := exists_cover_fine_split_of_boundaryInt hU hV f hf
  exact ⟨i, chainIncl U n pU, chainIncl V n pV,
    LinearMap.mem_range_self (chainIncl U n) pU, LinearMap.mem_range_self (chainIncl V n) pV, hsplit⟩

omit [T2Space ↑X] in
/-- **The double-support δφ-kill** (Brick J, integral). ℤ port of
`SingularConnSquareCloseNC.cap_relCochains_pair_double_support_eq_boundary`. Signs: the chain homotopy
`∂Dₘ + Dₘ∂ = 1 − Sdᵐ` is signed and the cocycle cap-map carries `(-1)ᵏ`
(`capInt_cocycle_chainMap`); the `(-1)ᵏ` is absorbed into the witness `E`. -/
theorem cap_relCochains_pair_double_support_eq_boundaryInt {A B P : Set ↑X}
    (hA : IsOpen A) (hB : IsOpen B) (hP : IsOpen P)
    (hcover : P ∪ (A ∪ B) = Set.univ) {k n : ℕ}
    (a : SingularCochainInt X k) (hac : coboundary X k a = 0)
    (haA : ∀ τ, a (simplexIncl A k τ) = 0)
    (haB : ∀ τ, a (simplexIncl B k τ) = 0)
    (c : SingularChainInt X (k + n + 1)) (hcP : c ∈ subspaceChainsInt P (k + n + 1))
    (D : SingularChainInt X (k + n + 1 + 1)) (ρ : SingularChainInt X (k + n + 1))
    (hρ : ρ ∈ subspaceChainsInt (A ∪ B) (k + n + 1))
    (heq : c = chainBoundary X (k + n + 1) D + ρ)
    (u' : SingularChainInt (sub A) (k + n)) (w' : SingularChainInt (sub B) (k + n))
    (hbd : chainBoundary X (k + n) c = chainIncl A (k + n) u' + chainIncl B (k + n) w') :
    ∃ E : SingularChainInt X (n + 1 + 1), E ∈ subspaceChainsInt P (n + 1 + 1)
      ∧ capInt (m := n + 1) a c = chainBoundary X (n + 1) E := by
  -- small D over the total cover (P, A∪B)
  have hDmem : D ∈ subspaceChainsInt (P ∪ (A ∪ B)) (k + n + 1 + 1) :=
    mem_subspaceChainsInt_of_support (fun τ _ => by rw [hcover]; exact Set.subset_univ _)
  obtain ⟨ν, D₁, D₂, hD₁, hD₂, hDsplit⟩ :=
    exists_iterate_cover_split_ambInt hP (hA.union hB) D hDmem
  have hhD := iterHomotopyInt_chainHomotopy X ν (k + n + 1) D
  -- ∂D = ∂D₁ + ∂D₂ + ∂(Dᵥ(∂D))  (signed telescope: same final shape as mod-2)
  have hDbnd : chainBoundary X (k + n + 1) D
      = chainBoundary X (k + n + 1) D₁ + chainBoundary X (k + n + 1) D₂
        + chainBoundary X (k + n + 1)
            (iterHomotopyInt X (k + n + 1) ν (chainBoundary X (k + n + 1) D)) := by
    have h1 := congrArg (chainBoundary X (k + n + 1)) hhD
    rw [map_add, boundary_comp_boundary, zero_add, map_sub, hDsplit, map_add] at h1
    rw [h1]; abel
  -- Dᵥ(∂D) = Dᵥc − Dᵥρ  (signed: ∂D = c − ρ over ℤ)
  have hTsplitInt : iterHomotopyInt X (k + n + 1) ν (chainBoundary X (k + n + 1) D)
      = iterHomotopyInt X (k + n + 1) ν c - iterHomotopyInt X (k + n + 1) ν ρ := by
    have hdD : chainBoundary X (k + n + 1) D = c - ρ := by rw [heq]; abel
    rw [hdD, ← iterHomotopyIntₗ_apply, map_sub, iterHomotopyIntₗ_apply, iterHomotopyIntₗ_apply]
  -- b defined by its C(A∪B)-formula (signed: −∂(Dᵥρ)); C(P) comes from the equation
  set b : SingularChainInt X (k + n + 1) := ρ + chainBoundary X (k + n + 1) D₂
    - chainBoundary X (k + n + 1) (iterHomotopyInt X (k + n + 1) ν ρ) with hbdef
  have hbeqInt : c = chainBoundary X (k + n + 1)
      (D₁ + iterHomotopyInt X (k + n + 1) ν c) + b := by
    conv_lhs => rw [heq]
    rw [hDbnd, hTsplitInt, hbdef]
    simp only [map_add, map_sub]
    abel
  have hb2Int : b = c - chainBoundary X (k + n + 1)
      (D₁ + iterHomotopyInt X (k + n + 1) ν c) := by
    rw [eq_sub_iff_add_eq, add_comm b]; exact hbeqInt.symm
  have hbPInt : b ∈ subspaceChainsInt P (k + n + 1) := by
    rw [hb2Int]
    exact Submodule.sub_mem _ hcP (chainBoundary_mem_subspaceChainsInt P (k + n + 1) _
      (Submodule.add_mem _ hD₁ (iterHomotopyInt_mem_subspaceChainsInt hcP ν)))
  have hbABInt : b ∈ subspaceChainsInt (A ∪ B) (k + n + 1) := by
    rw [hbdef]
    exact Submodule.sub_mem _ (Submodule.add_mem _ hρ
      (chainBoundary_mem_subspaceChainsInt (A ∪ B) (k + n + 1) _ hD₂))
      (chainBoundary_mem_subspaceChainsInt (A ∪ B) (k + n + 1) _
        (iterHomotopyInt_mem_subspaceChainsInt hρ ν))
  have hbInterInt : b ∈ subspaceChainsInt ((P ∩ A) ∪ (P ∩ B)) (k + n + 1) := by
    have h := Submodule.mem_inf.mpr ⟨hbPInt, hbABInt⟩
    rw [subspaceChainsInt_inf, Set.inter_union_distrib_left] at h
    exact h
  obtain ⟨κ, bA, bB, hbA, hbB, hbSplit⟩ :=
    exists_iterate_cover_split_ambInt (hP.inter hA) (hP.inter hB) b hbInterInt
  have hhbInt := iterHomotopyInt_chainHomotopy X κ (k + n) b
  have hkill1Int : capInt (m := n + 1) a ((⇑(singularSdInt X (k + n + 1)))^[κ] b) = 0 := by
    have hbAA : bA ∈ subspaceChainsInt A (k + n + 1) :=
      subspaceChainsInt_mono Set.inter_subset_right (k + n + 1) hbA
    have hbBB : bB ∈ subspaceChainsInt B (k + n + 1) :=
      subspaceChainsInt_mono Set.inter_subset_right (k + n + 1) hbB
    rw [hbSplit, ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply,
      capInt_subspaceChainInt_eq_zero (m := n + 1) A a haA hbAA,
      capInt_subspaceChainInt_eq_zero (m := n + 1) B a haB hbBB, add_zero]
  have hkill2Int : capInt (m := n + 1) a
      (iterHomotopyInt X (k + n) κ (chainBoundary X (k + n) b)) = 0 := by
    have hcbdInt : chainBoundary X (k + n) b = chainBoundary X (k + n) c := by
      rw [hb2Int, map_sub, boundary_comp_boundary, sub_zero]
    rw [hcbdInt, hbd,
      show iterHomotopyInt X (k + n) κ (chainIncl A (k + n) u' + chainIncl B (k + n) w')
          = iterHomotopyInt X (k + n) κ (chainIncl A (k + n) u')
            + iterHomotopyInt X (k + n) κ (chainIncl B (k + n) w')
        from by rw [← iterHomotopyIntₗ_apply, map_add, iterHomotopyIntₗ_apply,
          iterHomotopyIntₗ_apply],
      ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply,
      capInt_subspaceChainInt_eq_zero (m := n + 1) A a haA
        (iterHomotopyInt_mem_subspaceChainsInt (LinearMap.mem_range_self (chainIncl A (k + n)) u') κ),
      capInt_subspaceChainInt_eq_zero (m := n + 1) B a haB
        (iterHomotopyInt_mem_subspaceChainsInt (LinearMap.mem_range_self (chainIncl B (k + n)) w') κ),
      add_zero]
  have hcbInt : capInt (m := n + 1) a c
      = capInt (m := n + 1) a (chainBoundary X (k + n + 1)
          (D₁ + iterHomotopyInt X (k + n + 1) ν c))
        + capInt (m := n + 1) a b := by
    conv_lhs => rw [hbeqInt]
    rw [← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply]
  have hb3'Int : (chainBoundary X (k + n + 1) (iterHomotopyInt X (k + n + 1) κ b)
      + iterHomotopyInt X (k + n) κ (chainBoundary X (k + n) b))
      + (⇑(singularSdInt X (k + n + 1)))^[κ] b = b := by
    rw [hhbInt]; abel
  have hbcap : capInt (m := n + 1) a b
      = capInt (m := n + 1) a (chainBoundary X (k + n + 1)
          (iterHomotopyInt X (k + n + 1) κ b)) := by
    conv_lhs => rw [← hb3'Int]
    rw [← capIntₗ_apply, map_add, map_add, capIntₗ_apply, capIntₗ_apply, capIntₗ_apply,
      hkill2Int, hkill1Int, add_zero, add_zero]
  -- cocycle cap-map: `a ⌢ ∂Y = (-1)ᵏ · ∂(a ⌢ Y)` for a cocycle `a`
  have hcocyc : ∀ (Y : SingularChainInt X (k + n + 1 + 1)),
      capInt (m := n + 1) a (chainBoundary X (k + n + 1) Y)
        = (-1 : ℤ) ^ k • chainBoundary X (n + 1) (capInt (m := n + 1 + 1) a Y) := by
    intro Y
    have hcm : chainBoundary X (n + 1) (capInt (m := n + 1 + 1) a Y)
        = (-1 : ℤ) ^ k • capInt (m := n + 1) a (chainBoundary X (k + n + 1) Y) :=
      capInt_cocycle_chainMap (m := n + 1) a hac Y
    rw [hcm, smul_smul, ← pow_add, show k + k = 2 * k from by ring, pow_mul, neg_one_sq, one_pow,
      one_smul]
  have hY₁P : (D₁ + iterHomotopyInt X (k + n + 1) ν c) ∈ subspaceChainsInt P (k + n + 1 + 1) :=
    Submodule.add_mem _ hD₁ (iterHomotopyInt_mem_subspaceChainsInt hcP ν)
  have hY₂P : iterHomotopyInt X (k + n + 1) κ b ∈ subspaceChainsInt P (k + n + 1 + 1) :=
    iterHomotopyInt_mem_subspaceChainsInt hbPInt κ
  have hEbd : chainBoundary X (n + 1)
        ((-1 : ℤ) ^ k • (capInt (m := n + 1 + 1) a (D₁ + iterHomotopyInt X (k + n + 1) ν c)
          + capInt (m := n + 1 + 1) a (iterHomotopyInt X (k + n + 1) κ b)))
      = (-1 : ℤ) ^ k • chainBoundary X (n + 1)
            (capInt (m := n + 1 + 1) a (D₁ + iterHomotopyInt X (k + n + 1) ν c))
        + (-1 : ℤ) ^ k • chainBoundary X (n + 1)
            (capInt (m := n + 1 + 1) a (iterHomotopyInt X (k + n + 1) κ b)) := by
    rw [map_smul, map_add, smul_add]
  refine ⟨(-1 : ℤ) ^ k • (capInt (m := n + 1 + 1) a (D₁ + iterHomotopyInt X (k + n + 1) ν c)
      + capInt (m := n + 1 + 1) a (iterHomotopyInt X (k + n + 1) κ b)),
    Submodule.smul_mem _ _ (Submodule.add_mem _
      (capInt_mem_subspaceChainsInt (m := n + 1 + 1) P a hY₁P)
      (capInt_mem_subspaceChainsInt (m := n + 1 + 1) P a hY₂P)), ?_⟩
  rw [hcbInt, hbcap, hcocyc (D₁ + iterHomotopyInt X (k + n + 1) ν c),
    hcocyc (iterHomotopyInt X (k + n + 1) κ b), hEbd]

end SKEFTHawking.SingularConnSquareCloseNCInt
