/-
# Phase 5q.H (E1 CSC-PD tower) — the cochainSplit k-slack bypass (integral, hcore brick 6e-D)

The constructive, field-independent resolution of the seam-match "k-slack" — the step where the mod-2
proof used the forbidden Kronecker non-degeneracy pairing (dead over ℤ). The k-slack is NOT a genuine
Kronecker wall: the mod-2 SPINE for it is the `cochainSplit`/∈-boundaries route, which is coefficient-agnostic.

* `cochainSplitInt` (+ `_mem_relCochainsInt`, `_compl_mem_relCochainsInt`) — the `S`-part killer `ω` off the
  `S`-simplices / `0` on them (verbatim ℤ port of `SingularCohomologySnake.cochainSplit`).
* `capInt_coboundary_cochainSplit_eqInt` — the slack-as-boundary chain identity: for `∂c = u + w`
  (`u∈C(U)`, `w∈C(V)`), `capInt(δ(cochainSplit U ω)) c = capInt ω w + ∂e`. NO `k`, NO Kronecker; the
  `(-1)^N` sign (from `capInt_leibniz`) is absorbed into the bounding chain `e`. The integral port of
  `SingularConnSquareCloseNC.cap_coboundary_cochainSplit_eq`.
* `indUf_eq_cochainSplitInt` — `indUf U = cochainSplitInt U` (both zero exactly on the `U`-simplices),
  via the factoring reflection `range σ ⊆ U ↔ ∃τ, simplexIncl U τ = σ`. Makes the committed
  `midCocycleInt = δ(indUf)` machinery interchangeable with `cochainSplit`.
* `relCohomMvConnectingInt_eq_mk_coboundary_cochainSplitInt` — the CLASS identity
  `relCohomMvConnectingInt[ω] = [δ(cochainSplitInt U ω)]`, proven CONSTRUCTIVELY via the committed
  `relCohomMvConnectingInt_mk_eq` with `k = 0` (the "arbitrary k" collapses to zero because
  `indUf = cochainSplit`) — NOT via `relCohomology_eq_zero_of_relKroneckerH` non-degeneracy (which is
  field-only). This is the explicit, k-free cocycle rep the seam-match RHS needs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt

open scoped Classical
open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcisionIsoInt (single_mem_subspaceChainsInt_of_subordinate)
open SKEFTHawking.SingularExcisionIso (simplexIncl_range_subset_iff)

namespace SKEFTHawking.SingularCochainSplitInt

variable {X : TopCat}

/-- **cochainSplit (integral)** — the `S`-part killer: `ω` off the `S`-simplices, `0` on them.
Coefficient-agnostic port of `SingularCohomologySnake.cochainSplit`. -/
noncomputable def cochainSplitInt (S : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n) :
    SingularCochainInt X n :=
  fun σ => if (∃ τ, simplexIncl S n τ = σ) then 0 else ω σ

/-- The `S`-part vanishes on `S`-chains, hence is a relative `S`-cochain (integral). -/
theorem cochainSplitInt_mem_relCochainsInt (S : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n) :
    cochainSplitInt S n ω ∈ relCochainsInt S n := by
  rw [mem_relCochainsInt]
  intro c hc
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | add d e hd he => rw [map_add, kronecker_add_right, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, kronecker_single]
      have hz : cochainSplitInt S n ω (simplexIncl S n τ) = 0 := if_pos ⟨τ, rfl⟩
      rw [hz, mul_zero]

/-- **The complementary part `ω − φ` is a relative `V`-cochain** when `ω ∈ relCochains(U∩V)` (integral). -/
theorem cochainSplitInt_compl_mem_relCochainsInt (U V : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n)
    (hω : ω ∈ relCochainsInt (U ∩ V) n) :
    ω - cochainSplitInt U n ω ∈ relCochainsInt V n := by
  rw [mem_relCochainsInt]
  intro c hc
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | add d e hd he => rw [map_add, kronecker_add_right, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, kronecker_single]
      have hψ : (ω - cochainSplitInt U n ω) (simplexIncl V n τ) = 0 := by
        show ω (simplexIncl V n τ) - cochainSplitInt U n ω (simplexIncl V n τ) = 0
        by_cases hin : ∃ τ'', simplexIncl U n τ'' = simplexIncl V n τ
        · have hcU : cochainSplitInt U n ω (simplexIncl V n τ) = 0 := if_pos hin
          rw [hcU, sub_zero]
          obtain ⟨τ'', hτ''⟩ := hin
          have hsubV : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl V n τ)) ⊆ V := by
            rw [simplexIncl_range_subset_iff V V τ]; exact fun x _ => x.2
          have hsubU : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl V n τ)) ⊆ U := by
            rw [← hτ'', simplexIncl_range_subset_iff U U τ'']; exact fun x _ => x.2
          have hmem : Finsupp.single (simplexIncl V n τ) (1 : ℤ) ∈ subspaceChainsInt (U ∩ V) n :=
            single_mem_subspaceChainsInt_of_subordinate (Set.subset_inter hsubU hsubV)
          have hzero := (mem_relCochainsInt (U ∩ V) n ω).mp hω _ hmem
          rw [kronecker_single, one_mul] at hzero
          exact hzero
        · have hcU : cochainSplitInt U n ω (simplexIncl V n τ) = ω (simplexIncl V n τ) := if_neg hin
          rw [hcU, sub_self]
      rw [hψ, mul_zero]

/-- **The slack-as-boundary chain identity** (integral, the k-slack bypass). For `∂c = u + w`
(`u ∈ C(U)`, `w ∈ C(V)`), the connecting cochain `δ(cochainSplit U ω)` capped against `c` equals
`capInt ω w` (the `V`-leg) plus a boundary — NO `k`, NO Kronecker. Integral port of
`SingularConnSquareCloseNC.cap_coboundary_cochainSplit_eq`, with the `(-1)^N` sign (from `capInt_leibniz`)
absorbed into the bounding chain `e`. -/
theorem capInt_coboundary_cochainSplit_eqInt (U V : Set ↑X) {N m : ℕ}
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (N + 1)))
    (c : SingularChainInt X (N + 1 + m + 1)) (u w : SingularChainInt X (N + 1 + m))
    (hu : u ∈ subspaceChainsInt U (N + 1 + m)) (hw : w ∈ subspaceChainsInt V (N + 1 + m))
    (hbd : chainBoundary X (N + 1 + m) c = u + w) (h : N + 1 + m + 1 = N + 1 + 1 + m) :
    ∃ e : SingularChainInt X (m + 1),
      capInt (m := m) (coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1)) (h ▸ c)
        = capInt (m := m) ω.1.1 w + chainBoundary X m e := by
  have hu0 : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) u = 0 :=
    capInt_subspaceChainInt_eq_zero U _ (fun τ => if_pos ⟨τ, rfl⟩) hu
  have hωw : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) w = capInt (m := m) ω.1.1 w := by
    have hψw : capInt (m := m) (ω.1.1 - cochainSplitInt U (N + 1) ω.1.1) w = 0 :=
      capInt_subspaceChainInt_eq_zero V _
        (fun τ => relCochainInt_vanish V
          ⟨_, cochainSplitInt_compl_mem_relCochainsInt U V (N + 1) ω.1.1 ω.1.2⟩ τ) hw
    have hsplit : capInt (m := m) (ω.1.1 - cochainSplitInt U (N + 1) ω.1.1) w
        = capInt (m := m) ω.1.1 w - capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) w := by
      rw [← capIntₗ_apply, ← capIntₗ_apply, ← capIntₗ_apply, map_sub, LinearMap.sub_apply]
    rw [hsplit, sub_eq_zero] at hψw
    exact hψw.symm
  have hφbd : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) (chainBoundary X (N + 1 + m) c)
      = capInt (m := m) ω.1.1 w := by
    rw [hbd, ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply, hu0, zero_add, hωw]
  refine ⟨(-1 : ℤ) ^ N • capInt (m := m + 1) (cochainSplitInt U (N + 1) ω.1.1) c, ?_⟩
  have hleib := capInt_leibniz (cochainSplitInt U (N + 1) ω.1.1) c h
  rw [hφbd] at hleib
  have h1 : ((-1 : ℤ) ^ N) * ((-1) ^ (N + 1 + 1)) = 1 := by
    rw [← pow_add, show N + (N + 1 + 1) = 2 * (N + 1) by ring, pow_mul]; norm_num
  have h2 : ((-1 : ℤ) ^ N) * ((-1) ^ (N + 1)) = -1 := by
    rw [← pow_add, show N + (N + 1) = 2 * N + 1 by ring, pow_add, pow_mul]; norm_num
  rw [map_smul, hleib, smul_add, smul_smul, smul_smul, h1, h2, one_smul, neg_one_smul]
  abel

/-- `indUf` and `cochainSplitInt` coincide: both zero exactly on the `U`-simplices, `ω` elsewhere.
(`range σ ⊆ U ↔ ∃τ, simplexIncl U τ = σ` — the factoring reflection.) -/
theorem indUf_eq_cochainSplitInt (U : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n) :
    SKEFTHawking.SingularRelativeCohomologyMVConnectingInt.indUf U n ω = cochainSplitInt U n ω := by
  funext σ
  rw [SKEFTHawking.SingularRelativeCohomologyMVConnectingInt.indUf_apply]
  unfold cochainSplitInt
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨((sub U).toSSetObjEquiv (op (SimplexCategory.mk n))).symm
        ⟨fun x => ⟨(X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) x, h ⟨x, rfl⟩⟩,
          (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).continuous.subtype_mk _⟩, ?_⟩
    apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    rw [SKEFTHawking.SingularExcision.toSSetObjEquiv_simplexIncl, Equiv.apply_symm_apply]
    ext x
    rfl
  · rintro ⟨τ, rfl⟩
    exact SKEFTHawking.SingularExcisionIsoInt.range_simplexIncl_subsetInt U τ

open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (indUf relCohomMvConnectingInt
  relCohomMvConnectingInt_mk_eq)
open SKEFTHawking.SingularQCohomologyInt (mvUnionCochainsInt)

/-- **Step 3 (class identity, constructive)**: the MV cohomology connecting map of `[ω]` is the class of
the explicit cocycle `δ(cochainSplitInt U ω)` — proven WITHOUT Kronecker non-degeneracy, via
`relCohomMvConnectingInt_mk_eq` with `k = 0` (the committed forward characterization) + `indUf = cochainSplit`
(`indUf_eq_cochainSplitInt`). The `(U∪V)`-membership `hmem`/cocycle `hcoc` are the small-simplices content,
supplied by the caller. -/
theorem relCohomMvConnectingInt_eq_mk_coboundary_cochainSplitInt (U V : Set ↑X) (hU : IsOpen U)
    (hV : IsOpen V) (N : ℕ) (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (N + 1)))
    (hmem : coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1) ∈ relCochainsInt (U ∪ V) (N + 2))
    (hcoc : (⟨coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1), hmem⟩ :
        relCochainsInt (U ∪ V) (N + 2)) ∈ LinearMap.ker (relCoboundaryIntₗ (U ∪ V) (N + 2))) :
    relCohomMvConnectingInt U V hU hV N (RelativeCohomologyInt.mk (U ∩ V) (N + 1) ω)
      = RelativeCohomologyInt.mk (U ∪ V) (N + 2)
          ⟨⟨coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1), hmem⟩, hcoc⟩ := by
  refine relCohomMvConnectingInt_mk_eq U V hU hV N ω ⟨⟨_, hmem⟩, hcoc⟩
    ⟨0, Submodule.zero_mem _⟩ ?_
  show coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1)
      = coboundary X (N + 1) (indUf U (N + 1) ω.1.1)
        + coboundary X (N + 1) ((0 : mvUnionCochainsInt U V (N + 1)) : SingularCochainInt X (N + 1))
  rw [indUf_eq_cochainSplitInt, ZeroMemClass.coe_zero,
    show coboundary X (N + 1) (0 : SingularCochainInt X (N + 1)) = 0 from
      map_zero (coboundaryₗ X (N + 1)), add_zero]

/-- **`δφ ∈ relCochains U`** (integral, unconditional): the coboundary of the `U`-part is a relative
`U`-cochain. The `A`-leg membership Route B's Brick J consumes (NOT `(U∪V)`-membership). Port of
`SingularCohomologySnake.cochainSplit_coboundary_mem_U`. -/
theorem cochainSplitInt_coboundary_mem_UInt (U : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n) :
    coboundary X n (cochainSplitInt U n ω) ∈ relCochainsInt U (n + 1) :=
  coboundary_mem_relCochainsInt U n _ (cochainSplitInt_mem_relCochainsInt U n ω)

/-- **`δφ ∈ relCochains V`** (integral) when `ω` is a `(U∩V)`-relative cocycle: from
`δ(φ + (ω − φ)) = δω = 0`, `δφ = −δ(ω − φ)`, and `ω − φ ∈ relCochains V`. The `B`-leg membership for
Brick J. Port of `SingularCohomologySnake.cochainSplit_coboundary_mem_V` with the honest ℤ subtraction
(no char-2 `ω − φ = ω + φ`). -/
theorem cochainSplitInt_coboundary_mem_VInt (U V : Set ↑X) (n : ℕ) (ω : SingularCochainInt X n)
    (hω : ω ∈ relCochainsInt (U ∩ V) n) (hcoc : coboundary X n ω = 0) :
    coboundary X n (cochainSplitInt U n ω) ∈ relCochainsInt V (n + 1) := by
  have hδψ : coboundary X n (ω - cochainSplitInt U n ω) ∈ relCochainsInt V (n + 1) :=
    coboundary_mem_relCochainsInt V n _ (cochainSplitInt_compl_mem_relCochainsInt U V n ω hω)
  have hsum : coboundary X n (cochainSplitInt U n ω) + coboundary X n (ω - cochainSplitInt U n ω) = 0 := by
    have h := congrArg (coboundaryₗ X n) (show cochainSplitInt U n ω + (ω - cochainSplitInt U n ω) = ω by
      abel)
    rw [map_add] at h
    have h2 : coboundary X n (cochainSplitInt U n ω) + coboundary X n (ω - cochainSplitInt U n ω)
        = coboundary X n ω := h
    rw [h2, hcoc]
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact (relCochainsInt V (n + 1)).neg_mem hδψ

end SKEFTHawking.SingularCochainSplitInt
