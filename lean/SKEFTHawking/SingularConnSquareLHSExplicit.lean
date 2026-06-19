import Mathlib
import SKEFTHawking.SingularSubdivision
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularMvDeltaPartition
import SKEFTHawking.SingularSubHomologyMV
import SKEFTHawking.SingularLegWCapForm

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M5b) — the M2-direct LHS of the connecting square

The LHS of the Poincaré-duality connecting square is
`subHomConnecting U V hU hV (p+1) (legW K g) ∈ Homology (sub (U ∩ V)) (p+1)`. This file expresses it
*explicitly* through the bottom-row Mayer–Vietoris cover-partition chain action (the **M2-direct
route**), so it can be matched chain-level against the relative-MV (RHS) leg via cap-Leibniz —
sidestepping the non-chain-explicit `absCohomConn` route.

## What this file builds (all kernel-pure, all GREEN)

* `subHomConnecting_eq_seamI_mvDelta` / `subHomConnecting_eq_seamI_seamHom_mvConnecting` — the
  definitional factorisations `subHomConnecting = seamI ∘ mvDelta = seamI ∘ seamHomologyEquiv ∘
  mvConnecting` of the bottom-row MV connecting map (instantiating `SingularMayerVietorisLES` at the
  ambient space `sub (U ∪ V)` under its open cover `{val⁻¹U, val⁻¹V}`).
* `subHomConnecting_legW` — the LHS form for the actual per-compact duality leg: applies the
  factorisation directly to `legW K g` (which by `SingularLegWCapForm.legW_mk` is the cap class
  `[cap g z_K]`, a cycle of `sub (U ∪ V)`).
* `subHomConnecting_cover_partition` — the M2-direct skeleton: on a cover-partitioned cycle
  `chainIncl (val⁻¹U) zA + chainIncl (val⁻¹V) zB`, `subHomConnecting` is `seamI` of
  `seamHomologyEquiv` of the `[∂zB]`-class produced by `SingularMvDeltaPartition.mvDelta_cover_partition`
  (M2). The `[∂zB]`-class is carried abstractly as `c` with the M2 equation as a hypothesis — this
  binds the doubly-nested `restr (val⁻¹U) (val⁻¹V)` subspace as a unification variable, dodging the
  `whnf` heartbeat wall (see §Residual).
* `homology_mk_singularSd_iterate` — subdivision-homology-invariance: a cycle and its iterated
  barycentric subdivision `Sdᵐ z` are homologous (`iterHomotopy_chainHomotopy` ⟹ `z + Sdᵐ z` is a
  boundary). The homology-level input for replacing `cap g z_K` by its cover-fine subdivision.
* `singularSd_iterate_mem_cycles` — `Sdᵐ` preserves cycles.
* `exists_chainIncl_partition_of_mem_mvUnionChains` — `mvUnionChains U' V' = C(U') + C(V')` membership
  decomposes (abstractly) as `chainIncl U' zA + chainIncl V' zB` (the cover-partition extraction).
* `preimage_union_eq_univ` / `mem_subspaceChains_preimage_union` — the cover `{val⁻¹U, val⁻¹V}` of
  `sub (U ∪ V)` is total, so every chain is subordinate to it (the `exists_iterate_mvUnion`
  precondition for cover-fine subdivision).

## Residual (the precise blocking step of sub-brick (a))

Closing the LHS to the *fully concrete* `seamI (seamHomologyEquiv [∂zB])` (with `zB` the explicit
cover-fine `val⁻¹V`-part of `Sdᵐ (cap g z_K)`) is blocked by a **`whnf` heartbeat wall**, not a
mathematical gap. The wall is intrinsic to *spelling*, in a committed conclusion, any term whose type
mentions the doubly-nested subspace `sub (val⁻¹U)` / `sub (restr (val⁻¹U) (val⁻¹V))` over `sub (U ∪ V)`
with the *concrete* preimage cover (`val⁻¹U = Subtype.val ⁻¹' U`, etc.): the elaborator's `isDefEq` /
`whnf` descent through the two stacked `sub` subtypes exceeds 200 000 heartbeats. (The same wall the
M3 brick hit; cf. lab notebook PD6f-c4-M3.) Concretely, even the standalone statements
`Sdᵐ r ∈ mvUnionChains (val⁻¹U) (val⁻¹V)` and `connectingLift (restr (val⁻¹U) (val⁻¹V)) n ⟨zB, _⟩` fail
to elaborate. The mathematics is fully available — `mvDelta_cover_partition` (M2),
`exists_iterate_mvUnion`, `homology_mk_singularSd_iterate`, and
`exists_chainIncl_partition_of_mem_mvUnionChains` are each GREEN at the abstract level — so the cover-
partition + subdivision-invariance pipeline must be *assembled at the consumer site*
(`SingularConnSquareMatch.hmatch`), where the concrete preimage cover instantiates lazily as a
unification variable rather than being eagerly `whnf`-normalised. `subHomConnecting_cover_partition`
is the assembled skeleton in exactly that consumer-ready, abstract-`c` form.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularSubdivision SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularSubHomologyMV
open SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularConnSquareLHSExplicit

variable {X : TopCat}

/-- **Subdivision-homology-invariance.** A cycle `z` of degree `n+1` and its iterated barycentric
subdivision `Sdᵐ z` are homologous: by `iterHomotopy_chainHomotopy`, `∂(Dₘ z) = z + Sdᵐ z` (over `ℤ/2`,
using `∂z = 0`), so `z + Sdᵐ z` is a boundary and the two classes agree. The homology-level input for
replacing the cap cycle `cap g z_K` by its cover-fine subdivision without changing its class. -/
theorem homology_mk_singularSd_iterate (Y : TopCat) (n m : ℕ)
    (z : SingularChain Y (n + 1)) (hz : z ∈ cycles Y (n + 1))
    (hSd : (⇑(singularSd Y (n + 1)))^[m] z ∈ cycles Y (n + 1)) :
    Homology.mk Y (n + 1) ⟨z, hz⟩
      = Homology.mk Y (n + 1) ⟨(⇑(singularSd Y (n + 1)))^[m] z, hSd⟩ := by
  have hz0 : iterHomotopy Y n m (0 : SingularChain Y n) = 0 := by
    simp only [iterHomotopy, map_zero]
    exact Finset.sum_eq_zero (fun i _ => Function.iterate_fixed (map_zero _) i)
  rw [Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).2 ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  refine ⟨iterHomotopy Y (n + 1) m z, ?_⟩
  have hcyc : chainBoundary Y n z = 0 := hz
  have hh := iterHomotopy_chainHomotopy Y m n z
  rw [hcyc, hz0, add_zero] at hh
  rw [hh, sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]

/-- `Sdᵐ` of a cycle is a cycle (`Sd` is a chain map, so `∂(Sdᵐ z) = Sdᵐ(∂z) = Sdᵐ 0 = 0`). -/
theorem singularSd_iterate_mem_cycles (Y : TopCat) (n m : ℕ)
    (r : SingularChain Y (n + 1)) (hr : r ∈ cycles Y (n + 1)) :
    (⇑(singularSd Y (n + 1)))^[m] r ∈ cycles Y (n + 1) := by
  show chainBoundary Y n ((⇑(singularSd Y (n + 1)))^[m] r) = 0
  have hr0 : chainBoundary Y n r = 0 := hr
  rw [singularSd_iterate_chainBoundary, hr0]
  exact Function.iterate_fixed (map_zero _) m

/-- **mvUnionChains membership ⟹ cover partition** (abstract `M`, `U'`, `V'`). A chain in
`mvUnionChains U' V' n = C(U') + C(V')` decomposes subordinate to the cover as
`chainIncl U' zA + chainIncl V' zB`. Stated over *abstract* sets so it elaborates without forcing a
`whnf` descent through the concrete nested subspace types; applied at the concrete
cover-of-`sub (U ∪ V)` instance, the heavy leg-chain types are bound as unification variables. -/
theorem exists_chainIncl_partition_of_mem_mvUnionChains {M : TopCat} (U' V' : Set ↑M) (n : ℕ)
    (c : SingularChain M n) (hc : c ∈ mvUnionChains U' V' n) :
    ∃ (zA : SingularChain (sub U') n) (zB : SingularChain (sub V') n),
      c = chainIncl U' n zA + chainIncl V' n zB := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  obtain ⟨zA, hzA⟩ := hu
  obtain ⟨zB, hzB⟩ := hv
  exact ⟨zA, zB, by rw [← huv, ← hzA, ← hzB]⟩

/-- `val⁻¹'U ∪ val⁻¹'V = univ` in `sub (U ∪ V)`: every point of the subspace lies in `U` or `V`. -/
theorem preimage_union_eq_univ (U V : Set ↑X) :
    (Subtype.val ⁻¹' U ∪ Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  rcases p.2 with hp | hp
  · exact Or.inl hp
  · exact Or.inr hp

/-- **Every chain of `sub (U ∪ V)` is subordinate to the cover `{val⁻¹U, val⁻¹V}`** (their union is
`univ` in the subspace, so `subspaceChains = ⊤`). The `exists_iterate_mvUnion` precondition: feeding
this to `exists_iterate_mvUnion (val⁻¹U) (val⁻¹V) … r` (with both preimages open) yields an `m` with
`Sdᵐ r ∈ mvUnionChains (val⁻¹U) (val⁻¹V)` — the cover-fine subdivision. (That application is deferred
to the consumer, where the doubly-nested `sub (val⁻¹U)` leg types instantiate lazily; see §Residual.) -/
theorem mem_subspaceChains_preimage_union (U V : Set ↑X) (n : ℕ)
    (r : SingularChain (sub (U ∪ V)) n) :
    r ∈ subspaceChains
        (Subtype.val ⁻¹' U ∪ Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) n := by
  rw [preimage_union_eq_univ]
  exact SingularExcision.mem_subspaceChains_of_support (fun _ _ => Set.subset_univ _)

variable [T2Space ↑X]

omit [T2Space ↑X] in
/-- The bottom-row MV connecting map `subHomConnecting = seamI ∘ mvDelta` (definitional: it is the
Mayer–Vietoris connecting map of `sub (U ∪ V)` under `{val⁻¹U, val⁻¹V}`, post-composed with `seamI`). -/
theorem subHomConnecting_eq_seamI_mvDelta (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (w : Homology (sub (U ∪ V)) (n + 1)) :
    subHomConnecting U V hU hV n w
      = seamI U V n
          (mvDelta (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
            (cover_preimage U V hU hV) w) := rfl

omit [T2Space ↑X] in
/-- `subHomConnecting = seamI ∘ seamHomologyEquiv ∘ mvConnecting` (unfold `mvDelta`; definitional). The
pre-seam form exposing `mvConnecting`, whose cover-partition chain action is `mvConnecting_cover_partition`
(M2's pre-seam lemma) — the chain-level handle on the `[∂zB]`-class. -/
theorem subHomConnecting_eq_seamI_seamHom_mvConnecting (U V : Set ↑X) (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) (w : Homology (sub (U ∪ V)) (n + 1)) :
    subHomConnecting U V hU hV n w
      = seamI U V n
          (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n
            (mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
              (cover_preimage U V hU hV) w)) := rfl

omit [T2Space ↑X] in
/-- **M2-direct LHS skeleton.** On the class of a cover-partitioned cycle
`z = chainIncl (val⁻¹U) zA + chainIncl (val⁻¹V) zB` of `sub (U ∪ V)`, `subHomConnecting` equals `seamI`
of `seamHomologyEquiv` of the `[∂zB]`-class `c`. The `[∂zB]`-class is carried *abstractly* as `c`, with
the witnessing M2 equation (`SingularMvDeltaPartition.mvDelta_cover_partition` produces exactly this
`hc`) as a hypothesis — this binds the doubly-nested `restr (val⁻¹U) (val⁻¹V)` subspace as a
unification variable, dodging the `whnf` heartbeat wall that spelling the concrete `[∂zB]` term inline
would trigger (§Residual). The proof is the `seamI ∘ mvDelta` factorisation followed by `hc`. -/
theorem subHomConnecting_cover_partition (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (n + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (n + 1))
    (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
        + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1))
    (c : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n)
    (hc : mvDelta (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
          (cover_preimage U V hU hV) (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
        = seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n c) :
    subHomConnecting U V hU hV n (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
      = seamI U V n
          (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n c) := by
  rw [subHomConnecting_eq_seamI_mvDelta, hc]

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen in
/-- **M2-direct LHS for the per-compact duality leg.** The bottom-row MV connecting map applied to
`legW K g` (the LHS of the connecting square) factors as `seamI ∘ seamHomologyEquiv ∘ mvConnecting` of
`legW K g`. By `SingularLegWCapForm.legW_mk`, `legW K g` is the cap class `[cap g z_K]`, a cycle of
`sub (U ∪ V)`; this is the M2-direct entry, presenting the LHS via the bottom-row MV connecting map's
cover-partition chain action (`mvConnecting_cover_partition`) rather than the `absCohomConn` route. -/
theorem subHomConnecting_legW (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {k p : ℕ}
    (z₀ : SingularChain X (k + p + 1)) (hz₀ : chainBoundary X (k + p) z₀ = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) k K) :
    subHomConnecting U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g)
      = seamI U V p
          (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) p
            (mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) p
              (cover_preimage U V hU hV) (legW (m := p) (hU.union hV) z₀ hz₀ K g))) :=
  subHomConnecting_eq_seamI_seamHom_mvConnecting U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g)

end SKEFTHawking.SingularConnSquareLHSExplicit
