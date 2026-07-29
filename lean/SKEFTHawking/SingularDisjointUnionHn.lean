import Mathlib
import SKEFTHawking.SingularDisjointUnion

/-!
# Degree-general disjoint-union additivity (`Hₙ(A ⊔ B) ≅ Hₙ(A) × Hₙ(B)`)

`SingularDisjointUnion` proves the additivity isomorphism `H₀(X) ≅ H₀(U) × H₀(Uᶜ)` for a clopen
partition `X = U ⊔ Uᶜ`. The chain-level argument behind it is **degree-agnostic**: a singular simplex
has connected image, so it lands wholly in `U` or in `Uᶜ` (`simplex_range_subset_or_compl`), whence
`Cₖ(X) = Cₖ(U) ⊔ Cₖ(Uᶜ)` at *every* `k` (`subspaceChains_sup_compl_eq_top`,
`subspaceChains_inf_compl_eq_bot` are already stated for all `k`). This module lifts the split from
`H₀` to **every degree `n`**:

* `cycles_split` — a chain `iU(zU) + iUᶜ(zUc)` is a cycle of `X` iff each piece is a cycle of its own
  subspace (the only degree-sensitive step: for `n = 0` cycles are `⊤`, for `n = m+1` the boundary
  splits across the clopen partition and the two pieces separate);
* `splitHn` / `splitHnEquiv` — the additivity map `Hₙ(U) × Hₙ(Uᶜ) → Hₙ(X)` and its bijectivity,
  proved by the same surjectivity (chain split) + injectivity (`chainIncl_add_mem_boundaries_split_n`)
  pattern as the degree-0 case.

This is the missing H₁ ⊔-additivity the membrane-realization seam (`GeoMembrane.bInc`) consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularReducedH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcision
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularDisjointUnionHn

/-- Over a `ℤ/2`-module, `a + b = 0` forces `a = b` (every element is its own negative). -/
private theorem eq_of_add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b : M}
    (h : a + b = 0) : a = b := by
  rw [← neg_eq_of_add_eq_zero_left h]; exact neg_eq_of_add_eq_zero_left (ZModModule.add_self b)

/-! ## §1. The cycle split -/

/-- **A split chain is a cycle iff both pieces are cycles.** The only degree-sensitive step of
degree-general additivity: in degree `0` every chain is a cycle (`⊤`); in degree `m+1` the boundary
`∂(iU zU + iUᶜ zUc) = iU(∂zU) + iUᶜ(∂zUc)` splits across the clopen partition, and since the two
pieces live in `subspaceChains U m` and `subspaceChains Uᶜ m` with intersection `⊥`, `∂(iU zU + iUᶜ
zUc) = 0` forces each `∂` to vanish (chain-inclusion injectivity). -/
theorem cycles_split {X : TopCat} {U : Set ↑X} (n : ℕ) (zU : SingularChain (sub U) n)
    (zUc : SingularChain (sub Uᶜ) n)
    (h : chainIncl U n zU + chainIncl Uᶜ n zUc ∈ cycles X n) :
    zU ∈ cycles (sub U) n ∧ zUc ∈ cycles (sub Uᶜ) n := by
  cases n with
  | zero => exact ⟨Submodule.mem_top, Submodule.mem_top⟩
  | succ m =>
    rw [cycles, LinearMap.mem_ker, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary]
      at h
    have hkey : chainIncl U m (chainBoundary (sub U) m zU)
        = chainIncl Uᶜ m (chainBoundary (sub Uᶜ) m zUc) := eq_of_add_eq_zero_two h
    have hmemU : chainIncl U m (chainBoundary (sub U) m zU)
        ∈ subspaceChains (S := U) m ⊓ subspaceChains (S := Uᶜ) m := ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
    rw [subspaceChains_inf_compl_eq_bot, Submodule.mem_bot] at hmemU
    have hzU : chainBoundary (sub U) m zU = 0 :=
      chainIncl_injective U m (hmemU.trans (map_zero _).symm)
    have hzUc : chainBoundary (sub Uᶜ) m zUc = 0 :=
      chainIncl_injective Uᶜ m ((hkey ▸ hmemU).trans (map_zero _).symm)
    exact ⟨LinearMap.mem_ker.mpr hzU, LinearMap.mem_ker.mpr hzUc⟩

/-! ## §2. The additivity map and its bijectivity -/

/-- **The degree-`n` additivity map** `Hₙ(U) × Hₙ(Uᶜ) → Hₙ(X)`, `(a, b) ↦ i_*(a) + i_*(b)`. -/
noncomputable def splitHn {X : TopCat} (U : Set ↑X) (n : ℕ) :
    Homology (sub U) n × Homology (sub Uᶜ) n →ₗ[ZMod 2] Homology X n :=
  (homIncl U n).coprod (homIncl Uᶜ n)

/-- `splitHn` is **surjective**: every `n`-cycle of `X` splits across the clopen partition
(`subspaceChains_sup_compl_eq_top`), and each piece is again a cycle (`cycles_split`). -/
theorem splitHn_surjective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ) :
    Function.Surjective (splitHn U n) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : SingularChain X n) ∈ subspaceChains (S := U) n ⊔ subspaceChains (S := Uᶜ) n := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hz
  obtain ⟨_, ⟨zU, rfl⟩, _, ⟨zUc, rfl⟩, hsum⟩ := hz
  obtain ⟨hzUc, hzUcc⟩ := cycles_split n zU zUc (hsum ▸ z.2)
  refine ⟨(Homology.mk (sub U) n ⟨zU, hzUc⟩, Homology.mk (sub Uᶜ) n ⟨zUc, hzUcc⟩), ?_⟩
  show homIncl U n (Homology.mk (sub U) n _) + homIncl Uᶜ n (Homology.mk (sub Uᶜ) n _)
      = Homology.mk X n z
  rw [homIncl_mk, homIncl_mk,
    show z = (⟨_, chainIncl_mem_cycles U n _ hzUc⟩ : cycles X n)
        + ⟨_, chainIncl_mem_cycles Uᶜ n _ hzUcc⟩ from Subtype.ext hsum.symm]
  rfl

/-- **The chain-level injectivity core** (degree-general): if a `U`-cycle plus a `Uᶜ`-cycle is a
boundary in `X`, each piece is a boundary in its own subspace. Splits the bounding `(n+1)`-chain
across the clopen partition and separates the two pieces. Verbatim the degree-0 argument with `0 ↦ n`,
`1 ↦ n+1`. -/
theorem chainIncl_add_mem_boundaries_split_n {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ)
    (zU : SingularChain (sub U) n) (zUc : SingularChain (sub Uᶜ) n)
    (h : chainIncl U n zU + chainIncl Uᶜ n zUc ∈ boundaries X n) :
    zU ∈ boundaries (sub U) n ∧ zUc ∈ boundaries (sub Uᶜ) n := by
  obtain ⟨w, hw⟩ := h
  have hwsplit : w ∈ subspaceChains (S := U) (n + 1) ⊔ subspaceChains (S := Uᶜ) (n + 1) := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hwsplit
  obtain ⟨_, ⟨wU, rfl⟩, _, ⟨wUc, rfl⟩, hwsum⟩ := hwsplit
  rw [← hwsum, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at hw
  set bU := chainBoundary (sub U) n wU
  set bUc := chainBoundary (sub Uᶜ) n wUc
  have hkey : chainIncl U n (bU + zU) = chainIncl Uᶜ n (bUc + zUc) := by
    apply eq_of_add_eq_zero_two
    rw [map_add, map_add,
      show chainIncl U n bU + chainIncl U n zU + (chainIncl Uᶜ n bUc + chainIncl Uᶜ n zUc)
        = (chainIncl U n bU + chainIncl Uᶜ n bUc) + (chainIncl U n zU + chainIncl Uᶜ n zUc) from by
          abel,
      hw, ZModModule.add_self]
  have hmemU : chainIncl U n (bU + zU) ∈ subspaceChains (S := U) n ⊓ subspaceChains (S := Uᶜ) n :=
    ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
  rw [subspaceChains_inf_compl_eq_bot, Submodule.mem_bot] at hmemU
  have hzU : zU = bU :=
    (eq_of_add_eq_zero_two (chainIncl_injective U n (hmemU.trans (map_zero _).symm))).symm
  have hzUc : zUc = bUc :=
    (eq_of_add_eq_zero_two
      (chainIncl_injective Uᶜ n ((hkey ▸ hmemU).trans (map_zero _).symm))).symm
  exact ⟨⟨wU, hzU.symm⟩, ⟨wUc, hzUc.symm⟩⟩

/-- `splitHn` on a pair of quotient representatives is the class of the summed cycle. Extracted
from `splitHn_injective` as its own declaration: the defeq is `rfl`, but at Mathlib v4.32 unfolding
`splitHn`/`coprod`/`homIncl` down to `Homology.mk` costs enough that keeping it inline exhausts the
caller's heartbeat budget. -/
private theorem splitHn_mk_mk {X : TopCat} (U : Set ↑X) (n : ℕ) (zU : cycles (sub U) n)
    (zUc : cycles (sub Uᶜ) n) :
    splitHn U n (Submodule.Quotient.mk zU, Submodule.Quotient.mk zUc)
      = Homology.mk X n ⟨chainIncl U n (zU : SingularChain (sub U) n)
          + chainIncl Uᶜ n (zUc : SingularChain (sub Uᶜ) n),
          Submodule.add_mem _ (chainIncl_mem_cycles U n _ zU.2)
            (chainIncl_mem_cycles Uᶜ n _ zUc.2)⟩ := rfl

/-- A homology class vanishes exactly when its representing cycle is a boundary. Stated with the
`submoduleOf` membership verbatim: rephrasing the right-hand side as `↑z ∈ boundaries X n` inside
this declaration makes v4.32 reconcile the two membership forms by `isDefEq` and blows the budget. -/
private theorem mk_eq_zero_iff {X : TopCat} (n : ℕ) (z : cycles X n) :
    Homology.mk X n z = 0 ↔ z ∈ (boundaries X n).submoduleOf (cycles X n) :=
  Submodule.Quotient.mk_eq_zero _

/-- `splitHn` is **injective** (the chain-level core `chainIncl_add_mem_boundaries_split_n`). -/
theorem splitHn_injective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ) :
    Function.Injective (splitHn U n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [splitHn_mk_mk] at hab
  have hab' : chainIncl U n (zU : SingularChain (sub U) n)
      + chainIncl Uᶜ n (zUc : SingularChain (sub Uᶜ) n) ∈ boundaries X n :=
    Submodule.mem_comap.mp ((mk_eq_zero_iff n _).mp hab)
  obtain ⟨hzU, hzUc⟩ := chainIncl_add_mem_boundaries_split_n hU n _ _ hab'
  rw [Submodule.mem_bot, Prod.ext_iff]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzU),
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzUc)⟩

/-- **Degree-`n` disjoint-union additivity**: `Hₙ(X) ≅ Hₙ(U) × Hₙ(Uᶜ)` for a clopen partition. -/
noncomputable def splitHnEquiv {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (n : ℕ) :
    (Homology (sub U) n × Homology (sub Uᶜ) n) ≃ₗ[ZMod 2] Homology X n :=
  LinearEquiv.ofBijective (splitHn U n) ⟨splitHn_injective hU n, splitHn_surjective hU n⟩

end SKEFTHawking.SingularDisjointUnionHn
