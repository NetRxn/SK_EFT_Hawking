/-
# Route (c′) P2 — the cap–connecting naturality square

The pair-LES connecting map `δ = SingularPairLES.connecting` intertwines the RELATIVE cap `capRelH`
(in `X`) with the ABSOLUTE cap `capH` (in the subspace `sub S`) restricted along the inclusion:

  **`connecting S 2 (capRelH 2 2 a z) = capH 2 1 (restrict a) (connecting S 4 z)`**

for `a ∈ H²(X)`, `z ∈ H₅(X,S)`, `restrict a = a|_{sub S}` the cohomology pullback along `sub S ↪ X`.
Chain-level: on a lift representative `c` (`∂c ∈ C(S)`) both sides descend to
`[∂(a ⌢ c)] = [(a|_S) ⌢ ∂c]` in `Hₙ(sub S)`, via the cocycle cap chain-map `∂(a⌢c) = a⌢∂c`
(`cap_cocycle_chainMap`) and the cap–inclusion naturality `a ⌢ (chainIncl d) = chainIncl ((a|_S) ⌢ d)`
(`SingularCapChainIncl.cap_chainIncl`) — front-faces of `S`-simplices are `S`-simplices. This is the
route-(c′) intertwining that pushes `a₀ ⌢ cls` to the closed boundary `H₂(S²×S²)`, generic in `(X, S)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularRelativeCapHomology
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularCohomologyFunctoriality

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularCapChainIncl

namespace SKEFTHawking.SingularCapConnecting

variable {X : TopCat} (S : Set X)

/-- **The subspace inclusion as a continuous map** `sub S ↪ X` (`Subtype.val`). The map along which the
cochain is restricted; `cohomologyPullback (inclC S)` is the `H²` restriction `a ↦ a|_{sub S}`. -/
def inclC : C(↑(sub S), ↑X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- `mapSimplex (inclC S)` is `simplexIncl S` — both push a `sub S`-simplex through the inclusion
`sub S ↪ X`. -/
theorem mapSimplex_inclC (n : ℕ)
    (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    SKEFTHawking.SingularFunctoriality.mapSimplex (inclC S) σ = simplexIncl S n σ := rfl

/-- The cohomology-level restriction's cochain `cochainPullback (inclC S)` IS the connecting-square
restriction `pullbackCochain S` (both `f ↦ f ∘ simplexIncl`). -/
theorem cochainPullback_inclC (k : ℕ) (f : SingularCochain X k) :
    cochainPullback (inclC S) k f = pullbackCochain S k f := rfl

/-! ## §1. Cap preserves the connecting lift-submodule -/

/-- **Capping an absolute cocycle preserves the lift-submodule** `Z_n = {c | ∂c ∈ C(S)}`: for a cocycle
`f` and `c ∈ Z_{k+n}`, `∂(f ⌢ c) = f ⌢ (∂c) ∈ C(S)` (`cap_cocycle_chainMap` + `cap_mem_subspaceChains`),
so `f ⌢ c ∈ Z_n`. -/
theorem cap_mem_relCycleLift (f : SingularCochain X 2) (hf : coboundaryₗ X 2 f = 0)
    (c : relCycleLift S 4) :
    cap (m := 3) f (c : SingularChain X 5) ∈ relCycleLift S 2 := by
  show chainBoundary X 2 (cap (m := 3) f (c : SingularChain X 5)) ∈ subspaceChains S 2
  rw [cap_cocycle_chainMap (m := 2) f hf (c : SingularChain X 5)]
  exact cap_mem_subspaceChains f (Submodule.mem_comap.mp c.2)

/-! ## §2. The chain-level core: `boundaryExtract (f ⌢ c) = (f|_S) ⌢ boundaryExtract c` -/

/-- **The connecting-cap chain identity.** In the subspace complex, extracting the boundary of the
capped lift-chain equals capping the restricted cochain against the extracted boundary:
`(chainIncl)⁻¹ ∂(f ⌢ c) = (f|_S) ⌢ (chainIncl)⁻¹ ∂c`. Both re-include (via `chainIncl`, injective) to
`f ⌢ ∂c` — LHS by `cap_cocycle_chainMap`, RHS by `cap_chainIncl` (cap–inclusion naturality). -/
theorem boundaryExtract_cap (f : SingularCochain X 2) (hf : coboundaryₗ X 2 f = 0)
    (c : relCycleLift S 4) :
    boundaryExtract S 2 ⟨cap (m := 3) f (c : SingularChain X 5), cap_mem_relCycleLift S f hf c⟩
      = cap (m := 2) (pullbackCochain S 2 f) (boundaryExtract S 4 c) := by
  apply chainIncl_injective S 2
  have hL : chainIncl S 2
        (boundaryExtract S 2 ⟨cap (m := 3) f (c : SingularChain X 5), cap_mem_relCycleLift S f hf c⟩)
      = cap (m := 2) f (chainBoundary X 4 (c : SingularChain X 5)) := by
    rw [chainIncl_boundaryExtract, cap_cocycle_chainMap (m := 2) f hf (c : SingularChain X 5)]
  have hR : chainIncl S 2 (cap (m := 2) (pullbackCochain S 2 f) (boundaryExtract S 4 c))
      = cap (m := 2) f (chainBoundary X 4 (c : SingularChain X 5)) := by
    rw [← cap_chainIncl (S := S) (k := 2) (m := 2) f (boundaryExtract S 4 c),
      chainIncl_boundaryExtract]
  rw [hL, hR]

/-! ## §3. The homology-level naturality square -/

/-- **The cap–connecting naturality square.** `δ(a ⌢ z) = (a|_S) ⌢ (δ z)`: the connecting map carries
the relative cap `capRelH 2 2` to the absolute cap `capH 2 1` of the restricted class. Generic in the
pair `(X, S)`; the route-(c′) intertwining. -/
theorem connecting_capRelH (a : Cohomology X 2) (z : RelativeHomology S 5) :
    connecting S 2 (capRelH 2 2 a z)
      = capH 2 1 (cohomologyPullback (inclC S) 2 a) (connecting S 4 z) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S 4 z
  rw [show (Submodule.Quotient.mk f : Cohomology X 2) = Cohomology.mk X 2 f from rfl]
  -- LHS: express `capRelH 2 2 [f] (relCycleToHom c)` as `relCycleToHom (f ⌢ c)`.
  have hcap := cap_mem_relCycleLift S f.1 f.2 c
  have hz_eq : capRelH 2 2 (Cohomology.mk X 2 f) (relCycleToHom S 4 c)
      = relCycleToHom S 2 ⟨cap (m := 3) f.1 (c : SingularChain X 5), hcap⟩ := by
    rw [relCycleToHom_apply, capRelH_mk_mk, relCycleToHom_apply]
    congr 1
  rw [hz_eq, connecting_relCycleToHom, connectingLift_apply, connecting_relCycleToHom,
    connectingLift_apply, cohomologyPullback_mk, capH_mk_mk]
  -- reduce to the chain-level core (`cochainPullback (inclC S) = pullbackCochain S` by defeq)
  refine congrArg (Homology.mk (sub S) 2) (Subtype.ext ?_)
  rw [capCyclesₗ_coe]
  exact boundaryExtract_cap S f.1 f.2 c

end SKEFTHawking.SingularCapConnecting
