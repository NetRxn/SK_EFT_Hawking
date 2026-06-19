import Mathlib
import SKEFTHawking.SingularRelativeMV

/-!
# Naturality of the relative Mayer–Vietoris connecting map under cover inclusion

The MV connecting map `δ : Hₙ₊₁(M, A∪B) → Hₙ(M, A∩B)` is **natural** under an inclusion of pairs
`(A', B') ⊆ (A, B)` (componentwise `A' ⊆ A`, `B' ⊆ B`): the square

```
        δ_{A',B'}
Hₙ₊₁(M, A'∪B') ────────────► Hₙ(M, A'∩B')
     │                              │
     │ relIncl (A'∪B' ⊆ A∪B)        │ relIncl (A'∩B' ⊆ A∩B)
     ▼                              ▼
Hₙ₊₁(M, A∪B)  ────────────► Hₙ(M, A∩B)
        δ_{A,B}
```

commutes. This is the standard naturality of the MV connecting map for a map of excisive (open)
covers; the proof is entirely chain-level bookkeeping, because every inclusion here is induced by
`id_M`, which leaves the *underlying* singular chain unchanged and only re-targets its
equivalence relation / quotient submodule.
-/

namespace SKEFTHawking.SingularRelativeMVNaturality

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV

variable {M : TopCat}

/-- The chain-level pushforward of the middle term `B' = C(M,A')×C(M,B')` into `B = C(M,A)×C(M,B)`
along the cover inclusion `(A',B') ⊆ (A,B)`, induced by `id_M` on each component. -/
noncomputable def liftInclChain (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ) :
    RelativeChain A' (k + 1) × RelativeChain B' (k + 1) →ₗ[ZMod 2]
      RelativeChain A (k + 1) × RelativeChain B (k + 1) :=
  (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) (k + 1)).prodMap
    (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) (k + 1))

@[simp] theorem liftInclChain_mk (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (a c : SingularChain M (k + 1)) :
    liftInclChain A B A' B' hAA' hBB' k
        (RelativeChain.mk A' (k + 1) a, RelativeChain.mk B' (k + 1) c)
      = (RelativeChain.mk A (k + 1) a, RelativeChain.mk B (k + 1) c) := by
  simp only [liftInclChain, LinearMap.prodMap_apply, relMapChain_mk, mapChain_id]

/-- `∂_B` commutes with the lift inclusion. -/
theorem bBoundary_liftInclChain (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : RelativeChain A' (k + 1) × RelativeChain B' (k + 1)) :
    bBoundary A B k (liftInclChain A B A' B' hAA' hBB' k p)
      = (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) k).prodMap
          (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) k) (bBoundary A' B' k p) := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show bBoundary A B k (liftInclChain A B A' B' hAA' hBB' k
        (RelativeChain.mk A' (k + 1) a, RelativeChain.mk B' (k + 1) c))
      = (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) k).prodMap
          (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) k)
          (bBoundary A' B' k (RelativeChain.mk A' (k + 1) a, RelativeChain.mk B' (k + 1) c))
  rw [liftInclChain_mk, bBoundary_mk, bBoundary_mk, LinearMap.prodMap_apply, relMapChain_mk,
    relMapChain_mk, mapChain_id, mapChain_id]

/-- `C(A')+C(B') ⊆ C(A)+C(B)` for the union (small-chains) submodules under cover inclusion. -/
theorem mvUnionChains_mono (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ) :
    mvUnionChains A' B' k ≤ mvUnionChains A B k :=
  sup_le_sup (SingularMayerVietoris.subspaceChains_mono hAA' k)
    (SingularMayerVietoris.subspaceChains_mono hBB' k)

/-- `Σ` commutes with the lift inclusion up to the `QChain` inclusion `[c]_{A'B'} ↦ [c]_{AB}`:
`Σ_{AB}(liftIncl p) = ⟦Σ_{A'B'} p⟧` (the represented chain is unchanged; only the quotient
widens). -/
theorem relMvChainSum_liftInclChain (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : RelativeChain A' k × RelativeChain B' k) :
    relMvChainSum A B k
        ((relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) k).prodMap
          (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) k) p)
      = Submodule.mapQ (mvUnionChains A' B' k) (mvUnionChains A B k) LinearMap.id
          (by rw [Submodule.comap_id]; exact mvUnionChains_mono A B A' B' hAA' hBB' k)
          (relMvChainSum A' B' k p) := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show relMvChainSum A B k
      ((relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) k).prodMap
        (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) k)
        (RelativeChain.mk A' k a, RelativeChain.mk B' k c)) = _
  rw [LinearMap.prodMap_apply, relMapChain_mk, relMapChain_mk, mapChain_id, mapChain_id,
    relMvChainSum_mk]
  show Submodule.Quotient.mk (a + c)
      = Submodule.mapQ _ _ LinearMap.id _ (relMvChainSum A' B' k
          (RelativeChain.mk A' k a, RelativeChain.mk B' k c))
  rw [relMvChainSum_mk, Submodule.mapQ_apply, LinearMap.id_apply]

/-- The lift inclusion sends `L_{A'B'}` into `L_{AB}` (lift-membership is preserved). -/
theorem liftInclChain_mem (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : relLift A' B' k) :
    liftInclChain A B A' B' hAA' hBB' k (p : RelativeChain A' (k + 1) × RelativeChain B' (k + 1))
      ∈ relLift A B k := by
  rw [relLift, LinearMap.mem_ker, LinearMap.comp_apply, bBoundary_liftInclChain,
    relMvChainSum_liftInclChain]
  have hp : relMvChainSum A' B' k (bBoundary A' B' k (p : _)) = 0 := by
    have := LinearMap.mem_ker.mp p.2; rwa [LinearMap.comp_apply] at this
  rw [hp, map_zero]

/-- `Δ` is natural under the cover inclusion: pushing `(A'∩B')`-relative chains forward into `(A∩B)`
and applying `Δ_{AB}` equals applying `Δ_{A'B'}` then pushing both components into `(A,B)`. -/
theorem relMvChainDiag_natural (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (x : RelativeChain (A' ∩ B') k) :
    relMvChainDiag A B k
        (relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_inter hAA' hBB' hx) k x)
      = (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hAA' hx) k).prodMap
          (relMapChain (ContinuousMap.id ↑M) (fun _ hx => hBB' hx) k)
          (relMvChainDiag A' B' k x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relMvChainDiag A B k
      (relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_inter hAA' hBB' hx) k
        (RelativeChain.mk (A' ∩ B') k c)) = _
  rw [relMapChain_mk, mapChain_id, relMvChainDiag_mk,
    show (Submodule.Quotient.mk c : RelativeChain (A' ∩ B') k) = RelativeChain.mk (A' ∩ B') k c
      from rfl, relMvChainDiag_mk, LinearMap.prodMap_apply, relMapChain_mk, relMapChain_mk,
    mapChain_id]

/-- The chain-level `extractA` is natural: the extracted `(A'∩B')`-cycle pushed forward to `(A∩B)`
equals the `(A∩B)`-extraction of the pushed-forward lift (same underlying singular chain). -/
theorem extractA_natural (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : relLift A' B' k) :
    relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_inter hAA' hBB' hx) k
        (extractA A' B' k p)
      = extractA A B k ⟨liftInclChain A B A' B' hAA' hBB' k (p : _),
          liftInclChain_mem A B A' B' hAA' hBB' k p⟩ := by
  apply relMvChainDiag_injective A B k
  rw [relMvChainDiag_natural, relMvChainDiag_extractA, relMvChainDiag_extractA,
    bBoundary_liftInclChain]

/-- **Bridge 2 (connecting-lift naturality)**: pushing the snake-connecting class `[extractA p]`
forward along `(A'∩B') ⊆ (A∩B)` equals the snake-connecting class of the pushed-forward lift. -/
theorem relConnectingLift_natural (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : relLift A' B' k) :
    relIncl (Set.inter_subset_inter hAA' hBB') k (relConnectingLift A' B' k p)
      = relConnectingLift A B k ⟨liftInclChain A B A' B' hAA' hBB' k (p : _),
          liftInclChain_mem A B A' B' hAA' hBB' k p⟩ := by
  rw [relConnectingLift_apply, relConnectingLift_apply, relIncl_mk]
  refine congrArg (RelativeHomology.mk (A ∩ B) k) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  exact extractA_natural A B A' B' hAA' hBB' k p

/-- `ι ∘ (b ↦ [Σ b])` on a lift-chain `p` is the `Hₙ₊₁(M, U∪V)`-class of `π(Σ p)` (the underlying
singular sum), the building block for naturality of `relConnecting`'s domain identification. -/
theorem iota_relLiftToQHom (U V : Set ↑M) (k : ℕ) (p : relLift U V k) :
    iota U V (k + 1) (relLiftToQHom U V k p)
      = RelativeHomology.mk (U ∪ V) (k + 1)
          ⟨piMap U V (k + 1) (relMvChainSum U V (k + 1) (p : _)),
            piMap_mem_relCycles U V (k + 1) _ (relMvChainSum_mem_qCycles U V k p)⟩ := by
  rw [relLiftToQHom_apply, iota_mk]

/-- The underlying chain of `π(Σ p)` is unchanged by the lift inclusion: pushing
`π_{A'B'}(Σ_{A'B'} p)` forward to `(A∪B)` equals `π_{AB}(Σ_{AB}(liftIncl p))` (both are `[a + c]`
in `C(M, A∪B)`). -/
theorem piMap_relMvChainSum_liftInclChain (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B)
    (k : ℕ) (p : RelativeChain A' (k + 1) × RelativeChain B' (k + 1)) :
    relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.union_subset_union hAA' hBB' hx) (k + 1)
        (piMap A' B' (k + 1) (relMvChainSum A' B' (k + 1) p))
      = piMap A B (k + 1) (relMvChainSum A B (k + 1) (liftInclChain A B A' B' hAA' hBB' k p)) := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.union_subset_union hAA' hBB' hx) (k + 1)
      (piMap A' B' (k + 1) (relMvChainSum A' B' (k + 1)
        (RelativeChain.mk A' (k + 1) a, RelativeChain.mk B' (k + 1) c)))
    = piMap A B (k + 1) (relMvChainSum A B (k + 1) (liftInclChain A B A' B' hAA' hBB' k
        (RelativeChain.mk A' (k + 1) a, RelativeChain.mk B' (k + 1) c)))
  rw [relMvChainSum_mk, liftInclChain_mk, relMvChainSum_mk]
  show relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.union_subset_union hAA' hBB' hx) (k + 1)
      (piMap A' B' (k + 1) (QChain.mk A' B' (k + 1) (a + c)))
    = piMap A B (k + 1) (QChain.mk A B (k + 1) (a + c))
  rw [piMap_mk, piMap_mk, relMapChain_mk, mapChain_id]

/-- **Bridge 3 (`ι ∘ Σ` naturality)**: the small-chains identification of the snake domain is
natural — pushing `ι_{A'B'}([Σ p])` forward to `Hₙ₊₁(M, A∪B)` equals `ι_{AB}([Σ (liftIncl p)])`. -/
theorem iota_relLiftToQHom_natural (A B A' B' : Set ↑M) (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (k : ℕ)
    (p : relLift A' B' k) :
    relIncl (Set.union_subset_union hAA' hBB') (k + 1)
        (iota A' B' (k + 1) (relLiftToQHom A' B' k p))
      = iota A B (k + 1) (relLiftToQHom A B k ⟨liftInclChain A B A' B' hAA' hBB' k (p : _),
          liftInclChain_mem A B A' B' hAA' hBB' k p⟩) := by
  rw [iota_relLiftToQHom, iota_relLiftToQHom, relIncl_mk]
  refine congrArg (RelativeHomology.mk (A ∪ B) (k + 1)) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  exact piMap_relMvChainSum_liftInclChain A B A' B' hAA' hBB' k (p : _)

theorem relMvDelta_naturality (A B A' B' : Set ↑M)
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (hAA' : A' ⊆ A)
    (hBB' : B' ⊆ B) (k : ℕ) (w : RelativeHomology (A' ∪ B') (k + 1)) :
    SKEFTHawking.SingularRelativeMV.relIncl (Set.inter_subset_inter hAA' hBB') k
        (SKEFTHawking.SingularRelativeMV.relMvDelta A' B' hA' hB' k w)
      = SKEFTHawking.SingularRelativeMV.relMvDelta A B hA hB k
        (SKEFTHawking.SingularRelativeMV.relIncl (Set.union_subset_union hAA' hBB') (k + 1) w) := by
  -- Pick a lift-chain `b'` representing `(iotaEquiv A' B').symm w` in the snake domain.
  obtain ⟨b', hb'⟩ :=
    relLiftToQHom_surjective A' B' k ((iotaEquiv A' B' hA' hB' k).symm w)
  set b : relLift A B k :=
    ⟨liftInclChain A B A' B' hAA' hBB' k (b' : _), liftInclChain_mem A B A' B' hAA' hBB' k b'⟩
    with hb_def
  -- LHS: `relMvDelta A' B' w = relConnecting A' B' (iotaEquiv.symm w) = relConnectingLift b'`.
  have hLHS : relMvDelta A' B' hA' hB' k w = relConnectingLift A' B' k b' := by
    rw [relMvDelta, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb', relConnecting_relLiftToQHom]
  -- The pushed-up class `relIncl(∪) w` is `iota A B (relLiftToQHom b)`.
  have hw : relIncl (Set.union_subset_union hAA' hBB') (k + 1) w
      = iota A B (k + 1) (relLiftToQHom A B k b) := by
    have hwq : w = iota A' B' (k + 1) (relLiftToQHom A' B' k b') := by
      rw [hb']
      exact ((iotaEquiv A' B' hA' hB' k).apply_symm_apply w).symm
    rw [hwq, hb_def, iota_relLiftToQHom_natural]
  -- RHS: `relMvDelta A B (relIncl(∪) w) = relConnectingLift A B b`.
  have hRHS : relMvDelta A B hA hB k (relIncl (Set.union_subset_union hAA' hBB') (k + 1) w)
      = relConnectingLift A B k b := by
    rw [hw, relMvDelta, LinearMap.comp_apply, LinearEquiv.coe_coe,
      show (iotaEquiv A B hA hB k).symm (iota A B (k + 1) (relLiftToQHom A B k b))
        = relLiftToQHom A B k b from (iotaEquiv A B hA hB k).symm_apply_apply _,
      relConnecting_relLiftToQHom]
  rw [hLHS, hRHS, relConnectingLift_natural]

end SKEFTHawking.SingularRelativeMVNaturality
