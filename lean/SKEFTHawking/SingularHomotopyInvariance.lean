import Mathlib
import SKEFTHawking.SingularPrism
import SKEFTHawking.SingularFunctoriality

/-!
# Homotopy invariance, functor level

The prism's endpoint chain map `endMap H r` is exactly the pushforward `mapChain` of the time-`r`
slice `H(·, r) : X → Y` (`endMap_eq_mapChain`). Combined with `endMap_add_mem_boundaries`, this gives
homotopy invariance of the homology functor: homotopic maps induce equal maps on `Hₙ(·; ℤ/2)`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularPrism
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularExcisionPushforward

namespace SKEFTHawking.SingularHomotopyInvariance

/-- The time-`r` slice of a homotopy `H : X × I → Y` as a continuous map `X → Y`, `x ↦ H(x, r)`. -/
noncomputable def slice {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval) :
    C(↑X, ↑Y) :=
  H.comp ((ContinuousMap.id ↑X).prodMk (ContinuousMap.const ↑X r))

/-- The endpoint simplex is the pushforward of the slice (definitionally). -/
theorem endSimplex_eq_mapSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (r : unitInterval) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    endSimplex H r σ = mapSimplex (slice H r) σ := rfl

/-- **The endpoint map is the pushforward of the slice**: `endMap H r = (H(·, r))_#`. This transports
the prism's chain-level homotopy invariance to the homology functor. -/
theorem endMap_eq_mapChain {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval) (n : ℕ)
    (c : SingularChain X n) :
    endMap H r n c = mapChain (slice H r) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => rw [endMap_single, mapChain_single, endSimplex_eq_mapSimplex]

/-- **Homotopy invariance, chain level** (restated for slices): for a cycle `z`, the two slices
`H(·, 1)_#` and `H(·, 0)_#` differ by a boundary. This is `endMap_add_mem_boundaries` transported
across `endMap_eq_mapChain`; it is the engine of acyclicity (a contractible space has `Hₖ = 0` for
`k ≥ 1`), proved at the submodule level to avoid the homology-quotient elaboration. -/
theorem mapChain_slice_add_mem_boundaries {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (z : SingularChain X (n + 1)) (hz : chainBoundary X n z = 0) :
    mapChain (slice H 1) (n + 1) z + mapChain (slice H 0) (n + 1) z ∈ boundaries Y (n + 1) := by
  rw [← endMap_eq_mapChain, ← endMap_eq_mapChain]
  exact endMap_add_mem_boundaries H z hz

/-! ## §2. The constant simplex (towards acyclicity of contractible spaces) -/

/-- The **constant `k`-simplex** at a point `b ∈ X`: the realization `Δᵏ → X` of the constant map. -/
noncomputable def constSimplex {X : TopCat} (b : ↑X) (k : ℕ) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk k)) :=
  (X.toSSetObjEquiv (op (SimplexCategory.mk k))).symm (ContinuousMap.const _ b)

/-- Every face of a constant simplex is the constant simplex one degree down. -/
theorem face_constSimplex {X : TopCat} (b : ↑X) (k : ℕ) (i : Fin (k + 2)) :
    face i (constSimplex b (k + 1)) = constSimplex b k := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  simp only [constSimplex, toSSetObjEquiv_symm_face, Equiv.apply_symm_apply]
  rfl

/-- **The boundary of a constant simplex**: `∂(c_b^{k+1}) = (k : ℤ/2) · c_b^k` — the `k + 2` faces all
coincide with `c_b^k`, so over ℤ/2 the sum is `(k + 2) ≡ k` copies. This is the heart of the parity
computation `Hₖ(point) = 0` and of acyclicity. -/
theorem chainBoundary_constSimplex {X : TopCat} (b : ↑X) (k : ℕ) :
    chainBoundary X k (Finsupp.single (constSimplex b (k + 1)) 1)
      = Finsupp.single (constSimplex b k) (k : ZMod 2) := by
  rw [chainBoundary_single, boundaryBasis]
  have hface : ∀ i : Fin (k + 2),
      Finsupp.single (face i (constSimplex b (k + 1))) (1 : ZMod 2)
        = Finsupp.single (constSimplex b k) 1 :=
    fun i => congrArg (Finsupp.single · (1 : ZMod 2)) (face_constSimplex b k i)
  rw [Finset.sum_congr rfl (fun i _ => hface i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finsupp.smul_single, nsmul_eq_mul, mul_one]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_self, add_zero]

end SKEFTHawking.SingularHomotopyInvariance
