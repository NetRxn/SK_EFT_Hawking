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

/-- The pushforward of any simplex along the constant map `const_b` is the constant simplex. -/
theorem mapSimplex_const {X : TopCat} (b : ↑X) {k : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk k))) :
    mapSimplex (ContinuousMap.const ↑X b) σ = constSimplex b k := rfl

/-- **The constant chain map collapses to a single constant simplex** weighted by the augmentation
`ε(z) = ∑_σ z_σ`: `(const_b)_#(z) = ε(z) · c_b^k`. (All simplices push to the same `c_b^k`.) -/
theorem mapChain_const {X : TopCat} (b : ↑X) {k : ℕ} (z : SingularChain X k) :
    mapChain (ContinuousMap.const ↑X b) k z
      = Finsupp.single (constSimplex b k) (z.sum fun _ a => a) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.single_add]
  | single σ a => rw [mapChain_single, mapSimplex_const, Finsupp.sum_single_index rfl]

/-- **The constant-simplex chain `m · c_b^{k+1}` is a boundary** when its own boundary vanishes
(`m · (k : ℤ/2) = 0`). Parity: if `k` is even then `c_b^{k+1}` is itself `∂(c_b^{k+2})`; if `k` is odd
the cycle condition forces `m = 0`. -/
theorem single_constSimplex_mem_boundaries {U : TopCat} (b : ↑U) {n : ℕ} (m : ZMod 2)
    (hcyc : m * (n : ZMod 2) = 0) :
    Finsupp.single (constSimplex b (n + 1)) m ∈ boundaries U (n + 1) := by
  by_cases hn : (n : ZMod 2) = 0
  · have hb : Finsupp.single (constSimplex b (n + 1)) (1 : ZMod 2) ∈ boundaries U (n + 1) := by
      refine ⟨Finsupp.single (constSimplex b (n + 2)) 1, ?_⟩
      rw [chainBoundary_constSimplex]
      congr 1
      push_cast
      rw [hn, zero_add]
    rw [show Finsupp.single (constSimplex b (n + 1)) m
        = m • Finsupp.single (constSimplex b (n + 1)) (1 : ZMod 2) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    exact (boundaries U (n + 1)).smul_mem m hb
  · have hm0 : m = 0 := by
      have hn1 : (n : ZMod 2) = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
      rw [hn1, mul_one] at hcyc
      exact hcyc
    rw [hm0, Finsupp.single_zero]
    exact (boundaries U (n + 1)).zero_mem

/-! ## §3. Acyclicity of contractible spaces -/

/-- **Acyclicity from a contraction**: if `U` carries a contraction `H` (a homotopy with
`H(·, 0) = id` and `H(·, 1) = const_b`), then every cycle in degree `n + 1 ≥ 1` is a boundary —
`Hₙ₊₁(U; ℤ/2) = 0`. Hence contractible spaces are acyclic in positive degrees.

The contraction gives `z = H₀_#(z) = (H₁_#(z) + H₀_#(z)) + H₁_#(z)`; the first summand is a boundary
by homotopy invariance and the second is the constant chain `ε(z)·c_b^{n+1}`, a boundary by parity. -/
theorem cycle_mem_boundaries_of_contraction {U : TopCat} {n : ℕ} (H : C(↑U × unitInterval, ↑U))
    (b : ↑U) (h0 : slice H 0 = ContinuousMap.id ↑U) (h1 : slice H 1 = ContinuousMap.const ↑U b)
    (z : SingularChain U (n + 1)) (hz : chainBoundary U n z = 0) :
    z ∈ boundaries U (n + 1) := by
  have hkey := mapChain_slice_add_mem_boundaries H z hz
  rw [h0, h1, mapChain_id] at hkey
  have hcyc0 : chainBoundary U n (mapChain (ContinuousMap.const ↑U b) (n + 1) z) = 0 := by
    rw [chainBoundary_mapChain, hz, map_zero]
  rw [mapChain_const] at hcyc0 hkey
  have hcyc : (z.sum fun _ a => a) * (n : ZMod 2) = 0 := by
    rw [show Finsupp.single (constSimplex b (n + 1)) (z.sum fun _ a => a)
        = (z.sum fun _ a => a) • Finsupp.single (constSimplex b (n + 1)) (1 : ZMod 2) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, chainBoundary_constSimplex,
        Finsupp.smul_single, smul_eq_mul, Finsupp.single_eq_zero] at hcyc0
    exact hcyc0
  have hconst := single_constSimplex_mem_boundaries b (z.sum fun _ a => a) hcyc
  have hz_eq : z = (Finsupp.single (constSimplex b (n + 1)) (z.sum fun _ a => a) + z)
      + Finsupp.single (constSimplex b (n + 1)) (z.sum fun _ a => a) := by
    rw [add_right_comm, ZModModule.add_self, zero_add]
  rw [hz_eq]
  exact (boundaries U (n + 1)).add_mem hkey hconst

end SKEFTHawking.SingularHomotopyInvariance
