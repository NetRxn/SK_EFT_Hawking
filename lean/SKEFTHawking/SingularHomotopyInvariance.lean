import Mathlib
import SKEFTHawking.SingularPrism
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularH0

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

/-- The underlying chain of a cycle-level difference is `f_#(z) + g_#(z)` (over ℤ/2 the subtraction
is addition). Stated for generic `f`, `g` so the homology-quotient proof never elaborates the
expensive `slice` map. -/
private theorem cyclesMap_sub_coe {X Y : TopCat} (f g : C(↑X, ↑Y)) (n : ℕ) (z : cycles X (n + 1)) :
    (cycles Y (n + 1)).subtype (cyclesMap f (n + 1) z - cyclesMap g (n + 1) z)
      = mapChain f (n + 1) (z : SingularChain X (n + 1))
        + mapChain g (n + 1) (z : SingularChain X (n + 1)) := by
  rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply, cyclesMap_coe, cyclesMap_coe,
    sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]

/-- **Homology agreement from a chain-level boundary condition**: if `f_#(z) + g_#(z)` is a boundary
for every cycle `z`, then `f` and `g` induce the same map on `Hₙ₊₁(·; ℤ/2)`. Generic `f`, `g` keeps
the quotient manipulation away from the expensive `slice` whnf. -/
theorem Homology.map_eq_of_chain_add_mem {X Y : TopCat} (f g : C(↑X, ↑Y)) (n : ℕ)
    (hfg : ∀ z : SingularChain X (n + 1), chainBoundary X n z = 0 →
        mapChain f (n + 1) z + mapChain g (n + 1) z ∈ boundaries Y (n + 1)) :
    Homology.map f (n + 1) = Homology.map g (n + 1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Homology.map, Homology.map]
  refine (Submodule.mapQ_apply _ _ _ _).trans
    (Eq.trans ((Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ?_))
      (Submodule.mapQ_apply _ _ _ _).symm)
  rw [cyclesMap_sub_coe]
  exact hfg z z.2

/-- **Homotopy invariance of the homology functor** (degree `≥ 1`): the two slices `H(·, 1)` and
`H(·, 0)` induce the same map on `Hₙ₊₁(·; ℤ/2)`, so homotopic maps are equal on homology. -/
theorem Homology.map_slice_eq {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ) :
    Homology.map (slice H 1) (n + 1) = Homology.map (slice H 0) (n + 1) :=
  Homology.map_eq_of_chain_add_mem (slice H 1) (slice H 0) n
    (fun z hz => mapChain_slice_add_mem_boundaries H z hz)

/-- **Homotopic maps induce equal maps on homology** (degree `≥ 1`): if `f` and `g` are the two ends
of a homotopy `H` then `Hₙ₊₁(f) = Hₙ₊₁(g)`. -/
theorem Homology.map_eq_of_homotopic {X Y : TopCat} {f g : C(↑X, ↑Y)}
    (H : C(↑X × unitInterval, ↑Y)) (h0 : slice H 0 = f) (h1 : slice H 1 = g) (n : ℕ) :
    Homology.map f (n + 1) = Homology.map g (n + 1) := by
  rw [← h0, ← h1]
  exact (Homology.map_slice_eq H n).symm

/-- **A homotopy equivalence induces an isomorphism on homology** (degree `≥ 1`): given `f : X → Y`,
`g : Y → X` with `g ∘ f ≃ id_X` and `f ∘ g ≃ id_Y` (witnessed by homotopies), `Hₙ₊₁(f)` is bijective.
This is the engine behind `ℝⁿ ∖ 0 ≃ Sⁿ⁻¹` and the Mayer–Vietoris hemisphere identifications. -/
theorem Homology.map_bijective_of_homotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (Homology.map f (n + 1)) := by
  have hgf : (Homology.map g (n + 1)).comp (Homology.map f (n + 1)) = LinearMap.id := by
    rw [← Homology.map_comp, Homology.map_eq_of_homotopic Hgf hgf0 hgf1, Homology.map_id]
  have hfg : (Homology.map f (n + 1)).comp (Homology.map g (n + 1)) = LinearMap.id := by
    rw [← Homology.map_comp, Homology.map_eq_of_homotopic Hfg hfg0 hfg1, Homology.map_id]
  have hL : Function.LeftInverse (Homology.map g (n + 1)) (Homology.map f (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hgf, LinearMap.id_apply]
  have hR : Function.RightInverse (Homology.map g (n + 1)) (Homology.map f (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hfg, LinearMap.id_apply]
  exact ⟨hL.injective, hR.surjective⟩

/-- **A pair of maps with identity composites** (e.g. the two halves of a homeomorphism) induces an
isomorphism on `Hₙ₊₁(·; ℤ/2)`. Special case of `map_bijective_of_homotopyEquiv` with the constant
homotopies (the composites are literally the identity). -/
theorem Homology.map_bijective_of_comp_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (Homology.map f (n + 1)) :=
  Homology.map_bijective_of_homotopyEquiv f g ⟨fun p => p.1, continuous_fst⟩
    (by rw [hgf]; exact ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
    ⟨fun p => p.1, continuous_fst⟩
    (by rw [hfg]; exact ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n

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

/-! ## §4. Reduced `H̃₀ = 0` of a contractible space -/

/-- **Reduced `H̃₀ = 0` from a contraction**: if `U` carries a contraction `H` (`H(·, 0) = id`,
`H(·, 1) = const_b`), then every `0`-chain in the kernel of the augmentation `ε` is a boundary.
Since every `0`-chain is a cycle (`cycles U 0 = ⊤`) this says the augmentation `H₀(U; ℤ/2) → ℤ/2`
is injective, hence (with `augmentation_surjective`) `H₀(U) ≅ ℤ/2` and reduced `H̃₀(U) = 0`.

Degree-`0` analogue of `cycle_mem_boundaries_of_contraction`, but cleaner: the degree-`0` prism
homotopy `∂ ∘ P = g_# + f_#` has no `P∂` term, so `∂(P z) = (const_b)_#(z) + z`, and the constant
pushforward `(const_b)_#(z) = ε(z) · c_b⁰` vanishes on `ker ε`. No parity argument is needed. -/
theorem augmentation_ker_le_boundaries_of_contraction {U : TopCat} (H : C(↑U × unitInterval, ↑U))
    (b : ↑U) (h0 : slice H 0 = ContinuousMap.id ↑U) (h1 : slice H 1 = ContinuousMap.const ↑U b)
    (z : SingularChain U 0) (hz : SingularH0.augmentation U z = 0) :
    z ∈ boundaries U 0 := by
  refine ⟨prismOp H 0 z, ?_⟩
  rw [prism_chainHomotopy_zero, endMap_eq_mapChain, endMap_eq_mapChain, h0, h1, mapChain_id,
    mapChain_const, ← SingularH0.augmentation_apply, hz, Finsupp.single_zero, zero_add]

/-- **The augmentation `ε̄ : H₀(U) → ℤ/2` is injective for a contractible space** — its kernel is
reduced `H̃₀(U)`, trivial by `augmentation_ker_le_boundaries_of_contraction`. -/
theorem augH_injective_of_contraction {U : TopCat} (H : C(↑U × unitInterval, ↑U)) (b : ↑U)
    (h0 : slice H 0 = ContinuousMap.id ↑U) (h1 : slice H 1 = ContinuousMap.const ↑U b) :
    Function.Injective (SingularH0.augH U) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot _).mpr ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ?_))
  exact augmentation_ker_le_boundaries_of_contraction H b h0 h1 (z : SingularChain U 0) hx

/-- **`H₀(U; ℤ/2) ≅ ℤ/2` for a contractible space** `U`: the augmentation `ε̄` is bijective
(surjective on any nonempty space, injective by contractibility). Hence reduced `H̃₀(U) = 0`. -/
noncomputable def homologyZeroContractibleEquiv {U : TopCat} (H : C(↑U × unitInterval, ↑U)) (b : ↑U)
    (h0 : slice H 0 = ContinuousMap.id ↑U) (h1 : slice H 1 = ContinuousMap.const ↑U b) :
    Homology U 0 ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (SingularH0.augH U)
    ⟨augH_injective_of_contraction H b h0 h1, SingularH0.augH_surjective U (constSimplex b 0)⟩

end SKEFTHawking.SingularHomotopyInvariance
