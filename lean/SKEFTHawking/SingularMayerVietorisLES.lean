import Mathlib
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularMayerVietoris
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularHomotopyInvariance

/-!
# Mayer–Vietoris: the homology-level maps `Hₙ(A∩B) → Hₙ(A)⊕Hₙ(B) → Hₙ(X)`

The "easy half" of the Mayer–Vietoris long exact sequence (toward the fundamental-class gluing,
Hatcher 3.26). Built on the general homology functoriality `Homology.map` (`SingularFunctoriality`)
applied to the subspace inclusions:

* `mvHomDiag : Hₙ(A∩B) → Hₙ(A) ⊕ Hₙ(B)`, `w ↦ ((ι_{A∩B↪A})_* w, (ι_{A∩B↪B})_* w)` — the diagonal of
  the two inclusion-induced maps;
* `mvHomSum : Hₙ(A) ⊕ Hₙ(B) → Hₙ(X)`, `(u, v) ↦ (ι_{A↪X})_* u + (ι_{B↪X})_* v` — the sum (a difference
  over `ℤ/2`) of the two inclusions.

The composite property `mvHomSum ∘ mvHomDiag = 0` holds because both routes `A∩B ↪ A ↪ X` and
`A∩B ↪ B ↪ X` equal the single inclusion `A∩B ↪ X` (functoriality `Homology.map_comp`), so the sum is
`(ι_{A∩B↪X})_* w + (ι_{A∩B↪X})_* w = 0` over `ℤ/2`. This is the chain-complex condition of the MV
sequence at `Hₙ(A)⊕Hₙ(B)`; with the connecting map `δ` (next brick) it becomes the full LES.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SingularMayerVietorisLES

variable {X : TopCat}

/-- The inclusion of a subspace into the ambient space `↥S ↪ X` as a continuous map. -/
def ambIncl (S : Set ↑X) : C(↑(sub S), ↑X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of one subspace into a larger one `↥s ↪ ↥t` (for `s ⊆ t`) as a continuous map. -/
def subIncl {s t : Set ↑X} (h : s ⊆ t) : C(↑(sub s), ↑(sub t)) :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The two routes `↥(A∩B) ↪ ↥A ↪ X` and `↥(A∩B) ↪ X` agree (both are `Subtype.val`). -/
theorem ambIncl_comp_subIncl_left (A B : Set ↑X) :
    (ambIncl A).comp (subIncl (Set.inter_subset_left (s := A) (t := B))) = ambIncl (A ∩ B) :=
  ContinuousMap.ext fun _ => rfl

theorem ambIncl_comp_subIncl_right (A B : Set ↑X) :
    (ambIncl B).comp (subIncl (Set.inter_subset_right (s := A) (t := B))) = ambIncl (A ∩ B) :=
  ContinuousMap.ext fun _ => rfl

/-- **The MV diagonal** `Hₙ(A∩B) → Hₙ(A) ⊕ Hₙ(B)`, `w ↦ ((ι_A)_* w, (ι_B)_* w)`. -/
noncomputable def mvHomDiag (A B : Set ↑X) (n : ℕ) :
    Homology (sub (A ∩ B)) n →ₗ[ZMod 2] Homology (sub A) n × Homology (sub B) n :=
  (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n).prod
    (Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n)

/-- **The MV sum** `Hₙ(A) ⊕ Hₙ(B) → Hₙ(X)`, `(u, v) ↦ (ι_A)_* u + (ι_B)_* v` (a difference over `ℤ/2`). -/
noncomputable def mvHomSum (A B : Set ↑X) (n : ℕ) :
    Homology (sub A) n × Homology (sub B) n →ₗ[ZMod 2] Homology X n :=
  (Homology.map (ambIncl A) n).coprod (Homology.map (ambIncl B) n)

@[simp] theorem mvHomDiag_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomDiag A B n w
      = (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n w,
         Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n w) := rfl

@[simp] theorem mvHomSum_apply (A B : Set ↑X) (n : ℕ)
    (p : Homology (sub A) n × Homology (sub B) n) :
    mvHomSum A B n p = Homology.map (ambIncl A) n p.1 + Homology.map (ambIncl B) n p.2 := rfl

/-- **The MV chain-complex condition** `mvHomSum ∘ mvHomDiag = 0`: both inclusion routes from `A∩B`
land in `Hₙ(X)` as the same map, so over `ℤ/2` the sum is `c + c = 0`. -/
theorem mvHomSum_mvHomDiag (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomSum A B n (mvHomDiag A B n w) = 0 := by
  rw [mvHomDiag_apply, mvHomSum_apply]
  rw [show Homology.map (ambIncl A) n
          (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n w)
        = Homology.map (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.map_comp, ambIncl_comp_subIncl_left],
    show Homology.map (ambIncl B) n
          (Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n w)
        = Homology.map (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.map_comp, ambIncl_comp_subIncl_right]]
  exact ZModModule.add_self _

/-! ## The Mayer–Vietoris connecting homomorphism `δ : Hₙ₊₁(X) → Hₙ(A ∩ B)` -/

/-- **The Mayer–Vietoris connecting homomorphism** `δ : Hₙ₊₁(X) → Hₙ(A ∩ B)`, assembled
Barratt–Whitehead-style from the already-built pair LES (`SingularPairLES`) and singular excision
(`SingularExcisionIso`) — no new homology theory needed. It is the composite
`∂' ∘ excision⁻¹ ∘ j_* : Hₙ₊₁(X) → Hₙ₊₁(X, A) → Hₙ₊₁(B, A ∩ B) → Hₙ(A ∩ B)`: project to the relative
group (`homProj`), cross the excision isomorphism backwards (`excisionEquiv.symm`), then apply the pair
connecting map (`connecting`). This is exactly the composite proven for the sphere suspension
(`SingularSphereBottom.bottomSuspMap`), now stated for an arbitrary space `X` and a two-set cover.
With `mvHomDiag`/`mvHomSum` it completes the Mayer–Vietoris long exact sequence — the engine of the
fundamental-class gluing (Hatcher 3.26–3.27). `Hₙ(A ∩ B)` is realized intrinsically as
`Hₙ(sub (restr A B))` (the form excision produces): `restr A B = Subtype.val ⁻¹' A : Set (sub B)`. -/
noncomputable def mvConnecting (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ZMod 2] Homology (sub (restr A B)) n :=
  (connecting (restr A B) n).comp
    (((excisionEquiv A B n hcov).symm.toLinearMap).comp (homProj A (n + 1)))

/-! ## The `A ∩ B` representation seam: `Hₙ(sub (restr A B)) ≅ Hₙ(sub (A ∩ B))` -/

/-- The homeomorphism `sub (restr A B) ≃ₜ sub (A ∩ B)` reassociating the nested subtype
`{p : sub B // p.val ∈ A}` with `{x // x ∈ A ∩ B}`. Both carry the subspace topology on `A ∩ B`;
the underlying map on `X` is the identity. Bridges `mvConnecting`'s codomain (which excision produces
as `sub (restr A B)`) to `mvHomDiag`'s domain (`sub (A ∩ B)`). -/
def seamHomeo (A B : Set X) : ↥(sub (restr A B)) ≃ₜ ↥(sub (A ∩ B)) where
  toFun p := ⟨p.1.1, p.2, p.1.2⟩
  invFun q := ⟨⟨q.1, q.2.2⟩, q.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The seam **homology isomorphism** `Hₙ(sub (restr A B)) ≅ Hₙ(sub (A ∩ B))`, induced by `seamHomeo`
(a homeomorphism, so functoriality + `map_bijective_of_comp_id_all` give the iso in every degree). -/
noncomputable def seamHomologyEquiv (A B : Set X) (n : ℕ) :
    Homology (sub (restr A B)) n ≃ₗ[ZMod 2] Homology (sub (A ∩ B)) n :=
  LinearEquiv.ofBijective
    (Homology.map ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n)
    (Homology.map_bijective_of_comp_id_all ⟨seamHomeo A B, (seamHomeo A B).continuous⟩
      ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n)

/-- **The Mayer–Vietoris connecting map** `δ : Hₙ₊₁(X) → Hₙ(A ∩ B)` in the `sub (A ∩ B)` representation
— `mvConnecting` post-composed with the seam isomorphism, so its codomain matches `mvHomDiag`'s domain.
This is the `δ` that closes the Mayer–Vietoris long exact sequence
`⋯ → Hₙ₊₁(X) →[δ] Hₙ(A∩B) →[mvHomDiag] Hₙ(A)⊕Hₙ(B) →[mvHomSum] Hₙ(X) → ⋯`. -/
noncomputable def mvDelta (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ZMod 2] Homology (sub (A ∩ B)) n :=
  (seamHomologyEquiv A B n).toLinearMap.comp (mvConnecting A B n hcov)

/-! ## Naturality of the connecting map under excision (the Barratt–Whitehead square) -/

/-- The inclusion `A ∩ B ↪ A`, from the `restr A B` (inside `sub B`) representation, as a
`ContinuousMap` `sub (restr A B) → sub A` (`p.1 ∈ restr A B = Subtype.val ⁻¹' A` gives `p.1.1 ∈ A`). -/
def inclRA (A B : Set X) : C(↥(sub (restr A B)), ↥(sub A)) :=
  ⟨fun p => ⟨p.1.1, p.2⟩, by fun_prop⟩

/-- The functorial pushforward `mapSimplex (ambIncl S)` along the subspace inclusion coincides with
`simplexIncl S` (both apply the inclusion `sub S ↪ X` to a singular simplex). -/
theorem mapSimplex_ambIncl (S : Set ↑X) {n : ℕ}
    (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    mapSimplex (ambIncl S) σ = simplexIncl S n σ := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  rw [SingularExcision.toSSetObjEquiv_simplexIncl]
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- **chainIncl–mapChain bridge**: `mapChain (ambIncl S) = chainIncl S` — the LES-side functorial
pushforward (`Homology.map`/`mapChain`) and the `connecting`-side chain inclusion (`chainIncl`) along
the subspace inclusion `sub S ↪ X` are the same linear map. Reused throughout Mayer–Vietoris exactness
to move between the two formulations. -/
theorem mapChain_ambIncl (S : Set ↑X) (n : ℕ) :
    mapChain (ambIncl S) n = chainIncl S n := by
  refine LinearMap.ext fun c => ?_
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single σ a => rw [mapChain_single, chainIncl_single, mapSimplex_ambIncl]

/-- The functorial `Homology.map (ambIncl S)` equals the pair-LES inclusion-induced map `homIncl S`
(both descend from the chain inclusion, via `mapChain_ambIncl`). Lets the Mayer–Vietoris complex
conditions reuse the pair-LES `homIncl_connecting`. -/
theorem Homology.map_ambIncl (S : Set ↑X) (n : ℕ) :
    Homology.map (ambIncl S) n = homIncl S n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Homology.map (ambIncl S) n (Homology.mk (sub S) n z) = homIncl S n (Homology.mk (sub S) n z)
  rw [Homology.map_mk, homIncl_mk]
  exact congrArg (Homology.mk X n) (Subtype.ext (by rw [cyclesMap_coe, mapChain_ambIncl]))

/-- **Naturality of the connecting map under excision** (the Barratt–Whitehead commutativity square):
the inclusion `A ∩ B ↪ A` after the `(B, A∩B)` connecting map equals the `(X, A)` connecting map after
excision. The crux of Mayer–Vietoris exactness at `Hₙ(A∩B)` and `Hₙ(X)`. -/
theorem inclRA_connecting (A B : Set X) (n : ℕ) (y : RelativeHomology (restr A B) (n + 1)) :
    Homology.map (inclRA A B) n (connecting (restr A B) n y)
      = connecting A n (excisionMap A B (n + 1) y) := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective (restr A B) n y
  rw [connecting_relCycleToHom]
  have hc' : chainBoundary X n (chainIncl B (n + 1) (c : SingularChain (sub B) (n + 1)))
      ∈ subspaceChains A n := by
    rw [← chainIncl_chainBoundary]
    exact (chainIncl_mem_subspaceChains_iff A B _).2 (Submodule.mem_comap.mp c.2)
  have hexc : excisionMap A B (n + 1) (relCycleToHom (restr A B) n c)
      = relCycleToHom A n ⟨chainIncl B (n + 1) c, hc'⟩ := by
    rw [relCycleToHom_apply, excisionMap_mk, relCycleToHom_apply]
    exact congrArg (RelativeHomology.mk A (n + 1)) (Subtype.ext (relChainIncl_mk A B (n + 1) c))
  rw [hexc, connecting_relCycleToHom, connectingLift_apply, connectingLift_apply, Homology.map_mk]
  refine congrArg (Homology.mk (sub A) n) (Subtype.ext ?_)
  rw [cyclesMap_coe]
  apply chainIncl_injective A n
  rw [chainIncl_boundaryExtract, ← chainIncl_chainBoundary,
    ← chainIncl_boundaryExtract (restr A B) n c, ← mapChain_ambIncl A, ← mapChain_ambIncl B,
    ← mapChain_ambIncl (restr A B), ← mapChain_comp, ← mapChain_comp]
  congr 1

/-! ## Mayer–Vietoris exactness -/

/-- The `A`-inclusion after the seam isomorphism is `Homology.map inclRA` (functoriality;
`subIncl_{A∩B↪A} ∘ seamHomeo = inclRA`). -/
theorem map_subInclL_seam (A B : Set X) (n : ℕ) (y : Homology (sub (restr A B)) n) :
    Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n (seamHomologyEquiv A B n y)
      = Homology.map (inclRA A B) n y := by
  rw [show seamHomologyEquiv A B n y
        = Homology.map ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n y from rfl,
    ← LinearMap.comp_apply, ← Homology.map_comp]
  rfl

/-- The `B`-inclusion after the seam isomorphism is `homIncl (restr A B)` (functoriality + the
`Homology.map ↔ homIncl` bridge; `subIncl_{A∩B↪B} ∘ seamHomeo = ambIncl (restr A B)`). -/
theorem map_subInclR_seam (A B : Set X) (n : ℕ) (y : Homology (sub (restr A B)) n) :
    Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n (seamHomologyEquiv A B n y)
      = homIncl (restr A B) n y := by
  rw [show seamHomologyEquiv A B n y
        = Homology.map ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n y from rfl,
    ← LinearMap.comp_apply, ← Homology.map_comp,
    show (subIncl (Set.inter_subset_right (s := A) (t := B))).comp
          ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ = ambIncl (restr A B) from rfl,
    Homology.map_ambIncl]

/-- **MV complex condition at `Hₙ(A∩B)`**: `mvHomDiag ∘ δ = 0`. -/
theorem mvHomDiag_mvDelta (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) (x : Homology X (n + 1)) :
    mvHomDiag A B n (mvDelta A B n hcov x) = 0 := by
  refine Prod.ext ?_ ?_
  · show Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n
        (seamHomologyEquiv A B n (connecting (restr A B) n
          ((excisionEquiv A B n hcov).symm (homProj A (n + 1) x)))) = 0
    rw [map_subInclL_seam, inclRA_connecting,
      show excisionMap A B (n + 1) ((excisionEquiv A B n hcov).symm (homProj A (n + 1) x))
        = homProj A (n + 1) x from (excisionEquiv A B n hcov).apply_symm_apply _,
      connecting_homProj]
  · show Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n
        (seamHomologyEquiv A B n (connecting (restr A B) n
          ((excisionEquiv A B n hcov).symm (homProj A (n + 1) x)))) = 0
    rw [map_subInclR_seam, homIncl_connecting]

end SKEFTHawking.SingularMayerVietorisLES
