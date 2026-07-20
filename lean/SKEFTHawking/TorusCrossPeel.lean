/-
# Phase 5q.H · K1-b — the torus-step cross cycle and the spine-peel evaluation engine

The **EZ-free cross-value engine** for the torus tower `Tor Y = Y × S¹`. Two components:

1. **The glued cross** `torCross : Cₙ(Y;ℤ) → Cₙ₊₁(Tor Y;ℤ)` — the sum of the two arc-cylinder
   prisms (`prismOpInt` along the homotopies `(y,t) ↦ (y, arc t)` for the two half-circle arcs of
   `CircleWindingCocycle`). For a cycle `c` the endpoint slices cancel in pairs
   (`arcA 1 = arcB 0`, `arcB 1 = arcA 0`), so `torCross c` is an honest **absolute** cycle — the
   chain-level `c × [S¹]` with no Eilenberg–Zilber input.

2. **The spine peels** — termwise evaluations of Alexander–Whitney cups of factor-pulled-back
   cochains against `torCross c`. On each prism simplex the interval coordinate is vertical in
   **exactly one** spine edge, so a cup with a single `snd*windS` factor evaluates termwise: the
   `A`-cylinder dies (arc weight `0`), the `B`-cylinder contributes once (arc weight `1`), and the
   value collapses to a pairing one torus-factor down. This kills the historical mechanism walls:
   no prism naturality, no relative sources, no shuffle homotopy — only face combinatorics of
   explicit chains.

Peels landed: the degree-generic right-peel `kronecker_cup_snd_torCross`
(`⟨fst*w ⌣ snd*α̂, torCross c⟩ = (−1)ⁿ ⟨w, c⟩`) and the concrete mid-peels at bidegrees `(1,2)`,
`(1,1)`, `(0,1)` (`⟨(fst*w ⌣ snd*α̂) ⌣ u, torCross c⟩ = −⟨w ⌣ e_*u, c⟩` with `e` the basepoint
slice), plus the subsingleton evaluation-vanish lemma for the no-`snd` patterns.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CircleWindingCocycle
import SKEFTHawking.SingularHomotopyInvarianceInt
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.KummerTorusStep

namespace SKEFTHawking.TorusCrossPeel

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single
  endMapInt_eq_mapChainInt)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex slice)
open SKEFTHawking.SingularHomotopyInvarianceInt
open SKEFTHawking.SingularPrism (prismSimplex prismAlpha prismBeta)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.CircleWindingCocycle (windS windS_cocycle windS_const windS_pathEdge_arcA
  windS_pathEdge_arcB arcA arcB arcA_one_eq_arcB_zero arcB_one_eq_arcA_zero pathEdge rl
  rl_pathEdge iota faceC rl_face mapSimplex_constSimplex)

/-! ## §0. Projections, arc homotopies, and endpoint slices -/

/-- The second-factor projection of a product carrier. -/
noncomputable def prodSnd (Y C : TopCat) : C(↑(ProdSp Y C), ↑C) := ⟨Prod.snd, continuous_snd⟩

/-- The arc-cylinder homotopy `(y, t) ↦ (y, arc t) : Y × I → Tor Y`. -/
noncomputable def arcH (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1))) :
    C(↑Y × unitInterval, ↑(Tor Y)) :=
  ⟨fun p => (p.1, arc p.2), by fun_prop⟩

/-- The horizontal slice `y ↦ (y, s) : Y → Tor Y` at a point `s ∈ S¹`. -/
noncomputable def endAt (Y : TopCat) (s : ↑(Sph 1)) : C(↑Y, ↑(Tor Y)) :=
  ⟨fun y => (y, s), by fun_prop⟩

theorem slice_arcH (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1))) (r : unitInterval) :
    slice (arcH Y arc) r = endAt Y (arc r) :=
  ContinuousMap.ext fun _ => rfl

/-! ## §1. The glued torus-step cross and its cycle law -/

/-- **The glued torus-step cross** `Cₘ(Y;ℤ) → Cₘ₊₁(Tor Y;ℤ)`: the sum of the two arc-cylinder
prisms. The chain-level `c × [S¹]`. -/
noncomputable def torCross (Y : TopCat) (m : ℕ) :
    SingularChainInt Y m →ₗ[ℤ] SingularChainInt (Tor Y) (m + 1) :=
  prismOpInt (arcH Y arcA) m + prismOpInt (arcH Y arcB) m

theorem torCross_apply (Y : TopCat) (m : ℕ) (c : SingularChainInt Y m) :
    torCross Y m c = prismOpInt (arcH Y arcA) m c + prismOpInt (arcH Y arcB) m c :=
  rfl

/-- **The cross of a cycle is an absolute cycle**: the four endpoint slices cancel in two pairs
(`arcA 1 = arcB 0`, `arcB 1 = arcA 0`). This is what six prior arcs could not reach through
relative sources — the *glued* cross needs no pair map. -/
theorem chainBoundary_torCross (Y : TopCat) (n : ℕ) (c : SingularChainInt Y (n + 1))
    (hc : chainBoundary Y n c = 0) :
    chainBoundary (Tor Y) (n + 1) (torCross Y (n + 1) c) = 0 := by
  have hA := prism_chainHomotopyInt (arcH Y arcA) c
  have hB := prism_chainHomotopyInt (arcH Y arcB) c
  rw [hc, map_zero, add_zero] at hA hB
  have hsplit : chainBoundary (Tor Y) (n + 1) (torCross Y (n + 1) c)
      = (endMapInt (arcH Y arcA) 1 (n + 1) c - endMapInt (arcH Y arcA) 0 (n + 1) c)
        + (endMapInt (arcH Y arcB) 1 (n + 1) c - endMapInt (arcH Y arcB) 0 (n + 1) c) := by
    rw [torCross_apply, map_add, hA, hB]
  rw [hsplit, endMapInt_eq_mapChainInt, endMapInt_eq_mapChainInt, endMapInt_eq_mapChainInt,
    endMapInt_eq_mapChainInt, slice_arcH, slice_arcH, slice_arcH, slice_arcH,
    arcA_one_eq_arcB_zero, arcB_one_eq_arcA_zero]
  abel

/-! ## §2. The affine toolkit: prism factors under `stdSimplex.map` -/

/-- The bundled affine realization of a vertex map. -/
noncomputable def sSC {k m : ℕ} (g : Fin (k + 1) → Fin (m + 1)) :
    C(stdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (m + 1))) :=
  ⟨stdSimplex.map g, stdSimplex.continuous_map g⟩

/-- The coordinate readout of `stdSimplex.map`: the fiber sum. -/
theorem stdSimplex_map_coord {k m : ℕ} (f : Fin (k + 1) → Fin (m + 1))
    (d : stdSimplex ℝ (Fin (k + 1))) (j : Fin (m + 1)) :
    ((stdSimplex.map f d : stdSimplex ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ) j
      = ∑ x ∈ Finset.univ.filter (fun x => f x = j), (d : Fin (k + 1) → ℝ) x :=
  FunOnFinite.linearMap_apply_apply ℝ ℝ f _ j

/-- The coordinate readout of `stdSimplex.vertex`. -/
theorem stdSimplex_vertex_coord {m : ℕ} (k j : Fin (m + 1)) :
    ((stdSimplex.vertex k : stdSimplex ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ) j
      = if k = j then 1 else 0 := by
  show (Pi.single k 1 : Fin (m + 1) → ℝ) j = _
  rw [Pi.single_apply]
  simp [eq_comm]

/-- `prismAlpha i` is the affine realization of the vertex map `Fin.predAbove i`. -/
theorem prismAlpha_eq_sSC {n : ℕ} (i : Fin (n + 1)) :
    prismAlpha i = sSC (Fin.predAbove i) := by
  refine ContinuousMap.ext fun d => Subtype.ext (funext fun m => ?_)
  have hL : ((prismAlpha i d : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) m
      = (∑ j, (d : Fin (n + 2) → ℝ) j •
          ((stdSimplex.vertex (Fin.predAbove i j) : stdSimplex ℝ (Fin (n + 1)))
            : Fin (n + 1) → ℝ)) m :=
    congrFun (SKEFTHawking.SingularExcisionPushforward.affineSimplexStd_coe_apply
      (fun k => stdSimplex.vertex (Fin.predAbove i k)) d) m
  have hR : ((sSC (Fin.predAbove i) d : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) m
      = ∑ j ∈ Finset.univ.filter (fun j => Fin.predAbove i j = m), (d : Fin (n + 2) → ℝ) j :=
    stdSimplex_map_coord _ d m
  show ((prismAlpha i d : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) m
    = ((sSC (Fin.predAbove i) d : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) m
  rw [hL, hR, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, stdSimplex_vertex_coord]
  by_cases h : Fin.predAbove i j = m
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The interval coordinate of a prism simplex under an affine reindexing: the filtered sum of the
barycentric coordinates whose image vertex sits strictly above `i`. -/
theorem prismBeta_map {n k : ℕ} (i : Fin (n + 1)) (f : Fin (k + 1) → Fin (n + 1 + 1))
    (d : stdSimplex ℝ (Fin (k + 1))) :
    ((prismBeta i (stdSimplex.map f d) : unitInterval) : ℝ)
      = ∑ j ∈ Finset.univ.filter (fun j => i.castSucc < f j), (d : Fin (k + 1) → ℝ) j := by
  have hstart : ((prismBeta i (stdSimplex.map f d) : unitInterval) : ℝ)
      = ∑ m ∈ Finset.univ.filter (i.castSucc < ·),
          ((stdSimplex.map f d : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) m := rfl
  rw [hstart, Finset.sum_congr rfl (fun m _ => stdSimplex_map_coord f d m)]
  have hsplit : ∀ m ∈ Finset.univ.filter (fun m : Fin (n + 2) => i.castSucc < m),
      (Finset.univ.filter (fun j => f j = m))
        = (Finset.univ.filter (fun j => i.castSucc < f j)).filter (fun j => f j = m) := by
    intro m hm
    have hm' := (Finset.mem_filter.mp hm).2
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨h ▸ hm', h⟩
    · intro h
      exact h.2
  rw [Finset.sum_congr rfl (fun m hm => by rw [hsplit m hm])]
  exact Finset.sum_fiberwise_of_maps_to (g := f)
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
    (fun j => (d : Fin (k + 1) → ℝ) j)

/-- The edge specialization of `prismBeta_map`, in fully expanded `if`-form. -/
theorem prismBeta_map_edge {n : ℕ} (i : Fin (n + 1)) (f : Fin 2 → Fin (n + 1 + 1))
    (d : stdSimplex ℝ (Fin 2)) :
    ((prismBeta i (stdSimplex.map f d) : unitInterval) : ℝ)
      = (if i.castSucc < f 0 then (d : Fin 2 → ℝ) 0 else 0)
        + (if i.castSucc < f 1 then (d : Fin 2 → ℝ) 1 else 0) := by
  refine (prismBeta_map i f d).trans ?_
  rw [Finset.sum_filter, Fin.sum_univ_two]

/-! ## §3. Face extraction of prism simplices — the snd factor -/

/-- Realization of the `toSSet` action along any simplex-category morphism (definitional
`toSSetObjEquiv`-naturality, the general-φ form of `toSSetObjEquiv_face`). -/
theorem rl_mapOp {X : TopCat} {k m : ℕ} (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk m))) :
    rl ((TopCat.toSSet.obj X).map φ.op σ)
      = (rl σ).comp (sSC (⇑(ConcreteCategory.hom φ))) :=
  rfl

/-- Realization of a prism simplex (definitional). -/
theorem rl_prismSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    rl (prismSimplex H σ i)
      = H.comp (((rl σ).comp (prismAlpha i)).prodMk (prismBeta i)) :=
  Equiv.apply_symm_apply _ _

/-- Realization of a pushforward (definitional). -/
theorem rl_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    rl (mapSimplex φ σ) = φ.comp (rl σ) :=
  Equiv.apply_symm_apply _ _

section FaceExtraction

variable (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1))) {n : ℕ}
  (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1))

/-- **The horizontal-edge collapse (level 0)**: an edge whose image vertices both sit at or below
the prism level `i` projects to the constant edge at `arc 0` on the circle factor. -/
theorem sndFace_prism_lo (e : SimplexCategory.mk 1 ⟶ SimplexCategory.mk (n + 1))
    (h : ∀ j : Fin 2, ¬ i.castSucc < (ConcreteCategory.hom e) j) :
    mapSimplex (prodSnd Y (Sph 1))
        ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i))
      = constSimplex (arc 0) 1 := by
  apply ((Sph 1).toSSetObjEquiv (op (SimplexCategory.mk 1))).injective
  show rl (mapSimplex (prodSnd Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i)))
    = rl (constSimplex (arc 0) 1)
  rw [rl_mapSimplex, rl_mapOp, rl_prismSimplex]
  refine ContinuousMap.ext fun d => ?_
  show arc (prismBeta i (stdSimplex.map (⇑(ConcreteCategory.hom e)) d)) = arc 0
  congr 1
  apply Subtype.ext
  refine (prismBeta_map_edge i (⇑(ConcreteCategory.hom e)) d).trans ?_
  rw [if_neg (h (0 : Fin 2)), if_neg (h (1 : Fin 2)), add_zero]
  rfl

/-- **The horizontal-edge collapse (level 1)**: an edge whose image vertices both sit strictly
above the prism level `i` projects to the constant edge at `arc 1`. -/
theorem sndFace_prism_hi (e : SimplexCategory.mk 1 ⟶ SimplexCategory.mk (n + 1))
    (h : ∀ j : Fin 2, i.castSucc < (ConcreteCategory.hom e) j) :
    mapSimplex (prodSnd Y (Sph 1))
        ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i))
      = constSimplex (arc 1) 1 := by
  apply ((Sph 1).toSSetObjEquiv (op (SimplexCategory.mk 1))).injective
  show rl (mapSimplex (prodSnd Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i)))
    = rl (constSimplex (arc 1) 1)
  rw [rl_mapSimplex, rl_mapOp, rl_prismSimplex]
  refine ContinuousMap.ext fun d => ?_
  show arc (prismBeta i (stdSimplex.map (⇑(ConcreteCategory.hom e)) d)) = arc 1
  congr 1
  apply Subtype.ext
  refine (prismBeta_map_edge i (⇑(ConcreteCategory.hom e)) d).trans ?_
  rw [if_pos (h (0 : Fin 2)), if_pos (h (1 : Fin 2))]
  exact (Fin.sum_univ_two (fun j => (d : Fin 2 → ℝ) j)).symm.trans d.2.2

/-- **The vertical-edge detection**: the edge crossing the prism level (`e 0` at or below `i`,
`e 1` strictly above) projects to the arc's path edge — the unique interval contribution. -/
theorem sndFace_prism_mid (e : SimplexCategory.mk 1 ⟶ SimplexCategory.mk (n + 1))
    (h0 : ¬ i.castSucc < (ConcreteCategory.hom e) (0 : Fin 2))
    (h1 : i.castSucc < (ConcreteCategory.hom e) (1 : Fin 2)) :
    mapSimplex (prodSnd Y (Sph 1))
        ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i))
      = pathEdge (Sph 1) arc := by
  apply ((Sph 1).toSSetObjEquiv (op (SimplexCategory.mk 1))).injective
  show rl (mapSimplex (prodSnd Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map e.op (prismSimplex (arcH Y arc) σ i)))
    = rl (pathEdge (Sph 1) arc)
  rw [rl_mapSimplex, rl_mapOp, rl_prismSimplex, rl_pathEdge]
  refine ContinuousMap.ext fun d => ?_
  show arc (prismBeta i (stdSimplex.map (⇑(ConcreteCategory.hom e)) d)) = arc (iota d)
  congr 1
  apply Subtype.ext
  refine (prismBeta_map_edge i (⇑(ConcreteCategory.hom e)) d).trans ?_
  rw [if_neg h0, if_pos h1, zero_add]
  rfl

/-! ## §4. Face extraction of prism simplices — the fst factor and the level-1 tail -/

/-- **The fst-projection of a prism face is a face of the base simplex**: the `Y`-projection of the
`φ`-face of the `i`-th prism simplex is the face of `σ` along the degeneracy-composite `ψ`
(`ψ = predAbove i ∘ φ` on vertices). -/
theorem fstFace_prism {k : ℕ} (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk (n + 1))
    (ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n)
    (hcomp : ∀ j, Fin.predAbove i ((ConcreteCategory.hom φ) j) = (ConcreteCategory.hom ψ) j) :
    mapSimplex (prodFst Y (Sph 1))
        ((TopCat.toSSet.obj (Tor Y)).map φ.op (prismSimplex (arcH Y arc) σ i))
      = (TopCat.toSSet.obj Y).map ψ.op σ := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  show rl (mapSimplex (prodFst Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map φ.op (prismSimplex (arcH Y arc) σ i)))
    = rl ((TopCat.toSSet.obj Y).map ψ.op σ)
  rw [rl_mapSimplex, rl_mapOp, rl_prismSimplex, rl_mapOp]
  refine ContinuousMap.ext fun d => ?_
  show rl σ (prismAlpha i (stdSimplex.map (⇑(ConcreteCategory.hom φ)) d))
    = rl σ (stdSimplex.map (⇑(ConcreteCategory.hom ψ)) d)
  congr 1
  rw [prismAlpha_eq_sSC]
  show stdSimplex.map (Fin.predAbove i) (stdSimplex.map (⇑(ConcreteCategory.hom φ)) d) = _
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext j
  exact hcomp j

/-- **The level-1 tail**: the `φ`-face of the `i`-th prism simplex, when every `φ`-vertex sits
strictly above `i`, is the level-1 pushforward of the `ψ`-face of `σ`. -/
theorem tailFace_prism {k : ℕ} (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk (n + 1))
    (ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n)
    (hcomp : ∀ j, Fin.predAbove i ((ConcreteCategory.hom φ) j) = (ConcreteCategory.hom ψ) j)
    (hup : ∀ j, i.castSucc < (ConcreteCategory.hom φ) j) :
    (TopCat.toSSet.obj (Tor Y)).map φ.op (prismSimplex (arcH Y arc) σ i)
      = mapSimplex (endAt Y (arc 1)) ((TopCat.toSSet.obj Y).map ψ.op σ) := by
  apply ((Tor Y).toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  show rl ((TopCat.toSSet.obj (Tor Y)).map φ.op (prismSimplex (arcH Y arc) σ i))
    = rl (mapSimplex (endAt Y (arc 1)) ((TopCat.toSSet.obj Y).map ψ.op σ))
  rw [rl_mapOp, rl_prismSimplex, rl_mapSimplex, rl_mapOp]
  refine ContinuousMap.ext fun d => ?_
  show (rl σ (prismAlpha i (stdSimplex.map (⇑(ConcreteCategory.hom φ)) d)),
      arc (prismBeta i (stdSimplex.map (⇑(ConcreteCategory.hom φ)) d)))
    = (rl σ (stdSimplex.map (⇑(ConcreteCategory.hom ψ)) d), arc 1)
  refine Prod.ext ?_ ?_
  · show rl σ _ = rl σ _
    congr 1
    rw [prismAlpha_eq_sSC]
    show stdSimplex.map (Fin.predAbove i) (stdSimplex.map (⇑(ConcreteCategory.hom φ)) d) = _
    rw [stdSimplex.map_comp_apply]
    congr 1
    funext j
    exact hcomp j
  · show arc _ = arc 1
    congr 1
    apply Subtype.ext
    refine (prismBeta_map i (⇑(ConcreteCategory.hom φ)) d).trans ?_
    refine (Finset.sum_congr (Finset.filter_true_of_mem fun j _ => hup j)
      (fun _ _ => rfl)).trans ?_
    exact d.2.2

end FaceExtraction

/-! ## §5. The evaluation helpers and the degree-generic right peel -/

/-- `⟨Φ, prismBasisInt σ⟩` is the signed sum of the per-prism-simplex values. -/
theorem kronecker_prismBasisInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) {n : ℕ}
    (Φ : SingularCochainInt Y (n + 1))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    kronecker Φ (prismBasisInt H n σ)
      = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) * Φ (prismSimplex H σ i) := by
  rw [prismBasisInt, kronecker_eq_linearCombination, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Finsupp.linearCombination_single, one_smul, smul_eq_mul]

/-- Chain-level extension: a uniform per-basis value `⟨Φ, P σ⟩ = r · ω σ` extends linearly to
`⟨Φ, P c⟩ = r · ⟨ω, c⟩`. -/
theorem kronecker_prismOpInt_of_basis {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) {n : ℕ}
    (Φ : SingularCochainInt Y (n + 1)) (ω : SingularCochainInt X n) (r : ℤ)
    (h : ∀ σ, kronecker Φ (prismBasisInt H n σ) = r * ω σ) (c : SingularChainInt X n) :
    kronecker Φ (prismOpInt H n c) = r * kronecker ω c := by
  induction c using Finsupp.induction_linear with
  | zero =>
      rw [map_zero]
      show kroneckerₗ (n + 1) Φ 0 = r * kroneckerₗ n ω 0
      rw [map_zero, map_zero, mul_zero]
  | add c₁ c₂ h₁ h₂ =>
      rw [map_add, kronecker_add_right, kronecker_add_right, h₁, h₂, mul_add]
  | single σ a =>
      rw [prismOpInt_single, kronecker_smul_right, h σ, kronecker_single]
      ring

/-- Only the last prism simplex survives against a rightmost `snd` factor: `predAbove (last n)`
retracts the front inclusion. -/
theorem predAbove_last_front (n : ℕ) (j : Fin (n + 1)) :
    Fin.predAbove (Fin.last n) ((ConcreteCategory.hom (frontIncl n 1)) j) = j := by
  have hval : (((ConcreteCategory.hom (frontIncl n 1)) j) : ℕ) = (j : ℕ) := rfl
  rw [Fin.predAbove]
  split
  · next h =>
      exfalso
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, hval] at h
      omega
  · apply Fin.ext
    rw [Fin.coe_castPred, hval]

/-- **The degree-generic right peel**: against a single arc cylinder,
`⟨fst*w ⌣ snd*windS, P_arc c⟩ = (−1)ⁿ · windS(arcEdge) · ⟨w, c⟩`. Termwise: on every prism simplex
except the last the back edge is horizontal (`windS` kills it); on the last it is the arc edge and
the front face is the base simplex itself. -/
theorem kronecker_cup_snd_prism (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1))) {n : ℕ}
    (w : SingularCochainInt Y n) (c : SingularChainInt Y n) :
    kronecker (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS))
      (prismOpInt (arcH Y arc) n c)
      = (-1 : ℤ) ^ n * (windS (pathEdge (Sph 1) arc) * kronecker w c) := by
  rw [show (-1 : ℤ) ^ n * (windS (pathEdge (Sph 1) arc) * kronecker w c)
      = ((-1 : ℤ) ^ n * windS (pathEdge (Sph 1) arc)) * kronecker w c by ring]
  refine kronecker_prismOpInt_of_basis _ _ _ _ (fun σ => ?_) c
  rw [kronecker_prismBasisInt]
  have hterm : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) (prismSimplex (arcH Y arc) σ i) = 0 := by
    intro i hi
    rw [cup_apply, cochainPullbackInt_apply, cochainPullbackInt_apply]
    have hback : backFace (prismSimplex (arcH Y arc) σ i)
        = (TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op (prismSimplex (arcH Y arc) σ i) := rfl
    rw [hback]
    have hhi : ∀ j : Fin 2, i.castSucc < (ConcreteCategory.hom (backIncl n 1)) j := by
      intro j
      show ((i : ℕ) : ℕ) < n + (j : ℕ)
      have : (i : ℕ) < n := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      omega
    rw [sndFace_prism_hi Y arc σ i (backIncl n 1) hhi, windS_const, mul_zero]
  rw [Finset.sum_eq_single (Fin.last n)
      (fun i _ hi => by rw [hterm i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [cup_apply, cochainPullbackInt_apply, cochainPullbackInt_apply]
  have hback : backFace (prismSimplex (arcH Y arc) σ (Fin.last n))
      = (TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op
          (prismSimplex (arcH Y arc) σ (Fin.last n)) := rfl
  have hfront : frontFace (prismSimplex (arcH Y arc) σ (Fin.last n))
      = (TopCat.toSSet.obj (Tor Y)).map (frontIncl n 1).op
          (prismSimplex (arcH Y arc) σ (Fin.last n)) := rfl
  rw [hback, hfront]
  have hmid : mapSimplex (prodSnd Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op
        (prismSimplex (arcH Y arc) σ (Fin.last n)))
      = pathEdge (Sph 1) arc := by
    refine sndFace_prism_mid Y arc σ (Fin.last n) (backIncl n 1) ?_ ?_
    · show ¬ (((Fin.last n : Fin (n + 1)) : ℕ) < n + 0)
      rw [Fin.val_last]
      omega
    · show ((Fin.last n : Fin (n + 1)) : ℕ) < n + 1
      rw [Fin.val_last]
      omega
  have hfst : mapSimplex (prodFst Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map (frontIncl n 1).op
        (prismSimplex (arcH Y arc) σ (Fin.last n)))
      = σ := by
    rw [fstFace_prism Y arc σ (Fin.last n) (frontIncl n 1) (𝟙 (SimplexCategory.mk n))
        (fun j => by rw [predAbove_last_front]; rfl)]
    exact FunctorToTypes.map_id_apply _ _
  rw [hmid, hfst, Fin.val_last]
  ring

/-- **The glued right peel**: `⟨fst*w ⌣ snd*windS, torCross c⟩ = (−1)ⁿ ⟨w, c⟩` — the `A`-cylinder
weight is `0`, the `B`-cylinder weight is `1`. -/
theorem kronecker_cup_snd_torCross (Y : TopCat) {n : ℕ}
    (w : SingularCochainInt Y n) (c : SingularChainInt Y n) :
    kronecker (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS))
      (torCross Y n c)
      = (-1 : ℤ) ^ n * kronecker w c := by
  rw [torCross_apply, kronecker_add_right, kronecker_cup_snd_prism, kronecker_cup_snd_prism,
    windS_pathEdge_arcA, windS_pathEdge_arcB]
  ring

/-- **The no-`snd` vanish**: a cocycle in a degree where the target homology is trivial pairs to
zero with every cycle. The engine for all Gram entries missing a given circle factor. -/
theorem kronecker_eq_zero_of_cocycle_subsingleton {X : TopCat} {n : ℕ}
    [Subsingleton (Homology X (n + 1))]
    (w : SingularCochainInt X (n + 1)) (hw : coboundaryₗ X (n + 1) w = 0)
    (z : SingularChainInt X (n + 1)) (hz : chainBoundary X n z = 0) :
    kronecker w z = 0 := by
  have hzc : z ∈ cycles X (n + 1) := LinearMap.mem_ker.mpr hz
  have hcls : Homology.mk X (n + 1) ⟨z, hzc⟩ = (0 : Homology X (n + 1)) :=
    Subsingleton.elim _ _
  have hcls' : (Submodule.Quotient.mk (⟨z, hzc⟩ : cycles X (n + 1))
      : (cycles X (n + 1)) ⧸ (boundaries X (n + 1)).submoduleOf (cycles X (n + 1))) = 0 := hcls
  rw [Submodule.Quotient.mk_eq_zero] at hcls'
  have hzb : z ∈ boundaries X (n + 1) := hcls'
  obtain ⟨d, hd⟩ := hzb
  rw [← hd]
  exact kronecker_eq_zero_of_cocycle_boundary w hw d

/-! ## §7. The concrete mid peels -/

/-- **The `(0,1)` mid peel (single cylinder)**: a leading `snd*windS` factor detects the `i = 0`
prism simplex; the residue pulls the tail back along the level-1 slice. -/
theorem kronecker_cupMid_prism_0_1 (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1)))
    (u : SingularCochainInt (Tor Y) 1) (c : SingularChainInt Y 1) :
    kronecker (cup (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS) u)
      (prismOpInt (arcH Y arc) 1 c)
      = windS (pathEdge (Sph 1) arc)
          * kronecker (cochainPullbackInt (endAt Y (arc 1)) 1 u) c := by
  refine kronecker_prismOpInt_of_basis _ _ _ _ (fun σ => ?_) c
  rw [kronecker_prismBasisInt]
  have hvals : ∀ i : Fin (1 + 1),
      (-1 : ℤ) ^ (i : ℕ) * (cup (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS) u)
          (prismSimplex (arcH Y arc) σ i)
        = if i = 0 then windS (pathEdge (Sph 1) arc)
            * (cochainPullbackInt (endAt Y (arc 1)) 1 u) σ else 0 := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, cup_apply, cochainPullbackInt_apply]
      have hfront : frontFace (prismSimplex (arcH Y arc) σ 0)
          = (TopCat.toSSet.obj (Tor Y)).map (frontIncl 1 1).op
              (prismSimplex (arcH Y arc) σ 0) := rfl
      have hback : backFace (prismSimplex (arcH Y arc) σ 0)
          = (TopCat.toSSet.obj (Tor Y)).map (backIncl 1 1).op
              (prismSimplex (arcH Y arc) σ 0) := rfl
      rw [hfront, hback,
        sndFace_prism_mid Y arc σ 0 (frontIncl 1 1) (by decide) (by decide),
        tailFace_prism Y arc σ 0 (backIncl 1 1) (𝟙 (SimplexCategory.mk 1))
          (by decide) (by decide),
        CategoryTheory.op_id, FunctorToTypes.map_id_apply, cochainPullbackInt_apply,
        Fin.val_zero, pow_zero, one_mul]
    · have hi1 : i = 1 := by
        apply Fin.ext
        show (i : ℕ) = 1
        have h2 := i.isLt
        have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        omega
      subst hi1
      rw [if_neg (by decide), cup_apply, cochainPullbackInt_apply]
      have hfront : frontFace (prismSimplex (arcH Y arc) σ 1)
          = (TopCat.toSSet.obj (Tor Y)).map (frontIncl 1 1).op
              (prismSimplex (arcH Y arc) σ 1) := rfl
      rw [hfront, sndFace_prism_lo Y arc σ 1 (frontIncl 1 1) (by decide), windS_const,
        zero_mul, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hvals i), Finset.sum_ite_eq' Finset.univ (0 : Fin (1 + 1))
    (fun _ => windS (pathEdge (Sph 1) arc) * (cochainPullbackInt (endAt Y (arc 1)) 1 u) σ),
    if_pos (Finset.mem_univ _)]

/-- **The `(1,1)` mid peel (single cylinder)**: the vertical edge sits at spine position 2 of a
3-simplex; only the `i = 1` prism simplex contributes, with sign `−1`. -/
theorem kronecker_cupMid_prism_1_1 (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1)))
    (w : SingularCochainInt Y 1) (u : SingularCochainInt (Tor Y) 1)
    (c : SingularChainInt Y 2) :
    kronecker (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
      (prismOpInt (arcH Y arc) 2 c)
      = -(windS (pathEdge (Sph 1) arc)
          * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 1 u)) c) := by
  rw [show -(windS (pathEdge (Sph 1) arc)
        * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 1 u)) c)
      = (-(windS (pathEdge (Sph 1) arc)))
          * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 1 u)) c by ring]
  refine kronecker_prismOpInt_of_basis _ _ _ _ (fun σ => ?_) c
  rw [kronecker_prismBasisInt]
  have hmid : ∀ i' : Fin (2 + 1),
      backFace (p := 1) (q := 1) (frontFace (p := 1 + 1) (q := 1)
          (prismSimplex (arcH Y arc) σ i'))
      = (TopCat.toSSet.obj (Tor Y)).map ((backIncl 1 1 ≫ frontIncl (1 + 1) 1)).op
          (prismSimplex (arcH Y arc) σ i') := by
    intro i'
    show (TopCat.toSSet.obj (Tor Y)).map (backIncl 1 1).op
        ((TopCat.toSSet.obj (Tor Y)).map (frontIncl (1 + 1) 1).op
          (prismSimplex (arcH Y arc) σ i'))
      = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hvals : ∀ i : Fin (2 + 1),
      (-1 : ℤ) ^ (i : ℕ) * (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
          (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
          (prismSimplex (arcH Y arc) σ i)
        = if i = 1 then (-(windS (pathEdge (Sph 1) arc)))
            * (cup w (cochainPullbackInt (endAt Y (arc 1)) 1 u)) σ else 0 := by
    intro i
    by_cases hi1 : i = 1
    · subst hi1
      rw [if_pos rfl, cup_apply, cup_apply, cochainPullbackInt_apply,
        cochainPullbackInt_apply, hmid 1]
      have hspine : frontFace (p := 1) (q := 1) (frontFace (p := 1 + 1) (q := 1)
              (prismSimplex (arcH Y arc) σ 1))
          = (TopCat.toSSet.obj (Tor Y)).map ((frontIncl 1 1 ≫ frontIncl (1 + 1) 1)).op
              (prismSimplex (arcH Y arc) σ 1) := by
        show (TopCat.toSSet.obj (Tor Y)).map (frontIncl 1 1).op
            ((TopCat.toSSet.obj (Tor Y)).map (frontIncl (1 + 1) 1).op
              (prismSimplex (arcH Y arc) σ 1))
          = _
        rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      have hback : backFace (p := 1 + 1) (q := 1) (prismSimplex (arcH Y arc) σ 1)
          = (TopCat.toSSet.obj (Tor Y)).map (backIncl (1 + 1) 1).op
              (prismSimplex (arcH Y arc) σ 1) := rfl
      rw [hspine, hback,
        sndFace_prism_mid Y arc σ 1 (backIncl 1 1 ≫ frontIncl (1 + 1) 1)
          (by decide) (by decide),
        fstFace_prism (n := 2) Y arc σ 1 (frontIncl 1 1 ≫ frontIncl (1 + 1) 1) (frontIncl 1 1)
          (by decide),
        tailFace_prism (n := 2) Y arc σ 1 (backIncl (1 + 1) 1) (backIncl 1 1)
          (by decide) (by decide),
        cup_apply, cochainPullbackInt_apply,
        show frontFace (p := 1) (q := 1) σ = (TopCat.toSSet.obj Y).map (frontIncl 1 1).op σ
          from rfl,
        show backFace (p := 1) (q := 1) σ = (TopCat.toSSet.obj Y).map (backIncl 1 1).op σ
          from rfl]
      show (-1 : ℤ) ^ 1 * _ = _
      ring
    · by_cases hi0 : i = 0
      · subst hi0
        rw [if_neg (by decide), cup_apply, cup_apply, cochainPullbackInt_apply,
          cochainPullbackInt_apply, hmid 0,
          sndFace_prism_hi Y arc σ 0 (backIncl 1 1 ≫ frontIncl (1 + 1) 1) (by decide),
          windS_const, mul_zero, zero_mul, mul_zero]
      · have hi2 : i = 2 := by
          apply Fin.ext
          show (i : ℕ) = 2
          have hv := i.isLt
          have h1' : (i : ℕ) ≠ 1 := fun h =>
            hi1 (Fin.ext (show (i : ℕ) = ((1 : Fin (2 + 1)) : ℕ) from h))
          have h0' : (i : ℕ) ≠ 0 := fun h =>
            hi0 (Fin.ext (show (i : ℕ) = ((0 : Fin (2 + 1)) : ℕ) from h))
          omega
        subst hi2
        rw [if_neg (by decide), cup_apply, cup_apply, cochainPullbackInt_apply,
          cochainPullbackInt_apply, hmid 2,
          sndFace_prism_lo Y arc σ 2 (backIncl 1 1 ≫ frontIncl (1 + 1) 1) (by decide),
          windS_const, mul_zero, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hvals i), Finset.sum_ite_eq' Finset.univ (1 : Fin (2 + 1))
    (fun _ => (-(windS (pathEdge (Sph 1) arc)))
      * (cup w (cochainPullbackInt (endAt Y (arc 1)) 1 u)) σ),
    if_pos (Finset.mem_univ _)]

/-- **The `(1,2)` mid peel (single cylinder)**: the vertical edge sits at spine position 2 of a
4-simplex; only the `i = 1` prism simplex contributes, with sign `−1`. -/
theorem kronecker_cupMid_prism_1_2 (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1)))
    (w : SingularCochainInt Y 1) (u : SingularCochainInt (Tor Y) 2)
    (c : SingularChainInt Y 3) :
    kronecker (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
      (prismOpInt (arcH Y arc) 3 c)
      = -(windS (pathEdge (Sph 1) arc)
          * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 2 u)) c) := by
  rw [show -(windS (pathEdge (Sph 1) arc)
        * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 2 u)) c)
      = (-(windS (pathEdge (Sph 1) arc)))
          * kronecker (cup w (cochainPullbackInt (endAt Y (arc 1)) 2 u)) c by ring]
  refine kronecker_prismOpInt_of_basis _ _ _ _ (fun σ => ?_) c
  rw [kronecker_prismBasisInt]
  have hmid : ∀ i' : Fin (3 + 1),
      backFace (p := 1) (q := 1) (frontFace (p := 1 + 1) (q := 2)
          (prismSimplex (arcH Y arc) σ i'))
      = (TopCat.toSSet.obj (Tor Y)).map ((backIncl 1 1 ≫ frontIncl (1 + 1) 2)).op
          (prismSimplex (arcH Y arc) σ i') := by
    intro i'
    show (TopCat.toSSet.obj (Tor Y)).map (backIncl 1 1).op
        ((TopCat.toSSet.obj (Tor Y)).map (frontIncl (1 + 1) 2).op
          (prismSimplex (arcH Y arc) σ i'))
      = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hvals : ∀ i : Fin (3 + 1),
      (-1 : ℤ) ^ (i : ℕ) * (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
          (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
          (prismSimplex (arcH Y arc) σ i)
        = if i = 1 then (-(windS (pathEdge (Sph 1) arc)))
            * (cup w (cochainPullbackInt (endAt Y (arc 1)) 2 u)) σ else 0 := by
    intro i
    by_cases hi1 : i = 1
    · subst hi1
      rw [if_pos rfl, cup_apply, cup_apply, cochainPullbackInt_apply,
        cochainPullbackInt_apply, hmid 1]
      have hspine : frontFace (p := 1) (q := 1) (frontFace (p := 1 + 1) (q := 2)
              (prismSimplex (arcH Y arc) σ 1))
          = (TopCat.toSSet.obj (Tor Y)).map ((frontIncl 1 1 ≫ frontIncl (1 + 1) 2)).op
              (prismSimplex (arcH Y arc) σ 1) := by
        show (TopCat.toSSet.obj (Tor Y)).map (frontIncl 1 1).op
            ((TopCat.toSSet.obj (Tor Y)).map (frontIncl (1 + 1) 2).op
              (prismSimplex (arcH Y arc) σ 1))
          = _
        rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      have hback : backFace (p := 1 + 1) (q := 2) (prismSimplex (arcH Y arc) σ 1)
          = (TopCat.toSSet.obj (Tor Y)).map (backIncl (1 + 1) 2).op
              (prismSimplex (arcH Y arc) σ 1) := rfl
      rw [hspine, hback,
        sndFace_prism_mid Y arc σ 1 (backIncl 1 1 ≫ frontIncl (1 + 1) 2)
          (by decide) (by decide),
        fstFace_prism (n := 3) Y arc σ 1 (frontIncl 1 1 ≫ frontIncl (1 + 1) 2) (frontIncl 1 2)
          (by decide),
        tailFace_prism (n := 3) Y arc σ 1 (backIncl (1 + 1) 2) (backIncl 1 2)
          (by decide) (by decide),
        cup_apply, cochainPullbackInt_apply,
        show frontFace (p := 1) (q := 2) σ = (TopCat.toSSet.obj Y).map (frontIncl 1 2).op σ
          from rfl,
        show backFace (p := 1) (q := 2) σ = (TopCat.toSSet.obj Y).map (backIncl 1 2).op σ
          from rfl]
      show (-1 : ℤ) ^ 1 * _ = _
      ring
    · by_cases hi0 : i = 0
      · subst hi0
        rw [if_neg (by decide), cup_apply, cup_apply, cochainPullbackInt_apply,
          cochainPullbackInt_apply, hmid 0,
          sndFace_prism_hi Y arc σ 0 (backIncl 1 1 ≫ frontIncl (1 + 1) 2) (by decide),
          windS_const, mul_zero, zero_mul, mul_zero]
      · by_cases hi2 : i = 2
        · subst hi2
          rw [if_neg (by decide), cup_apply, cup_apply, cochainPullbackInt_apply,
            cochainPullbackInt_apply, hmid 2,
            sndFace_prism_lo Y arc σ 2 (backIncl 1 1 ≫ frontIncl (1 + 1) 2) (by decide),
            windS_const, mul_zero, zero_mul, mul_zero]
        · have hi3 : i = 3 := by
            apply Fin.ext
            show (i : ℕ) = 3
            have hv := i.isLt
            have h1' : (i : ℕ) ≠ 1 := fun h =>
              hi1 (Fin.ext (show (i : ℕ) = ((1 : Fin (3 + 1)) : ℕ) from h))
            have h0' : (i : ℕ) ≠ 0 := fun h =>
              hi0 (Fin.ext (show (i : ℕ) = ((0 : Fin (3 + 1)) : ℕ) from h))
            have h2' : (i : ℕ) ≠ 2 := fun h =>
              hi2 (Fin.ext (show (i : ℕ) = ((2 : Fin (3 + 1)) : ℕ) from h))
            omega
          subst hi3
          rw [if_neg (by decide), cup_apply, cup_apply, cochainPullbackInt_apply,
            cochainPullbackInt_apply, hmid 3,
            sndFace_prism_lo Y arc σ 3 (backIncl 1 1 ≫ frontIncl (1 + 1) 2) (by decide),
            windS_const, mul_zero, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hvals i), Finset.sum_ite_eq' Finset.univ (1 : Fin (3 + 1))
    (fun _ => (-(windS (pathEdge (Sph 1) arc)))
      * (cup w (cochainPullbackInt (endAt Y (arc 1)) 2 u)) σ),
    if_pos (Finset.mem_univ _)]


/-! ## §8. The glued mid peels — the basepoint slice -/

/-- The circle basepoint (`arcA 0 = arcB 1`, the image of `1 ∈ Circle`). -/
noncomputable def basePt : ↑(Sph 1) := arcA 0

theorem endAt_arcB_one (Y : TopCat) : endAt Y (arcB 1) = endAt Y basePt := by
  rw [show arcB 1 = basePt from arcB_one_eq_arcA_zero]

/-- **The glued `(0,1)` peel**: `⟨snd*windS ⌣ u, torCross c⟩ = ⟨bp* u, c⟩`. -/
theorem kronecker_cupMid_torCross_0_1 (Y : TopCat)
    (u : SingularCochainInt (Tor Y) 1) (c : SingularChainInt Y 1) :
    kronecker (cup (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS) u)
      (torCross Y 1 c)
      = kronecker (cochainPullbackInt (endAt Y basePt) 1 u) c := by
  rw [torCross_apply, kronecker_add_right, kronecker_cupMid_prism_0_1,
    kronecker_cupMid_prism_0_1, windS_pathEdge_arcA, windS_pathEdge_arcB, endAt_arcB_one]
  ring

/-- **The glued `(1,1)` peel**: `⟨(fst*w ⌣ snd*windS) ⌣ u, torCross c⟩ = −⟨w ⌣ bp* u, c⟩`. -/
theorem kronecker_cupMid_torCross_1_1 (Y : TopCat)
    (w : SingularCochainInt Y 1) (u : SingularCochainInt (Tor Y) 1)
    (c : SingularChainInt Y 2) :
    kronecker (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
      (torCross Y 2 c)
      = -(kronecker (cup w (cochainPullbackInt (endAt Y basePt) 1 u)) c) := by
  rw [torCross_apply, kronecker_add_right, kronecker_cupMid_prism_1_1,
    kronecker_cupMid_prism_1_1, windS_pathEdge_arcA, windS_pathEdge_arcB, endAt_arcB_one]
  ring

/-- **The glued `(1,2)` peel**: `⟨(fst*w ⌣ snd*windS) ⌣ u, torCross c⟩ = −⟨w ⌣ bp* u, c⟩`. -/
theorem kronecker_cupMid_torCross_1_2 (Y : TopCat)
    (w : SingularCochainInt Y 1) (u : SingularCochainInt (Tor Y) 2)
    (c : SingularChainInt Y 3) :
    kronecker (cup (cup (cochainPullbackInt (prodFst Y (Sph 1)) 1 w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS)) u)
      (torCross Y 3 c)
      = -(kronecker (cup w (cochainPullbackInt (endAt Y basePt) 2 u)) c) := by
  rw [torCross_apply, kronecker_add_right, kronecker_cupMid_prism_1_2,
    kronecker_cupMid_prism_1_2, windS_pathEdge_arcA, windS_pathEdge_arcB, endAt_arcB_one]
  ring

end SKEFTHawking.TorusCrossPeel
