import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularHomotopyInvarianceInt

/-!
# Functoriality of singular **integral** homology

A continuous map `φ : X → Y` post-composes each singular simplex, inducing an integral chain map
`mapChainInt φ : Cₙ(X;ℤ) → Cₙ(Y;ℤ)` and hence `Homology.mapInt φ : Hₙ(X;ℤ) → Hₙ(Y;ℤ)`. This is the
covariant functor `Hₙ(·;ℤ)` on `TopCat`, the integral mirror of `SingularFunctoriality`.

The **simplex-level** lemmas (`mapSimplex`, `face_mapSimplex`, `mapSimplex_comp`, `mapSimplex_id`)
are reused verbatim from the mod-2 `SingularFunctoriality` (coefficient-free). Combined with the
integral prism (`SingularHomotopyInvarianceInt`), this gives: homotopy-equivalent spaces have
isomorphic integral homology (the engine transporting `ℝ⁴∖0 ≃ S³` to `H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex face_mapSimplex mapSimplex_comp mapSimplex_id)
open SKEFTHawking.SingularCohomologyMod2 (face)

namespace SKEFTHawking.SingularFunctorialityInt

/-! ## §1. The integral pushforward chain map -/

/-- **The integral pushforward chain map** `φ_# : Cₙ(X;ℤ) → Cₙ(Y;ℤ)`, the ℤ-linear extension of the
simplex pushforward `mapSimplex φ`. -/
noncomputable def mapChainInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    SingularChainInt X n →ₗ[ℤ] SingularChainInt Y n :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (mapSimplex φ σ) 1)

@[simp] theorem mapChainInt_single {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    mapChainInt φ n (Finsupp.single σ a) = Finsupp.single (mapSimplex φ σ) a := by
  rw [mapChainInt, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **`mapChainInt φ` is a chain map**: `∂ ∘ φ_# = φ_# ∘ ∂` (integral, signed). Uses the
coefficient-free `face_mapSimplex`. -/
theorem chainBoundary_mapChainInt {X Y : TopCat} {n : ℕ} (φ : C(↑X, ↑Y))
    (c : SingularChainInt X (n + 1)) :
    chainBoundary Y n (mapChainInt φ (n + 1) c) = mapChainInt φ n (chainBoundary X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single σ a =>
      rw [mapChainInt_single, chainBoundary_single_smul, chainBoundary_single_smul, boundaryBasis,
        boundaryBasis, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, mapChainInt_single,
        show SingularCohomologyInt.face i (mapSimplex φ σ)
          = mapSimplex φ (SingularCohomologyInt.face i σ) from face_mapSimplex φ σ i,
        Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §2. Functoriality -/

/-- **Functoriality**: `(ψ ∘ φ)_# = ψ_# ∘ φ_#`. -/
theorem mapChainInt_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ)
    (c : SingularChainInt X n) :
    mapChainInt (ψ.comp φ) n c = mapChainInt ψ n (mapChainInt φ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single σ a => rw [mapChainInt_single, mapSimplex_comp, mapChainInt_single, mapChainInt_single]

/-- **Functoriality**: `(id_X)_# = id`. -/
theorem mapChainInt_id {X : TopCat} (n : ℕ) (c : SingularChainInt X n) :
    mapChainInt (ContinuousMap.id ↑X) n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]
  | single σ a => rw [mapChainInt_single, mapSimplex_id]

/-! ## §3. The induced map on integral homology -/

/-- `mapChainInt φ` preserves cycles. -/
theorem mapChainInt_mem_cycles {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ} {z : SingularChainInt X n}
    (hz : z ∈ cycles X n) : mapChainInt φ n z ∈ cycles Y n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      have hz' : chainBoundary X m z = 0 := hz
      show chainBoundary Y m (mapChainInt φ (m + 1) z) = 0
      rw [chainBoundary_mapChainInt, hz', map_zero]

/-- `mapChainInt φ` preserves boundaries. -/
theorem mapChainInt_mem_boundaries {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    {w : SingularChainInt X n} (hw : w ∈ boundaries X n) : mapChainInt φ n w ∈ boundaries Y n := by
  obtain ⟨u, rfl⟩ := hw
  exact ⟨mapChainInt φ (n + 1) u, chainBoundary_mapChainInt φ u⟩

/-- The induced map on cycles `Zₙ(X;ℤ) → Zₙ(Y;ℤ)`. -/
noncomputable def cyclesMapInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    cycles X n →ₗ[ℤ] cycles Y n :=
  (mapChainInt φ n).restrict (fun _ hz => mapChainInt_mem_cycles φ hz)

@[simp] theorem cyclesMapInt_coe {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) (z : cycles X n) :
    (cyclesMapInt φ n z : SingularChainInt Y n) = mapChainInt φ n (z : SingularChainInt X n) := rfl

/-- **The induced map on integral homology** `Hₙ(φ) : Hₙ(X;ℤ) → Hₙ(Y;ℤ)`. -/
noncomputable def Homology.mapInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    Homology X n →ₗ[ℤ] Homology Y n :=
  Submodule.mapQ _ _ (cyclesMapInt φ n) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    exact mapChainInt_mem_boundaries φ hzb)

@[simp] theorem Homology.mapInt_mk {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) (z : cycles X n) :
    Homology.mapInt φ n (Homology.mk X n z) = Homology.mk Y n (cyclesMapInt φ n z) :=
  Submodule.mapQ_apply _ _ _ _

/-- **Homology functoriality**: `Hₙ(ψ ∘ φ) = Hₙ(ψ) ∘ Hₙ(φ)`. -/
theorem Homology.mapInt_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ) :
    Homology.mapInt (ψ.comp φ) n = (Homology.mapInt ψ n).comp (Homology.mapInt φ n) := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Homology.mapInt (ψ.comp φ) n (Homology.mk X n z)
    = Homology.mapInt ψ n (Homology.mapInt φ n (Homology.mk X n z))
  simp only [Homology.mapInt_mk]
  exact congrArg (Homology.mk Z n) (Subtype.ext (mapChainInt_comp ψ φ n z))

/-- The induced map on cycles of the identity is the identity. -/
theorem cyclesMapInt_id {X : TopCat} (n : ℕ) :
    cyclesMapInt (ContinuousMap.id ↑X) n = LinearMap.id := by
  refine LinearMap.ext fun z => Subtype.ext ?_
  rw [cyclesMapInt_coe, mapChainInt_id, LinearMap.id_apply]

/-- **Homology functoriality**: `Hₙ(id) = id`. -/
theorem Homology.mapInt_id {X : TopCat} (n : ℕ) :
    Homology.mapInt (ContinuousMap.id ↑X) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.id_apply, Homology.mapInt]
  exact (Submodule.mapQ_apply _ _ _ _).trans
    (congrArg Submodule.Quotient.mk ((LinearMap.congr_fun (cyclesMapInt_id n) z).trans
      (LinearMap.id_apply z)))

/-! ## §4. Homotopy invariance at the homology level -/

open SKEFTHawking.SingularHomotopyInvarianceInt

/-- The integral endpoint map is the pushforward of the homotopy slice: `endMapInt H r = mapChainInt
(slice H r)`. (The integral analogue of `endMap_eq_mapChain`; both send `single σ 1` to
`single (endSimplex H r σ) 1 = single (mapSimplex (slice H r) σ) 1` via `endSimplex_eq_mapSimplex`.) -/
theorem endMapInt_eq_mapChainInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (n : ℕ) (c : SingularChainInt X n) :
    endMapInt H r n c = mapChainInt (SingularHomotopyInvariance.slice H r) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single σ a =>
      rw [endMapInt_single, mapChainInt_single, SingularHomotopyInvariance.endSimplex_eq_mapSimplex]

/-- **Homotopy invariance of the induced map**: homotopic maps `f ≃ g` (via `H`, `slice H 0 = f`,
`slice H 1 = g`) induce equal maps on integral homology, `Hₙ(f) = Hₙ(g)`. From the prism identity
`∂P + P∂ = g_# - f_#`, the two pushforwards differ by a boundary on cycles. -/
theorem Homology.mapInt_eq_of_homotopic {X Y : TopCat} {f g : C(↑X, ↑Y)}
    (H : C(↑X × unitInterval, ↑Y)) (h0 : SingularHomotopyInvariance.slice H 0 = f)
    (h1 : SingularHomotopyInvariance.slice H 1 = g) (n : ℕ) :
    Homology.mapInt g (n + 1) = Homology.mapInt f (n + 1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- g_#(z) - f_#(z) = ∂(P z) is a boundary (z a cycle), so the classes agree.
  have hz : chainBoundary X n (z : SingularChainInt X (n + 1)) = 0 := z.2
  have hbdry : mapChainInt g (n + 1) (z : SingularChainInt X (n + 1))
      - mapChainInt f (n + 1) (z : SingularChainInt X (n + 1)) ∈ boundaries Y (n + 1) := by
    have hkey := prism_chainHomotopyInt H (z : SingularChainInt X (n + 1))
    rw [hz, map_zero, add_zero, endMapInt_eq_mapChainInt, endMapInt_eq_mapChainInt, h0, h1] at hkey
    rw [← hkey]
    exact ⟨prismOpInt H (n + 1) (z : SingularChainInt X (n + 1)), rfl⟩
  show Homology.mapInt g (n + 1) (Homology.mk X (n + 1) z)
    = Homology.mapInt f (n + 1) (Homology.mk X (n + 1) z)
  rw [Homology.mapInt_mk, Homology.mapInt_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  exact hbdry

/-- **A homotopy equivalence induces a homology isomorphism** (bijective): if `g ∘ f ≃ id_X` and
`f ∘ g ≃ id_Y`, then `Hₙ₊₁(f)` is bijective. The engine transporting `ℝ⁴∖0 ≃ S³` to
`H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)`. -/
theorem Homology.mapInt_bijective_of_homotopyEquiv {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : SingularHomotopyInvariance.slice Hgf 0 = g.comp f)
    (hgf1 : SingularHomotopyInvariance.slice Hgf 1 = ContinuousMap.id ↑X)
    (Hfg : C(↑Y × unitInterval, ↑Y)) (hfg0 : SingularHomotopyInvariance.slice Hfg 0 = f.comp g)
    (hfg1 : SingularHomotopyInvariance.slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (Homology.mapInt f (n + 1)) := by
  have hgf : Homology.mapInt (ContinuousMap.id ↑X) (n + 1) = Homology.mapInt (g.comp f) (n + 1) :=
    Homology.mapInt_eq_of_homotopic Hgf hgf0 hgf1 n
  have hfg : Homology.mapInt (ContinuousMap.id ↑Y) (n + 1) = Homology.mapInt (f.comp g) (n + 1) :=
    Homology.mapInt_eq_of_homotopic Hfg hfg0 hfg1 n
  rw [Homology.mapInt_id, Homology.mapInt_comp] at hgf
  rw [Homology.mapInt_id, Homology.mapInt_comp] at hfg
  constructor
  · intro a b hab
    have : Homology.mapInt g (n + 1) (Homology.mapInt f (n + 1) a)
        = Homology.mapInt g (n + 1) (Homology.mapInt f (n + 1) b) := by rw [hab]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hgf, LinearMap.id_apply,
      LinearMap.id_apply] at this
    exact this
  · intro y
    refine ⟨Homology.mapInt g (n + 1) y, ?_⟩
    rw [← LinearMap.comp_apply, ← hfg, LinearMap.id_apply]

end SKEFTHawking.SingularFunctorialityInt
