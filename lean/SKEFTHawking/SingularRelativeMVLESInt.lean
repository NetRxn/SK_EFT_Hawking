import Mathlib
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.ChainComplexLESInt

/-!
# The integral relative Mayer–Vietoris **long exact sequence** for a pair of opens

Only *middle* exactness (`range Δ_* = ker Σ_*`) was previously exposed at homology level
(`SingularRelativeMVInt.relMvInt_exact_middle'`). This module assembles the **full** relative MV LES
by feeding the on-main chain-level short exact sequence

`0 → C(M, U∩V) --Δ--> C(M,U) ⊕ C(M,V) --Σ--> Q = C(M)/(C(U)+C(V)) → 0`

(`relMvChainDiagInt_injective`, `relMvChain_exactInt`, `relMvChainSumInt_surjective`) into the
abstract zig-zag engine `ChainComplexLESInt`, and then transporting the middle term along the
product-complex homology iso and the third term along the small-chains iso `iotaEquivInt`.

Output (`U`, `V` open):

`⋯ → Hₙ₊₁(M, U∪V) --δ--> Hₙ(M, U∩V) --Δ_*--> Hₙ(M,U) ⊕ Hₙ(M,V) --Σ_*--> Hₙ(M, U∪V) → ⋯`

With `Hₙ(M|A) := Hₙ(M, M∖A)` and `U = M∖A`, `V = M∖B` this is the *local-homology* Mayer–Vietoris
used in Hatcher's Lemma 3.36 — the tool that computes `Hₙ(M|K)` by decomposing `K`.

Contents:
* §1 — the chain-map / `∂∘∂ = 0` conditions the engine wants;
* §2 — `prodHmlEquivInt` : `Hₙ(C(M,U) ⊕ C(M,V)) ≅ Hₙ(M,U) × Hₙ(M,V)` (the homology of a product
  complex is the product of the homologies), plus the identifications naming the engine's induced
  maps as the project's `relMvHomDiagInt` / `relMvHomSumQInt`;
* §3 — the connecting map `relMvDeltaQInt` (Q-form) and `relMvDeltaInt` (textbook form, opens), and
  the two remaining exactness statements.

Ambient higher-order implicits of the engine (`M : ℕ → Type`) are **pinned** at every use site via
`(M := …)`; unpinned they do not unify against `fun n => RelativeChainInt U n × RelativeChainInt V n`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularRelativeMVLESInt

variable {X : TopCat}

/-- The **middle complex** `C(M,U) ⊕ C(M,V)` of the relative MV chain SES, as an ℕ-graded family.
An `abbrev` (reducible) so the engine's instance search and the `(M := …)` pins still see through
it. -/
abbrev bChainInt (U V : Set ↑X) : ℕ → Type := fun n => RelativeChainInt U n × RelativeChainInt V n

/-! ## §1. The chain SES data -/

/-- `Δ` is a **chain map**: `∂_B ∘ Δ = Δ ∘ ∂`. -/
theorem relMvChainDiagInt_chainMap (U V : Set ↑X) (n : ℕ)
    (x : RelativeChainInt (U ∩ V) (n + 1)) :
    bBoundaryInt U V n (relMvChainDiagInt U V (n + 1) x)
      = relMvChainDiagInt U V n (relBoundaryInt (U ∩ V) n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show bBoundaryInt U V n (relMvChainDiagInt U V (n + 1) (RelativeChainInt.mk (U ∩ V) (n + 1) c))
      = relMvChainDiagInt U V n (relBoundaryInt (U ∩ V) n (RelativeChainInt.mk (U ∩ V) (n + 1) c))
  rw [relMvChainDiagInt_mk, bBoundaryInt_mk, relBoundaryInt_mk, relMvChainDiagInt_mk]

/-- `∂_B ∘ ∂_B = 0` on the middle complex. -/
theorem bBoundaryInt_bBoundaryInt (U V : Set ↑X) (n : ℕ)
    (x : RelativeChainInt U (n + 2) × RelativeChainInt V (n + 2)) :
    bBoundaryInt U V n (bBoundaryInt U V (n + 1) x) = 0 := by
  refine Prod.ext ?_ ?_
  · show relBoundaryInt U n (relBoundaryInt U (n + 1) x.1) = 0
    rw [← LinearMap.comp_apply, relBoundaryInt_comp_relBoundaryInt, LinearMap.zero_apply]
  · show relBoundaryInt V n (relBoundaryInt V (n + 1) x.2) = 0
    rw [← LinearMap.comp_apply, relBoundaryInt_comp_relBoundaryInt, LinearMap.zero_apply]

/-- The chain SES is **exact in the middle** as the `range = ker` equation the engine wants. -/
theorem relMvChain_range_eq_kerInt (U V : Set ↑X) (n : ℕ) :
    LinearMap.range (relMvChainDiagInt U V n) = LinearMap.ker (relMvChainSumInt U V n) :=
  (relMvChain_exactInt U V n).linearMap_ker_eq.symm

/-! ## §2. Homology of the product complex -/

/-- Membership in the middle complex's cycles is componentwise. -/
theorem mem_bCyclesInt_iff (U V : Set ↑X) (n : ℕ)
    (z : RelativeChainInt U n × RelativeChainInt V n) :
    z ∈ ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n
      ↔ z.1 ∈ relCyclesInt U n ∧ z.2 ∈ relCyclesInt V n := by
  cases n with
  | zero => exact ⟨fun _ => ⟨Submodule.mem_top, Submodule.mem_top⟩, fun _ => Submodule.mem_top⟩
  | succ m =>
    show bBoundaryInt U V m z = 0 ↔ _
    rw [bBoundaryInt, LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact Iff.rfl

/-- Membership in the middle complex's boundaries is componentwise. -/
theorem mem_bBoundariesInt_iff (U V : Set ↑X) (n : ℕ)
    (z : RelativeChainInt U n × RelativeChainInt V n) :
    z ∈ ChainComplexLESInt.boundaries (M := bChainInt U V) (bBoundaryInt U V) n
      ↔ z.1 ∈ relBoundariesInt U n ∧ z.2 ∈ relBoundariesInt V n := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨w.1, rfl⟩, ⟨w.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- First-component projection on middle-complex cycles. -/
noncomputable def bCycFstInt (U V : Set ↑X) (n : ℕ) :
    ↥(ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n) →ₗ[ℤ]
      ↥(relCyclesInt U n) :=
  (LinearMap.fst ℤ (RelativeChainInt U n) (RelativeChainInt V n)).restrict
    (fun z hz => ((mem_bCyclesInt_iff U V n z).mp hz).1)

/-- Second-component projection on middle-complex cycles. -/
noncomputable def bCycSndInt (U V : Set ↑X) (n : ℕ) :
    ↥(ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n) →ₗ[ℤ]
      ↥(relCyclesInt V n) :=
  (LinearMap.snd ℤ (RelativeChainInt U n) (RelativeChainInt V n)).restrict
    (fun z hz => ((mem_bCyclesInt_iff U V n z).mp hz).2)

/-- `a ↦ (a, 0)` on cycles. -/
noncomputable def bCycInlInt (U V : Set ↑X) (n : ℕ) :
    ↥(relCyclesInt U n) →ₗ[ℤ]
      ↥(ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n) :=
  (LinearMap.inl ℤ (RelativeChainInt U n) (RelativeChainInt V n)).restrict
    (fun _ ha => (mem_bCyclesInt_iff U V n _).mpr ⟨ha, Submodule.zero_mem _⟩)

/-- `b ↦ (0, b)` on cycles. -/
noncomputable def bCycInrInt (U V : Set ↑X) (n : ℕ) :
    ↥(relCyclesInt V n) →ₗ[ℤ]
      ↥(ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n) :=
  (LinearMap.inr ℤ (RelativeChainInt U n) (RelativeChainInt V n)).restrict
    (fun _ hb => (mem_bCyclesInt_iff U V n _).mpr ⟨Submodule.zero_mem _, hb⟩)

/-- **Forward map** `Hₙ(C(M,U) ⊕ C(M,V)) → Hₙ(M,U) × Hₙ(M,V)`, componentwise on classes. -/
noncomputable def bHmlToProdInt (U V : Set ↑X) (n : ℕ) :
    ChainComplexLESInt.Hml (M := bChainInt U V) (bBoundaryInt U V) n →ₗ[ℤ]
      RelHomologyInt U n × RelHomologyInt V n :=
  Submodule.liftQ _
    (((Submodule.mkQ ((relBoundariesInt U n).submoduleOf (relCyclesInt U n))).comp
        (bCycFstInt U V n)).prod
      ((Submodule.mkQ ((relBoundariesInt V n).submoduleOf (relCyclesInt V n))).comp
        (bCycSndInt U V n)))
    (by
      rintro z hz
      rw [ChainComplexLESInt.mem_submoduleOf] at hz
      obtain ⟨hzU, hzV⟩ := (mem_bBoundariesInt_iff U V n (z : bChainInt U V n)).mp hz
      rw [LinearMap.mem_ker]
      refine Prod.ext ?_ ?_
      · show RelHomologyInt.mk U n (bCycFstInt U V n z) = 0
        exact (RelHomologyInt.mk_eq_zero_iff U n _).mpr hzU
      · show RelHomologyInt.mk V n (bCycSndInt U V n z) = 0
        exact (RelHomologyInt.mk_eq_zero_iff V n _).mpr hzV)

/-- **Backward map** `Hₙ(M,U) × Hₙ(M,V) → Hₙ(C(M,U) ⊕ C(M,V))`, `([a],[b]) ↦ [(a,0)] + [(0,b)]`. -/
noncomputable def prodToBHmlInt (U V : Set ↑X) (n : ℕ) :
    RelHomologyInt U n × RelHomologyInt V n →ₗ[ℤ]
      ChainComplexLESInt.Hml (M := bChainInt U V) (bBoundaryInt U V) n :=
  LinearMap.coprod
    (Submodule.liftQ _
      ((ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n).comp
        (bCycInlInt U V n))
      (by
        rintro a ha
        rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at ha
        rw [LinearMap.mem_ker]
        show ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n _ = 0
        exact (ChainComplexLESInt.Hml.mk_eq_zero_iff _ n _).mpr
          ((mem_bBoundariesInt_iff U V n _).mpr ⟨ha, Submodule.zero_mem _⟩)))
    (Submodule.liftQ _
      ((ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n).comp
        (bCycInrInt U V n))
      (by
        rintro b hb
        rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hb
        rw [LinearMap.mem_ker]
        show ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n _ = 0
        exact (ChainComplexLESInt.Hml.mk_eq_zero_iff _ n _).mpr
          ((mem_bBoundariesInt_iff U V n _).mpr ⟨Submodule.zero_mem _, hb⟩)))

theorem bHmlToProdInt_mk (U V : Set ↑X) (n : ℕ)
    (z : ↥(ChainComplexLESInt.cycles (M := bChainInt U V) (bBoundaryInt U V) n)) :
    bHmlToProdInt U V n (ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n z)
      = (RelHomologyInt.mk U n (bCycFstInt U V n z),
         RelHomologyInt.mk V n (bCycSndInt U V n z)) := rfl

theorem prodToBHmlInt_mk (U V : Set ↑X) (n : ℕ) (a : relCyclesInt U n) (b : relCyclesInt V n) :
    prodToBHmlInt U V n (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b)
      = ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n (bCycInlInt U V n a)
        + ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n
            (bCycInrInt U V n b) := rfl

/-- **Homology of the product complex is the product of the homologies**:
`Hₙ(C(M,U) ⊕ C(M,V)) ≅ Hₙ(M,U) × Hₙ(M,V)`. This is the bridge that lets the abstract zig-zag
engine's middle term be read as the project's `Hₙ(M,U) ⊕ Hₙ(M,V)`. -/
noncomputable def bHmlProdEquivInt (U V : Set ↑X) (n : ℕ) :
    ChainComplexLESInt.Hml (M := bChainInt U V) (bBoundaryInt U V) n ≃ₗ[ℤ]
      RelHomologyInt U n × RelHomologyInt V n :=
  LinearEquiv.ofLinear (bHmlToProdInt U V n) (prodToBHmlInt U V n)
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨pu, pv⟩ := p
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
      show bHmlToProdInt U V n
          (prodToBHmlInt U V n (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b))
        = (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b)
      rw [prodToBHmlInt_mk, map_add, bHmlToProdInt_mk, bHmlToProdInt_mk]
      refine Prod.ext ?_ ?_
      · show RelHomologyInt.mk U n a + RelHomologyInt.mk U n 0 = RelHomologyInt.mk U n a
        rw [show RelHomologyInt.mk U n 0 = 0 from Submodule.Quotient.mk_zero _, add_zero]
      · show RelHomologyInt.mk V n 0 + RelHomologyInt.mk V n b = RelHomologyInt.mk V n b
        rw [show RelHomologyInt.mk V n 0 = 0 from Submodule.Quotient.mk_zero _, zero_add])
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      show prodToBHmlInt U V n
          (bHmlToProdInt U V n (ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n z))
        = ChainComplexLESInt.Hml.mk (M := bChainInt U V) (bBoundaryInt U V) n z
      rw [bHmlToProdInt_mk, prodToBHmlInt_mk]
      show ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n
            (bCycInlInt U V n (bCycFstInt U V n z))
          + ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n
            (bCycInrInt U V n (bCycSndInt U V n z))
        = ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n z
      rw [← map_add]
      exact congrArg (ChainComplexLESInt.Hml.mkHom (M := bChainInt U V) (bBoundaryInt U V) n)
        (Subtype.ext (Prod.ext (add_zero _) (zero_add _))))

/-! ## §3. The connecting homomorphism and the two remaining exactness statements -/

/-- `Σ` is a chain map in the engine's orientation. -/
theorem relMvChainSumInt_chainMap' (U V : Set ↑X) (n : ℕ)
    (x : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)) :
    qBoundaryInt U V n (relMvChainSumInt U V (n + 1) x)
      = relMvChainSumInt U V n (bBoundaryInt U V n x) :=
  (relMvChainSumInt_chainMap U V n x).symm

/-- The engine's induced map on the middle term, read in the product presentation:
`Δ_* : Hₙ(M, U∩V) → Hₙ(M,U) × Hₙ(M,V)`. -/
theorem prod_Hmap_diagInt (U V : Set ↑X) (n : ℕ) (w : RelHomologyInt (U ∩ V) n) :
    bHmlProdEquivInt U V n
        (ChainComplexLESInt.Hmap (M := fun k => RelativeChainInt (U ∩ V) k) (N := bChainInt U V)
          (f := relMvChainDiagInt U V) (dM := relBoundaryInt (U ∩ V)) (dN := bBoundaryInt U V)
          (relMvChainDiagInt_chainMap U V) n w)
      = relMvHomDiagInt U V n w := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

/-- The engine's induced map out of the middle term, read in the product presentation:
`Σ_* : Hₙ(M,U) × Hₙ(M,V) → Hₙ(Q)`. -/
theorem Hmap_sum_prodInt (U V : Set ↑X) (n : ℕ) (p : RelHomologyInt U n × RelHomologyInt V n) :
    ChainComplexLESInt.Hmap (M := bChainInt U V) (N := fun k => QChainInt U V k)
        (f := relMvChainSumInt U V) (dM := bBoundaryInt U V) (dN := qBoundaryInt U V)
        (relMvChainSumInt_chainMap' U V) n ((bHmlProdEquivInt U V n).symm p)
      = relMvHomSumQInt U V n p := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show ChainComplexLESInt.Hmap (M := bChainInt U V) (N := fun k => QChainInt U V k)
      (f := relMvChainSumInt U V) (dM := bBoundaryInt U V) (dN := qBoundaryInt U V)
      (relMvChainSumInt_chainMap' U V) n
      (prodToBHmlInt U V n (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b))
    = relMvHomSumQInt U V n (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b)
  rw [prodToBHmlInt_mk, map_add, ChainComplexLESInt.Hmap_mk, ChainComplexLESInt.Hmap_mk,
    relMvHomSumQInt_mk]
  show ChainComplexLESInt.Hml.mkHom (M := fun k => QChainInt U V k) (qBoundaryInt U V) n _
      + ChainComplexLESInt.Hml.mkHom (M := fun k => QChainInt U V k) (qBoundaryInt U V) n _ = _
  rw [← map_add]
  refine congrArg (ChainComplexLESInt.Hml.mkHom (M := fun k => QChainInt U V k)
    (qBoundaryInt U V) n) (Subtype.ext ?_)
  show relMvChainSumInt U V n ((a : RelativeChainInt U n), 0)
      + relMvChainSumInt U V n (0, (b : RelativeChainInt V n))
    = relMvChainSumInt U V n ((a : RelativeChainInt U n), (b : RelativeChainInt V n))
  rw [← map_add]
  exact congrArg (relMvChainSumInt U V n) (Prod.ext (add_zero _) (zero_add _))

/-- **The relative MV connecting homomorphism, `Q`-form**: `δ : Hₙ₊₁(Q) → Hₙ(M, U∩V)`, the zig-zag
of the relative MV chain SES. -/
noncomputable def relMvDeltaQInt (U V : Set ↑X) (n : ℕ) :
    QHomologyInt U V (n + 1) →ₗ[ℤ] RelHomologyInt (U ∩ V) n :=
  ChainComplexLESInt.delta (M := fun k => RelativeChainInt (U ∩ V) k) (N := bChainInt U V)
    (P := fun k => QChainInt U V k) (dM := relBoundaryInt (U ∩ V)) (dN := bBoundaryInt U V)
    (dP := qBoundaryInt U V) (f := relMvChainDiagInt U V) (g := relMvChainSumInt U V)
    (relMvChainDiagInt_chainMap U V) (relMvChainSumInt_chainMap' U V)
    (bBoundaryInt_bBoundaryInt U V) (relMvChainDiagInt_injective U V)
    (relMvChainSumInt_surjective U V) (relMvChain_range_eq_kerInt U V) n

/-- **Relative MV exactness at `Hₙ(M, U∩V)`** (`Q`-form): `ker Δ_* = im δ`. -/
theorem relMvQ_exact_delta_diagInt (U V : Set ↑X) (n : ℕ) :
    Function.Exact (relMvDeltaQInt U V n) (relMvHomDiagInt U V n) := by
  intro w
  rw [← prod_Hmap_diagInt U V n w, (bHmlProdEquivInt U V n).map_eq_zero_iff]
  exact ChainComplexLESInt.exact_delta_Hmap (M := fun k => RelativeChainInt (U ∩ V) k)
    (N := bChainInt U V) (P := fun k => QChainInt U V k) (dM := relBoundaryInt (U ∩ V))
    (dN := bBoundaryInt U V) (dP := qBoundaryInt U V) (f := relMvChainDiagInt U V)
    (g := relMvChainSumInt U V) (relMvChainDiagInt_chainMap U V) (relMvChainSumInt_chainMap' U V)
    (bBoundaryInt_bBoundaryInt U V) (relMvChainDiagInt_injective U V)
    (relMvChainSumInt_surjective U V) (relMvChain_range_eq_kerInt U V) n w

/-- **Relative MV exactness at `Hₙ₊₁(Q)`** (`Q`-form): `ker δ = im Σ_*`. -/
theorem relMvQ_exact_sum_deltaInt (U V : Set ↑X) (n : ℕ) :
    Function.Exact (relMvHomSumQInt U V (n + 1)) (relMvDeltaQInt U V n) := by
  intro z
  have hE := ChainComplexLESInt.exact_Hmap_delta (M := fun k => RelativeChainInt (U ∩ V) k)
      (N := bChainInt U V) (P := fun k => QChainInt U V k) (dM := relBoundaryInt (U ∩ V))
      (dN := bBoundaryInt U V) (dP := qBoundaryInt U V) (f := relMvChainDiagInt U V)
      (g := relMvChainSumInt U V) (relMvChainDiagInt_chainMap U V) (relMvChainSumInt_chainMap' U V)
      (bBoundaryInt_bBoundaryInt U V) (relMvChainDiagInt_injective U V)
      (relMvChainSumInt_surjective U V) (relMvChain_range_eq_kerInt U V) n z
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := hE.mp hz
    refine ⟨bHmlProdEquivInt U V (n + 1) y, ?_⟩
    rw [← Hmap_sum_prodInt U V (n + 1) (bHmlProdEquivInt U V (n + 1) y),
      LinearEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨p, rfl⟩
    exact hE.mpr ⟨(bHmlProdEquivInt U V (n + 1)).symm p, Hmap_sum_prodInt U V (n + 1) p⟩

/-! ### Textbook form (`U`, `V` open): the third term is `Hₙ(M, U∪V)` -/

/-- **The relative Mayer–Vietoris connecting homomorphism** `δ : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` for a
pair of **opens** — the `Q`-form `δ` pulled back along the small-chains iso `ι`. -/
noncomputable def relMvDeltaInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    RelHomologyInt (U ∪ V) (n + 1) →ₗ[ℤ] RelHomologyInt (U ∩ V) n :=
  (relMvDeltaQInt U V n).comp (iotaEquivInt U V hU hV n).symm.toLinearMap

/-- **Relative MV exactness at `Hₙ(M, U∩V)`** (textbook form): `ker Δ_* = im δ`. -/
theorem relMv_exact_delta_diagInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Exact (relMvDeltaInt U V hU hV n) (relMvHomDiagInt U V n) := by
  intro w
  rw [relMvQ_exact_delta_diagInt U V n w]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨iotaEquivInt U V hU hV n q, by
      show relMvDeltaQInt U V n ((iotaEquivInt U V hU hV n).symm
        (iotaEquivInt U V hU hV n q)) = _
      rw [LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(iotaEquivInt U V hU hV n).symm y, rfl⟩

/-- **Relative MV exactness at `Hₙ₊₁(M, U∪V)`** (textbook form): `ker δ = im Σ_*`. -/
theorem relMv_exact_sum_deltaInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Exact (relMvHomSumInt U V (n + 1)) (relMvDeltaInt U V hU hV n) := by
  intro z
  rw [show relMvDeltaInt U V hU hV n z
      = relMvDeltaQInt U V n ((iotaEquivInt U V hU hV n).symm z) from rfl,
    relMvQ_exact_sum_deltaInt U V n _]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [← iota_relMvHomSumQInt U V (n + 1) p,
      show iotaInt U V (n + 1) (relMvHomSumQInt U V (n + 1) p)
        = iotaEquivInt U V hU hV n (relMvHomSumQInt U V (n + 1) p) from rfl, hp,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    rw [← iota_relMvHomSumQInt U V (n + 1) p,
      show iotaInt U V (n + 1) (relMvHomSumQInt U V (n + 1) p)
        = iotaEquivInt U V hU hV n (relMvHomSumQInt U V (n + 1) p) from rfl,
      LinearEquiv.symm_apply_apply]

/-- **The assembly corollary — `δ` is an isomorphism when both pieces vanish.** If
`Hₙ(M,U) = Hₙ(M,V) = 0` and `Hₙ₊₁(M,U) = Hₙ₊₁(M,V) = 0`, the relative MV connecting map is a linear
equivalence `Hₙ₊₁(M, U∪V) ≅ Hₙ(M, U∩V)`.

In the local-homology reading (`U = M∖A`, `V = M∖B`) this is
`Hₙ₊₁(M|A∩B) ≅ Hₙ(M|A∪B)` whenever `Hₙ(M|A) = Hₙ(M|B) = Hₙ₊₁(M|A) = Hₙ₊₁(M|B) = 0` — exactly the
step that computes `H₂(M|S²)` from `H₃(M|equator)` once the two hemispheres are shown acyclic. -/
noncomputable def relMvDeltaEquivInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hUn : ∀ x : RelHomologyInt U n, x = 0) (hVn : ∀ x : RelHomologyInt V n, x = 0)
    (hUn1 : ∀ x : RelHomologyInt U (n + 1), x = 0) (hVn1 : ∀ x : RelHomologyInt V (n + 1), x = 0) :
    RelHomologyInt (U ∪ V) (n + 1) ≃ₗ[ℤ] RelHomologyInt (U ∩ V) n :=
  LinearEquiv.ofBijective (relMvDeltaInt U V hU hV n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨p, rfl⟩ := (relMv_exact_sum_deltaInt U V hU hV n x).mp hx
      rw [show p = 0 from Prod.ext (hUn1 p.1) (hVn1 p.2), map_zero],
     by
      intro y
      obtain ⟨q, hq⟩ := (relMvQ_exact_delta_diagInt U V n y).mp
        (Prod.ext (hUn (relMvHomDiagInt U V n y).1) (hVn (relMvHomDiagInt U V n y).2))
      refine ⟨iotaEquivInt U V hU hV n q, ?_⟩
      show relMvDeltaQInt U V n ((iotaEquivInt U V hU hV n).symm
        (iotaEquivInt U V hU hV n q)) = y
      rw [LinearEquiv.symm_apply_apply]
      exact hq⟩

end SKEFTHawking.SingularRelativeMVLESInt
