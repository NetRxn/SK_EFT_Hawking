import Mathlib
import SKEFTHawking.SingularRelativeFunctorialityInt
import SKEFTHawking.SingularExcisionIsoInt

/-!
# Integral relative Mayer–Vietoris: middle exactness `ker Σ_* = im Δ_*`

The ℤ analog of `SKEFTHawking.SingularRelativeMV.relMv_exact_middle'`. With `Hₙ(M|A) := Hₙ(M, M∖A)`
and opens `U = M∖A`, `V = M∖B` of `M` (so `U∩V = M∖(A∪B)`, `U∪V = M∖(A∩B)`), the **relative**
Mayer–Vietoris diagonal and sum are the inclusion-of-pairs maps induced by `id_M`:

* `Δ_*(w) = (relInclInt w, relInclInt w) : Hₙ(M,U) ⊕ Hₙ(M,V)` (both inclusions), and
* `Σ_*(a, b) = relInclInt a − relInclInt b : Hₙ(M, U∪V)` (the standard integral **difference**, not
  the mod-2 sum).

The chain-complex condition `Σ_* ∘ Δ_* = 0` holds because both inclusion routes `(M, U∩V) → (M, U∪V)`
are the single inclusion, so over ℤ the difference `c − c = 0`. Middle exactness `ker Σ_* = im Δ_*`
is the shared foundation of the oriented fundamental-class induction and the integral Poincaré-duality
cap-iso: two classes that restrict to the **same** class in `Hₙ(M, U∪V)` have difference `0`, hence
lie in `im Δ_*`.

This mirrors the mod-2 `SingularRelativeMV.lean` structurally verbatim; the only changes are the
coefficient (`ZMod 2 → ℤ`) and the sum-sign convention (`+ → −`). The integral (co)homology,
functoriality, excision-iso, and subdivision primitives are reused wholesale from
`SingularRelHomologyInt`, `SingularRelativeFunctorialityInt`, `SingularExcisionIsoInt`,
`SingularSubdivisionInt`, `SingularExcisionInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularExcisionInt

namespace SKEFTHawking.SingularRelativeMVInt

variable {M : TopCat}

/-! ## §1. The homology-level relative MV maps and the chain-complex condition -/

/-- The inclusion-of-pairs map `Hₙ(M, S; ℤ) → Hₙ(M, T; ℤ)` for `S ⊆ T`, induced by `id_M`. -/
noncomputable def relInclInt {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    RelHomologyInt S n →ₗ[ℤ] RelHomologyInt T n :=
  RelHomologyInt.map (ContinuousMap.id ↑M) (fun _ hx => h hx) n

/-- Composing two inclusion-of-pairs maps is the inclusion over the composite subset relation. -/
theorem relInclInt_trans {S T W : Set ↑M} (h1 : S ⊆ T) (h2 : T ⊆ W) (n : ℕ)
    (x : RelHomologyInt S n) :
    relInclInt h2 n (relInclInt h1 n x) = relInclInt (h1.trans h2) n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [relInclInt, relInclInt, relInclInt, RelHomologyInt.map_mk, RelHomologyInt.map_mk,
    RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  rw [← relMapChainInt_comp (φ := ContinuousMap.id ↑M) (hAB := fun _ hx => h1 hx)
    (ContinuousMap.id ↑M) (fun _ hx => h2 hx) n (z : RelativeChainInt S n)]
  rfl

/-- **Integral relative MV diagonal** `Hₙ(M|A∩B) → Hₙ(M|A) ⊕ Hₙ(M|B)`, the two inclusions
`U∩V ↪ U`, `U∩V ↪ V`. -/
noncomputable def relMvHomDiagInt (U V : Set ↑M) (n : ℕ) :
    RelHomologyInt (U ∩ V) n →ₗ[ℤ] RelHomologyInt U n × RelHomologyInt V n :=
  (relInclInt Set.inter_subset_left n).prod (relInclInt Set.inter_subset_right n)

/-- **Integral relative MV sum** `Hₙ(M|A) ⊕ Hₙ(M|B) → Hₙ(M|A∪B)`, the *difference* of the inclusions
`U ↪ U∪V`, `V ↪ U∪V`. -/
noncomputable def relMvHomSumInt (U V : Set ↑M) (n : ℕ) :
    RelHomologyInt U n × RelHomologyInt V n →ₗ[ℤ] RelHomologyInt (U ∪ V) n :=
  (relInclInt Set.subset_union_left n).coprod (-relInclInt Set.subset_union_right n)

/-- **Integral relative MV chain-complex condition** `Σ_* ∘ Δ_* = 0`: both routes `(M, U∩V) → (M, U∪V)`
equal the single inclusion, so over ℤ the difference is `c − c = 0`. -/
theorem relMvHomSumInt_relMvHomDiagInt (U V : Set ↑M) (n : ℕ) (w : RelHomologyInt (U ∩ V) n) :
    relMvHomSumInt U V n (relMvHomDiagInt U V n w) = 0 := by
  show relInclInt Set.subset_union_left n (relInclInt Set.inter_subset_left n w)
      + (-relInclInt Set.subset_union_right n) (relInclInt Set.inter_subset_right n w) = 0
  rw [LinearMap.neg_apply, relInclInt_trans, relInclInt_trans, ← sub_eq_add_neg, sub_self]

/-! ## §2. Chain-level relative MV short exact sequence (toward the connecting map)

The chain-level diagonal `Δ`, its injectivity, the union submodule `C(U)+C(V)`, the factor maps,
the chain-level sum `Σ` (a **difference** over ℤ), and middle exactness `ker Σ = range Δ`. -/

/-- The chain-level relative MV **diagonal** `C(M, U∩V) → C(M, U) × C(M, V)`, `[c] ↦ ([c], [c])`. -/
noncomputable def relMvChainDiagInt (U V : Set ↑M) (n : ℕ) :
    RelativeChainInt (U ∩ V) n →ₗ[ℤ] RelativeChainInt U n × RelativeChainInt V n :=
  (relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n).prod
    (relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n)

@[simp] theorem relMvChainDiagInt_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) :
    relMvChainDiagInt U V n (RelativeChainInt.mk (U ∩ V) n c)
      = (RelativeChainInt.mk U n c, RelativeChainInt.mk V n c) := by
  simp only [relMvChainDiagInt, LinearMap.prod_apply, Function.prod_def, relMapChainInt_mk,
    SingularFunctorialityInt.mapChainInt_id]

/-- `Δ` is **injective**: `([c]_U, [c]_V) = 0` forces `c ∈ C(U) ∩ C(V) = C(U∩V)`, i.e. `[c]_{U∩V} = 0`. -/
theorem relMvChainDiagInt_injective (U V : Set ↑M) (n : ℕ) :
    Function.Injective (relMvChainDiagInt U V n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) n) = RelativeChainInt.mk (U ∩ V) n c from rfl,
    relMvChainDiagInt_mk, Prod.mk_eq_zero, RelativeChainInt.mk_eq_zero_iff, RelativeChainInt.mk_eq_zero_iff] at hx
  rw [show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) n) = RelativeChainInt.mk (U ∩ V) n c from rfl,
    RelativeChainInt.mk_eq_zero_iff, ← SingularExcisionIsoInt.subspaceChainsInt_inf]
  exact Submodule.mem_inf.2 hx

/-! ### The chain-level union submodule and the relative MV sum (third SES term) -/

/-- The **small (`U`-or-`V`) chains** `C_n(U) + C_n(V) ⊆ C_n(M)`. -/
noncomputable def mvUnionChainsInt (U V : Set ↑M) (n : ℕ) : Submodule ℤ (SingularChainInt M n) :=
  subspaceChainsInt U n + subspaceChainsInt V n

theorem subspaceChainsInt_le_mvUnionChainsInt_left (U V : Set ↑M) (n : ℕ) :
    subspaceChainsInt U n ≤ mvUnionChainsInt U V n := le_sup_left

theorem subspaceChainsInt_le_mvUnionChainsInt_right (U V : Set ↑M) (n : ℕ) :
    subspaceChainsInt V n ≤ mvUnionChainsInt U V n := le_sup_right

/-- The factor map `C(M,U) = C(M)/C(U) → C(M)/(C(U)+C(V))`. -/
noncomputable def relMvFactorLInt (U V : Set ↑M) (n : ℕ) :
    RelativeChainInt U n →ₗ[ℤ] SingularChainInt M n ⧸ mvUnionChainsInt U V n :=
  Submodule.mapQ (subspaceChainsInt U n) (mvUnionChainsInt U V n) LinearMap.id
    (by rw [Submodule.comap_id]; exact subspaceChainsInt_le_mvUnionChainsInt_left U V n)

/-- The factor map `C(M,V) = C(M)/C(V) → C(M)/(C(U)+C(V))`. -/
noncomputable def relMvFactorRInt (U V : Set ↑M) (n : ℕ) :
    RelativeChainInt V n →ₗ[ℤ] SingularChainInt M n ⧸ mvUnionChainsInt U V n :=
  Submodule.mapQ (subspaceChainsInt V n) (mvUnionChainsInt U V n) LinearMap.id
    (by rw [Submodule.comap_id]; exact subspaceChainsInt_le_mvUnionChainsInt_right U V n)

@[simp] theorem relMvFactorLInt_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) :
    relMvFactorLInt U V n (RelativeChainInt.mk U n c) = Submodule.Quotient.mk c :=
  rfl

@[simp] theorem relMvFactorRInt_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) :
    relMvFactorRInt U V n (RelativeChainInt.mk V n c) = Submodule.Quotient.mk c :=
  rfl

/-- The chain-level relative MV **sum** `C(M,U) × C(M,V) → C(M)/(C(U)+C(V))`, `([a],[b]) ↦ [a−b]`
(a **difference** over ℤ). -/
noncomputable def relMvChainSumInt (U V : Set ↑M) (n : ℕ) :
    RelativeChainInt U n × RelativeChainInt V n →ₗ[ℤ] SingularChainInt M n ⧸ mvUnionChainsInt U V n :=
  (relMvFactorLInt U V n).coprod (-relMvFactorRInt U V n)

@[simp] theorem relMvChainSumInt_mk (U V : Set ↑M) (n : ℕ) (a b : SingularChainInt M n) :
    relMvChainSumInt U V n (RelativeChainInt.mk U n a, RelativeChainInt.mk V n b)
      = Submodule.Quotient.mk (a - b) := by
  rw [relMvChainSumInt, LinearMap.coprod_apply, LinearMap.neg_apply, relMvFactorLInt_mk,
    relMvFactorRInt_mk, sub_eq_add_neg, ← Submodule.Quotient.mk_neg, ← Submodule.Quotient.mk_add]

/-- **Relative MV chain SES — chain-complex condition** `Σ ∘ Δ = 0`. -/
theorem relMvChainSumInt_relMvChainDiagInt (U V : Set ↑M) (n : ℕ) (w : RelativeChainInt (U ∩ V) n) :
    relMvChainSumInt U V n (relMvChainDiagInt U V n w) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) n) = RelativeChainInt.mk (U ∩ V) n c from rfl,
    relMvChainDiagInt_mk, relMvChainSumInt_mk, sub_self]
  exact Submodule.Quotient.mk_zero _

/-- **Relative MV chain SES — `Σ` is surjective**. -/
theorem relMvChainSumInt_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relMvChainSumInt U V n) := by
  intro q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨(RelativeChainInt.mk U n c, 0), ?_⟩
  rw [relMvChainSumInt, LinearMap.coprod_apply, map_zero, add_zero, relMvFactorLInt_mk]

/-- **Relative MV chain SES — exactness in the middle**: `ker Σ = range Δ`. `[a−b] = 0` means
`a − b = u + v` with `u ∈ C(U)`, `v ∈ C(V)`; then `c := a − u = b + v` satisfies `Δ[c] = ([a],[b])`. -/
theorem relMvChain_exactInt (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvChainDiagInt U V n) (relMvChainSumInt U V n) := by
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (subspaceChainsInt U n) p.1
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (subspaceChainsInt V n) p.2
    have hpe : p = (RelativeChainInt.mk U n a, RelativeChainInt.mk V n b) := Prod.ext ha.symm hb.symm
    subst hpe
    rw [relMvChainSumInt_mk, Submodule.Quotient.mk_eq_zero] at hp
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hp
    refine ⟨RelativeChainInt.mk (U ∩ V) n (a - u), ?_⟩
    rw [relMvChainDiagInt_mk]
    refine Prod.ext ?_ ?_
    · rw [show RelativeChainInt.mk U n (a - u) = RelativeChainInt.mk U n a - RelativeChainInt.mk U n u from rfl,
        (RelativeChainInt.mk_eq_zero_iff U n u).2 hu, sub_zero]
    · have hc : a - u = b + v := by
        have h2 : a - b = u + v := huv.symm
        rw [sub_eq_iff_eq_add] at h2 ⊢; rw [h2]; abel
      rw [hc, show RelativeChainInt.mk V n (b + v) = RelativeChainInt.mk V n b + RelativeChainInt.mk V n v from rfl,
        (RelativeChainInt.mk_eq_zero_iff V n v).2 hv, add_zero]
  · rintro ⟨w, rfl⟩
    exact relMvChainSumInt_relMvChainDiagInt U V n w

/-! ## §3. The third-term complex `Q = C(M)/(C(U)+C(V))` and its homology -/

/-- The boundary preserves `C(U)+C(V)` (each summand is boundary-stable). -/
theorem chainBoundary_mem_mvUnionChainsInt (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M (n + 1))
    (hc : c ∈ mvUnionChainsInt U V (n + 1)) : chainBoundary M n c ∈ mvUnionChainsInt U V n := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hc
  rw [map_add]
  exact Submodule.add_mem_sup (chainBoundary_mem_subspaceChainsInt U n u hu)
    (chainBoundary_mem_subspaceChainsInt V n v hv)

/-- The **third-term chains** `Q_n = C_n(M) / (C_n(U)+C_n(V))`. -/
abbrev QChainInt (U V : Set ↑M) (n : ℕ) : Type := SingularChainInt M n ⧸ mvUnionChainsInt U V n

/-- The `Q`-class of an absolute chain. -/
noncomputable def QChainInt.mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) : QChainInt U V n :=
  Submodule.Quotient.mk c

theorem QChainInt.mk_eq_zero_iff (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) :
    QChainInt.mk U V n c = 0 ↔ c ∈ mvUnionChainsInt U V n :=
  Submodule.Quotient.mk_eq_zero _

/-- The induced boundary `∂ : Q_{n+1} → Q_n`. -/
noncomputable def qBoundaryInt (U V : Set ↑M) (n : ℕ) :
    QChainInt U V (n + 1) →ₗ[ℤ] QChainInt U V n :=
  Submodule.mapQ (mvUnionChainsInt U V (n + 1)) (mvUnionChainsInt U V n) (chainBoundary M n)
    (fun c hc => chainBoundary_mem_mvUnionChainsInt U V n c hc)

theorem qBoundaryInt_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M (n + 1)) :
    qBoundaryInt U V n (QChainInt.mk U V (n + 1) c) = QChainInt.mk U V n (chainBoundary M n c) := rfl

theorem qBoundaryInt_comp_qBoundaryInt (U V : Set ↑M) (n : ℕ) :
    (qBoundaryInt U V n).comp (qBoundaryInt U V (n + 1)) = 0 := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  show qBoundaryInt U V n (qBoundaryInt U V (n + 1) (QChainInt.mk U V (n + 1 + 1) c)) = 0
  rw [qBoundaryInt_mk, qBoundaryInt_mk,
    show chainBoundary M n (chainBoundary M (n + 1) c) = 0 by
      rw [← LinearMap.comp_apply, chainBoundary_comp_chainBoundary, LinearMap.zero_apply]]
  rfl

/-- The `Q`-**cycles** (`⊤` in degree 0; `ker ∂` otherwise). -/
noncomputable def qCyclesInt (U V : Set ↑M) (n : ℕ) : Submodule ℤ (QChainInt U V n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (qBoundaryInt U V m)

/-- The `Q`-**boundaries** `im ∂`. -/
noncomputable def qBoundariesInt (U V : Set ↑M) (n : ℕ) : Submodule ℤ (QChainInt U V n) :=
  LinearMap.range (qBoundaryInt U V n)

theorem qBoundariesInt_le_qCyclesInt (U V : Set ↑M) (n : ℕ) :
    qBoundariesInt U V n ≤ qCyclesInt U V n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (qBoundaryInt U V (m + 1)) ≤ LinearMap.ker (qBoundaryInt U V m)
    rw [LinearMap.range_le_ker_iff]
    exact qBoundaryInt_comp_qBoundaryInt U V m

/-- **The third-term homology** `QHomologyInt n = Hₙ(C(M)/(C(U)+C(V)))`. -/
def QHomologyInt (U V : Set ↑M) (n : ℕ) : Type :=
  (qCyclesInt U V n) ⧸ (qBoundariesInt U V n).submoduleOf (qCyclesInt U V n)

noncomputable instance (U V : Set ↑M) (n : ℕ) : AddCommGroup (QHomologyInt U V n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (U V : Set ↑M) (n : ℕ) : Module ℤ (QHomologyInt U V n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The `Q`-homology class of a `Q`-cycle. -/
noncomputable def QHomologyInt.mk (U V : Set ↑M) (n : ℕ) (z : qCyclesInt U V n) : QHomologyInt U V n :=
  Submodule.Quotient.mk z

theorem QHomologyInt.mk_eq_zero_iff (U V : Set ↑M) (n : ℕ) (z : qCyclesInt U V n) :
    QHomologyInt.mk U V n z = 0 ↔ (z : QChainInt U V n) ∈ qBoundariesInt U V n := by
  constructor
  · intro h
    have h2 : z ∈ (qBoundariesInt U V n).submoduleOf (qCyclesInt U V n) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

/-! ## §4. The chain-map property `Σ ∘ ∂_B = ∂_Q ∘ Σ` and the homology-level sum `Σ_*` -/

/-- The boundary on the middle term `B = C(M,U) × C(M,V)` (`∂ ⊕ ∂`). -/
noncomputable def bBoundaryInt (U V : Set ↑M) (n : ℕ) :
    RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1) →ₗ[ℤ]
      RelativeChainInt U n × RelativeChainInt V n :=
  (relBoundaryInt U n).prodMap (relBoundaryInt V n)

theorem bBoundaryInt_mk (U V : Set ↑M) (n : ℕ) (a b : SingularChainInt M (n + 1)) :
    bBoundaryInt U V n (RelativeChainInt.mk U (n + 1) a, RelativeChainInt.mk V (n + 1) b)
      = (RelativeChainInt.mk U n (chainBoundary M n a), RelativeChainInt.mk V n (chainBoundary M n b)) := by
  rw [bBoundaryInt, LinearMap.prodMap_apply, relBoundaryInt_mk, relBoundaryInt_mk]

/-- `Σ` is a **chain map**: `Σ ∘ ∂_B = ∂_Q ∘ Σ`. -/
theorem relMvChainSumInt_chainMap (U V : Set ↑M) (n : ℕ)
    (p : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)) :
    relMvChainSumInt U V n (bBoundaryInt U V n p) = qBoundaryInt U V n (relMvChainSumInt U V (n + 1) p) := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show relMvChainSumInt U V n
      (bBoundaryInt U V n (RelativeChainInt.mk U (n + 1) a, RelativeChainInt.mk V (n + 1) b))
    = qBoundaryInt U V n
      (relMvChainSumInt U V (n + 1) (RelativeChainInt.mk U (n + 1) a, RelativeChainInt.mk V (n + 1) b))
  rw [bBoundaryInt_mk, relMvChainSumInt_mk, relMvChainSumInt_mk]
  show Submodule.Quotient.mk (chainBoundary M n a - chainBoundary M n b)
      = Submodule.Quotient.mk (chainBoundary M n (a - b))
  rw [map_sub]

theorem relMvFactorLInt_chainMap (U V : Set ↑M) (n : ℕ) (x : RelativeChainInt U (n + 1)) :
    relMvFactorLInt U V n (relBoundaryInt U n x) = qBoundaryInt U V n (relMvFactorLInt U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChainInt U (n + 1)) = RelativeChainInt.mk U (n + 1) c from rfl,
    relBoundaryInt_mk, relMvFactorLInt_mk, relMvFactorLInt_mk]
  rfl

theorem relMvFactorRInt_chainMap (U V : Set ↑M) (n : ℕ) (x : RelativeChainInt V (n + 1)) :
    relMvFactorRInt U V n (relBoundaryInt V n x) = qBoundaryInt U V n (relMvFactorRInt U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChainInt V (n + 1)) = RelativeChainInt.mk V (n + 1) c from rfl,
    relBoundaryInt_mk, relMvFactorRInt_mk, relMvFactorRInt_mk]
  rfl

theorem relMvFactorLInt_mem_qCyclesInt (U V : Set ↑M) (n : ℕ) (z : RelativeChainInt U n)
    (hz : z ∈ relCyclesInt U n) : relMvFactorLInt U V n z ∈ qCyclesInt U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : relBoundaryInt U m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : qBoundaryInt U V m (relMvFactorLInt U V (m + 1) z) = 0 := by
      rw [← relMvFactorLInt_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem relMvFactorRInt_mem_qCyclesInt (U V : Set ↑M) (n : ℕ) (z : RelativeChainInt V n)
    (hz : z ∈ relCyclesInt V n) : relMvFactorRInt U V n z ∈ qCyclesInt U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : relBoundaryInt V m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : qBoundaryInt U V m (relMvFactorRInt U V (m + 1) z) = 0 := by
      rw [← relMvFactorRInt_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem relMvFactorLInt_mem_qBoundariesInt (U V : Set ↑M) (n : ℕ) (z : RelativeChainInt U n)
    (hz : z ∈ relBoundariesInt U n) : relMvFactorLInt U V n z ∈ qBoundariesInt U V n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMvFactorLInt U V (n + 1) w, (relMvFactorLInt_chainMap U V n w).symm⟩

theorem relMvFactorRInt_mem_qBoundariesInt (U V : Set ↑M) (n : ℕ) (z : RelativeChainInt V n)
    (hz : z ∈ relBoundariesInt V n) : relMvFactorRInt U V n z ∈ qBoundariesInt U V n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMvFactorRInt U V (n + 1) w, (relMvFactorRInt_chainMap U V n w).symm⟩

/-- The induced map `Hₙ(M,U) → Hₙ(Q)` of the factor chain map `relMvFactorLInt`. -/
noncomputable def relFactorLHomInt (U V : Set ↑M) (n : ℕ) :
    RelHomologyInt U n →ₗ[ℤ] QHomologyInt U V n :=
  Submodule.mapQ _ _ (LinearMap.restrict (relMvFactorLInt U V n)
      (fun z hz => relMvFactorLInt_mem_qCyclesInt U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relMvFactorLInt_mem_qBoundariesInt U V n _ hz)

/-- The induced map `Hₙ(M,V) → Hₙ(Q)` of the factor chain map `relMvFactorRInt`. -/
noncomputable def relFactorRHomInt (U V : Set ↑M) (n : ℕ) :
    RelHomologyInt V n →ₗ[ℤ] QHomologyInt U V n :=
  Submodule.mapQ _ _ (LinearMap.restrict (relMvFactorRInt U V n)
      (fun z hz => relMvFactorRInt_mem_qCyclesInt U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relMvFactorRInt_mem_qBoundariesInt U V n _ hz)

theorem relFactorLHomInt_mk (U V : Set ↑M) (n : ℕ) (z : relCyclesInt U n) :
    relFactorLHomInt U V n (RelHomologyInt.mk U n z)
      = QHomologyInt.mk U V n ⟨relMvFactorLInt U V n z, relMvFactorLInt_mem_qCyclesInt U V n z z.2⟩ := rfl

theorem relFactorRHomInt_mk (U V : Set ↑M) (n : ℕ) (z : relCyclesInt V n) :
    relFactorRHomInt U V n (RelHomologyInt.mk V n z)
      = QHomologyInt.mk U V n ⟨relMvFactorRInt U V n z, relMvFactorRInt_mem_qCyclesInt U V n z z.2⟩ := rfl

/-- **The homology-level relative MV sum** `Σ_* : Hₙ(M,U) × Hₙ(M,V) → Hₙ(Q)`, `([a],[b]) ↦ [a−b]`
(a **difference** over ℤ). -/
noncomputable def relMvHomSumQInt (U V : Set ↑M) (n : ℕ) :
    RelHomologyInt U n × RelHomologyInt V n →ₗ[ℤ] QHomologyInt U V n :=
  (relFactorLHomInt U V n).coprod (-relFactorRHomInt U V n)

/-! ## §5. Q-form middle exactness `range Δ_* = ker Σ_*` -/

/-- The homology inclusion `relInclInt` on the class of a relative cycle. -/
theorem relInclInt_mk {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) (z : relCyclesInt S n) :
    relInclInt h n (RelHomologyInt.mk S n z)
      = RelHomologyInt.mk T n (relCyclesMapInt (ContinuousMap.id ↑M) (fun _ hx => h hx) n z) := by
  rw [relInclInt]
  exact RelHomologyInt.map_mk _ _ n z

/-- The image of `mk_S c` under `relMapChainInt id` is `mk_T c`. -/
theorem relMapChainInt_id_mk {S T : Set ↑M} (h : Set.MapsTo (ContinuousMap.id ↑M) S T) (n : ℕ)
    (c : SingularChainInt M n) :
    relMapChainInt (ContinuousMap.id ↑M) h n (RelativeChainInt.mk S n c) = RelativeChainInt.mk T n c := by
  rw [relMapChainInt_mk, SingularFunctorialityInt.mapChainInt_id]

/-- The `U`-component of `relMvHomDiagInt` on `[mk c]` is `[mk_U c]`. -/
theorem relMvHomDiagInt_fst_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n)
    (hc : RelativeChainInt.mk (U ∩ V) n c ∈ relCyclesInt (U ∩ V) n)
    (hcU : RelativeChainInt.mk U n c ∈ relCyclesInt U n) :
    (relMvHomDiagInt U V n (RelHomologyInt.mk (U ∩ V) n ⟨_, hc⟩)).1
      = RelHomologyInt.mk U n ⟨RelativeChainInt.mk U n c, hcU⟩ := by
  show relInclInt Set.inter_subset_left n (RelHomologyInt.mk (U ∩ V) n ⟨_, hc⟩) = _
  rw [relInclInt_mk]
  refine congrArg (RelHomologyInt.mk U n) (Subtype.ext ?_)
  rw [relCyclesMapInt_coe]
  show relMapChainInt (ContinuousMap.id ↑M) _ n (RelativeChainInt.mk (U ∩ V) n c) = RelativeChainInt.mk U n c
  rw [relMapChainInt_mk, SingularFunctorialityInt.mapChainInt_id]

/-- The `V`-component of `relMvHomDiagInt` on `[mk c]` is `[mk_V c]`. -/
theorem relMvHomDiagInt_snd_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n)
    (hc : RelativeChainInt.mk (U ∩ V) n c ∈ relCyclesInt (U ∩ V) n)
    (hcV : RelativeChainInt.mk V n c ∈ relCyclesInt V n) :
    (relMvHomDiagInt U V n (RelHomologyInt.mk (U ∩ V) n ⟨_, hc⟩)).2
      = RelHomologyInt.mk V n ⟨RelativeChainInt.mk V n c, hcV⟩ := by
  show relInclInt Set.inter_subset_right n (RelHomologyInt.mk (U ∩ V) n ⟨_, hc⟩) = _
  rw [relInclInt_mk]
  refine congrArg (RelHomologyInt.mk V n) (Subtype.ext ?_)
  rw [relCyclesMapInt_coe]
  show relMapChainInt (ContinuousMap.id ↑M) _ n (RelativeChainInt.mk (U ∩ V) n c) = RelativeChainInt.mk V n c
  rw [relMapChainInt_mk, SingularFunctorialityInt.mapChainInt_id]

/-- Two relative cycles differing by a relative boundary have the same homology class. -/
theorem relHomologyInt_mk_eq_of {S : Set ↑M} (n : ℕ) (w z : relCyclesInt S n)
    (h : (w : RelativeChainInt S n) - (z : RelativeChainInt S n) ∈ relBoundariesInt S n) :
    RelHomologyInt.mk S n w = RelHomologyInt.mk S n z := by
  show Submodule.Quotient.mk w = Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    AddSubgroupClass.coe_sub]
  exact h

/-- `Σ(↑a, ↑b)` (the difference `a − b`) is a `Q`-cycle when `a, b` are relative cycles. -/
theorem relMvChainSumInt_pair_mem_qCyclesInt (U V : Set ↑M) (n : ℕ) (a : relCyclesInt U n)
    (b : relCyclesInt V n) :
    relMvChainSumInt U V n ((a : RelativeChainInt U n), (b : RelativeChainInt V n)) ∈ qCyclesInt U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have ha : relBoundaryInt U m (a : RelativeChainInt U (m + 1)) = 0 := LinearMap.mem_ker.mp a.2
    have hb : relBoundaryInt V m (b : RelativeChainInt V (m + 1)) = 0 := LinearMap.mem_ker.mp b.2
    have h0 : qBoundaryInt U V m (relMvChainSumInt U V (m + 1) ((a : _), (b : _))) = 0 := by
      rw [← relMvChainSumInt_chainMap, bBoundaryInt, LinearMap.prodMap_apply, ha, hb]
      exact map_zero _
    exact LinearMap.mem_ker.mpr h0

/-- `Σ_*` on a class of cycles is `[Σ(↑a, ↑b)]`. -/
theorem relMvHomSumQInt_mk (U V : Set ↑M) (n : ℕ) (a : relCyclesInt U n) (b : relCyclesInt V n) :
    relMvHomSumQInt U V n (RelHomologyInt.mk U n a, RelHomologyInt.mk V n b)
      = QHomologyInt.mk U V n ⟨relMvChainSumInt U V n ((a : _), (b : _)),
          relMvChainSumInt_pair_mem_qCyclesInt U V n a b⟩ := by
  rw [relMvHomSumQInt, LinearMap.coprod_apply, LinearMap.neg_apply, relFactorLHomInt_mk,
    relFactorRHomInt_mk]
  show QHomologyInt.mk U V n (⟨relMvFactorLInt U V n (a : _), _⟩ + -⟨relMvFactorRInt U V n (b : _), _⟩)
      = QHomologyInt.mk U V n ⟨relMvChainSumInt U V n ((a : _), (b : _)), _⟩
  refine congrArg (QHomologyInt.mk U V n) (Subtype.ext ?_)
  show relMvFactorLInt U V n (a : _) + -relMvFactorRInt U V n (b : _)
      = relMvChainSumInt U V n ((a : _), (b : _))
  rw [relMvChainSumInt, LinearMap.coprod_apply, LinearMap.neg_apply]

/-- **Q-form relative MV exactness at `Hₙ(M,U) ⊕ Hₙ(M,V)`**: `range Δ_* = ker Σ_*` (the snake middle,
`Q`-form). Two relative cycles whose difference is a `Q`-boundary come from a single `(U∩V)`-class. -/
theorem relMv_exact_middleInt (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvHomDiagInt U V n) (relMvHomSumQInt U V n) := by
  intro p
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  constructor
  · intro hp
    rw [show relMvHomSumQInt U V n (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
        = QHomologyInt.mk U V n ⟨relMvChainSumInt U V n ((a : _), (b : _)),
            relMvChainSumInt_pair_mem_qCyclesInt U V n a b⟩ from relMvHomSumQInt_mk U V n a b,
      QHomologyInt.mk_eq_zero_iff] at hp
    obtain ⟨δq, hδq⟩ := hp
    obtain ⟨b'', hb''⟩ := relMvChainSumInt_surjective U V (n + 1) δq
    have hker : relMvChainSumInt U V n
        (((a : RelativeChainInt U n), (b : RelativeChainInt V n)) - bBoundaryInt U V n b'') = 0 := by
      rw [map_sub, relMvChainSumInt_chainMap, hb'', hδq, sub_self]
    obtain ⟨w, hw⟩ := (relMvChain_exactInt U V n _).mp hker
    have hfst : relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n w
        = (a : RelativeChainInt U n) - relBoundaryInt U n (b'').1 := by
      have h := congrArg Prod.fst hw
      simpa only [relMvChainDiagInt, LinearMap.prod_apply, Prod.fst_sub, bBoundaryInt,
        LinearMap.prodMap_apply] using h
    have hsnd : relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n w
        = (b : RelativeChainInt V n) - relBoundaryInt V n (b'').2 := by
      have h := congrArg Prod.snd hw
      simpa only [relMvChainDiagInt, LinearMap.prod_apply, Prod.snd_sub, bBoundaryInt,
        LinearMap.prodMap_apply] using h
    have hw_cyc : w ∈ relCyclesInt (U ∩ V) n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
        rw [show relCyclesInt (U ∩ V) (m + 1) = LinearMap.ker (relBoundaryInt (U ∩ V) m) from rfl,
          LinearMap.mem_ker]
        apply relMvChainDiagInt_injective U V m
        rw [map_zero]
        have hchainmap : relMvChainDiagInt U V m (relBoundaryInt (U ∩ V) m w)
            = bBoundaryInt U V m (relMvChainDiagInt U V (m + 1) w) := by
          obtain ⟨cc, rfl⟩ := Submodule.Quotient.mk_surjective _ w
          rw [show (Submodule.Quotient.mk cc : RelativeChainInt (U ∩ V) (m + 1))
                = RelativeChainInt.mk (U ∩ V) (m + 1) cc from rfl,
            relBoundaryInt_mk, relMvChainDiagInt_mk, relMvChainDiagInt_mk, bBoundaryInt_mk]
        rw [hchainmap, hw, map_sub, bBoundaryInt, bBoundaryInt, LinearMap.prodMap_apply,
          LinearMap.prodMap_apply, LinearMap.prodMap_apply]
        have hbb : relBoundaryInt U m ((relBoundaryInt U (m + 1)) (b'').1) = 0 := by
          rw [← LinearMap.comp_apply, relBoundaryInt_comp_relBoundaryInt, LinearMap.zero_apply]
        have hbb2 : relBoundaryInt V m ((relBoundaryInt V (m + 1)) (b'').2) = 0 := by
          rw [← LinearMap.comp_apply, relBoundaryInt_comp_relBoundaryInt, LinearMap.zero_apply]
        rw [LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
        simp only [Prod.mk_sub_mk, hbb, hbb2, sub_zero]
        rfl
    obtain ⟨wc, hwc⟩ := Submodule.Quotient.mk_surjective _ w
    have hwcEqL : RelativeChainInt.mk U n wc
        = relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n w := by
      rw [← hwc, show (Submodule.Quotient.mk wc : RelativeChainInt (U ∩ V) n)
          = RelativeChainInt.mk (U ∩ V) n wc from rfl, relMapChainInt_id_mk]
    have hwcEqR : RelativeChainInt.mk V n wc
        = relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n w := by
      rw [← hwc, show (Submodule.Quotient.mk wc : RelativeChainInt (U ∩ V) n)
          = RelativeChainInt.mk (U ∩ V) n wc from rfl, relMapChainInt_id_mk]
    have hwU : RelativeChainInt.mk U n wc ∈ relCyclesInt U n := by
      rw [hwcEqL]; exact relMapChainInt_mem_relCyclesInt _ _ n w hw_cyc
    have hwV : RelativeChainInt.mk V n wc ∈ relCyclesInt V n := by
      rw [hwcEqR]; exact relMapChainInt_mem_relCyclesInt _ _ n w hw_cyc
    refine ⟨RelHomologyInt.mk (U ∩ V) n ⟨w, hw_cyc⟩, ?_⟩
    have hzc : (⟨w, hw_cyc⟩ : relCyclesInt (U ∩ V) n)
        = ⟨RelativeChainInt.mk (U ∩ V) n wc,
            by rw [show RelativeChainInt.mk (U ∩ V) n wc = w from hwc]; exact hw_cyc⟩ :=
      Subtype.ext hwc.symm
    rw [hzc]
    refine Prod.ext ?_ ?_
    · rw [relMvHomDiagInt_fst_mk U V n wc _ hwU]
      refine relHomologyInt_mk_eq_of n _ a ?_
      show RelativeChainInt.mk U n wc - (a : RelativeChainInt U n) ∈ relBoundariesInt U n
      rw [hwcEqL, hfst, sub_sub_cancel_left]
      exact ⟨-(b'').1, by rw [map_neg]⟩
    · rw [relMvHomDiagInt_snd_mk U V n wc _ hwV]
      refine relHomologyInt_mk_eq_of n _ b ?_
      show RelativeChainInt.mk V n wc - (b : RelativeChainInt V n) ∈ relBoundariesInt V n
      rw [hwcEqR, hsnd, sub_sub_cancel_left]
      exact ⟨-(b'').2, by rw [map_neg]⟩
  · rintro ⟨w, hw⟩
    rw [← hw]
    obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChainInt (U ∩ V) n)
    have hcU : RelativeChainInt.mk U n c ∈ relCyclesInt U n := by
      rw [show RelativeChainInt.mk U n c
          = relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n
              (zc : RelativeChainInt (U ∩ V) n) by
        rw [← hc, show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) n)
            = RelativeChainInt.mk (U ∩ V) n c from rfl, relMapChainInt_id_mk]]
      exact relMapChainInt_mem_relCyclesInt _ _ n _ zc.2
    have hcV : RelativeChainInt.mk V n c ∈ relCyclesInt V n := by
      rw [show RelativeChainInt.mk V n c
          = relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n
              (zc : RelativeChainInt (U ∩ V) n) by
        rw [← hc, show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) n)
            = RelativeChainInt.mk (U ∩ V) n c from rfl, relMapChainInt_id_mk]]
      exact relMapChainInt_mem_relCyclesInt _ _ n _ zc.2
    have hzc : (zc : relCyclesInt (U ∩ V) n)
        = ⟨RelativeChainInt.mk (U ∩ V) n c,
            by rw [show RelativeChainInt.mk (U ∩ V) n c = (zc : RelativeChainInt (U ∩ V) n) from hc]
               exact zc.2⟩ := Subtype.ext hc.symm
    rw [show (Submodule.Quotient.mk zc : RelHomologyInt (U ∩ V) n)
        = RelHomologyInt.mk (U ∩ V) n zc from rfl, hzc,
      show relMvHomDiagInt U V n (RelHomologyInt.mk (U ∩ V) n ⟨RelativeChainInt.mk (U ∩ V) n c, _⟩)
        = (RelHomologyInt.mk U n ⟨RelativeChainInt.mk U n c, hcU⟩,
           RelHomologyInt.mk V n ⟨RelativeChainInt.mk V n c, hcV⟩) from
      Prod.ext (relMvHomDiagInt_fst_mk U V n c _ hcU) (relMvHomDiagInt_snd_mk U V n c _ hcV),
      relMvHomSumQInt_mk, QHomologyInt.mk_eq_zero_iff]
    show relMvChainSumInt U V n (RelativeChainInt.mk U n c, RelativeChainInt.mk V n c) ∈ qBoundariesInt U V n
    rw [relMvChainSumInt_mk, sub_self]
    exact Submodule.zero_mem _

/-! ## §6. The small-chains projection `π : Q → C(M, U∪V)` and its iso `ι : Hₙ(Q) ≅ Hₙ(M, U∪V)`

`C(U)+C(V) ⊆ C(U∪V)` gives a projection `π : Q → C(M, U∪V)`, inducing `ι := π_*`. By the integral
small-chains theorem `ι` is an isomorphism (open `U, V`), so the Q-form middle exactness transports to
the textbook `Hₙ(M, U∪V)` codomain. -/

open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcision (IsSubordinate)

/-- Monotonicity of the integral subspace chains under set inclusion. -/
theorem subspaceChainsInt_mono {A B : Set ↑M} (h : A ⊆ B) (n : ℕ) :
    subspaceChainsInt A n ≤ subspaceChainsInt B n := fun _c hc =>
  SingularExcisionIsoInt.mem_subspaceChainsInt_of_support
    (fun _τ hτ => (SingularExcisionIsoInt.range_of_mem_subspaceChainsInt hc hτ).trans h)

theorem mvUnionChainsInt_le_subspaceChainsInt_union (U V : Set ↑M) (n : ℕ) :
    mvUnionChainsInt U V n ≤ subspaceChainsInt (U ∪ V) n :=
  sup_le (subspaceChainsInt_mono Set.subset_union_left n)
    (subspaceChainsInt_mono Set.subset_union_right n)

/-- The projection `π : Q = C(M)/(C(U)+C(V)) → C(M, U∪V) = C(M)/C(U∪V)`. -/
noncomputable def piMapInt (U V : Set ↑M) (n : ℕ) :
    QChainInt U V n →ₗ[ℤ] RelativeChainInt (U ∪ V) n :=
  Submodule.mapQ (mvUnionChainsInt U V n) (subspaceChainsInt (U ∪ V) n) LinearMap.id
    (by rw [Submodule.comap_id]; exact mvUnionChainsInt_le_subspaceChainsInt_union U V n)

theorem piMapInt_mk (U V : Set ↑M) (n : ℕ) (c : SingularChainInt M n) :
    piMapInt U V n (QChainInt.mk U V n c) = RelativeChainInt.mk (U ∪ V) n c := rfl

/-- `π` is a **chain map**: `π ∘ ∂_Q = ∂_{M,U∪V} ∘ π`. -/
theorem piMapInt_chainMap (U V : Set ↑M) (n : ℕ) (x : QChainInt U V (n + 1)) :
    piMapInt U V n (qBoundaryInt U V n x) = relBoundaryInt (U ∪ V) n (piMapInt U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show piMapInt U V n (qBoundaryInt U V n (QChainInt.mk U V (n + 1) c))
      = relBoundaryInt (U ∪ V) n (piMapInt U V (n + 1) (QChainInt.mk U V (n + 1) c))
  rw [qBoundaryInt_mk, piMapInt_mk, piMapInt_mk, relBoundaryInt_mk]

theorem piMapInt_mem_relCyclesInt (U V : Set ↑M) (n : ℕ) (z : QChainInt U V n)
    (hz : z ∈ qCyclesInt U V n) : piMapInt U V n z ∈ relCyclesInt (U ∪ V) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : qBoundaryInt U V m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : relBoundaryInt (U ∪ V) m (piMapInt U V (m + 1) z) = 0 := by
      rw [← piMapInt_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem piMapInt_mem_relBoundariesInt (U V : Set ↑M) (n : ℕ) (z : QChainInt U V n)
    (hz : z ∈ qBoundariesInt U V n) : piMapInt U V n z ∈ relBoundariesInt (U ∪ V) n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨piMapInt U V (n + 1) w, (piMapInt_chainMap U V n w).symm⟩

/-- **The small-chains map** `ι : Hₙ(Q) → Hₙ(M, U∪V)`, induced by `π`. -/
noncomputable def iotaInt (U V : Set ↑M) (n : ℕ) :
    QHomologyInt U V n →ₗ[ℤ] RelHomologyInt (U ∪ V) n :=
  Submodule.mapQ _ _ (LinearMap.restrict (piMapInt U V n)
      (fun z hz => piMapInt_mem_relCyclesInt U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact piMapInt_mem_relBoundariesInt U V n _ hz)

theorem iotaInt_mk (U V : Set ↑M) (n : ℕ) (z : qCyclesInt U V n) :
    iotaInt U V n (QHomologyInt.mk U V n z)
      = RelHomologyInt.mk (U ∪ V) n ⟨piMapInt U V n z, piMapInt_mem_relCyclesInt U V n z z.2⟩ := rfl

/-! ### The small-chains transport (core of the `ι` isomorphism) -/

/-- Pushing a `{U', V'}`-small chain of `sub(U∪V)` into `M` lands in `C(U)+C(V)`: a simplex of
`sub(U∪V)` subordinate to `U' = val⁻¹ U` includes to a simplex of `M` with image in `U`. -/
theorem chainIncl_mem_mvUnion_of_smallInt (U V : Set ↑M) (n : ℕ)
    (e : SingularChainInt (sub (U ∪ V)) n)
    (he : e ∈ smallChainsInt ({Subtype.val ⁻¹' U, Subtype.val ⁻¹' V} :
      Set (Set ↥(U ∪ V))) n) :
    chainIncl (U ∪ V) n e ∈ mvUnionChainsInt U V n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ he
  · rintro _ ⟨τ', ⟨W, hW, hsub⟩, rfl⟩
    rw [chainIncl_single]
    rcases hW with rfl | rfl
    · refine Submodule.mem_sup_left (single_mem_subspaceChainsInt_of_subordinate ?_)
      rw [SingularExcision.toSSetObjEquiv_simplexIncl]
      rintro _ ⟨t, rfl⟩
      exact hsub ⟨t, rfl⟩
    · refine Submodule.mem_sup_right (single_mem_subspaceChainsInt_of_subordinate ?_)
      rw [SingularExcision.toSSetObjEquiv_simplexIncl]
      rintro _ ⟨t, rfl⟩
      exact hsub ⟨t, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **The small-chains transport core** (integral): a chain in `C(U∪V)` becomes `C(U)+C(V)`-small after
enough subdivisions. The `{U,V}` cover of `U∪V` is global in `sub(U∪V)`, so `exists_iterate_smallChainsInt`
applies there; push back along `chainIncl`. -/
theorem exists_iterate_mvUnionInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (c : SingularChainInt M n) (hc : c ∈ subspaceChainsInt (U ∪ V) n) :
    ∃ m, (⇑(singularSdInt M n))^[m] c ∈ mvUnionChainsInt U V n := by
  obtain ⟨d, rfl⟩ := hc
  have hcov : (⋃ W ∈ ({Subtype.val ⁻¹' U, Subtype.val ⁻¹' V} : Set (Set ↥(U ∪ V))),
      interior W) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    rcases p.2 with hpU | hpV
    · refine Set.mem_biUnion (Set.mem_insert _ _) ?_
      rw [((hU.preimage continuous_subtype_val).interior_eq)]
      exact hpU
    · refine Set.mem_biUnion (Set.mem_insert_of_mem _ rfl) ?_
      rw [((hV.preimage continuous_subtype_val).interior_eq)]
      exact hpV
  obtain ⟨m, hm⟩ := exists_iterate_smallChainsInt hcov d
  have hnat : ∀ (k : ℕ) (d' : SingularChainInt (sub (U ∪ V)) n),
      (⇑(singularSdInt M n))^[k] (chainIncl (U ∪ V) n d')
        = chainIncl (U ∪ V) n ((⇑(singularSdInt (sub (U ∪ V)) n))^[k] d') := by
    intro k
    induction k with
    | zero => intro d'; rfl
    | succ j ih =>
      intro d'
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, singularSdInt_chainIncl]
  refine ⟨m, ?_⟩
  rw [hnat]
  exact chainIncl_mem_mvUnion_of_smallInt U V n _ hm

/-- **`ι` is surjective**: every relative `(U∪V)`-class has a small (`Q`-cycle) representative —
subdivide its boundary into `C(U)+C(V)` (`exists_iterate_mvUnionInt`), then `[c] = [Sdᵐc]`. -/
theorem iotaInt_surjective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Surjective (iotaInt U V n) := by
  intro h
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  cases n with
  | zero =>
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChainInt (U ∪ V) 0)
    refine ⟨QHomologyInt.mk U V 0 ⟨QChainInt.mk U V 0 c', Submodule.mem_top⟩, ?_⟩
    rw [iotaInt_mk]
    refine congrArg (RelHomologyInt.mk (U ∪ V) 0) (Subtype.ext ?_)
    show piMapInt U V 0 (QChainInt.mk U V 0 c') = (zc : RelativeChainInt (U ∪ V) 0)
    rw [piMapInt_mk]; exact hc'
  | succ k =>
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChainInt (U ∪ V) (k + 1))
    have hbdry : chainBoundary M k c' ∈ subspaceChainsInt (U ∪ V) k := by
      have hz := LinearMap.mem_ker.mp zc.2
      rw [← hc', show (Submodule.Quotient.mk c' : RelativeChainInt (U ∪ V) (k + 1))
          = RelativeChainInt.mk (U ∪ V) (k + 1) c' from rfl, relBoundaryInt_mk,
        RelativeChainInt.mk_eq_zero_iff] at hz
      exact hz
    obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt U V hU hV k (chainBoundary M k c') hbdry
    have hqcyc : QChainInt.mk U V (k + 1) ((⇑(singularSdInt M (k + 1)))^[m] c') ∈ qCyclesInt U V (k + 1) := by
      rw [show qCyclesInt U V (k + 1) = LinearMap.ker (qBoundaryInt U V k) from rfl, LinearMap.mem_ker,
        qBoundaryInt_mk, QChainInt.mk_eq_zero_iff, singularSdInt_iterate_chainBoundary]
      exact hm
    refine ⟨QHomologyInt.mk U V (k + 1) ⟨_, hqcyc⟩, ?_⟩
    rw [iotaInt_mk]
    refine relHomologyInt_mk_eq_of (k + 1) _ zc ?_
    show piMapInt U V (k + 1) (QChainInt.mk U V (k + 1) ((⇑(singularSdInt M (k + 1)))^[m] c'))
        - (zc : RelativeChainInt (U ∪ V) (k + 1)) ∈ relBoundariesInt (U ∪ V) (k + 1)
    rw [piMapInt_mk, ← hc',
      show (Submodule.Quotient.mk c' : RelativeChainInt (U ∪ V) (k + 1))
        = RelativeChainInt.mk (U ∪ V) (k + 1) c' from rfl]
    have key := relative_sub_singularSdInt_iterate_mem_relBoundariesInt hbdry m
    have hthis : RelativeChainInt.mk (U ∪ V) (k + 1) ((⇑(singularSdInt M (k + 1)))^[m] c')
        - RelativeChainInt.mk (U ∪ V) (k + 1) c'
        = -(RelativeChainInt.mk (U ∪ V) (k + 1) c'
            - RelativeChainInt.mk (U ∪ V) (k + 1) ((⇑(singularSdInt M (k + 1)))^[m] c')) := by abel
    rw [hthis]
    exact Submodule.neg_mem _ key

/-- **`ι` is injective** (positive degree): a `Q`-cycle whose `(U∪V)`-image is a relative boundary is a
`Q`-boundary — push the boundary witness into `C(U)+C(V)` via the subdivision homotopy. -/
theorem iotaInt_injective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Injective (iotaInt U V (k + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _ (z : QChainInt U V (k + 1))
  rw [show (Submodule.Quotient.mk z : QHomologyInt U V (k + 1)) = QHomologyInt.mk U V (k + 1) z from rfl,
    iotaInt_mk, RelHomologyInt.mk_eq_zero_iff] at hx
  change piMapInt U V (k + 1) (z : QChainInt U V (k + 1)) ∈ relBoundariesInt (U ∪ V) (k + 1) at hx
  rw [show piMapInt U V (k + 1) (z : QChainInt U V (k + 1)) = RelativeChainInt.mk (U ∪ V) (k + 1) zc by
    rw [← hzc]; rfl] at hx
  obtain ⟨W, hW⟩ := hx
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ W
  -- `y := zc − ∂w ∈ C(U∪V)` (from `∂W = mk zc`); its boundary `∂y = ∂zc ∈ C(U)+C(V)` (`z` a Q-cycle).
  set y := zc - chainBoundary M (k + 1) w with hy_def
  have hy_union : y ∈ subspaceChainsInt (U ∪ V) (k + 1) := by
    rw [← RelativeChainInt.mk_eq_zero_iff,
      show RelativeChainInt.mk (U ∪ V) (k + 1) y
        = RelativeChainInt.mk (U ∪ V) (k + 1) zc
          - relBoundaryInt (U ∪ V) (k + 1) (RelativeChainInt.mk (U ∪ V) (k + 2) w) from rfl,
      show RelativeChainInt.mk (U ∪ V) (k + 2) w = W from hw, hW, sub_self]
  have hzc_cyc : chainBoundary M k zc ∈ mvUnionChainsInt U V k := by
    have hq : qBoundaryInt U V k (z : QChainInt U V (k + 1)) = 0 := LinearMap.mem_ker.mp z.2
    rw [← hzc, show (Submodule.Quotient.mk zc : QChainInt U V (k + 1)) = QChainInt.mk U V (k + 1) zc from rfl,
      qBoundaryInt_mk, QChainInt.mk_eq_zero_iff] at hq
    exact hq
  have hdy : chainBoundary M k y ∈ mvUnionChainsInt U V k := by
    rw [hy_def, map_sub,
      show chainBoundary M k (chainBoundary M (k + 1) w) = 0 by
        rw [← LinearMap.comp_apply, chainBoundary_comp_chainBoundary, LinearMap.zero_apply],
      sub_zero]
    exact hzc_cyc
  -- `Sdᵐy ∈ C(U)+C(V)` and `Dₘ(∂y) ∈ C(U)+C(V)`.
  obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt U V hU hV (k + 1) y hy_union
  have hDdy : iterHomotopyInt M k m (chainBoundary M k y) ∈ mvUnionChainsInt U V (k + 1) := by
    rw [show mvUnionChainsInt U V (k + 1) = smallChainsInt ({U, V} : Set (Set ↑M)) (k + 1) from
      (smallChainsInt_two_eq U V (k + 1)).symm]
    refine iterHomotopyInt_mem_smallChainsInt ?_ m
    rw [show smallChainsInt ({U, V} : Set (Set ↑M)) k = mvUnionChainsInt U V k from
      smallChainsInt_two_eq U V k]
    exact hdy
  -- Homotopy `∂(Dₘy) + Dₘ(∂y) = y − Sdᵐy`, so `y − ∂(Dₘy) = Sdᵐy + Dₘ(∂y) ∈ C(U)+C(V)`.
  have hh := iterHomotopyInt_chainHomotopy M m k y
  have hkey : zc - chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y + w)
      ∈ mvUnionChainsInt U V (k + 1) := by
    have h2 : y - chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y)
        = (⇑(singularSdInt M (k + 1)))^[m] y + iterHomotopyInt M k m (chainBoundary M k y) := by
      -- abstract the three homotopy terms to fresh `A, B, S` so `hh : A + B = y - S` closes it by `abel`.
      generalize hA : chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y) = A at hh ⊢
      generalize hB : iterHomotopyInt M k m (chainBoundary M k y) = B at hh ⊢
      generalize hS : (⇑(singularSdInt M (k + 1)))^[m] y = S at hh ⊢
      rw [eq_sub_iff_add_eq] at hh
      rw [← hh]; abel
    rw [map_add,
      show zc - (chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y) + chainBoundary M (k + 1) w)
        = (zc - chainBoundary M (k + 1) w) - chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y) by abel,
      ← hy_def, h2]
    exact Submodule.add_mem _ hm hDdy
  -- Conclude `[z] = 0`: `zc ≡ ∂_Q(mk(Dₘy + w))`.
  rw [show (Submodule.Quotient.mk z : QHomologyInt U V (k + 1)) = QHomologyInt.mk U V (k + 1) z from rfl,
    QHomologyInt.mk_eq_zero_iff, ← hzc]
  refine ⟨QChainInt.mk U V (k + 2) (iterHomotopyInt M (k + 1) m y + w), ?_⟩
  rw [qBoundaryInt_mk]
  show Submodule.Quotient.mk (chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y + w))
      = Submodule.Quotient.mk zc
  rw [Submodule.Quotient.eq]
  show chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y + w) - zc ∈ mvUnionChainsInt U V (k + 1)
  rw [show chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y + w) - zc
      = -(zc - chainBoundary M (k + 1) (iterHomotopyInt M (k + 1) m y + w)) by abel]
  exact Submodule.neg_mem _ hkey

/-- **The small-chains isomorphism** `ι : Hₙ₊₁(Q) ≅ Hₙ₊₁(M, U∪V)` (`U, V` open). Lets the relative MV
middle exactness be stated in its textbook `Hₙ(M, U∪V)` form. -/
noncomputable def iotaEquivInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    QHomologyInt U V (k + 1) ≃ₗ[ℤ] RelHomologyInt (U ∪ V) (k + 1) :=
  LinearEquiv.ofBijective (iotaInt U V (k + 1))
    ⟨iotaInt_injective U V hU hV k, iotaInt_surjective U V hU hV (k + 1)⟩

/-- **The `ι ∘ Σ_* = relMvHomSumInt` bridge**: the small-chains iso applied to the `Q`-form sum
(difference) is the textbook sum (difference), landing in `Hₙ(M, U∪V)`. -/
theorem iota_relMvHomSumQInt (U V : Set ↑M) (n : ℕ)
    (p : RelHomologyInt U n × RelHomologyInt V n) :
    iotaInt U V n (relMvHomSumQInt U V n p) = relMvHomSumInt U V n p := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  rw [show relMvHomSumQInt U V n (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
      = QHomologyInt.mk U V n ⟨relMvChainSumInt U V n ((a : _), (b : _)),
          relMvChainSumInt_pair_mem_qCyclesInt U V n a b⟩ from relMvHomSumQInt_mk U V n a b, iotaInt_mk,
    relMvHomSumInt, LinearMap.coprod_apply, LinearMap.neg_apply, relInclInt, relInclInt,
    RelHomologyInt.map_mk, RelHomologyInt.map_mk]
  refine congrArg (RelHomologyInt.mk (U ∪ V) n) (Subtype.ext ?_)
  simp only [← sub_eq_add_neg]
  rw [AddSubgroupClass.coe_sub, relCyclesMapInt_coe, relCyclesMapInt_coe]
  obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _ (a : RelativeChainInt U n)
  obtain ⟨b', hb'⟩ := Submodule.Quotient.mk_surjective _ (b : RelativeChainInt V n)
  rw [← ha', ← hb',
    show (Submodule.Quotient.mk a' : RelativeChainInt U n) = RelativeChainInt.mk U n a' from rfl,
    show (Submodule.Quotient.mk b' : RelativeChainInt V n) = RelativeChainInt.mk V n b' from rfl,
    relMvChainSumInt_mk, relMapChainInt_id_mk, relMapChainInt_id_mk,
    show (Submodule.Quotient.mk (a' - b') : QChainInt U V n) = QChainInt.mk U V n (a' - b') from rfl,
    piMapInt_mk]
  rfl

/-- **Integral relative MV exactness at `Hₙ(M,U) ⊕ Hₙ(M,V)`** in textbook form: `range Δ_* = ker Σ_*`
(positive degree). Transported from the `Q`-form middle exactness through the iso `ι`. This is the shared
foundation for the oriented fundamental-class induction and the integral Poincaré-duality cap-iso:
two relative classes restricting to the SAME class in `Hₙ(M, U∪V)` have difference `0`, hence lie in
`im Δ_*`. -/
theorem relMvInt_exact_middle' (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Exact (relMvHomDiagInt U V (k + 1)) (relMvHomSumInt U V (k + 1)) := by
  intro p
  constructor
  · intro hp
    refine (relMv_exact_middleInt U V (k + 1) p).mp ?_
    have h0 : iotaInt U V (k + 1) (relMvHomSumQInt U V (k + 1) p) = 0 := by
      rw [iota_relMvHomSumQInt]; exact hp
    exact (iotaEquivInt U V hU hV k).map_eq_zero_iff.mp h0
  · intro hp
    rw [← iota_relMvHomSumQInt,
      show relMvHomSumQInt U V (k + 1) p = 0 from (relMv_exact_middleInt U V (k + 1) p).mpr hp, map_zero]

end SKEFTHawking.SingularRelativeMVInt
