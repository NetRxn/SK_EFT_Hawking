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
  simp only [relMvChainDiagInt, LinearMap.prod_apply, Pi.prod, relMapChainInt_mk,
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

end SKEFTHawking.SingularRelativeMVInt
