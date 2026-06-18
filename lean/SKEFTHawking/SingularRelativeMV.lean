import Mathlib
import SKEFTHawking.SingularRelativeFunctoriality
import SKEFTHawking.SingularMayerVietoris

/-!
# Relative Mayer–Vietoris: the maps `Hₙ(M|A∩B) → Hₙ(M|A) ⊕ Hₙ(M|B) → Hₙ(M|A∪B)`

Toward the fundamental class (Hatcher 3.27). With `Hₙ(M|A) := Hₙ(M, M∖A)` and opens `U = M∖A`,
`V = M∖B` of `M` (so `U∩V = M∖(A∪B)`, `U∪V = M∖(A∩B)`), the **relative** Mayer–Vietoris diagonal and
sum are the inclusion-of-pairs maps induced by `id_M` on `(M, U∩V) → (M, U)`, `(M, U) → (M, U∪V)`,
etc. (`RelativeHomology.map`). The chain-complex condition `Σ ∘ Δ = 0` holds because both inclusion
routes `(M, U∩V) → (M, U∪V)` are the single inclusion, so over `ℤ/2` the sum is `c + c = 0`. With the
connecting map (next brick) this becomes the relative MV long exact sequence — the engine of the
`Hₙ(M|A)` compactness induction giving the fundamental class `[M]`. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality

namespace SKEFTHawking.SingularRelativeMV

variable {M : TopCat}

/-- The inclusion-of-pairs map `Hₙ(M, S) → Hₙ(M, T)` for `S ⊆ T`, induced by `id_M` (a map of pairs
`(M, S) → (M, T)` since `id` sends `S` into `T`). -/
noncomputable def relIncl {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    RelativeHomology S n →ₗ[ZMod 2] RelativeHomology T n :=
  RelativeHomology.map (ContinuousMap.id ↑M) (fun _ hx => h hx) n

/-- Composing two inclusion-of-pairs maps is the inclusion over the composite subset relation
(functoriality of relative homology + `id ∘ id = id`). -/
theorem relIncl_trans {S T W : Set ↑M} (h1 : S ⊆ T) (h2 : T ⊆ W) (n : ℕ)
    (x : RelativeHomology S n) :
    relIncl h2 n (relIncl h1 n x) = relIncl (h1.trans h2) n x := by
  rw [relIncl, relIncl, relIncl, ← LinearMap.comp_apply, ← RelativeHomology.map_comp]
  rfl

/-- **Relative MV diagonal** `Hₙ(M|A∩B) → Hₙ(M|A) ⊕ Hₙ(M|B)`, the two inclusions `U∩V ↪ U`, `U∩V ↪ V`. -/
noncomputable def relMvHomDiag (U V : Set ↑M) (n : ℕ) :
    RelativeHomology (U ∩ V) n →ₗ[ZMod 2] RelativeHomology U n × RelativeHomology V n :=
  (relIncl Set.inter_subset_left n).prod (relIncl Set.inter_subset_right n)

/-- **Relative MV sum** `Hₙ(M|A) ⊕ Hₙ(M|B) → Hₙ(M|A∪B)`, the inclusions `U ↪ U∪V`, `V ↪ U∪V`
(a difference over `ℤ/2`). -/
noncomputable def relMvHomSum (U V : Set ↑M) (n : ℕ) :
    RelativeHomology U n × RelativeHomology V n →ₗ[ZMod 2] RelativeHomology (U ∪ V) n :=
  (relIncl Set.subset_union_left n).coprod (relIncl Set.subset_union_right n)

/-- **Relative MV chain-complex condition** `Σ ∘ Δ = 0`: both routes `(M, U∩V) → (M, U∪V)` equal the
single inclusion, so over `ℤ/2` the sum is `c + c = 0`. -/
theorem relMvHomSum_relMvHomDiag (U V : Set ↑M) (n : ℕ) (w : RelativeHomology (U ∩ V) n) :
    relMvHomSum U V n (relMvHomDiag U V n w) = 0 := by
  show relIncl Set.subset_union_left n (relIncl Set.inter_subset_left n w)
      + relIncl Set.subset_union_right n (relIncl Set.inter_subset_right n w) = 0
  rw [relIncl_trans, relIncl_trans]
  exact ZModModule.add_self _

/-! ## Chain-level relative MV short exact sequence (toward the connecting map) -/

/-- The chain-level relative MV **diagonal** `C(M, U∩V) → C(M, U) × C(M, V)`, `[c] ↦ ([c], [c])`
(induced by `id_M` on relative chains). -/
noncomputable def relMvChainDiag (U V : Set ↑M) (n : ℕ) :
    RelativeChain (U ∩ V) n →ₗ[ZMod 2] RelativeChain U n × RelativeChain V n :=
  (relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n).prod
    (relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n)

@[simp] theorem relMvChainDiag_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) :
    relMvChainDiag U V n (RelativeChain.mk (U ∩ V) n c)
      = (RelativeChain.mk U n c, RelativeChain.mk V n c) := by
  simp only [relMvChainDiag, LinearMap.prod_apply, Pi.prod, relMapChain_mk, mapChain_id]

/-- `Δ` is **injective**: `([c]_U, [c]_V) = 0` forces `c ∈ C(U) ∩ C(V) = C(U∩V)`, i.e. `[c]_{U∩V} = 0`. -/
theorem relMvChainDiag_injective (U V : Set ↑M) (n : ℕ) :
    Function.Injective (relMvChainDiag U V n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) n) = RelativeChain.mk (U ∩ V) n c from rfl,
    relMvChainDiag_mk, Prod.mk_eq_zero, RelativeChain.mk_eq_zero_iff, RelativeChain.mk_eq_zero_iff] at hx
  rw [show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) n) = RelativeChain.mk (U ∩ V) n c from rfl,
    RelativeChain.mk_eq_zero_iff, ← SingularExcision.subspaceChains_inf]
  exact Submodule.mem_inf.2 hx

/-! ### The chain-level union submodule and the relative MV sum (third SES term) -/

/-- The **small (`U`-or-`V`) chains** `C_n(U) + C_n(V) ⊆ C_n(M)`. The relative MV third term is the
quotient `C_n(M) / (C_n(U) + C_n(V))`; by the small-simplices theorem its homology computes
`Hₙ(M, U∪V)` for an open cover `{U, V}`. -/
noncomputable def mvUnionChains (U V : Set ↑M) (n : ℕ) : Submodule (ZMod 2) (SingularChain M n) :=
  subspaceChains U n + subspaceChains V n

theorem subspaceChains_le_mvUnionChains_left (U V : Set ↑M) (n : ℕ) :
    subspaceChains U n ≤ mvUnionChains U V n := le_sup_left

theorem subspaceChains_le_mvUnionChains_right (U V : Set ↑M) (n : ℕ) :
    subspaceChains V n ≤ mvUnionChains U V n := le_sup_right

/-- The factor map `C(M,U) = C(M)/C(U) → C(M)/(C(U)+C(V))` (`C(U) ⊆ C(U)+C(V)`). -/
noncomputable def relMvFactorL (U V : Set ↑M) (n : ℕ) :
    RelativeChain U n →ₗ[ZMod 2] SingularChain M n ⧸ mvUnionChains U V n :=
  Submodule.mapQ (subspaceChains U n) (mvUnionChains U V n) LinearMap.id
    (by rw [Submodule.comap_id]; exact subspaceChains_le_mvUnionChains_left U V n)

/-- The factor map `C(M,V) = C(M)/C(V) → C(M)/(C(U)+C(V))` (`C(V) ⊆ C(U)+C(V)`). -/
noncomputable def relMvFactorR (U V : Set ↑M) (n : ℕ) :
    RelativeChain V n →ₗ[ZMod 2] SingularChain M n ⧸ mvUnionChains U V n :=
  Submodule.mapQ (subspaceChains V n) (mvUnionChains U V n) LinearMap.id
    (by rw [Submodule.comap_id]; exact subspaceChains_le_mvUnionChains_right U V n)

@[simp] theorem relMvFactorL_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) :
    relMvFactorL U V n (RelativeChain.mk U n c) = Submodule.Quotient.mk c :=
  rfl

@[simp] theorem relMvFactorR_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) :
    relMvFactorR U V n (RelativeChain.mk V n c) = Submodule.Quotient.mk c :=
  rfl

/-- The chain-level relative MV **sum** `C(M,U) × C(M,V) → C(M)/(C(U)+C(V))`, `([a],[b]) ↦ [a+b]`
(a difference over `ℤ/2`). -/
noncomputable def relMvChainSum (U V : Set ↑M) (n : ℕ) :
    RelativeChain U n × RelativeChain V n →ₗ[ZMod 2] SingularChain M n ⧸ mvUnionChains U V n :=
  (relMvFactorL U V n).coprod (relMvFactorR U V n)

@[simp] theorem relMvChainSum_mk (U V : Set ↑M) (n : ℕ) (a b : SingularChain M n) :
    relMvChainSum U V n (RelativeChain.mk U n a, RelativeChain.mk V n b)
      = Submodule.Quotient.mk (a + b) := by
  rw [relMvChainSum, LinearMap.coprod_apply, relMvFactorL_mk, relMvFactorR_mk, ← Submodule.Quotient.mk_add]

/-- **Relative MV chain SES — chain-complex condition** `Σ ∘ Δ = 0`. -/
theorem relMvChainSum_relMvChainDiag (U V : Set ↑M) (n : ℕ) (w : RelativeChain (U ∩ V) n) :
    relMvChainSum U V n (relMvChainDiag U V n w) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) n) = RelativeChain.mk (U ∩ V) n c from rfl,
    relMvChainDiag_mk, relMvChainSum_mk, ZModModule.add_self]
  exact Submodule.Quotient.mk_zero _

/-- **Relative MV chain SES — `Σ` is surjective** (`C(M) ↠ C(M)/(C(U)+C(V))` factors through `Σ`). -/
theorem relMvChainSum_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relMvChainSum U V n) := by
  intro q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨(RelativeChain.mk U n c, 0), ?_⟩
  rw [relMvChainSum, LinearMap.coprod_apply, map_zero, add_zero, relMvFactorL_mk]

/-- **Relative MV chain SES — exactness in the middle**: `ker Σ = range Δ`. The substantive direction:
`[a+b] = 0` in `C(M)/(C(U)+C(V))` means `a + b = u + v` with `u ∈ C(U)`, `v ∈ C(V)`; then over `ℤ/2`
the chain `c := a + u = b + v` satisfies `Δ[c] = ([a],[b])`. -/
theorem relMvChain_exact (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvChainDiag U V n) (relMvChainSum U V n) := by
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (subspaceChains U n) p.1
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (subspaceChains V n) p.2
    have hpe : p = (RelativeChain.mk U n a, RelativeChain.mk V n b) := Prod.ext ha.symm hb.symm
    subst hpe
    rw [relMvChainSum_mk, Submodule.Quotient.mk_eq_zero] at hp
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hp
    have hc : a + u = b + v := by
      have h0 : a + u + (b + v) = 0 := by
        rw [show a + u + (b + v) = u + v + (a + b) by abel, huv, ZModModule.add_self]
      rw [← sub_eq_zero, sub_eq_add_neg,
        neg_eq_of_add_eq_zero_left (ZModModule.add_self (b + v)), h0]
    refine ⟨RelativeChain.mk (U ∩ V) n (a + u), ?_⟩
    rw [relMvChainDiag_mk]
    refine Prod.ext ?_ ?_
    · rw [show RelativeChain.mk U n (a + u) = RelativeChain.mk U n a + RelativeChain.mk U n u from rfl,
        (RelativeChain.mk_eq_zero_iff U n u).2 hu, add_zero]
    · rw [hc, show RelativeChain.mk V n (b + v) = RelativeChain.mk V n b + RelativeChain.mk V n v from rfl,
        (RelativeChain.mk_eq_zero_iff V n v).2 hv, add_zero]
  · rintro ⟨w, rfl⟩
    exact relMvChainSum_relMvChainDiag U V n w

/-! ### The third-term complex `Q = C(M)/(C(U)+C(V))` and its homology

A near-verbatim copy of the `RelativeHomology` complex, but quotienting by the union submodule
`C(U)+C(V)` (still boundary-stable, being a sum of two boundary-stable submodules) rather than by a
single subspace's chains. This is the third term of the relative MV chain SES; the snake-lemma
connecting map of that SES (next brick) is `δ : QHomology (n+1) → RelativeHomology (U∩V) n`. -/

/-- The boundary preserves `C(U)+C(V)` (each summand is boundary-stable). -/
theorem chainBoundary_mem_mvUnionChains (U V : Set ↑M) (n : ℕ) (c : SingularChain M (n + 1))
    (hc : c ∈ mvUnionChains U V (n + 1)) : chainBoundary M n c ∈ mvUnionChains U V n := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hc
  rw [map_add]
  exact Submodule.add_mem_sup (chainBoundary_mem_subspaceChains U n u hu)
    (chainBoundary_mem_subspaceChains V n v hv)

/-- The **third-term chains** `Q_n = C_n(M) / (C_n(U)+C_n(V))`. A reducible abbreviation so the raw
quotient and `QChain` are transparently identified (Mathlib's quotient `Module`/`AddCommGroup`
instances apply directly, and `relMvChainSum`'s codomain is defeq-free `QChain`). -/
abbrev QChain (U V : Set ↑M) (n : ℕ) : Type := SingularChain M n ⧸ mvUnionChains U V n

/-- The `Q`-class of an absolute chain. -/
noncomputable def QChain.mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) : QChain U V n :=
  Submodule.Quotient.mk c

theorem QChain.mk_eq_zero_iff (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) :
    QChain.mk U V n c = 0 ↔ c ∈ mvUnionChains U V n :=
  Submodule.Quotient.mk_eq_zero _

/-- The induced boundary `∂ : Q_{n+1} → Q_n`. -/
noncomputable def qBoundary (U V : Set ↑M) (n : ℕ) :
    QChain U V (n + 1) →ₗ[ZMod 2] QChain U V n :=
  Submodule.mapQ (mvUnionChains U V (n + 1)) (mvUnionChains U V n) (chainBoundary M n)
    (fun c hc => chainBoundary_mem_mvUnionChains U V n c hc)

theorem qBoundary_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M (n + 1)) :
    qBoundary U V n (QChain.mk U V (n + 1) c) = QChain.mk U V n (chainBoundary M n c) := rfl

theorem qBoundary_comp_qBoundary (U V : Set ↑M) (n : ℕ) :
    (qBoundary U V n).comp (qBoundary U V (n + 1)) = 0 := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  show qBoundary U V n (qBoundary U V (n + 1) (QChain.mk U V (n + 1 + 1) c)) = 0
  rw [qBoundary_mk, qBoundary_mk, chainBoundary_chainBoundary_apply]
  rfl

/-- The `Q`-**cycles** (`⊤` in degree 0; `ker ∂` otherwise). -/
noncomputable def qCycles (U V : Set ↑M) (n : ℕ) : Submodule (ZMod 2) (QChain U V n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (qBoundary U V m)

/-- The `Q`-**boundaries** `im ∂`. -/
noncomputable def qBoundaries (U V : Set ↑M) (n : ℕ) : Submodule (ZMod 2) (QChain U V n) :=
  LinearMap.range (qBoundary U V n)

theorem qBoundaries_le_qCycles (U V : Set ↑M) (n : ℕ) : qBoundaries U V n ≤ qCycles U V n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (qBoundary U V (m + 1)) ≤ LinearMap.ker (qBoundary U V m)
    rw [LinearMap.range_le_ker_iff]
    exact qBoundary_comp_qBoundary U V m

/-- **The third-term homology** `QHomology n = Hₙ(C(M)/(C(U)+C(V)))`. By the relative small-chains
theorem (brick 72c-2e) this computes `Hₙ(M, U∪V)` for an open cover `{U, V}`. -/
def QHomology (U V : Set ↑M) (n : ℕ) : Type :=
  (qCycles U V n) ⧸ (qBoundaries U V n).submoduleOf (qCycles U V n)

noncomputable instance (U V : Set ↑M) (n : ℕ) : AddCommGroup (QHomology U V n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (U V : Set ↑M) (n : ℕ) : Module (ZMod 2) (QHomology U V n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The `Q`-homology class of a `Q`-cycle. -/
noncomputable def QHomology.mk (U V : Set ↑M) (n : ℕ) (z : qCycles U V n) : QHomology U V n :=
  Submodule.Quotient.mk z

theorem QHomology.mk_eq_zero_iff (U V : Set ↑M) (n : ℕ) (z : qCycles U V n) :
    QHomology.mk U V n z = 0 ↔ (z : QChain U V n) ∈ qBoundaries U V n := by
  constructor
  · intro h
    have h2 : z ∈ (qBoundaries U V n).submoduleOf (qCycles U V n) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

/-! ### The relative MV connecting map `δ : QHomology (n+1) → RelativeHomology (U∩V) n`

Built snake-lemma–style on the chain SES `0 → C(M,U∩V) →[Δ] B →[Σ] Q → 0`, `B := C(M,U)×C(M,V)`,
mirroring `SingularPairLES`. Because `Δ` is **injective** (`relMvChainDiag_injective`), the snake
extraction `∂_B b ↦ Δ⁻¹(∂_B b)` is a genuine *linear* map (via `LinearEquiv.ofInjective Δ`), avoiding
any non-canonical `C(U)+C(V)` splitting — the `boundaryExtract` analog. -/

/-- The boundary on the middle term `B = C(M,U) × C(M,V)` (`∂ ⊕ ∂`). -/
noncomputable def bBoundary (U V : Set ↑M) (n : ℕ) :
    RelativeChain U (n + 1) × RelativeChain V (n + 1) →ₗ[ZMod 2]
      RelativeChain U n × RelativeChain V n :=
  (relBoundary U n).prodMap (relBoundary V n)

theorem bBoundary_mk (U V : Set ↑M) (n : ℕ) (a b : SingularChain M (n + 1)) :
    bBoundary U V n (RelativeChain.mk U (n + 1) a, RelativeChain.mk V (n + 1) b)
      = (RelativeChain.mk U n (chainBoundary M n a), RelativeChain.mk V n (chainBoundary M n b)) := by
  rw [bBoundary, LinearMap.prodMap_apply, relBoundary_mk, relBoundary_mk]

/-- `Δ` is a **chain map**: `Δ ∘ ∂_{U∩V} = ∂_B ∘ Δ`. -/
theorem relMvChainDiag_chainMap (U V : Set ↑M) (n : ℕ) (w : RelativeChain (U ∩ V) (n + 1)) :
    relMvChainDiag U V n (relBoundary (U ∩ V) n w)
      = bBoundary U V n (relMvChainDiag U V (n + 1) w) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) (n + 1))
        = RelativeChain.mk (U ∩ V) (n + 1) c from rfl,
    relBoundary_mk, relMvChainDiag_mk, relMvChainDiag_mk, bBoundary_mk]

/-- `Σ` is a **chain map**: `Σ ∘ ∂_B = ∂_Q ∘ Σ`. -/
theorem relMvChainSum_chainMap (U V : Set ↑M) (n : ℕ)
    (p : RelativeChain U (n + 1) × RelativeChain V (n + 1)) :
    relMvChainSum U V n (bBoundary U V n p) = qBoundary U V n (relMvChainSum U V (n + 1) p) := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  show relMvChainSum U V n
      (bBoundary U V n (RelativeChain.mk U (n + 1) a, RelativeChain.mk V (n + 1) b))
    = qBoundary U V n
      (relMvChainSum U V (n + 1) (RelativeChain.mk U (n + 1) a, RelativeChain.mk V (n + 1) b))
  rw [bBoundary_mk, relMvChainSum_mk, relMvChainSum_mk]
  show Submodule.Quotient.mk (chainBoundary M n a + chainBoundary M n b)
      = Submodule.Quotient.mk (chainBoundary M n (a + b))
  rw [map_add]

/-- `∂_B² = 0` on the middle term (pointwise). -/
theorem bBoundary_bBoundary_apply (U V : Set ↑M) (n : ℕ)
    (p : RelativeChain U (n + 1 + 1) × RelativeChain V (n + 1 + 1)) :
    bBoundary U V n (bBoundary U V (n + 1) p) = 0 := by
  obtain ⟨pu, pv⟩ := p
  rw [bBoundary, bBoundary, LinearMap.prodMap_apply, LinearMap.prodMap_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, relBoundary_comp_relBoundary,
    relBoundary_comp_relBoundary, LinearMap.zero_apply, LinearMap.zero_apply]
  rfl

/-- The **lift submodule** `L_n = { b ∈ B_{n+1} | Σ(∂_B b) = 0 }` — middle `(n+1)`-chains whose boundary
maps to a `Q`-cycle. Every `Q`-`(n+1)`-cycle lifts here (`Σ` surjective). -/
noncomputable def relLift (U V : Set ↑M) (n : ℕ) :
    Submodule (ZMod 2) (RelativeChain U (n + 1) × RelativeChain V (n + 1)) :=
  LinearMap.ker ((relMvChainSum U V n).comp (bBoundary U V n))

/-- For `b ∈ L`, `∂_B b ∈ ker Σ = range Δ` (`relMvChain_exact`). -/
theorem bBoundary_mem_range_relMvChainDiag (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    bBoundary U V n (b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
      ∈ LinearMap.range (relMvChainDiag U V n) := by
  have hsum : relMvChainSum U V n (bBoundary U V n (b : _)) = 0 := by
    have := LinearMap.mem_ker.mp b.2; rwa [LinearMap.comp_apply] at this
  obtain ⟨a, ha⟩ := (relMvChain_exact U V n _).mp hsum
  exact ⟨a, ha⟩

/-- The snake **extraction** `L_n → C(M,U∩V)_n`, `b ↦ Δ⁻¹(∂_B b)` — linear because `Δ` is injective
(`LinearEquiv.ofInjective`), the `boundaryExtract` analog. -/
noncomputable def extractA (U V : Set ↑M) (n : ℕ) :
    relLift U V n →ₗ[ZMod 2] RelativeChain (U ∩ V) n :=
  (LinearEquiv.ofInjective (relMvChainDiag U V n)
      (relMvChainDiag_injective U V n)).symm.toLinearMap.comp
    ((bBoundary U V n).restrict (fun b hb => bBoundary_mem_range_relMvChainDiag U V n ⟨b, hb⟩))

/-- The extraction recovers `∂_B b` after re-applying `Δ`: `Δ (extractA b) = ∂_B b`. -/
theorem relMvChainDiag_extractA (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relMvChainDiag U V n (extractA U V n b)
      = bBoundary U V n (b : RelativeChain U (n + 1) × RelativeChain V (n + 1)) := by
  rw [extractA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply,
    LinearMap.restrict_coe_apply]

/-- The extracted chain is a **relative cycle** of `(M, U∩V)`: `∂(extractA b) = 0`
(from `∂_B² = 0` + `Δ` injective). -/
theorem extractA_mem_relCycles (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    extractA U V n b ∈ relCycles (U ∩ V) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show extractA U V (m + 1) b ∈ LinearMap.ker (relBoundary (U ∩ V) m)
    rw [LinearMap.mem_ker]
    apply relMvChainDiag_injective U V m
    rw [map_zero, relMvChainDiag_chainMap, relMvChainDiag_extractA, bBoundary_bBoundary_apply]

/-- The connecting map on lift-chains: `L_n →ₗ Hₙ(M,U∩V)`, `b ↦ [extractA b]`. -/
noncomputable def relConnectingLift (U V : Set ↑M) (n : ℕ) :
    relLift U V n →ₗ[ZMod 2] RelativeHomology (U ∩ V) n :=
  (Submodule.mkQ _).comp ((extractA U V n).codRestrict (relCycles (U ∩ V) n)
    (extractA_mem_relCycles U V n))

theorem relConnectingLift_apply (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relConnectingLift U V n b = RelativeHomology.mk (U ∩ V) n
      ⟨extractA U V n b, extractA_mem_relCycles U V n b⟩ := rfl

/-- `Σ b` is a `Q`-cycle for `b ∈ L`: `∂_Q (Σ b) = Σ(∂_B b) = 0`. -/
theorem relMvChainSum_mem_qCycles (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relMvChainSum U V (n + 1) (b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
      ∈ qCycles U V (n + 1) := by
  have h0 : qBoundary U V n (relMvChainSum U V (n + 1) (b : _)) = 0 := by
    rw [← relMvChainSum_chainMap]
    have := LinearMap.mem_ker.mp b.2; rwa [LinearMap.comp_apply] at this
  exact LinearMap.mem_ker.mpr h0

/-- The surjection `L_n ↠ Hₙ₊₁(Q)`, `b ↦ [Σ b]` — every `Q`-`(n+1)`-cycle lifts to the middle term. -/
noncomputable def relLiftToQHom (U V : Set ↑M) (n : ℕ) :
    relLift U V n →ₗ[ZMod 2] QHomology U V (n + 1) :=
  (Submodule.mkQ _).comp
    ((show relLift U V n →ₗ[ZMod 2] QChain U V (n + 1) from
        (relMvChainSum U V (n + 1)).comp (relLift U V n).subtype).codRestrict
      (qCycles U V (n + 1)) (fun b => relMvChainSum_mem_qCycles U V n b))

theorem relLiftToQHom_apply (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relLiftToQHom U V n b = QHomology.mk U V (n + 1)
      ⟨relMvChainSum U V (n + 1) (b : _), relMvChainSum_mem_qCycles U V n b⟩ := rfl

theorem relLiftToQHom_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relLiftToQHom U V n) := by
  intro h
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨b, hb⟩ := relMvChainSum_surjective U V (n + 1) (z : QChain U V (n + 1))
  have hbL : b ∈ relLift U V n := by
    rw [relLift, LinearMap.mem_ker, LinearMap.comp_apply, relMvChainSum_chainMap, hb]
    exact LinearMap.mem_ker.mp z.2
  refine ⟨⟨b, hbL⟩, ?_⟩
  rw [relLiftToQHom_apply]
  exact congrArg (QHomology.mk U V (n + 1)) (Subtype.ext hb)

/-- **Snake-lemma well-definedness**: `ker(b ↦ [Σ b]) ≤ ker(b ↦ [extractA b])`. If `[Σ b] = 0` in
`Hₙ₊₁(Q)`, write `Σ b = ∂_Q q'`, lift `q' = Σ b'`; then `b + ∂_B b' = Δ a'` (exactness), whence
`extractA b = ∂(extractA b)`'s witness `= ∂ a'` is a relative boundary. -/
theorem relConnecting_ker_le (U V : Set ↑M) (n : ℕ) :
    LinearMap.ker (relLiftToQHom U V n) ≤ LinearMap.ker (relConnectingLift U V n) := by
  intro b hb
  rw [LinearMap.mem_ker, relLiftToQHom_apply, QHomology.mk_eq_zero_iff] at hb
  rw [LinearMap.mem_ker, relConnectingLift_apply]
  obtain ⟨q', hq'⟩ := hb
  obtain ⟨b', hb'⟩ := relMvChainSum_surjective U V (n + 2) q'
  have hker : relMvChainSum U V (n + 1)
      ((b : RelativeChain U (n + 1) × RelativeChain V (n + 1)) + bBoundary U V (n + 1) b') = 0 := by
    rw [map_add, relMvChainSum_chainMap, hb', hq', ZModModule.add_self]
  obtain ⟨a', ha'⟩ := (relMvChain_exact U V (n + 1) _).mp hker
  refine (RelativeHomology.mk_eq_zero_iff (U ∩ V) n _).2 ?_
  show extractA U V n b ∈ relBoundaries (U ∩ V) n
  have hextract : extractA U V n b = relBoundary (U ∩ V) n a' := by
    apply relMvChainDiag_injective U V n
    rw [relMvChainDiag_extractA, relMvChainDiag_chainMap, ha', map_add, bBoundary_bBoundary_apply,
      add_zero]
  rw [hextract]
  exact LinearMap.mem_range_self _ a'

/-- **The relative MV connecting homomorphism** `δ : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` — in its `Q`-form
`Hₙ₊₁(Q) → Hₙ(M, U∩V)`, the snake descent of `relConnectingLift` through `relLiftToQHom`
(`relConnecting_ker_le` is well-definedness). The `Hₙ₊₁(Q) ≅ Hₙ₊₁(M, U∪V)` identification (brick
72c-2e) puts it in final form. -/
noncomputable def relConnecting (U V : Set ↑M) (n : ℕ) :
    QHomology U V (n + 1) →ₗ[ZMod 2] RelativeHomology (U ∩ V) n :=
  (Submodule.liftQ (LinearMap.ker (relLiftToQHom U V n)) (relConnectingLift U V n)
    (relConnecting_ker_le U V n)).comp
    (LinearMap.quotKerEquivOfSurjective (relLiftToQHom U V n)
      (relLiftToQHom_surjective U V n)).symm.toLinearMap

/-- The connecting map on the class of a lift-chain `b ∈ L_n` is `[extractA b]`. -/
theorem relConnecting_relLiftToQHom (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relConnecting U V n (relLiftToQHom U V n b) = relConnectingLift U V n b := by
  rw [relConnecting, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-! ### The homology-level sum map `Σ_* : Hₙ(M,U) × Hₙ(M,V) → Hₙ(Q)`

The factor chain maps `relMvFactorL/R : C(M,U)/C(M,V) → Q` induce homology maps (the `homIncl`
analog), and `Σ_* := relFactorLHom.coprod relFactorRHom`. With the small-chains iso `Hₙ(Q) ≅ Hₙ(M,U∪V)`
this is `relMvHomSum` (72c-1). -/

/-- `relMvFactorL` is a **chain map**: `Σ_L ∘ ∂_{M,U} = ∂_Q ∘ Σ_L`. -/
theorem relMvFactorL_chainMap (U V : Set ↑M) (n : ℕ) (x : RelativeChain U (n + 1)) :
    relMvFactorL U V n (relBoundary U n x) = qBoundary U V n (relMvFactorL U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChain U (n + 1)) = RelativeChain.mk U (n + 1) c from rfl,
    relBoundary_mk, relMvFactorL_mk, relMvFactorL_mk]
  rfl

/-- `relMvFactorR` is a **chain map**: `Σ_R ∘ ∂_{M,V} = ∂_Q ∘ Σ_R`. -/
theorem relMvFactorR_chainMap (U V : Set ↑M) (n : ℕ) (x : RelativeChain V (n + 1)) :
    relMvFactorR U V n (relBoundary V n x) = qBoundary U V n (relMvFactorR U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk c : RelativeChain V (n + 1)) = RelativeChain.mk V (n + 1) c from rfl,
    relBoundary_mk, relMvFactorR_mk, relMvFactorR_mk]
  rfl

theorem relMvFactorL_mem_qCycles (U V : Set ↑M) (n : ℕ) (z : RelativeChain U n)
    (hz : z ∈ relCycles U n) : relMvFactorL U V n z ∈ qCycles U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : relBoundary U m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : qBoundary U V m (relMvFactorL U V (m + 1) z) = 0 := by
      rw [← relMvFactorL_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem relMvFactorR_mem_qCycles (U V : Set ↑M) (n : ℕ) (z : RelativeChain V n)
    (hz : z ∈ relCycles V n) : relMvFactorR U V n z ∈ qCycles U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : relBoundary V m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : qBoundary U V m (relMvFactorR U V (m + 1) z) = 0 := by
      rw [← relMvFactorR_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem relMvFactorL_mem_qBoundaries (U V : Set ↑M) (n : ℕ) (z : RelativeChain U n)
    (hz : z ∈ relBoundaries U n) : relMvFactorL U V n z ∈ qBoundaries U V n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMvFactorL U V (n + 1) w, (relMvFactorL_chainMap U V n w).symm⟩

theorem relMvFactorR_mem_qBoundaries (U V : Set ↑M) (n : ℕ) (z : RelativeChain V n)
    (hz : z ∈ relBoundaries V n) : relMvFactorR U V n z ∈ qBoundaries U V n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨relMvFactorR U V (n + 1) w, (relMvFactorR_chainMap U V n w).symm⟩

/-- The induced map `Hₙ(M,U) → Hₙ(Q)` of the factor chain map `relMvFactorL`. -/
noncomputable def relFactorLHom (U V : Set ↑M) (n : ℕ) :
    RelativeHomology U n →ₗ[ZMod 2] QHomology U V n :=
  Submodule.mapQ _ _ (LinearMap.restrict (relMvFactorL U V n)
      (fun z hz => relMvFactorL_mem_qCycles U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relMvFactorL_mem_qBoundaries U V n _ hz)

/-- The induced map `Hₙ(M,V) → Hₙ(Q)` of the factor chain map `relMvFactorR`. -/
noncomputable def relFactorRHom (U V : Set ↑M) (n : ℕ) :
    RelativeHomology V n →ₗ[ZMod 2] QHomology U V n :=
  Submodule.mapQ _ _ (LinearMap.restrict (relMvFactorR U V n)
      (fun z hz => relMvFactorR_mem_qCycles U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relMvFactorR_mem_qBoundaries U V n _ hz)

theorem relFactorLHom_mk (U V : Set ↑M) (n : ℕ) (z : relCycles U n) :
    relFactorLHom U V n (RelativeHomology.mk U n z)
      = QHomology.mk U V n ⟨relMvFactorL U V n z, relMvFactorL_mem_qCycles U V n z z.2⟩ := rfl

theorem relFactorRHom_mk (U V : Set ↑M) (n : ℕ) (z : relCycles V n) :
    relFactorRHom U V n (RelativeHomology.mk V n z)
      = QHomology.mk U V n ⟨relMvFactorR U V n z, relMvFactorR_mem_qCycles U V n z z.2⟩ := rfl

/-- **The homology-level relative MV sum** `Σ_* : Hₙ(M,U) × Hₙ(M,V) → Hₙ(Q)`, `([a],[b]) ↦ [a+b]`. -/
noncomputable def relMvHomSumQ (U V : Set ↑M) (n : ℕ) :
    RelativeHomology U n × RelativeHomology V n →ₗ[ZMod 2] QHomology U V n :=
  (relFactorLHom U V n).coprod (relFactorRHom U V n)

/-! ### Exactness of the relative MV long exact sequence (`Q`-form) -/

/-- The homology inclusion `relIncl` on the class of a relative cycle. -/
theorem relIncl_mk {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) (z : relCycles S n) :
    relIncl h n (RelativeHomology.mk S n z)
      = RelativeHomology.mk T n (relCyclesMap (ContinuousMap.id ↑M) (fun _ hx => h hx) n z) := by
  rw [relIncl]
  exact RelativeHomology.map_mk _ _ n z

/-- The `U`-component of `relMvHomDiag` on `[mk c]` is the relative class `[mk_U c]`. -/
theorem relMvHomDiag_fst_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n)
    (hc : RelativeChain.mk (U ∩ V) n c ∈ relCycles (U ∩ V) n)
    (hcU : RelativeChain.mk U n c ∈ relCycles U n) :
    (relMvHomDiag U V n (RelativeHomology.mk (U ∩ V) n ⟨_, hc⟩)).1
      = RelativeHomology.mk U n ⟨RelativeChain.mk U n c, hcU⟩ := by
  show relIncl Set.inter_subset_left n (RelativeHomology.mk (U ∩ V) n ⟨_, hc⟩) = _
  rw [relIncl_mk]
  refine congrArg (RelativeHomology.mk U n) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  show relMapChain (ContinuousMap.id ↑M) _ n (RelativeChain.mk (U ∩ V) n c) = RelativeChain.mk U n c
  rw [relMapChain_mk, mapChain_id]

/-- The `V`-component of `relMvHomDiag` on `[mk c]` is the relative class `[mk_V c]`. -/
theorem relMvHomDiag_snd_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n)
    (hc : RelativeChain.mk (U ∩ V) n c ∈ relCycles (U ∩ V) n)
    (hcV : RelativeChain.mk V n c ∈ relCycles V n) :
    (relMvHomDiag U V n (RelativeHomology.mk (U ∩ V) n ⟨_, hc⟩)).2
      = RelativeHomology.mk V n ⟨RelativeChain.mk V n c, hcV⟩ := by
  show relIncl Set.inter_subset_right n (RelativeHomology.mk (U ∩ V) n ⟨_, hc⟩) = _
  rw [relIncl_mk]
  refine congrArg (RelativeHomology.mk V n) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  show relMapChain (ContinuousMap.id ↑M) _ n (RelativeChain.mk (U ∩ V) n c) = RelativeChain.mk V n c
  rw [relMapChain_mk, mapChain_id]

/-- The `U`-factor of `extractA b` is the boundary of `(↑b).1` (so its `Hₙ(M,U)` class vanishes). -/
theorem relMapChain_extractA_left (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n (extractA U V n b)
      = relBoundary U n (b : RelativeChain U (n + 1) × RelativeChain V (n + 1)).1 := by
  have h := relMvChainDiag_extractA U V n b
  rw [relMvChainDiag, LinearMap.prod_apply, bBoundary, LinearMap.prodMap_apply] at h
  exact congrArg Prod.fst h

/-- The `V`-factor of `extractA b` is the boundary of `(↑b).2`. -/
theorem relMapChain_extractA_right (U V : Set ↑M) (n : ℕ) (b : relLift U V n) :
    relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n (extractA U V n b)
      = relBoundary V n (b : RelativeChain U (n + 1) × RelativeChain V (n + 1)).2 := by
  have h := relMvChainDiag_extractA U V n b
  rw [relMvChainDiag, LinearMap.prod_apply, bBoundary, LinearMap.prodMap_apply] at h
  exact congrArg Prod.snd h

/-- **Relative MV exactness at `Hₙ(M, U∩V)`**: `range δ = ker(relMvHomDiag)`. With `Hₙ₊₁(Q) = 0`
(the inductive hypothesis), this gives injectivity of `Hₙ(M,U∩V) → Hₙ(M,U) ⊕ Hₙ(M,V)` — the gluing
step of Hatcher 3.27. -/
theorem relMv_exact_connecting (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relConnecting U V n) (relMvHomDiag U V n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hxU : relIncl Set.inter_subset_left n (RelativeHomology.mk (U ∩ V) n z) = 0 :=
      congrArg Prod.fst hx
    have hxV : relIncl Set.inter_subset_right n (RelativeHomology.mk (U ∩ V) n z) = 0 :=
      congrArg Prod.snd hx
    rw [relIncl_mk, RelativeHomology.mk_eq_zero_iff, relCyclesMap_coe] at hxU hxV
    obtain ⟨wU, hwU⟩ := hxU
    obtain ⟨wV, hwV⟩ := hxV
    have hbeq : bBoundary U V n (wU, wV) = relMvChainDiag U V n (z : RelativeChain (U ∩ V) n) := by
      rw [bBoundary, LinearMap.prodMap_apply, hwU, hwV]; rfl
    have hbL : (wU, wV) ∈ relLift U V n := by
      rw [relLift, LinearMap.mem_ker, LinearMap.comp_apply, hbeq, relMvChainSum_relMvChainDiag]
    have hextract : extractA U V n ⟨(wU, wV), hbL⟩ = (z : RelativeChain (U ∩ V) n) := by
      apply relMvChainDiag_injective U V n
      rw [relMvChainDiag_extractA]; exact hbeq
    refine ⟨relLiftToQHom U V n ⟨(wU, wV), hbL⟩, ?_⟩
    rw [relConnecting_relLiftToQHom, relConnectingLift_apply]
    exact congrArg (RelativeHomology.mk (U ∩ V) n) (Subtype.ext hextract)
  · rintro ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := relLiftToQHom_surjective U V n y
    rw [relConnecting_relLiftToQHom, relConnectingLift_apply]
    refine Prod.ext ?_ ?_
    · show relIncl Set.inter_subset_left n (RelativeHomology.mk (U ∩ V) n _) = 0
      rw [relIncl_mk, RelativeHomology.mk_eq_zero_iff, relCyclesMap_coe]
      show relMapChain (ContinuousMap.id ↑M) _ n (extractA U V n b) ∈ relBoundaries U n
      rw [relMapChain_extractA_left]
      exact LinearMap.mem_range_self _ _
    · show relIncl Set.inter_subset_right n (RelativeHomology.mk (U ∩ V) n _) = 0
      rw [relIncl_mk, RelativeHomology.mk_eq_zero_iff, relCyclesMap_coe]
      show relMapChain (ContinuousMap.id ↑M) _ n (extractA U V n b) ∈ relBoundaries V n
      rw [relMapChain_extractA_right]
      exact LinearMap.mem_range_self _ _

/-- `Σ(↑a, ↑b)` is a `Q`-cycle when `a, b` are relative cycles. -/
theorem relMvChainSum_pair_mem_qCycles (U V : Set ↑M) (n : ℕ) (a : relCycles U n)
    (b : relCycles V n) :
    relMvChainSum U V n ((a : RelativeChain U n), (b : RelativeChain V n)) ∈ qCycles U V n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have ha : relBoundary U m (a : RelativeChain U (m + 1)) = 0 := LinearMap.mem_ker.mp a.2
    have hb : relBoundary V m (b : RelativeChain V (m + 1)) = 0 := LinearMap.mem_ker.mp b.2
    have h0 : qBoundary U V m (relMvChainSum U V (m + 1) ((a : _), (b : _))) = 0 := by
      rw [← relMvChainSum_chainMap, bBoundary, LinearMap.prodMap_apply, ha, hb]
      exact map_zero _
    exact LinearMap.mem_ker.mpr h0

/-- `Σ_*` on a class of cycles is `[Σ(↑a, ↑b)]`. -/
theorem relMvHomSumQ_mk (U V : Set ↑M) (n : ℕ) (a : relCycles U n) (b : relCycles V n) :
    relMvHomSumQ U V n (RelativeHomology.mk U n a, RelativeHomology.mk V n b)
      = QHomology.mk U V n ⟨relMvChainSum U V n ((a : _), (b : _)),
          relMvChainSum_pair_mem_qCycles U V n a b⟩ := by
  rw [relMvHomSumQ, LinearMap.coprod_apply, relFactorLHom_mk, relFactorRHom_mk]
  show QHomology.mk U V n (⟨relMvFactorL U V n (a : _), _⟩ + ⟨relMvFactorR U V n (b : _), _⟩)
      = QHomology.mk U V n ⟨relMvChainSum U V n ((a : _), (b : _)), _⟩
  refine congrArg (QHomology.mk U V n) (Subtype.ext ?_)
  show relMvFactorL U V n (a : _) + relMvFactorR U V n (b : _)
      = relMvChainSum U V n ((a : _), (b : _))
  rw [relMvChainSum, LinearMap.coprod_apply]

/-- Two relative cycles differing by a relative boundary have the same homology class. -/
theorem relHomology_mk_eq_of {S : Set ↑M} (n : ℕ) (w z : relCycles S n)
    (h : (w : RelativeChain S n) - (z : RelativeChain S n) ∈ relBoundaries S n) :
    RelativeHomology.mk S n w = RelativeHomology.mk S n z := by
  show Submodule.Quotient.mk w = Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    AddSubgroupClass.coe_sub]
  exact h

/-- The image of `mk_S c` under `relMapChain id` is `mk_T c` (`id_#` is the factor map). -/
theorem relMapChain_id_mk {S T : Set ↑M} (h : Set.MapsTo (ContinuousMap.id ↑M) S T) (n : ℕ)
    (c : SingularChain M n) :
    relMapChain (ContinuousMap.id ↑M) h n (RelativeChain.mk S n c) = RelativeChain.mk T n c := by
  rw [relMapChain_mk, mapChain_id]

/-- **Relative MV exactness at `Hₙ(M,U) ⊕ Hₙ(M,V)`**: `range Δ_* = ker Σ_*` (the snake middle). -/
theorem relMv_exact_middle (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvHomDiag U V n) (relMvHomSumQ U V n) := by
  intro p
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  constructor
  · intro hp
    rw [show relMvHomSumQ U V n (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
        = QHomology.mk U V n ⟨relMvChainSum U V n ((a : _), (b : _)),
            relMvChainSum_pair_mem_qCycles U V n a b⟩ from relMvHomSumQ_mk U V n a b,
      QHomology.mk_eq_zero_iff] at hp
    obtain ⟨δq, hδq⟩ := hp
    obtain ⟨b'', hb''⟩ := relMvChainSum_surjective U V (n + 1) δq
    have hker : relMvChainSum U V n
        (((a : RelativeChain U n), (b : RelativeChain V n)) + bBoundary U V n b'') = 0 := by
      rw [map_add, relMvChainSum_chainMap, hb'', hδq, ZModModule.add_self]
    obtain ⟨w, hw⟩ := (relMvChain_exact U V n _).mp hker
    have hfst : relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n w
        = (a : RelativeChain U n) + relBoundary U n (b'').1 := by
      have h := congrArg Prod.fst hw
      simpa only [relMvChainDiag, LinearMap.prod_apply, Prod.fst_add, bBoundary,
        LinearMap.prodMap_apply] using h
    have hsnd : relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n w
        = (b : RelativeChain V n) + relBoundary V n (b'').2 := by
      have h := congrArg Prod.snd hw
      simpa only [relMvChainDiag, LinearMap.prod_apply, Prod.snd_add, bBoundary,
        LinearMap.prodMap_apply] using h
    have hw_cyc : w ∈ relCycles (U ∩ V) n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
        rw [show relCycles (U ∩ V) (m + 1) = LinearMap.ker (relBoundary (U ∩ V) m) from rfl,
          LinearMap.mem_ker]
        apply relMvChainDiag_injective U V m
        rw [map_zero, relMvChainDiag_chainMap, hw, map_add, bBoundary_bBoundary_apply, add_zero,
          bBoundary, LinearMap.prodMap_apply, LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
        rfl
    obtain ⟨wc, hwc⟩ := Submodule.Quotient.mk_surjective _ w
    have hwcEqL : RelativeChain.mk U n wc
        = relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n w := by
      rw [← hwc, show (Submodule.Quotient.mk wc : RelativeChain (U ∩ V) n)
          = RelativeChain.mk (U ∩ V) n wc from rfl, relMapChain_id_mk]
    have hwcEqR : RelativeChain.mk V n wc
        = relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n w := by
      rw [← hwc, show (Submodule.Quotient.mk wc : RelativeChain (U ∩ V) n)
          = RelativeChain.mk (U ∩ V) n wc from rfl, relMapChain_id_mk]
    have hwU : RelativeChain.mk U n wc ∈ relCycles U n := by
      rw [hwcEqL]; exact relMapChain_mem_relCycles _ _ n w hw_cyc
    have hwV : RelativeChain.mk V n wc ∈ relCycles V n := by
      rw [hwcEqR]; exact relMapChain_mem_relCycles _ _ n w hw_cyc
    refine ⟨RelativeHomology.mk (U ∩ V) n ⟨w, hw_cyc⟩, ?_⟩
    have hzc : (⟨w, hw_cyc⟩ : relCycles (U ∩ V) n)
        = ⟨RelativeChain.mk (U ∩ V) n wc,
            by rw [show RelativeChain.mk (U ∩ V) n wc = w from hwc]; exact hw_cyc⟩ :=
      Subtype.ext hwc.symm
    rw [hzc]
    refine Prod.ext ?_ ?_
    · rw [relMvHomDiag_fst_mk U V n wc _ hwU]
      refine relHomology_mk_eq_of n _ a ?_
      show RelativeChain.mk U n wc - (a : RelativeChain U n) ∈ relBoundaries U n
      rw [hwcEqL, hfst, add_sub_cancel_left]
      exact ⟨(b'').1, rfl⟩
    · rw [relMvHomDiag_snd_mk U V n wc _ hwV]
      refine relHomology_mk_eq_of n _ b ?_
      show RelativeChain.mk V n wc - (b : RelativeChain V n) ∈ relBoundaries V n
      rw [hwcEqR, hsnd, add_sub_cancel_left]
      exact ⟨(b'').2, rfl⟩
  · rintro ⟨w, hw⟩
    rw [← hw]
    obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChain (U ∩ V) n)
    have hcEqL : RelativeChain.mk U n c
        = relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n
            (zc : RelativeChain (U ∩ V) n) := by
      rw [← hc, show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) n)
          = RelativeChain.mk (U ∩ V) n c from rfl, relMapChain_id_mk]
    have hcEqR : RelativeChain.mk V n c
        = relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n
            (zc : RelativeChain (U ∩ V) n) := by
      rw [← hc, show (Submodule.Quotient.mk c : RelativeChain (U ∩ V) n)
          = RelativeChain.mk (U ∩ V) n c from rfl, relMapChain_id_mk]
    have hcU : RelativeChain.mk U n c ∈ relCycles U n := by
      rw [hcEqL]; exact relMapChain_mem_relCycles _ _ n _ zc.2
    have hcV : RelativeChain.mk V n c ∈ relCycles V n := by
      rw [hcEqR]; exact relMapChain_mem_relCycles _ _ n _ zc.2
    have hzc : (zc : relCycles (U ∩ V) n)
        = ⟨RelativeChain.mk (U ∩ V) n c,
            by rw [show RelativeChain.mk (U ∩ V) n c = (zc : RelativeChain (U ∩ V) n) from hc]
               exact zc.2⟩ := Subtype.ext hc.symm
    rw [show (Submodule.Quotient.mk zc : RelativeHomology (U ∩ V) n)
        = RelativeHomology.mk (U ∩ V) n zc from rfl, hzc,
      show relMvHomDiag U V n (RelativeHomology.mk (U ∩ V) n ⟨RelativeChain.mk (U ∩ V) n c, _⟩)
        = (RelativeHomology.mk U n ⟨RelativeChain.mk U n c, hcU⟩,
           RelativeHomology.mk V n ⟨RelativeChain.mk V n c, hcV⟩) from
      Prod.ext (relMvHomDiag_fst_mk U V n c _ hcU) (relMvHomDiag_snd_mk U V n c _ hcV),
      relMvHomSumQ_mk, QHomology.mk_eq_zero_iff]
    show relMvChainSum U V n (RelativeChain.mk U n c, RelativeChain.mk V n c) ∈ qBoundaries U V n
    rw [relMvChainSum_mk, ZModModule.add_self]
    exact Submodule.zero_mem _

/-- **Relative MV exactness at `Hₙ₊₁(Q)`**: `range Σ_* = ker δ` (the snake at the third term). -/
theorem relMv_exact_sum (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relMvHomSumQ U V (n + 1)) (relConnecting U V n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨b, rfl⟩ := relLiftToQHom_surjective U V n x
    rw [relConnecting_relLiftToQHom, relConnectingLift_apply, RelativeHomology.mk_eq_zero_iff] at hx
    obtain ⟨d, hd⟩ := hx
    have hbc0 : bBoundary U V n
        ((b : RelativeChain U (n + 1) × RelativeChain V (n + 1)) - relMvChainDiag U V (n + 1) d) = 0 := by
      rw [map_sub, (relMvChainDiag_extractA U V n b).symm, ← relMvChainDiag_chainMap, hd, sub_self]
    have ha_cyc : ((b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
        - relMvChainDiag U V (n + 1) d).1 ∈ relCycles U (n + 1) := by
      rw [show relCycles U (n + 1) = LinearMap.ker (relBoundary U n) from rfl, LinearMap.mem_ker]
      simpa only [bBoundary, LinearMap.prodMap_apply, Prod.fst_zero] using congrArg Prod.fst hbc0
    have hb_cyc : ((b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
        - relMvChainDiag U V (n + 1) d).2 ∈ relCycles V (n + 1) := by
      rw [show relCycles V (n + 1) = LinearMap.ker (relBoundary V n) from rfl, LinearMap.mem_ker]
      simpa only [bBoundary, LinearMap.prodMap_apply, Prod.snd_zero] using congrArg Prod.snd hbc0
    refine ⟨(RelativeHomology.mk U (n + 1) ⟨_, ha_cyc⟩,
      RelativeHomology.mk V (n + 1) ⟨_, hb_cyc⟩), ?_⟩
    rw [relMvHomSumQ_mk, relLiftToQHom_apply]
    refine congrArg (QHomology.mk U V (n + 1)) (Subtype.ext ?_)
    show relMvChainSum U V (n + 1)
        (((b : _) - relMvChainDiag U V (n + 1) d).1, ((b : _) - relMvChainDiag U V (n + 1) d).2)
      = relMvChainSum U V (n + 1) (b : _)
    rw [show (((b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
          - relMvChainDiag U V (n + 1) d).1,
        ((b : RelativeChain U (n + 1) × RelativeChain V (n + 1))
          - relMvChainDiag U V (n + 1) d).2)
        = (b : RelativeChain U (n + 1) × RelativeChain V (n + 1)) - relMvChainDiag U V (n + 1) d from rfl,
      map_sub, relMvChainSum_relMvChainDiag, sub_zero]
  · rintro ⟨pab, rfl⟩
    obtain ⟨pu, pv⟩ := pab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
    have hL : ((a : RelativeChain U (n + 1)), (b : RelativeChain V (n + 1))) ∈ relLift U V n := by
      rw [relLift, LinearMap.mem_ker, LinearMap.comp_apply, bBoundary, LinearMap.prodMap_apply,
        LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
      exact map_zero _
    have hSeq : relMvHomSumQ U V (n + 1) (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
        = relLiftToQHom U V n ⟨((a : _), (b : _)), hL⟩ := by
      rw [show relMvHomSumQ U V (n + 1) (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
          = QHomology.mk U V (n + 1) ⟨relMvChainSum U V (n + 1) ((a : _), (b : _)),
              relMvChainSum_pair_mem_qCycles U V (n + 1) a b⟩ from relMvHomSumQ_mk U V (n + 1) a b,
        relLiftToQHom_apply]
    rw [hSeq, relConnecting_relLiftToQHom, relConnectingLift_apply, RelativeHomology.mk_eq_zero_iff]
    have hextract : extractA U V n ⟨((a : _), (b : _)), hL⟩ = 0 := by
      apply relMvChainDiag_injective U V n
      rw [relMvChainDiag_extractA, map_zero, bBoundary, LinearMap.prodMap_apply,
        LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
      rfl
    show extractA U V n ⟨((a : _), (b : _)), hL⟩ ∈ relBoundaries (U ∩ V) n
    rw [hextract]
    exact Submodule.zero_mem _

/-! ### The projection `π : Q → C(M, U∪V)` and the small-chains map `ι : Hₙ(Q) → Hₙ(M, U∪V)`

`C(U)+C(V) ⊆ C(U∪V)` gives a projection `π : C(M)/(C(U)+C(V)) → C(M)/C(U∪V) = C(M, U∪V)`, inducing
`ι := π_* : Hₙ(Q) → Hₙ(M, U∪V)`. By the small-chains theorem `ι` is an isomorphism (the iso half is the
next brick); `ι ∘ Σ_* = relMvHomSum`, so the textbook relative MV LES transports through `ι`. -/

theorem mvUnionChains_le_subspaceChains_union (U V : Set ↑M) (n : ℕ) :
    mvUnionChains U V n ≤ subspaceChains (U ∪ V) n :=
  sup_le (SingularMayerVietoris.subspaceChains_mono Set.subset_union_left n)
    (SingularMayerVietoris.subspaceChains_mono Set.subset_union_right n)

/-- The projection `π : Q = C(M)/(C(U)+C(V)) → C(M, U∪V) = C(M)/C(U∪V)` (`C(U)+C(V) ⊆ C(U∪V)`). -/
noncomputable def piMap (U V : Set ↑M) (n : ℕ) :
    QChain U V n →ₗ[ZMod 2] RelativeChain (U ∪ V) n :=
  Submodule.mapQ (mvUnionChains U V n) (subspaceChains (U ∪ V) n) LinearMap.id
    (by rw [Submodule.comap_id]; exact mvUnionChains_le_subspaceChains_union U V n)

theorem piMap_mk (U V : Set ↑M) (n : ℕ) (c : SingularChain M n) :
    piMap U V n (QChain.mk U V n c) = RelativeChain.mk (U ∪ V) n c := rfl

/-- `π` is a **chain map**: `π ∘ ∂_Q = ∂_{M,U∪V} ∘ π`. -/
theorem piMap_chainMap (U V : Set ↑M) (n : ℕ) (x : QChain U V (n + 1)) :
    piMap U V n (qBoundary U V n x) = relBoundary (U ∪ V) n (piMap U V (n + 1) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show piMap U V n (qBoundary U V n (QChain.mk U V (n + 1) c))
      = relBoundary (U ∪ V) n (piMap U V (n + 1) (QChain.mk U V (n + 1) c))
  rw [qBoundary_mk, piMap_mk, piMap_mk, relBoundary_mk]

theorem piMap_mem_relCycles (U V : Set ↑M) (n : ℕ) (z : QChain U V n) (hz : z ∈ qCycles U V n) :
    piMap U V n z ∈ relCycles (U ∪ V) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz0 : qBoundary U V m z = 0 := LinearMap.mem_ker.mp hz
    have h0 : relBoundary (U ∪ V) m (piMap U V (m + 1) z) = 0 := by
      rw [← piMap_chainMap, hz0, map_zero]
    exact LinearMap.mem_ker.mpr h0

theorem piMap_mem_relBoundaries (U V : Set ↑M) (n : ℕ) (z : QChain U V n)
    (hz : z ∈ qBoundaries U V n) : piMap U V n z ∈ relBoundaries (U ∪ V) n := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨piMap U V (n + 1) w, (piMap_chainMap U V n w).symm⟩

/-- **The small-chains map** `ι : Hₙ(Q) → Hₙ(M, U∪V)`, induced by `π`. An isomorphism (next brick). -/
noncomputable def iota (U V : Set ↑M) (n : ℕ) :
    QHomology U V n →ₗ[ZMod 2] RelativeHomology (U ∪ V) n :=
  Submodule.mapQ _ _ (LinearMap.restrict (piMap U V n)
      (fun z hz => piMap_mem_relCycles U V n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact piMap_mem_relBoundaries U V n _ hz)

theorem iota_mk (U V : Set ↑M) (n : ℕ) (z : qCycles U V n) :
    iota U V n (QHomology.mk U V n z)
      = RelativeHomology.mk (U ∪ V) n ⟨piMap U V n z, piMap_mem_relCycles U V n z z.2⟩ := rfl

/-! ### The small-chains transport (core of the `ι` isomorphism) -/

open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision in
/-- Pushing a `{U', V'}`-small chain of `sub(U∪V)` into `M` lands in `C(U)+C(V)`: a simplex of
`sub(U∪V)` subordinate to `U' = val⁻¹ U` includes to a simplex of `M` with image in `U`. -/
theorem chainIncl_mem_mvUnion_of_small (U V : Set ↑M) (n : ℕ)
    (e : SingularChain (sub (U ∪ V)) n)
    (he : e ∈ smallChains ({Subtype.val ⁻¹' U, Subtype.val ⁻¹' V} :
      Set (Set ↥(U ∪ V))) n) :
    chainIncl (U ∪ V) n e ∈ mvUnionChains U V n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ he
  · rintro _ ⟨τ', ⟨W, hW, hsub⟩, rfl⟩
    rw [chainIncl_single]
    rcases hW with rfl | rfl
    · refine Submodule.mem_sup_left (single_mem_subspaceChains_of_subordinate ?_)
      rw [toSSetObjEquiv_simplexIncl]
      rintro _ ⟨t, rfl⟩
      exact hsub ⟨t, rfl⟩
    · refine Submodule.mem_sup_right (single_mem_subspaceChains_of_subordinate ?_)
      rw [toSSetObjEquiv_simplexIncl]
      rintro _ ⟨t, rfl⟩
      exact hsub ⟨t, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision in
/-- **The small-chains transport core**: a chain in `C(U∪V)` becomes `C(U)+C(V)`-small after enough
subdivisions. The geometric input to the `ι` isomorphism (the `{U,V}` cover of `U∪V` is global in the
subspace `sub(U∪V)`, so `exists_iterate_smallChains` applies there; push back along `chainIncl`). -/
theorem exists_iterate_mvUnion (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (c : SingularChain M n) (hc : c ∈ subspaceChains (U ∪ V) n) :
    ∃ m, (⇑(singularSd M n))^[m] c ∈ mvUnionChains U V n := by
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
  obtain ⟨m, hm⟩ := exists_iterate_smallChains hcov d
  have hnat : ∀ (k : ℕ) (d' : SingularChain (sub (U ∪ V)) n),
      (⇑(singularSd M n))^[k] (chainIncl (U ∪ V) n d')
        = chainIncl (U ∪ V) n ((⇑(singularSd (sub (U ∪ V)) n))^[k] d') := by
    intro k
    induction k with
    | zero => intro d'; rfl
    | succ j ih =>
      intro d'
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, singularSd_chainIncl]
  refine ⟨m, ?_⟩
  rw [hnat]
  exact chainIncl_mem_mvUnion_of_small U V n _ hm

open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision in
/-- **`ι` is surjective**: every relative `(U∪V)`-class has a small (`Q`-cycle) representative —
subdivide its boundary into `C(U)+C(V)` (`exists_iterate_mvUnion`), then `[c] = [Sdᵐc]`
(`relative_add_singularSd_iterate_mem_relBoundaries`). -/
theorem iota_surjective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Surjective (iota U V n) := by
  intro h
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  cases n with
  | zero =>
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChain (U ∪ V) 0)
    refine ⟨QHomology.mk U V 0 ⟨QChain.mk U V 0 c', Submodule.mem_top⟩, ?_⟩
    rw [iota_mk]
    refine congrArg (RelativeHomology.mk (U ∪ V) 0) (Subtype.ext ?_)
    show piMap U V 0 (QChain.mk U V 0 c') = (zc : RelativeChain (U ∪ V) 0)
    rw [piMap_mk]; exact hc'
  | succ k =>
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChain (U ∪ V) (k + 1))
    have hbdry : chainBoundary M k c' ∈ subspaceChains (U ∪ V) k := by
      have hz := LinearMap.mem_ker.mp zc.2
      rw [← hc', show (Submodule.Quotient.mk c' : RelativeChain (U ∪ V) (k + 1))
          = RelativeChain.mk (U ∪ V) (k + 1) c' from rfl, relBoundary_mk,
        RelativeChain.mk_eq_zero_iff] at hz
      exact hz
    obtain ⟨m, hm⟩ := exists_iterate_mvUnion U V hU hV k (chainBoundary M k c') hbdry
    have hqcyc : QChain.mk U V (k + 1) ((⇑(singularSd M (k + 1)))^[m] c') ∈ qCycles U V (k + 1) := by
      rw [show qCycles U V (k + 1) = LinearMap.ker (qBoundary U V k) from rfl, LinearMap.mem_ker,
        qBoundary_mk, QChain.mk_eq_zero_iff, singularSd_iterate_chainBoundary]
      exact hm
    refine ⟨QHomology.mk U V (k + 1) ⟨_, hqcyc⟩, ?_⟩
    rw [iota_mk]
    refine relHomology_mk_eq_of (k + 1) _ zc ?_
    show piMap U V (k + 1) (QChain.mk U V (k + 1) ((⇑(singularSd M (k + 1)))^[m] c'))
        - (zc : RelativeChain (U ∪ V) (k + 1)) ∈ relBoundaries (U ∪ V) (k + 1)
    rw [piMap_mk, ← hc', sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
    have key := relative_add_singularSd_iterate_mem_relBoundaries hbdry m
    rwa [add_comm (RelativeChain.mk (U ∪ V) (k + 1) c')] at key

open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision in
/-- **`ι` is injective** (positive degree): a `Q`-cycle whose `(U∪V)`-image is a relative boundary is a
`Q`-boundary — push the boundary witness into `C(U)+C(V)` via the subdivision homotopy
(`iterHomotopy_chainHomotopy` + `exists_iterate_mvUnion`). -/
theorem iota_injective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Injective (iota U V (k + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _ (z : QChain U V (k + 1))
  rw [show (Submodule.Quotient.mk z : QHomology U V (k + 1)) = QHomology.mk U V (k + 1) z from rfl,
    iota_mk, RelativeHomology.mk_eq_zero_iff] at hx
  change piMap U V (k + 1) (z : QChain U V (k + 1)) ∈ relBoundaries (U ∪ V) (k + 1) at hx
  rw [show piMap U V (k + 1) (z : QChain U V (k + 1)) = RelativeChain.mk (U ∪ V) (k + 1) zc by
    rw [← hzc]; rfl] at hx
  obtain ⟨W, hW⟩ := hx
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ W
  have hzcw : zc + chainBoundary M (k + 1) w ∈ subspaceChains (U ∪ V) (k + 1) := by
    rw [← RelativeChain.mk_eq_zero_iff,
      show RelativeChain.mk (U ∪ V) (k + 1) (zc + chainBoundary M (k + 1) w)
        = RelativeChain.mk (U ∪ V) (k + 1) zc
          + relBoundary (U ∪ V) (k + 1) (RelativeChain.mk (U ∪ V) (k + 2) w) from rfl,
      show RelativeChain.mk (U ∪ V) (k + 2) w = W from hw, hW, ZModModule.add_self]
  have hzc_cyc : chainBoundary M k zc ∈ mvUnionChains U V k := by
    have hq : qBoundary U V k (z : QChain U V (k + 1)) = 0 := LinearMap.mem_ker.mp z.2
    rw [← hzc, show (Submodule.Quotient.mk zc : QChain U V (k + 1)) = QChain.mk U V (k + 1) zc from rfl,
      qBoundary_mk, QChain.mk_eq_zero_iff] at hq
    exact hq
  set y := zc + chainBoundary M (k + 1) w with hy_def
  have hdy : chainBoundary M k y ∈ mvUnionChains U V k := by
    rw [hy_def, map_add, chainBoundary_chainBoundary_apply, add_zero]; exact hzc_cyc
  obtain ⟨m, hm⟩ := exists_iterate_mvUnion U V hU hV (k + 1) y hzcw
  have hDdy : iterHomotopy M k m (chainBoundary M k y) ∈ mvUnionChains U V (k + 1) := by
    rw [show mvUnionChains U V (k + 1) = smallChains ({U, V} : Set (Set ↑M)) (k + 1) from
      (smallChains_two_eq U V (k + 1)).symm]
    refine iterHomotopy_mem_smallChains ?_ m
    rw [show smallChains ({U, V} : Set (Set ↑M)) k = mvUnionChains U V k from smallChains_two_eq U V k]
    exact hdy
  have hh := iterHomotopy_chainHomotopy M m k y
  have h2 : chainBoundary M (k + 1) (iterHomotopy M (k + 1) m y)
      = y + (⇑(singularSd M (k + 1)))^[m] y + iterHomotopy M k m (chainBoundary M k y) := by
    rw [← hh, add_assoc (chainBoundary M (k + 1) (iterHomotopy M (k + 1) m y)),
      ZModModule.add_self (iterHomotopy M k m (chainBoundary M k y)), add_zero]
  -- the key chain identity: zc + ∂(Dₘy + w) = Sdᵐy + Dₘ(∂y) ∈ C(U)+C(V)
  have hident : zc + chainBoundary M (k + 1) (iterHomotopy M (k + 1) m y + w)
      ∈ mvUnionChains U V (k + 1) := by
    rw [map_add, h2,
      show zc + (y + (⇑(singularSd M (k + 1)))^[m] y + iterHomotopy M k m (chainBoundary M k y)
          + chainBoundary M (k + 1) w)
        = (zc + chainBoundary M (k + 1) w + y) + ((⇑(singularSd M (k + 1)))^[m] y
          + iterHomotopy M k m (chainBoundary M k y)) by abel,
      ← hy_def, ZModModule.add_self y, zero_add]
    exact Submodule.add_mem _ hm hDdy
  rw [show (Submodule.Quotient.mk z : QHomology U V (k + 1)) = QHomology.mk U V (k + 1) z from rfl,
    QHomology.mk_eq_zero_iff, ← hzc]
  refine ⟨QChain.mk U V (k + 2) (iterHomotopy M (k + 1) m y + w), ?_⟩
  rw [qBoundary_mk]
  show Submodule.Quotient.mk (chainBoundary M (k + 1) (iterHomotopy M (k + 1) m y + w))
      = Submodule.Quotient.mk zc
  rw [Submodule.Quotient.eq, sub_eq_add_neg,
    neg_eq_of_add_eq_zero_left (ZModModule.add_self zc),
    add_comm (chainBoundary M (k + 1) (iterHomotopy M (k + 1) m y + w)) zc]
  exact hident

/-- **The small-chains isomorphism** `ι : Hₙ₊₁(Q) ≅ Hₙ₊₁(M, U∪V)` (`U, V` open) — the projection
`π : C(M)/(C(U)+C(V)) ↠ C(M, U∪V)` is a homology isomorphism. Lets the relative MV LES be stated in
its textbook `Hₙ(M, U∪V)` form. -/
noncomputable def iotaEquiv (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    QHomology U V (k + 1) ≃ₗ[ZMod 2] RelativeHomology (U ∪ V) (k + 1) :=
  LinearEquiv.ofBijective (iota U V (k + 1))
    ⟨iota_injective U V hU hV k, iota_surjective U V hU hV (k + 1)⟩

/-! ### The textbook relative MV connecting map and exactness (`Hₙ(M, U∪V)` form) -/

/-- **The relative MV connecting map** `δ : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` in textbook form — the `Q`-form
connecting map `relConnecting` pulled back along the small-chains iso `ι`. -/
noncomputable def relMvDelta (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    RelativeHomology (U ∪ V) (k + 1) →ₗ[ZMod 2] RelativeHomology (U ∩ V) k :=
  (relConnecting U V k).comp (iotaEquiv U V hU hV k).symm.toLinearMap

/-- **Relative MV exactness at `Hₙ(M, U∩V)`** in textbook form: `range δ = ker(relMvHomDiag)`. The
gluing step of Hatcher 3.27 (`Hₙ₊₁(M,U∪V) = 0` ⟹ `Hₙ(M,U∩V) → Hₙ(M,U) ⊕ Hₙ(M,V)` injective). -/
theorem relMv_exact_connecting' (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Exact (relMvDelta U V hU hV k) (relMvHomDiag U V k) := by
  intro x
  rw [relMv_exact_connecting U V k x]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨iotaEquiv U V hU hV k y, ?_⟩
    rw [relMvDelta, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨(iotaEquiv U V hU hV k).symm y, rfl⟩

/-- **The `ι ∘ Σ_* = relMvHomSum` bridge**: the small-chains iso applied to the `Q`-form sum is the
textbook sum (72c-1, landing in `Hₙ(M, U∪V)`). -/
theorem iota_relMvHomSumQ (U V : Set ↑M) (n : ℕ)
    (p : RelativeHomology U n × RelativeHomology V n) :
    iota U V n (relMvHomSumQ U V n p) = relMvHomSum U V n p := by
  obtain ⟨pu, pv⟩ := p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ pu
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ pv
  rw [show relMvHomSumQ U V n (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
      = QHomology.mk U V n ⟨relMvChainSum U V n ((a : _), (b : _)),
          relMvChainSum_pair_mem_qCycles U V n a b⟩ from relMvHomSumQ_mk U V n a b, iota_mk,
    relMvHomSum, LinearMap.coprod_apply, relIncl, relIncl, RelativeHomology.map_mk,
    RelativeHomology.map_mk]
  refine congrArg (RelativeHomology.mk (U ∪ V) n) (Subtype.ext ?_)
  rw [AddMemClass.coe_add, relCyclesMap_coe, relCyclesMap_coe]
  show piMap U V n (relMvChainSum U V n ((a : RelativeChain U n), (b : RelativeChain V n)))
      = relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.subset_union_left hx) n
          (a : RelativeChain U n)
        + relMapChain (ContinuousMap.id ↑M) (fun _ hx => Set.subset_union_right hx) n
          (b : RelativeChain V n)
  obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _ (a : RelativeChain U n)
  obtain ⟨b', hb'⟩ := Submodule.Quotient.mk_surjective _ (b : RelativeChain V n)
  rw [← ha', ← hb',
    show (Submodule.Quotient.mk a' : RelativeChain U n) = RelativeChain.mk U n a' from rfl,
    show (Submodule.Quotient.mk b' : RelativeChain V n) = RelativeChain.mk V n b' from rfl,
    relMvChainSum_mk, relMapChain_id_mk, relMapChain_id_mk]
  rfl

/-- **Relative MV exactness at `Hₙ(M,U) ⊕ Hₙ(M,V)`** in textbook form: `range Δ_* = ker(relMvHomSum)`
(positive degree). Transported from the `Q`-form middle exactness through the iso `ι`. -/
theorem relMv_exact_middle' (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Exact (relMvHomDiag U V (k + 1)) (relMvHomSum U V (k + 1)) := by
  intro p
  constructor
  · intro hp
    refine (relMv_exact_middle U V (k + 1) p).mp ?_
    have h0 : iota U V (k + 1) (relMvHomSumQ U V (k + 1) p) = 0 := by
      rw [iota_relMvHomSumQ]; exact hp
    exact (iotaEquiv U V hU hV k).map_eq_zero_iff.mp h0
  · intro hp
    rw [← iota_relMvHomSumQ,
      show relMvHomSumQ U V (k + 1) p = 0 from (relMv_exact_middle U V (k + 1) p).mpr hp, map_zero]

end SKEFTHawking.SingularRelativeMV
