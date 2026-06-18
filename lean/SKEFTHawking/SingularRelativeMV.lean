import Mathlib
import SKEFTHawking.SingularRelativeFunctoriality

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

end SKEFTHawking.SingularRelativeMV
