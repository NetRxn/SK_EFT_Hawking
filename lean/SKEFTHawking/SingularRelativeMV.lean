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

/-- The **third-term chains** `Q_n = C_n(M) / (C_n(U)+C_n(V))`. -/
def QChain (U V : Set ↑M) (n : ℕ) : Type := SingularChain M n ⧸ mvUnionChains U V n

noncomputable instance (U V : Set ↑M) (n : ℕ) : AddCommGroup (QChain U V n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (U V : Set ↑M) (n : ℕ) : Module (ZMod 2) (QChain U V n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

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
  ext c
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

end SKEFTHawking.SingularRelativeMV
