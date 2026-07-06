/-
# Phase 5q.H (E1 integral topology) — Q-cohomology (cohomology of cochains vanishing on the small chains)

`QCohomologyInt U V n = Hⁿ` of the cochain complex `Cⁿ_Q = {f : Cⁿ(M;ℤ) | ⟨f, c⟩ = 0 ∀ c ∈ mvUnion}` where
`mvUnion = mvUnionChainsInt = C(U)+C(V)` (the small chains). Under the pairing `f ↦ ⟨f, ·⟩` this is
`Hⁿ(Hom(QChainInt, ℤ))` — the cohomology of the small-chains quotient complex. Structural mirror of
`SingularEuclideanCapIsoInt.RelativeCohomologyInt`, with `mvUnionChainsInt U V` in place of the single-set
`subspaceChainsInt S` (the coboundary preserves `C_Q` because `∂(mvUnion) ⊆ mvUnion`,
`chainBoundary_mem_mvUnionChainsInt`).

This is the codomain of the class `[χ']` in the relative-cohomology Mayer–Vietoris connecting snake; the dual
excision iso `QCohomologyInt(U∪V) ≅ RelativeCohomologyInt(U∪V)` (from the acyclic K-complex — the `(B)`-node's
`SingularKComplexAcyclicInt.hom_K_cocycle_eq_coboundary` + `exists_lift_cochain`) then lands the connecting map
in `RelativeCohomologyInt(U∪V)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularQCohomologyInt

variable {M : TopCat}

/-- **Q-cochains** `Cⁿ_Q`: integral `n`-cochains vanishing on the small chains `mvUnion = C(U)+C(V)`. The
annihilator of `mvUnionChainsInt U V n` under the Kronecker pairing (= `Hom(QChainInt U V n, ℤ)`). -/
def mvUnionCochainsInt (U V : Set ↑M) (n : ℕ) : Submodule ℤ (SingularCochainInt M n) where
  carrier := { f | ∀ c ∈ mvUnionChainsInt U V n, kronecker f c = 0 }
  zero_mem' := by
    intro c _
    simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
  add_mem' {f g} hf hg := by
    intro c hc
    rw [kronecker_add_left, hf c hc, hg c hc, add_zero]
  smul_mem' s f hf := by
    intro c hc
    rw [kronecker_smul_left, hf c hc, smul_zero]

theorem mem_mvUnionCochainsInt (U V : Set ↑M) (n : ℕ) (f : SingularCochainInt M n) :
    f ∈ mvUnionCochainsInt U V n ↔ ∀ c ∈ mvUnionChainsInt U V n, kronecker f c = 0 :=
  Iff.rfl

/-- **The coboundary preserves Q-cochains** (adjunction + `∂(mvUnion) ⊆ mvUnion`). -/
theorem coboundary_mem_mvUnionCochainsInt (U V : Set ↑M) (n : ℕ) (f : SingularCochainInt M n)
    (hf : f ∈ mvUnionCochainsInt U V n) : coboundary M n f ∈ mvUnionCochainsInt U V (n + 1) := by
  intro c hc
  rw [kronecker_coboundary_chainBoundary]
  exact hf _ (chainBoundary_mem_mvUnionChainsInt U V n c hc)

/-- **The Q-coboundary** `δⁿ_Q : Cⁿ_Q →ₗ Cⁿ⁺¹_Q`. -/
noncomputable def qCoboundaryIntₗ (U V : Set ↑M) (n : ℕ) :
    mvUnionCochainsInt U V n →ₗ[ℤ] mvUnionCochainsInt U V (n + 1) :=
  ((coboundaryₗ M n).domRestrict (mvUnionCochainsInt U V n)).codRestrict
    (mvUnionCochainsInt U V (n + 1)) (fun f => coboundary_mem_mvUnionCochainsInt U V n f.1 f.2)

@[simp] theorem qCoboundaryIntₗ_coe (U V : Set ↑M) (n : ℕ) (f : mvUnionCochainsInt U V n) :
    (qCoboundaryIntₗ U V n f : SingularCochainInt M (n + 1)) = coboundary M n f.1 := rfl

/-- The submodule of Q-coboundaries, `⊥` in degree `0`. -/
noncomputable def qCoboundaryRangeInt (U V : Set ↑M) (n : ℕ) :
    Submodule ℤ (mvUnionCochainsInt U V n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (qCoboundaryIntₗ U V m)

/-- Q-coboundaries are Q-cocycles, `im δⁿ⁻¹ ≤ ker δⁿ`. -/
theorem qCoboundaryRangeInt_le_ker (U V : Set ↑M) (n : ℕ) :
    qCoboundaryRangeInt U V n ≤ LinearMap.ker (qCoboundaryIntₗ U V n) := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    show LinearMap.range (qCoboundaryIntₗ U V m) ≤ LinearMap.ker (qCoboundaryIntₗ U V (m + 1))
    rw [LinearMap.range_le_ker_iff]
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    show coboundary M (m + 1) (coboundary M m g.1) = 0
    exact coboundary_comp_coboundary M m g.1

/-- **Integral Q-cohomology** `QCohomologyInt U V n = ker δⁿ_Q / im δⁿ⁻¹_Q`. -/
def QCohomologyInt (U V : Set ↑M) (n : ℕ) : Type :=
  (LinearMap.ker (qCoboundaryIntₗ U V n)) ⧸
    (qCoboundaryRangeInt U V n).submoduleOf (LinearMap.ker (qCoboundaryIntₗ U V n))

noncomputable instance (U V : Set ↑M) (n : ℕ) : AddCommGroup (QCohomologyInt U V n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (U V : Set ↑M) (n : ℕ) : Module ℤ (QCohomologyInt U V n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The Q-cohomology class of a Q-cocycle. -/
noncomputable def QCohomologyInt.mk (U V : Set ↑M) (n : ℕ)
    (z : LinearMap.ker (qCoboundaryIntₗ U V n)) : QCohomologyInt U V n :=
  Submodule.Quotient.mk z

theorem QCohomologyInt.mk_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (QCohomologyInt.mk U V n) :=
  Submodule.Quotient.mk_surjective _

theorem QCohomologyInt.mk_eq_zero_iff (U V : Set ↑M) (n : ℕ)
    (z : LinearMap.ker (qCoboundaryIntₗ U V n)) :
    QCohomologyInt.mk U V n z = 0 ↔
      z ∈ (qCoboundaryRangeInt U V n).submoduleOf (LinearMap.ker (qCoboundaryIntₗ U V n)) :=
  Submodule.Quotient.mk_eq_zero _

end SKEFTHawking.SingularQCohomologyInt
