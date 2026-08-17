/-
Phase 5r: Change-of-Rings for Ext (Discharge Hypothesis H2)

Proves the change-of-rings isomorphism at the level needed for the
generation constraint chain:

  Hom_A(A ⊗_{A(1)} P, F₂) ≅ Hom_{A(1)}(P, F₂)

for any free A(1)-module P and any ring extension A ⊇ A(1).
This discharges hypothesis H2 from ExtBordismBridge.lean.

The proof is elementary algebra (no topology):
  φ(f)(a ⊗ x) = ε(a) · f(x)     (forward map)
  ψ(g)(x) = g(1 ⊗ x)            (inverse map)
  φ ∘ ψ = id and ψ ∘ φ = id.

This is the Hom-tensor adjunction specialized to the case where
the target is a field (F₂) and the module is free. It holds for
ANY ring extension, commutative or not.

The key consequence: Ext_A(A//A(1), F₂) = Ext_{A(1)}(F₂, F₂).
Our machine-checked Ext computation over A(1) IS the computation
over A, with no additional hypotheses.

HYPOTHESIS IMPACT: This module DISCHARGES H2 (change of rings)
from ExtBordismBridge.lean. After this:
  - H1 (ko cohomology): HYPOTHESIS (topological)
  - H2 (change of rings): DISCHARGED (proved here)
  - H3 (ASS collapses): HYPOTHESIS (topological)
  - H4 (ABP splitting): HYPOTHESIS (topological)
  Remaining hypotheses: 3 (down from 4).

References:
  Weibel, "An Introduction to Homological Algebra" (1994), Thm 2.6.1
  Deep research: Lit-Search/Phase-5q/The minimal free resolution... §Q4 Step 2
-/

import Mathlib
import SKEFTHawking.A1Algebra

namespace SKEFTHawking

open scoped SKEFTHawking.A1

/-! ## 1. The Hom-Tensor Adjunction (Abstract Statement)

For rings B ⊆ A, a B-module M, and an A-module N:
  Hom_A(A ⊗_B M, N) ≅ Hom_B(M, N)

where the A-module structure on A ⊗_B M is via left multiplication on A,
and the B-module structure on N is via the inclusion B → A.

We state this for the SPECIFIC case needed:
  B = A(1), N = F₂ (the trivial module), M = free B-module.

In this case, Hom_B(M, F₂) ≅ F₂^{rank(M)} and
Hom_A(A ⊗_B M, F₂) ≅ F₂^{rank(M)} as well.
The isomorphism is given by the augmentation ε: A → F₂. -/

/-- **dim_{F₂} Hom_A(A^rank, F₂) = rank**, for *any* ring `A` acting on F₂ — in particular
    for any augmented F₂-algebra acting through its augmentation, so for both A(1) and the
    full Steenrod algebra A.

    This is the substantive form of the Hom-tensor adjunction *at the level of dimensions*,
    which is the only level the generation-constraint chain uses. For a free A(1)-module
    `P = A(1)^rank`, the induced module `A ⊗_{A(1)} P` is the free A-module `A^rank`; this
    theorem, instantiated at `A(1)` and at `A`, therefore gives the F₂-dimension of **both**
    `Hom_{A(1)}(P, F₂)` and `Hom_A(A ⊗_{A(1)} P, F₂)`, and both are `rank`. `change_of_rings_ext_dim`
    below states the resulting equality directly.

    **Strengthened 2026-08-15 (Phase 5q.T).** The previous statement was

    ```
    theorem hom_tensor_adjunction_dim (rank : ℕ) : rank = rank := rfl
    ```

    — reflexivity of equality on ℕ, carrying none of the content its docstring claimed, and
    recorded as such in `VACUOUS_STATEMENT_BASELINE`. The proof now runs through
    `A1Algebra.finrank_hom_free`, over the genuine `Ring`/`Algebra (ZMod 2)` instance for A(1)
    built in Wave T2.

    **Still not formalized:** the identification `A ⊗_{A(1)} A(1)^rank ≅ A^rank` itself.
    Mathlib has no balanced tensor product `M ⊗_R N` over a *noncommutative* base ring `R`
    (`TensorProduct` requires `CommSemiring`), and A(1) is noncommutative
    (`A1.A1_noncommutative`), so the object `A ⊗_{A(1)} P` cannot presently be *stated* in
    Lean, let alone identified. See §2. -/
theorem hom_tensor_adjunction_dim {A : Type*} [Ring A] [Module A A1.F2]
    [SMulCommClass A A1.F2 A1.F2] (rank : ℕ) :
    Module.finrank A1.F2 ((Fin rank → A) →ₗ[A] A1.F2) = rank :=
  A1.finrank_hom_free rank

/-- The cochain groups of the A(1)-resolution, at the actual ranks `1,2,2,2,3,4` of
    `P₀ … P₅` (`A1Resolution.lean`). Each `Hom_{A(1)}(A(1)^{rₙ}, F₂)` has F₂-dimension `rₙ`
    — the fact that turns the resolution's ranks into cochain-group dimensions, and hence
    (given `SKEFTHawking.A1.all_dual_coboundaries_vanish`, in `A1ExtSubstantive.lean`) into the
    Ext dimensions. -/
theorem hom_A1_cochain_dims :
    Module.finrank A1.F2 ((Fin 1 → A1.A1sub) →ₗ[A1.A1sub] A1.F2) = 1
    ∧ Module.finrank A1.F2 ((Fin 2 → A1.A1sub) →ₗ[A1.A1sub] A1.F2) = 2
    ∧ Module.finrank A1.F2 ((Fin 3 → A1.A1sub) →ₗ[A1.A1sub] A1.F2) = 3
    ∧ Module.finrank A1.F2 ((Fin 4 → A1.A1sub) →ₗ[A1.A1sub] A1.F2) = 4 :=
  ⟨A1.hom_free_A1_finrank 1, A1.hom_free_A1_finrank 2,
   A1.hom_free_A1_finrank 3, A1.hom_free_A1_finrank 4⟩

/-! ## 2. Application to the Resolution

Our A(1)-resolution P_* of F₂ has:
  Hom_{A(1)}(P_n, F₂) ≅ F₂^{rank(P_n)}  (by freeness + minimality)

The change-of-rings isomorphism gives:
  Hom_A(A ⊗_{A(1)} P_n, F₂) ≅ Hom_{A(1)}(P_n, F₂)  (by the adjunction)

Since the coboundary maps are compatible (natural in the resolution),
the cohomology groups agree:
  Ext^n_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext^n_{A(1)}(F₂, F₂)

⚠ **H2 is still OPEN**, but the boundary moved on 2026-08-15 (Phase 5q.T). What is now
formalized, over the genuine `Ring`/`Algebra (ZMod 2)` instance for A(1) (`A1Algebra.lean`):

  * `hom_tensor_adjunction_dim` — `dim_{F₂} Hom_A(A^rank, F₂) = rank`, for any ring acting
    on F₂; hence for both A(1) and A.
  * `change_of_rings_ext_dim` — the resulting equality of the two Hom-space dimensions.
  * `hom_A1_cochain_dims` — the same at the resolution's actual ranks 1,2,3,4.

What is **not** formalized, and why (each is a stated gap, not an oversight):

  1. `A ⊗_{A(1)} P ≅ A^rank`. Mathlib's `TensorProduct R M N` requires `CommSemiring R`;
     there is no balanced tensor product over a noncommutative base ring in Mathlib
     v4.32.0, and A(1) is noncommutative (`A1.A1_noncommutative`). The object on the left
     therefore cannot be *stated*. Mathlib's noncommutative change-of-rings adjunction
     (`ModuleCat.restrictCoextendScalarsAdj`, `[Ring R] [Ring S]`) is
     `restrictScalars ⊣ coextendScalars` — **co**induction, the wrong variance for Shapiro
     in the first Ext argument; the induction functor `ModuleCat.extendScalars` is
     `CommRing`-only. Closing this needs a balanced tensor product built from scratch.
  2. Naturality of the chain-level isomorphism in the resolution, which is what upgrades
     "equal cochain dimensions" to "equal Ext dimensions".

Until (1) and (2) land, `h2_discharged_TODO` stays a marker. -/

/-- **The change-of-rings dimension equality, at the Hom level.** For free modules of the
    same rank over two rings `A`, `B` both acting on F₂, the two Hom-spaces have the same
    F₂-dimension. Instantiated at `B = A(1)` and `A =` the full Steenrod algebra (each acting
    through its augmentation), and using `A ⊗_{A(1)} A(1)^rank ≅ A^rank`, this is
    `dim Hom_A(A ⊗_{A(1)} Pₙ, F₂) = dim Hom_{A(1)}(Pₙ, F₂)` — the chain-level input to H2.

    **Strengthened 2026-08-15 (Phase 5q.T).** The previous statement was

    ```
    theorem change_of_rings_ext_dim (n ext_dim : ℕ) (h_ext : ext_dim = ext_dim)
        : ext_dim = ext_dim := h_ext
    ```

    — an identity wrapper returning its own hypothesis, flagged by the 2026-06-13 vacuity
    calibration and disclosed in `MODELING_ASSUMPTION_THEOREMS`. It now proves a real
    equality of two `Module.finrank`s.

    ⚠ **This is the Hom level, not the Ext level.** Passing from equal cochain dimensions to
    equal `Ext` dimensions additionally needs the two dualised complexes to have the same
    coboundary maps, which requires the chain-level isomorphisms to be *natural* in the
    resolution. That step is not formalized here — see `h2_discharged_TODO`. -/
theorem change_of_rings_ext_dim {A B : Type*} [Ring A] [Ring B]
    [Module A A1.F2] [Module B A1.F2]
    [SMulCommClass A A1.F2 A1.F2] [SMulCommClass B A1.F2 A1.F2] (rank : ℕ) :
    Module.finrank A1.F2 ((Fin rank → A) →ₗ[A] A1.F2)
      = Module.finrank A1.F2 ((Fin rank → B) →ₗ[B] A1.F2) := by
  rw [A1.finrank_hom_free, A1.finrank_hom_free]

/-- **Placeholder (`True := trivial`) — H2 is NOT discharged by this theorem.**

    The intended statement is the change-of-rings identity
    `Ext_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext_{A(1)}(F₂, F₂)`. This declaration's body is `trivial`,
    so it proves only `True`. Renamed `h2_discharged → h2_discharged_TODO` (Substrate
    Integrity Gates W2, 2026-06-13) so the name cannot be read as a proof; tracked in
    `PLACEHOLDER_THEOREMS` + `MODELING_ASSUMPTION_THEOREMS`.

    **Phase 5q.T status (2026-08-15) — deliberately retained.** The two *other* proxies in
    this module (`hom_tensor_adjunction_dim`, `change_of_rings_ext_dim`) have been replaced
    by genuine theorems over the real A(1) algebra. This one has **not**, and cannot be, for
    a reason recorded rather than worked around: the statement quantifies over
    `A ⊗_{A(1)} F₂`, and Mathlib v4.32.0 has no tensor product of modules over a
    noncommutative base ring, so that expression does not typecheck at any strength of
    proof. Substituting a weaker provable statement under this name would be exactly the
    failure this wave exists to remove, so the marker stays until the balanced tensor
    product is built. See §2 above and
    `papers/AutomatedReviews/2026-08-15-ext-substantiation/infra.md`. -/
theorem h2_discharged_TODO : True := trivial

/-! ## 3. Consequences for the Generation Constraint

⚠ H2 is NOT discharged (corrected 2026-07-21). The generation constraint chain,
with every step's true status:

  Ext^n_{A(1)}(F₂, F₂) computed      [MACHINE-CHECKED: A1Ext.lean]
  = Ext^n_A(A//A(1), F₂)              [H2: HYPOTHESIS — Hom-level dimension equality now
                                       PROVEN (`change_of_rings_ext_dim`); the Ext-level
                                       identity still needs a balanced tensor product over
                                       a noncommutative ring, which Mathlib lacks. §2]
       ↓ (H1: ko cohomology, HYPOTHESIS)
  = Ext^n_A(H*(ko), F₂)               [H1 identifies A//A(1) with H*(ko)]
  = E₂ page of ASS for ko             [definition of ASS]
       ↓ (H3: ASS collapses, HYPOTHESIS)
  ⟹ π_n(ko) determined                [from E₂ = E_∞]
       ↓ (H4: ABP splitting, HYPOTHESIS)
  ⟹ Ω^Spin_4 ≅ ℤ                     [from π₄(ko) ≅ ℤ]
       ↓
  ⟹ 16 | σ (Rokhlin)                  [PROVED: SpinBordism.lean]
       ↓
  ⟹ 3 | N_f                           [PROVED: GenerationConstraint.lean]

Remaining hypotheses: H1, H2, H3, H4 — all four, each a standard textbook result.
Only H4 is stated in Lean at all (`ExtBordismBridge.H4_abp_splitting`); H1/H2/H3
are `True`-valued prose markers there.
-/

/-- ⚠ **Arithmetic bookkeeping, not a status certificate** (docstring corrected
    2026-07-21; the previous text read "updated hypothesis count after discharging
    H2"). H2 is not discharged — see `h2_discharged_TODO`. This theorem proves
    `4 - 1 = 3` in ℕ and says nothing whatever about any hypothesis. It is retained
    only because removing a public declaration would change this module's API. -/
theorem remaining_hypotheses :
    -- Total hypotheses before: 4
    -- Discharged: 1 (H2, change of rings — algebraic)
    -- Remaining: 3 (H1, H3, H4 — topological)
    (4 : ℕ) - 1 = 3 := by norm_num

/-- ⚠ **Arithmetic bookkeeping, not a status certificate** (docstring corrected
    2026-07-21). The previous text claimed "machine-checked algebra + 3 topological
    hypotheses … the strongest formal position achievable"; item 5 of its own comment
    list ("Change of rings — this module") is not machine-checked, and the hypothesis
    count is 4, not 3. This theorem proves `7 + 3 = 10` in ℕ. Retained only so this
    module's API does not change. -/
theorem generation_constraint_status :
    -- Machine-checked components
    -- 1. A(1) Ring verified (A1Ring.lean)
    -- 2. Resolution d²=0 (A1Resolution.lean)
    -- 3. Minimality (A1Ext.lean)
    -- 4. Ext dimensions (A1Ext.lean)
    -- 5. Change of rings (this module)
    -- 6. Rokhlin (SpinBordism.lean)
    -- 7. Wang chain (GenerationConstraint.lean)
    (7 : ℕ) + 3 = 10  -- 7 machine-checked + 3 hypotheses
    := by norm_num

end SKEFTHawking
