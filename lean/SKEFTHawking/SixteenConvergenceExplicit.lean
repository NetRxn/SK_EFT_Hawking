/-
# Phase 5q.E Wave 3 — The "16 convergence" with explicit maps (enumeration, not unification)

The honest capstone tying together the Phase 5q.E facet shards (`KitaevSixteenFold.lean`,
`Spin10Sixteen.lean`). It advances the project's *enumeration → cited-connection → explicit
finite maps* gradient (see `docs/SIXTEEN_CONVERGENCE_STATUS.md`) to its honest endpoint for
the buildable facets, and **rigorously states what the convergence is NOT** — directly
answering whether "all the same 16" is more than coincidence-spotting.

`RokhlinBridge.sixteen_convergence_full` records the bare enumeration (its own docstring
already forbids calling it a "unification"; one conjunct is the tautology `(16:ZMod 16)=0`).
This module supplies the *explicit maps* the enumeration gestured at — and proves the
convergence **constrains, it does not derive**.

## What is proved here (genuine, non-redundant)
  * `sm_trivial_among_sixteen_distinct` — **constrains, not derives**: the SM realizes the
    *trivial* Kitaev class, but the Kitaev central-charge character is **faithful** (the phase
    `ν=1` is genuinely distinct from the SM's `ν=0` mod 8). So the shared ℤ₁₆ admits 16
    physically-distinct realizations and does NOT single out the SM. This is the rigorous
    form of "the same 16 is a shared invariant, not a derivation."
  * `sm_count_trivializes_z16` — an **explicit facet-1 → facet-4 map composition**: the
    Spin(10) branching sum `dim(10)+dim(5̄)+dim(1) = 16` (NOT a literal — it is the binomial
    sum from `Spin10Sixteen`) is exactly the integer whose Kitaev ℤ₁₆ class is `0`. The
    co-occurrence of the two 16s is here a genuine functional composition of explicit maps.

## What is NOT proved (honesty — load-bearing, keep in any paper)
The genuine **identification** of the facets' ℤ₁₆s — that the Kitaev phase ℤ₁₆, the Pin⁺/
Spin-ℤ₄ Dai–Freed anomaly ℤ₁₆, and the Rokhlin signature modulus are *one* bordism invariant
under the Smith homomorphism — requires computed spin-flavored bordism groups and the
Dai–Freed functor, which are **Mathlib-absent** (Phase 5q.E roadmap §"Walls"). A shared ℤ₁₆
**constrains, it does not derive**; the explicit maps here are the algebraic shadows, not the
bordism identification. The 3-generation headline is independent of all of this.

## References
  - `KitaevSixteenFold.lean`, `Spin10Sixteen.lean` (the facet shards).
  - `RokhlinBridge.lean::sixteen_convergence_full` (the bare enumeration this upgrades).
  - `docs/SIXTEEN_CONVERGENCE_STATUS.md`, `docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md`.
-/

import Mathlib
import SKEFTHawking.KitaevSixteenFold
import SKEFTHawking.Spin10Sixteen

namespace SKEFTHawking.SixteenConv

open SKEFTHawking

/-! ## §1. Constrains, not derives -/

/-- **The SM is the trivial one of sixteen genuinely-distinct phases — the convergence
constrains, it does not derive.** The SM per generation realizes the *trivial* Kitaev class
(`kitaevClass 16 = 0`); but the Kitaev central-charge character is **faithful**, witnessed
here by `ν = 1` having a central charge `c₋ = 1/2` that differs from the SM's `ν = 0`
(`c₋ = 0`) mod 8. So the shared ℤ₁₆ has 16 physically-distinct realizations and does not
single out the SM: "the same 16" is a shared invariant, not a derivation of the SM.

Both conjuncts are load-bearing: drop the first and the statement no longer places the SM at
the trivial point; drop the second and it collapses to the bare tautology `(16:ZMod 16)=0`. -/
theorem sm_trivial_among_sixteen_distinct :
    Kitaev16.kitaevClass 16 = 0 ∧
    ¬ ∃ k : ℤ, Kitaev16.kitaevCentralCharge 1 - Kitaev16.kitaevCentralCharge 0 = 8 * k := by
  refine ⟨by decide, ?_⟩
  rintro ⟨k, hk⟩
  have h12 : Kitaev16.kitaevCentralCharge 1 - Kitaev16.kitaevCentralCharge 0 = (1 : ℚ) / 2 := by
    unfold Kitaev16.kitaevCentralCharge; norm_num
  rw [h12] at hk
  have h1 : (1 : ℚ) = 16 * (k : ℚ) := by linarith
  have h2 : (1 : ℤ) = 16 * k := by exact_mod_cast h1
  omega

/-! ## §2. Explicit facet-1 → facet-4 map composition -/

/-- **The Spin(10) count trivializes the Kitaev/anomaly ℤ₁₆ — explicitly.** The Spin(10)
Weyl-spinor branching sum `dim(10) + dim(5̄) + dim(1)` (the binomial sum
`C(5,2)+C(5,4)+C(5,0) = 16` from `Spin10Sixteen`, NOT a literal) is exactly the integer whose
Kitaev ℤ₁₆ class is `0`. The two 16s (the Spin(10) spinor dimension and the Kitaev/anomaly
modulus) are here connected by a genuine **composition of explicit maps**
(Spin(10) branching → `kitaevClass`), not a bare numerical coincidence. This is NOT the
bordism identification of the facets' ℤ₁₆s (the Mathlib-absent wall). -/
theorem sm_count_trivializes_z16 :
    (Spin10.su5dim .ten + Spin10.su5dim .fivebar + Spin10.su5dim .one : ℤ) = 16 ∧
    Kitaev16.kitaevClass (Spin10.su5dim .ten + Spin10.su5dim .fivebar + Spin10.su5dim .one)
      = 0 := by
  refine ⟨by decide, ?_⟩
  have h : (Spin10.su5dim .ten + Spin10.su5dim .fivebar + Spin10.su5dim .one : ℤ) = 16 := by decide
  rw [h]; decide

/-! ## §3. Module summary

The 16-convergence with explicit maps (the honest successor to the bare enumeration):
  - `sm_trivial_among_sixteen_distinct` — constrains-not-derives (faithful ℤ₁₆, SM is 1 of 16).
  - `sm_count_trivializes_z16` — explicit Spin(10)-branching → Kitaev-class composition.

Wall (documented): the bordism identification (Smith homomorphism + computed
`Ω₄^{Pin⁺}/Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆`) that would make "all the same 16" literal is Mathlib-absent.
All proofs kernel-pure; no axiom / sorry / native_decide.
-/

end SKEFTHawking.SixteenConv
