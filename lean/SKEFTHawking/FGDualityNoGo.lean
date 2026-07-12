/-
# Phase 5q.H (E1) — NO-GO: the ℤ-dual blow-up (the mod-2 Erdős–Kaplansky forcing does not transport to ℤ)

Kernel backing for the settled fork `5qH-fg-ek-over-Z-blocked` (SETTLED_FORKS, 2026-07-12; scout-verified
vs FNOP `1910.07372` + Blass–Göbel `math/9405206`): the mod-2 finiteness forcing
(`SingularUCFinite.finiteDimensional_of_linearEquiv_dual` — self-duality forces finite dimension, by
Erdős–Kaplansky) has NO ℤ-analog usable for `intH2_basis`. This module kernel-certifies the accessible
mechanism break — **the ℤ-dual blow-up**: the dual of the free ℤ-module of countably infinite rank
(`ℕ →₀ ℤ`, countable) is the Baer–Specker group `ℕ → ℤ` (uncountable, NOT finitely generated). So
"dualization stays in the size/f.g.-controllable class", the transport step the naive ℤ-mirror needs,
is FALSE over ℤ. The full literature refutation of the ℤ-EK statement itself — Specker's SELF-DUAL
non-f.g. group `(⊕ℤ) ⊕ ℤ^ℕ` — additionally needs slenderness of ℤ (`Hom(ℤ^ℕ,ℤ) ≅ ⊕ℤ`, Specker 1950;
Mathlib-absent); its formalization is queued, and the verdict file
`Lit-Search/Phase-5qH/FG_via_PD_duality_forcing_verdict_20260712.md` carries the citations.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.FGDualityNoGo

/-- **A finitely generated ℤ-module is countable** — the size bound the blow-up violates. (Span of a
finite family over the countable ring ℤ.) -/
theorem countable_of_finite_int_module (M : Type) [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] : Countable M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := M)
  have h : Countable ↥(Submodule.span ℤ (Set.range (fun x : ↥(s : Set M) => (x : M)))) :=
    Finsupp.instCountableSubtypeMemSubmoduleSpanRange _
  rw [Subtype.range_coe, hs] at h
  haveI := h
  exact Countable.of_equiv _ (Submodule.topEquiv (R := ℤ) (M := M)).toEquiv

/-- **The Baer–Specker group `ℕ → ℤ` is uncountable** — Cantor's diagonal (`g n := f n n + 1`). -/
theorem uncountable_baerSpecker : Uncountable (ℕ → ℤ) := by
  rw [uncountable_iff_forall_not_surjective]
  intro f hf
  obtain ⟨k, hk⟩ := hf (fun n => f n n + 1)
  have := congrFun hk k
  omega

/-- **The Baer–Specker group is not finitely generated over ℤ.** -/
theorem not_finite_baerSpecker : ¬ Module.Finite ℤ (ℕ → ℤ) := by
  intro h
  haveI := uncountable_baerSpecker
  exact not_countable (@countable_of_finite_int_module (ℕ → ℤ) _ _ h)

/-- **The ℤ-dual of the countable-rank free module IS the Baer–Specker group**:
`Dual ℤ (ℕ →₀ ℤ) ≃ₗ (ℕ → ℤ)` — evaluation on the standard basis (`Finsupp.lsum` + the
`ℤ →ₗ ℤ ≃ ℤ` collapse). -/
noncomputable def dualFinsuppEquivBaerSpecker :
    Module.Dual ℤ (ℕ →₀ ℤ) ≃ₗ[ℤ] (ℕ → ℤ) :=
  ((Finsupp.lsum ℤ).symm : Module.Dual ℤ (ℕ →₀ ℤ) ≃ₗ[ℤ] (ℕ → ℤ →ₗ[ℤ] ℤ)).trans
    (LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf ℤ ℤ ℤ)

/-- **THE ℤ-DUAL BLOW-UP (the registered no-go backing)** — the ℤ-dual of the free module of countably
infinite rank is NOT finitely generated: `¬ Module.Finite ℤ (Dual ℤ (ℕ →₀ ℤ))`. The source `ℕ →₀ ℤ` is
COUNTABLE free; its dual is the UNCOUNTABLE Baer–Specker group. This kernel-refutes the transport step
("dualization preserves the f.g./size class") that any ℤ-mirror of the mod-2 Erdős–Kaplansky finiteness
forcing (`SingularUCFinite`) would require — the settled fork `5qH-fg-ek-over-Z-blocked`. Falsifiable
and non-vacuous: over a FIELD the analogous dual of `ℕ →₀ K` is likewise big, but there the EK theorem
turns the blow-up into a POSITIVE forcing; over ℤ Specker's self-dual `(⊕ℤ) ⊕ ℤ^ℕ` (literature; see the
module docstring) kills the forcing itself. -/
theorem dual_blowup_not_finite : ¬ Module.Finite ℤ (Module.Dual ℤ (ℕ →₀ ℤ)) := by
  intro h
  exact not_finite_baerSpecker (Module.Finite.equiv dualFinsuppEquivBaerSpecker)

/-- The contrast half: the SOURCE `ℕ →₀ ℤ` is countable (finitely supported functions over countable
data) — so dualization genuinely ESCAPES the countable class. -/
theorem countable_finsuppNatInt : Countable (ℕ →₀ ℤ) := by infer_instance

end SKEFTHawking.FGDualityNoGo
