import SKEFTHawking.Basic
import SKEFTHawking.HeatKernelExpansion
import SKEFTHawking.MicroscopicCoefficientMatch
import SKEFTHawking.BHEntropyMicroscopic
import Mathlib

/-!
# Frolov–Fursaev induced-gravity 1/4 — Phase 6a Wave 9 (center-bridge C)

Closes **Gate A.2**: derive the Bekenstein–Hawking leading coefficient `1/(4 G_N)` in the
ADW Sakharov induced-gravity substrate WITHOUT γ-tuning. The conditional
`frolov_fursaev_quarter_coefficient` is, per the deep-research verdict
(`Lit-Search/Phase-6a/6a-Immirzi-area-gap-independence-for-Wave8.md`):

  `H_Sakharov (G_N fully induced) ∧ (S_BH = S_ent) ∧ (S_ent = Frolov–Fursaev a₂ form) ⟹ S_BH = A/(4 G_N)`.

**Anti-vacuity (strengthening checklist #5).** NONE of the three antecedents is `S = A/4G`:
(i) the Sakharov induction condition `G_N = G_N_from_a2 = 12π/(N_f Λ²)` (no bare action;
`HeatKernelExpansion`); (ii) the entanglement identification `S_BH = S_ent` (Sorkin–Bombelli);
(iii) the Frolov–Fursaev–Zelnikov / Susskind–Uglum heat-kernel result
`S_ent = (N_f Λ²/(48π))·A`. The `1/4` is the ratio `48 : 12 = 4 : 1` — the SAME Seeley–DeWitt
`a₂` coefficient fixes both the induced `G_N` (EH, `12π`) and the horizon entanglement entropy
(`48π`), and their ratio is exactly 4. So the `1/4` emerges algebraically, not by tuning γ
(Bianchi arXiv:1204.5122 corroborates γ-independence; the LQG counting `−3/2` is Wave 7B).

**Modeling note (checklist #5, honest input).** The conical-deficit replica derivation of the
`48π` prefactor is not formalized (Mathlib lacks conical heat kernels); it enters as a NAMED,
CITABLE, FALSIFIABLE physical input — a hypothesis, NOT an axiom. `frolov_fursaev_falsifier_wrong_coeff`
shows the coefficient is load-bearing: any `c ≠ N_f Λ²/(48π)` breaks the `A/(4G)` match.

Refs: Frolov–Fursaev–Zelnikov, Nucl. Phys. B 486 (1997), hep-th/9607104; Susskind–Uglum,
hep-th/9401070; Jacobson, gr-qc/9404039.
-/

namespace SKEFTHawking
namespace InducedGravityEntropy

open Real

/--
**Frolov–Fursaev horizon entanglement-entropy area density.** The leading (area-law)
entanglement entropy of `N_f` Dirac fermions across the horizon, from the Seeley–DeWitt `a₂`
heat-kernel coefficient (conical-deficit replica trick): `S_ent = (N_f Λ²/(48π))·A`. The
coefficient is the FFZ/Susskind–Uglum result — the SAME `a₂` that induces `G_N`
(`HeatKernelExpansion.G_N_from_a2 = 12π/(N_f Λ²)`), with the heat-kernel-to-EH ratio fixed to 4
(`48 = 4·12`). [The `48π` prefactor is a documented physical input, not derived here — see the
module header and `frolov_fursaev_falsifier_wrong_coeff`.]
-/
noncomputable def entanglementEntropyAreaLeading (N_f Λ A : ℝ) : ℝ :=
  N_f * Λ ^ 2 / (48 * Real.pi) * A

/-- **Sakharov induction condition.** The physical Newton constant is the fully-induced value
(no bare gravitational action): `G_N = G_N_from_a2 Λ N_f = 12π/(N_f Λ²)`. -/
def H_Sakharov (Λ N_f G_N : ℝ) : Prop := G_N = HeatKernelExpansion.G_N_from_a2 Λ N_f

/-- **Bridge: Sakharov induction ⟺ the substrate's `α_ADW = 1` (δG = 0).** Ties `H_Sakharov` to
`MicroscopicCoefficientMatch.matchResidual` (the existing Wave-5 δG residual): the physical
Newton constant `gNMicroscopic = α·G_N_from_a2` is the fully-induced value iff `α_ADW = 1`. -/
theorem H_Sakharov_iff_alpha_unity {Λ N_f α_ADW : ℝ} (hΛ : 0 < Λ) (hN : 0 < N_f) :
    H_Sakharov Λ N_f (MicroscopicCoefficientMatch.gNMicroscopic Λ N_f α_ADW) ↔ α_ADW = 1 := by
  rw [← MicroscopicCoefficientMatch.matchResidual_eq_zero_iff_alpha_unity hΛ hN,
      MicroscopicCoefficientMatch.matchResidual, H_Sakharov, sub_eq_zero]

/-- **The 1/4 ratio (substantive content).** The Frolov–Fursaev entanglement area density equals
`A/(4 · G_N^induced)` — i.e. the heat-kernel `a₂` ratio is `48 : 12 = 4 : 1`. This is the
algebraic heart: the `1/4` is forced by the shared `a₂`, with no free parameter. -/
theorem entanglement_area_eq_quarter_inv_G_induced (A Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    entanglementEntropyAreaLeading N_f Λ A
      = A / (4 * HeatKernelExpansion.G_N_from_a2 Λ N_f) := by
  unfold entanglementEntropyAreaLeading HeatKernelExpansion.G_N_from_a2
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hN' : N_f ≠ 0 := ne_of_gt hN
  have hΛ' : Λ ≠ 0 := ne_of_gt hΛ
  field_simp
  ring

/--
**Frolov–Fursaev induced-gravity quarter coefficient (THE conditional, Gate A.2).** Given the
Sakharov induction condition (`G_N` fully induced) and the entanglement identification
(`S_BH = S_ent`), with the Frolov–Fursaev heat-kernel `S_ent` coefficient, the black-hole entropy
is exactly `A/(4 G_N)` — the `1/4` from the `48:12` `a₂` ratio, NOT tuned. None of the three
antecedents contains `S = A/4G`.
-/
theorem frolov_fursaev_quarter_coefficient
    (A Λ N_f G_N S_BH S_ent : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f)
    (h_Sakharov : H_Sakharov Λ N_f G_N)
    (h_ident : S_BH = S_ent)
    (h_heatKernel : S_ent = entanglementEntropyAreaLeading N_f Λ A) :
    S_BH = A / (4 * G_N) := by
  rw [h_ident, h_heatKernel, h_Sakharov, entanglement_area_eq_quarter_inv_G_induced A Λ N_f hΛ hN]

/-- **Dirac witness.** For `N_f > 0` Dirac fermions at the Sakharov point, the conditional fires:
with `G_N` the induced value and `S_BH = S_ent =` the FF area density, `S_BH = A/(4 G_N)`. -/
theorem frolov_fursaev_dirac_witness (A Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    entanglementEntropyAreaLeading N_f Λ A
      = A / (4 * HeatKernelExpansion.G_N_from_a2 Λ N_f) :=
  frolov_fursaev_quarter_coefficient A Λ N_f (HeatKernelExpansion.G_N_from_a2 Λ N_f)
    (entanglementEntropyAreaLeading N_f Λ A) (entanglementEntropyAreaLeading N_f Λ A)
    hΛ hN rfl rfl rfl

/-- **Falsifier (the 48π coefficient is load-bearing).** If `S_ent = c·A` for any coefficient
`c ≠ N_f Λ²/(48π)` (a heat-kernel coefficient other than Frolov–Fursaev's), the induced-gravity
match `S_BH = A/(4 G_N)` FAILS. So the `1/4` genuinely depends on the FF coefficient — it is not
vacuously true for any input. -/
theorem frolov_fursaev_falsifier_wrong_coeff
    (A Λ N_f c : ℝ) (hA : 0 < A) (hΛ : 0 < Λ) (hN : 0 < N_f)
    (hc : c ≠ N_f * Λ ^ 2 / (48 * Real.pi)) :
    c * A ≠ A / (4 * HeatKernelExpansion.G_N_from_a2 Λ N_f) := by
  rw [← entanglement_area_eq_quarter_inv_G_induced A Λ N_f hΛ hN, entanglementEntropyAreaLeading]
  intro h
  exact hc (mul_right_cancel₀ (ne_of_gt hA) h)

/-- **Consistency with the Kaul–Majumdar leading term.** The Frolov–Fursaev induced-gravity
`A/(4 G_N)` is exactly the leading (area-law) part of the Wave-3 `kaulMajumdarS` closed form
`A/(4 G_N) − (3/2) log(A/(4 G_N))` at the induced `G_N`. The two routes agree on the `1/4`;
Wave 7B supplies the `−3/2` log from the literal count. -/
theorem frolov_fursaev_matches_kaulMajumdar_leading (A Λ N_f : ℝ) (hΛ : 0 < Λ) (hN : 0 < N_f) :
    entanglementEntropyAreaLeading N_f Λ A
      = BHEntropyMicroscopic.kaulMajumdarS A (HeatKernelExpansion.G_N_from_a2 Λ N_f) 0
        + (3 / 2) * Real.log (A / (4 * HeatKernelExpansion.G_N_from_a2 Λ N_f)) := by
  rw [entanglement_area_eq_quarter_inv_G_induced A Λ N_f hΛ hN]
  unfold BHEntropyMicroscopic.kaulMajumdarS
  ring

end InducedGravityEntropy
end SKEFTHawking
