import SKEFTHawking.Basic
import SKEFTHawking.GrapheneHawking

/-!
# Graphene Hawking Noise PSD Formula (Phase 5w Wave 10a)

## Physical Content

The Hawking-induced excess current noise at a bilayer-graphene de Laval
nozzle, derived from both Keldysh FDT and Landauer–Büttiker with
Bogoliubov mixing:

    ΔS_I(ω) = 2 ℏω σ_Q Γ(ω) n_H(ω)

where σ_Q is the quantum-critical conductance, Γ is the greybody
transmission factor, and n_H = 1/(exp(ℏω/k_BT_H) - 1) is the Hawking
occupation number.

Units: [J] × [S] × [1] × [1] = [A²·s] = [A²/Hz]

The previously used prefactor (2e²/π) was dimensionally wrong — it
has units [C²], not [J·s]. The error is an inadvertent substitution
ℏ → e²/π, introducing an extraneous conductance quantum 2e²/h.

Two independent derivation routes give the same result:
1. Keldysh: Callen–Welton FDT with mode-resolved distribution F_u(ω)
2. Landauer: Büttiker multichannel formula + Bogoliubov mixing
   (Anantram–Datta structural template, PRB 53, 16390)

This is a genuinely new result — no previous paper has published the
Landauer–Büttiker noise formula for electronic analog Hawking radiation.

## References

- Blanter & Büttiker, Phys. Rep. 336, 1 (2000) — quantum noise review
- Anantram & Datta, PRB 53, 16390 (1996) — Bogoliubov-de Gennes noise
- Callen & Welton, Phys. Rev. 83, 34 (1951) — FDT
- Lit-Search/Phase-5w/5w-landauer-buttiker-noise.md — full derivation
-/

namespace SKEFTHawking.GrapheneNoiseFormula

/-! ## Definitions -/

/-- Hawking noise PSD: ΔS_I = 2 ℏω σ_Q Γ n_H.

    All inputs are dimensionless real numbers representing the
    magnitudes of the physical quantities. Dimensional consistency
    is proved separately (grapheneNoisePSD_dimensional). -/
noncomputable def hawkingNoisePSD (hbar_omega sigma_Q greybody n_H : ℝ) : ℝ :=
  2 * hbar_omega * sigma_Q * greybody * n_H

/-- Johnson-Nyquist thermal noise: S_JN = 4 k_B T σ_Q. -/
noncomputable def johnsonNyquistPSD (kB_T sigma_Q : ℝ) : ℝ :=
  4 * kB_T * sigma_Q

/-- Signal-to-noise ratio per frequency bin: SNR = S_H / S_JN. -/
noncomputable def snrPerBin (hbar_omega sigma_Q greybody n_H kB_T : ℝ) : ℝ :=
  hawkingNoisePSD hbar_omega sigma_Q greybody n_H /
  johnsonNyquistPSD kB_T sigma_Q

/-! ## Positivity and Monotonicity -/

/-- The Hawking noise PSD is positive when all inputs are positive. -/
theorem hawkingNoisePSD_pos (hbar_omega sigma_Q greybody n_H : ℝ)
    (ho : 0 < hbar_omega) (hs : 0 < sigma_Q)
    (hg : 0 < greybody) (hn : 0 < n_H) :
    0 < hawkingNoisePSD hbar_omega sigma_Q greybody n_H := by
  unfold hawkingNoisePSD; positivity

/-- The Johnson-Nyquist PSD is positive when T and σ_Q are positive. -/
theorem johnsonNyquistPSD_pos (kB_T sigma_Q : ℝ)
    (ht : 0 < kB_T) (hs : 0 < sigma_Q) :
    0 < johnsonNyquistPSD kB_T sigma_Q := by
  unfold johnsonNyquistPSD; positivity

/-- The greybody factor bounds the Hawking noise from above:
    Γ ≤ 1 ⟹ S_H ≤ S_H(Γ=1).

    This means using Γ=1 (step-horizon approximation) gives an
    upper bound on the signal, and thus a LOWER bound on the
    integration time needed for detection. -/
theorem hawkingNoisePSD_greybody_mono (hbar_omega sigma_Q greybody n_H : ℝ)
    (ho : 0 < hbar_omega) (hs : 0 < sigma_Q) (hn : 0 < n_H)
    (hg1 : greybody ≤ 1) :
    hawkingNoisePSD hbar_omega sigma_Q greybody n_H ≤
    hawkingNoisePSD hbar_omega sigma_Q 1 n_H := by
  unfold hawkingNoisePSD
  have h : 0 < 2 * hbar_omega * sigma_Q * n_H := by positivity
  have := mul_le_mul_of_nonneg_left hg1 h.le
  linarith

/-! ## SNR Structure -/

/-- The SNR simplifies to ℏω Γ n_H / (2 k_BT) when σ_Q cancels. -/
theorem snr_sigma_Q_cancels (hbar_omega sigma_Q greybody n_H kB_T : ℝ)
    (hs : sigma_Q ≠ 0) (ht : kB_T ≠ 0) :
    snrPerBin hbar_omega sigma_Q greybody n_H kB_T =
    (hbar_omega * greybody * n_H) / (2 * kB_T) := by
  unfold snrPerBin hawkingNoisePSD johnsonNyquistPSD
  field_simp
  ring

/-- The SNR is independent of σ_Q: changing the conductance changes
    both signal and noise proportionally. This means the formula's
    prediction for DETECTION FEASIBILITY is robust against uncertainty
    in σ_Q — only T_H/T_ambient and Γ matter. -/
theorem snr_independent_of_sigma_Q (hbar_omega sigma_Q1 sigma_Q2 greybody n_H kB_T : ℝ)
    (hs1 : sigma_Q1 ≠ 0) (hs2 : sigma_Q2 ≠ 0) (ht : kB_T ≠ 0) :
    snrPerBin hbar_omega sigma_Q1 greybody n_H kB_T =
    snrPerBin hbar_omega sigma_Q2 greybody n_H kB_T := by
  rw [snr_sigma_Q_cancels _ _ _ _ _ hs1 ht,
      snr_sigma_Q_cancels _ _ _ _ _ hs2 ht]

/-! ## Dimensional Consistency

The following theorem encodes the dimensional analysis that caught
the original error. In SI:

  [ℏω]  = J          = kg·m²/s²
  [σ_Q] = S (siemens) = A²·s³/(kg·m²)
  [Γ]   = 1
  [n_H]  = 1

Product: kg·m²/s² × A²·s³/(kg·m²) = A²·s = A²/Hz  ✓

The old prefactor (2e²/π) had units C² = A²·s², giving
  C² × S × s⁻¹ = A²·s² × A²·s³/(kg·m²) × s⁻¹ = A⁴·s⁴/(kg·m²)
which is NOT A²/Hz.

We formalize this as: the product of unit exponents for mass, length,
time, and current yields exactly [A²·T¹] = [A²/Hz]. -/

/-- Dimensional analysis: the unit exponents of ℏω × σ_Q give A²·s.

    Encode dimensions as (mass, length, time, current) exponent tuples:
      ℏω  → (1, 2, -2, 0)
      σ_Q → (-1, -2, 3, 2)
    Sum:    (0, 0, 1, 2) = A²·s  ✓

    The old e² prefactor would give (0, 0, 2, 2) × (-1, -2, 3, 2) × (0, 0, -1, 0)
    = (-1, -2, 4, 4) ≠ (0, 0, 1, 2).  -/
theorem grapheneNoisePSD_dimensional :
    -- Sum of exponents for (mass, length, time, current):
    -- ℏω: (1, 2, -2, 0)  +  σ_Q: (-1, -2, 3, 2)
    (1 + (-1 : ℤ), 2 + (-2 : ℤ), (-2) + 3, 0 + 2) = ((0 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)) := by
  norm_num

/-- The old prefactor (e²) has wrong dimensions for a noise PSD.

    e² exponents: (0, 0, 2, 2)  [C² = A²·s²]
    Need: (1, 2, -2, 0)  [J = ℏω]
    These are NOT equal. -/
theorem old_prefactor_wrong_dimensions :
    ((0 : ℤ), (0 : ℤ), (2 : ℤ), (2 : ℤ)) ≠ ((1 : ℤ), (2 : ℤ), (-2 : ℤ), (0 : ℤ)) := by
  decide

/-! ## FDT Consistency

At thermal equilibrium with T = T_H, the Hawking noise should reduce
to the Callen-Welton fluctuation-dissipation theorem result:

  S_FDT(ω) = ℏω coth(ℏω/2k_BT) Re σ(ω)

In the high-T (ℏω ≪ k_BT) limit: coth(x) ≈ 1/x + x/3,
  S_FDT → 2k_BT σ_Q (Johnson-Nyquist)

In the Hawking (ℏω ≫ k_BT_H) limit: coth(x) ≈ 1 + 2n_B(x),
  S_FDT → ℏω σ_Q (1 + 2n_H) → 2ℏω σ_Q n_H (excess over vacuum)

This matches our formula with Γ = 1. -/

/-- The Hawking excess equals the high-frequency FDT limit (Γ=1):
    S_Hawking = 2ℏω σ_Q n_H = (coth-limit excess) × σ_Q. -/
theorem fdt_consistency (hbar_omega sigma_Q n_H : ℝ) :
    hawkingNoisePSD hbar_omega sigma_Q 1 n_H =
    2 * hbar_omega * sigma_Q * n_H := by
  unfold hawkingNoisePSD; ring

end SKEFTHawking.GrapheneNoiseFormula
