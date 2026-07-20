import Mathlib
import SKEFTHawking.SoftTheorems.Boostless

/-!
# Phase 6o Wave 1a.5: dissipative-IR S-matrix structural NO-GO

## Goal

Encode the Phase 6o Wave 1a.5 **structural negative theorem** per
On-Shell Methods DR §2.5 conjectured No-Go:

> "A genuinely dissipative SK-EFT — one in which the SK action contains
> a non-vanishing imaginary noise kernel that cannot be removed by
> integrating in auxiliary unitary fields — *cannot* admit a BCFW-style
> on-shell recursion for its retarded/advanced/Keldysh amplitudes."

## Substantive content (R-01 remediation, 2026-07-20)

This module now derives the no-go from a **concrete retarded-response
model** rather than from placeholder `True` hypotheses. The model is the
damped-oscillator inverse retarded propagator of the Crossley–Glorioso–Liu
/ Jain–Kovtun Schwinger–Keldysh EFT (Phase-2 KMS/FDR DR, "Resolution of
the zero-noise paradox"):

    K_R(ω) = (ω₀² − m ω²)  −  i γ ω
             └─ even in ω ─┘   └ odd in ω ┘
             conservative       dissipative

The odd-in-ω term `−iγω` is the genuine dissipative (noise-paired) part:
by the CGL FDR (`CGLTransform.lean`, `cgl_fdr`), a non-zero odd-ω
coefficient γ is *exactly* the condition that the system carries thermal
noise / genuine irreversibility. This is the "non-vanishing imaginary
noise kernel" of DR §2.5.

**The genuine no-go (mechanism (i) of DR §2.5 / §5.1 pt 3).** BCFW-style
on-shell recursion factorizes an amplitude on its physical poles *on the
real axis*. The poles of the retarded Green function `G_R = 1/K_R` are the
zeros of `K_R`. We prove:

  `dissipative_gapped_no_real_pole` — for a genuinely dissipative (γ > 0)
  and gapped (ω₀ ≠ 0) response, `K_R(ω) ≠ 0` for **every** real ω. The
  poles are pushed strictly off the real axis (into the lower half-plane),
  so no real-axis factorization is available and BCFW recursion cannot be
  set up.

This is a *derived contradiction* — `KMSBroken ∧ GappedIR ∧
FactorizationOnRealAxis` is provably inconsistent — not a restatement of a
hypothesis. The hypotheses are load-bearing: dropping dissipation (γ = 0),
the gapped elastic mode `elasticGappedMode` *does* recover a real-axis
pole (`elasticGappedMode_has_real_pole`).

### Scope note

Mechanism (ii) of DR §2.5 — the Keldysh i0 prescription breaking the
single-Riemann-sheet analyticity required for the Cauchy-residue
derivation — involves branch-cut structure of the Keldysh propagator and
is NOT modeled here (it would require a genuine analytic-continuation /
multi-sheet formalization absent from Mathlib). This module ships the
fully-genuine mechanism-(i) obstruction (complex poles); mechanism (ii) is
the complementary obstruction, documented as a gap.

## References

- On-Shell Methods DR §2.5 conjectured No-Go, §5.1.
- Crossley-Glorioso-Liu, JHEP 09 (2017) 095, arXiv:1511.03646;
  Jain-Kovtun, arXiv:2309.00511 (damped-oscillator FDR kernel).
- Phase-2 DR "Dynamical KMS symmetry and the FDR in SK-EFT" (in-tree,
  `Lit-Search/Phase-2/…`): K_R(ω) = −mω² + ω₀² − iγω, the −iγω term odd.
- Borsten-Jonsson-Kim, JHEP 08 (2024) 074, arXiv:2405.11110.
- Novikov, arXiv:1901.05414 (PT-symmetric scattering causality breakdown).
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-! ## §1. Concrete retarded-response model (damped-oscillator kernel) -/

/-- A quadratic retarded response, given by the damped-oscillator inverse
retarded propagator `K_R(ω) = (ω₀² − m ω²) − i γ ω`.

* `m`      — inertial coefficient (even-ω / conservative).
* `omega0` — restoring frequency ω₀ (even-ω / conservative; the IR gap).
* `gamma`  — friction / dissipative coefficient (odd-ω; the noise-paired
  transport coefficient of the CGL FDR). -/
structure RetardedResponse where
  /-- Inertial coefficient (even-ω, conservative). -/
  m : ℝ
  /-- Restoring frequency ω₀ (even-ω, conservative; the IR gap scale). -/
  omega0 : ℝ
  /-- Friction / dissipative coefficient γ (odd-ω, noise-paired). -/
  gamma : ℝ

/-- The retarded kernel `K_R(ω) = (ω₀² − m ω²) − i γ ω` as a ℂ-valued
function of the real frequency ω. Its zeros are the poles of the retarded
Green function `G_R = 1/K_R`. -/
def RetardedResponse.kernel (R : RetardedResponse) (ω : ℝ) : ℂ :=
  ((R.omega0 ^ 2 - R.m * ω ^ 2 : ℝ) : ℂ) - ((R.gamma * ω : ℝ) : ℂ) * Complex.I

@[simp] theorem RetardedResponse.kernel_re (R : RetardedResponse) (ω : ℝ) :
    (R.kernel ω).re = R.omega0 ^ 2 - R.m * ω ^ 2 := by
  simp only [RetardedResponse.kernel, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]

@[simp] theorem RetardedResponse.kernel_im (R : RetardedResponse) (ω : ℝ) :
    (R.kernel ω).im = -(R.gamma * ω) := by
  simp only [RetardedResponse.kernel, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub]

/-! ## §2. The three genuine hypotheses -/

/-- **Genuine dissipation.** The odd-in-ω dissipative coefficient γ is
positive: a non-vanishing imaginary noise kernel (the DR §2.5 condition,
KMS Z₂ acting non-trivially via the CGL FDR-paired dissipative term). -/
def KMSBroken (R : RetardedResponse) : Prop := 0 < R.gamma

/-- **Gapped IR.** The restoring frequency ω₀ is non-zero — the response
carries a genuine IR / horizon gap scale, so `K_R(0) = ω₀² ≠ 0`. -/
def GappedIR (R : RetardedResponse) : Prop := R.omega0 ≠ 0

/-- **Real-axis factorization requirement.** BCFW-style on-shell recursion
must factorize the amplitude on a physical pole lying on the real axis:
there is a real frequency ω where the retarded kernel vanishes (On-Shell
DR §5.1 pt 3). -/
def FactorizationOnRealAxis (R : RetardedResponse) : Prop :=
  ∃ ω : ℝ, R.kernel ω = 0

/-! ## §3. Substantive structural NO-GO -/

/-- **NO-GO core.** A genuinely dissipative (γ > 0), gapped (ω₀ ≠ 0)
retarded response has NO real-axis pole: `K_R(ω) ≠ 0` for every real ω.

Proof: at a real zero, the imaginary part `−γω` must vanish, forcing
ω = 0 (since γ > 0); but then the real part `K_R(0) = ω₀²` must also
vanish, forcing ω₀ = 0, contradicting the gap. The poles are thus pushed
strictly off the real axis (into the lower half-plane), so no BCFW-style
real-axis factorization exists. -/
theorem dissipative_gapped_no_real_pole (R : RetardedResponse)
    (hγ : KMSBroken R) (hg : GappedIR R) : ¬ FactorizationOnRealAxis R := by
  unfold KMSBroken at hγ
  unfold GappedIR at hg
  rintro ⟨ω, hω⟩
  have him : (R.kernel ω).im = 0 := by rw [hω]; rfl
  have hre : (R.kernel ω).re = 0 := by rw [hω]; rfl
  rw [RetardedResponse.kernel_im] at him
  rw [RetardedResponse.kernel_re] at hre
  have hω0 : ω = 0 := by
    rcases mul_eq_zero.mp (by linarith : R.gamma * ω = 0) with h | h
    · exact absurd h (ne_of_gt hγ)
    · exact h
  rw [hω0] at hre
  have h0 : R.omega0 ^ 2 = 0 := by nlinarith [hre]
  exact hg ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h0)

/-- A putative dissipative-IR BCFW-reconstructible S-matrix: it is
genuinely dissipative, gapped, and BCFW-factorizes on a real-axis pole.
Per On-Shell Methods DR §2.5 this is the configuration the conjectured
NO-GO targets. -/
def IsLindbladianSMatrix (R : RetardedResponse) : Prop :=
  KMSBroken R ∧ GappedIR R ∧ FactorizationOnRealAxis R

/-- **Lindbladian / dissipative S-matrix structural NO-GO** (Phase 6o Wave
1a.5 deliverable per On-Shell Methods DR §2.5, mechanism (i)).

No retarded response is simultaneously genuinely dissipative, gapped, and
BCFW-reconstructible on the real axis. The three conditions are provably
inconsistent — a genuinely dissipative gapped response has its poles off
the real axis, so BCFW recursion (which factorizes on real-axis poles)
cannot be set up. This is a derived contradiction, joining the program's
NO-GO landscape (gauge erasure, vestigial graviton, Phase 6n Wave 2b, …). -/
theorem lindbladianSMatrix_structural_no_go (R : RetardedResponse) :
    ¬ IsLindbladianSMatrix R := by
  rintro ⟨hγ, hg, hfac⟩
  exact dissipative_gapped_no_real_pole R hγ hg hfac

/-! ## §4. Non-vacuity + load-bearing hypotheses -/

/-- A concrete genuinely-dissipative, gapped mode: `m = ω₀ = γ = 1`,
kernel `K_R(ω) = 1 − ω² − iω`. -/
def dampedGappedMode : RetardedResponse := ⟨1, 1, 1⟩

theorem dampedGappedMode_dissipative : KMSBroken dampedGappedMode := by
  unfold KMSBroken dampedGappedMode; norm_num

theorem dampedGappedMode_gapped : GappedIR dampedGappedMode := by
  unfold GappedIR dampedGappedMode; norm_num

/-- The concrete damped gapped mode admits no BCFW real-axis recursion:
a non-vacuous instance of the structural NO-GO. -/
theorem dampedGappedMode_not_reconstructible :
    ¬ FactorizationOnRealAxis dampedGappedMode :=
  dissipative_gapped_no_real_pole _ dampedGappedMode_dissipative dampedGappedMode_gapped

/-- The gapped ELASTIC (dissipation-free, γ = 0) mode `K_R(ω) = 1 − ω²`
DOES have a real-axis pole, at ω = 1. This shows the γ > 0 hypothesis of
the NO-GO is load-bearing: drop the dissipation and real-axis
factorization reappears. -/
def elasticGappedMode : RetardedResponse := ⟨1, 1, 0⟩

theorem elasticGappedMode_has_real_pole :
    FactorizationOnRealAxis elasticGappedMode := by
  refine ⟨1, ?_⟩
  simp [RetardedResponse.kernel, elasticGappedMode]

/-! ## §5. Wave 1a.5 closure summary -/

/-- Substantive deliverables shipped at Wave 1a.5 (R-01 remediation):

1. `RetardedResponse` concrete damped-oscillator kernel model
   (CGL / Jain-Kovtun); `kernel_re` / `kernel_im` decomposition.
2. Genuine hypotheses `KMSBroken` (γ > 0), `GappedIR` (ω₀ ≠ 0),
   `FactorizationOnRealAxis` (real-axis pole exists).
3. `dissipative_gapped_no_real_pole` — the genuine derived obstruction.
4. `lindbladianSMatrix_structural_no_go` — the three conditions are
   provably inconsistent (a real NO-GO, not an identity wrapper).
5. `dampedGappedMode_not_reconstructible` (non-vacuous instance) +
   `elasticGappedMode_has_real_pole` (γ > 0 hypothesis load-bearing). -/
theorem wave_1a_5_dissipativeNoGo_closure :
    (∀ R : RetardedResponse, ¬ IsLindbladianSMatrix R) ∧
    (∀ R : RetardedResponse, KMSBroken R → GappedIR R →
       ¬ FactorizationOnRealAxis R) ∧
    FactorizationOnRealAxis elasticGappedMode :=
  ⟨lindbladianSMatrix_structural_no_go,
   dissipative_gapped_no_real_pole,
   elasticGappedMode_has_real_pole⟩

end SKEFTHawking.SoftTheorems
