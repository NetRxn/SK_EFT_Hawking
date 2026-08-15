import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.LinearizedEFE

/-!
# Phase 6e Wave 1: Seeley-DeWitt Heat-Kernel Expansion

## Goal

Formalize the leading Seeley-DeWitt coefficients of the Dirac heat
kernel `Tr exp(-τ D̸²)` as τ → 0⁺ on a 4D Riemannian manifold with N_f
free Dirac-fermion species. Closed-form rational + π expressions for
`a_0, a_2, a_4` (Gilkey / Vassilevich convention; the `a_4` rationals
are Christensen-Duff's arbitrary-spin table as collected by
Vassilevich).

**Trace convention (load-bearing, and the subject of a 2026-08-15
correction).** Every coefficient here carries the *fibre trace* `tr_V`
of Vassilevich Eqs. (4.26)–(4.28), so `tr_V 𝟙 = 4 N_f` for `N_f`
four-component Dirac species. `a_0` always carried this factor; `a_2`
and `a_4` previously did not, and now do. `a2_R_coefficient_eq_gilkey_trace`
pins `a_2` to `a_0`'s trace factor so the two can no longer drift apart.

The **load-bearing correctness-push** is the *Decision Gate E.2*
calibration: integrating the Λ²-divergent part of `a_2` over the
manifold gives the heat-kernel-induced Newton constant
`G_N_from_a2 = 3 π / (N_f Λ²)`, which is exactly **one quarter** of the
Phase 6a.1 `LinearizedEFE.G_N_sakharov = 12 π / (N_f Λ²)`
(`G_N_from_a2_eq_quarter_G_N_sakharov`). The ADW rescaling that makes
the two agree is therefore `α_ADW = 1/4`, not `1`
(`a2_matches_GNemerg_iff_alpha_ADW_quarter`).

⚠️ The factor of four is precisely the Dirac index trace. Phase 6a.1's
`G_N_sakharov` is stated independently (Adler RMP 54, 729 (1982),
Eq. (3.3)) and is **not** touched here; whether it carries the same
untraced defect is an open question for that module, not this one.

## Module structure

- §1: `(4π)²` Gaussian normalization (positivity lemmas)
- §2: `a0_dirac` — leading coefficient (cosmological-constant scale)
- §3: `a2_R_coefficient` — Ricci-scalar coefficient (Einstein-Hilbert
  scale)
- §4: Tracked-hypothesis structure `DiracHeatKernelAsymptotic`
  (PDE-level existence; witnessed externally per Vassilevich 2003
  Theorem 4.1)
- §5: `G_N_from_a2` — Newton constant by EH-action matching;
  cross-bridge `G_N_from_a2_eq_quarter_G_N_sakharov` to 6a.1
- §6: Quantitative anchor at fiducial `(Λ_UV, N_f) = (10¹⁶ GeV, 15)`
- §7: `a_4` higher-curvature basis (R², Ricci², Riemann²) with the
  Christensen-Duff spin-1/2 rational coefficients
- §8: Correctness-push biconditional
  `a2_matches_GNemerg_iff_alpha_ADW_quarter`

## References

- Gilkey, *Invariance Theory, the Heat Equation, and the Atiyah-Singer
  Index Theorem*, CRC Press 2nd ed. 1995 — Theorem 3.3.1, Cor. 4.8.16
- Vassilevich, Phys. Rep. 388, 279 (2003), §4.1 — Eq. (4.26) `a_0`,
  Eq. (4.27) `a_2`, Eq. (4.28) `a_4`, Eq. (4.35) + Table 1 (Weyl-basis
  `a_4` by spin; the spin-1/2 row is `(a,b,c,d) = (-7/2, -11, 6, 0)`
  and "Spin 1/2 means 4-component Dirac spinors")
- Christensen & Duff, *New gravitational index theorems and
  supertheorems*, Nucl. Phys. **B154**, 301 (1979) — the arbitrary-spin
  **`a_4`** calculation Vassilevich credits (his ref. [127]). It is not
  a source for `a_2`, and the 1978 *Phys. Lett. B* anomalies paper is a
  different work on a different subject.
- Adler, RMP 54, 729 (1982), Eq. (3.3) — induced-gravity coefficient
- Phase 6a.1 `LinearizedEFE.lean` — comparison target `G_N_sakharov`

## Scope lock

IN SCOPE: closed-form a_0/a_2/a_4 coefficients for free Dirac fermion
in 4D vacuum; calibration of a_2 → Sakharov-Adler G_N; tracked-Prop
structure for the asymptotic existence; Gauss-Bonnet identity check
on a_4.

OUT OF SCOPE: PDE-level proof of the heat-kernel asymptotic (deferred
to Mathlib's diff-geom infrastructure when ready); manifold-level
integration (deferred to 6f.1 Curvature.lean / 6f Lorentzian
infrastructure); torsion contributions to a_n (deferred to 6e.6
Einstein-Cartan); two-loop quantum corrections (out of scope for the
mean-field 6e program per strategy doc §15).
-/

noncomputable section

open Real

namespace SKEFTHawking.HeatKernelExpansion

/-! ## §1. `(4π)²` Gaussian normalization -/

/-- The squared 4π factor `(4π)²` arising from the τ → 0⁺ Gaussian
expansion in 4D Riemannian heat-kernel asymptotics. The full prefactor
in `Tr exp(-τ D̸²) ~ (4π τ)^(-d/2) Σ_n a_n τ^(n/2)` is `1/(4π τ)²` in
4D; the coefficient densities `a_n(x)` carry an additional `1/(4π)²`
when the integral measure absorbs the τ factors. -/
def fourPiSq : ℝ := (4 * Real.pi) ^ 2

/-- Inverse Gaussian normalization. -/
def fourPiSqInv : ℝ := 1 / fourPiSq

/-- `(4π)²` is positive. -/
theorem fourPiSq_pos : 0 < fourPiSq := by
  unfold fourPiSq
  exact pow_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) 2

/-- `1/(4π)²` is positive. -/
theorem fourPiSqInv_pos : 0 < fourPiSqInv := by
  unfold fourPiSqInv
  exact div_pos one_pos fourPiSq_pos

/-! ## §2. Leading Seeley-DeWitt coefficient `a_0` -/

/-- The leading Seeley-DeWitt coefficient density for `N_f` free
Dirac-fermion species in 4D vacuum:

  `a_0(x) = 4 N_f / (4π)²`

The factor 4 = `tr 𝟙_4` is the Dirac-spinor index trace per species.
This term, when integrated against the Λ⁴-divergent volume measure,
sets the cosmological-constant scale Λ_emerg^4 (cf. 6e.5). -/
def a0_dirac (N_f : ℝ) : ℝ := 4 * N_f * fourPiSqInv

/-- `a_0` is strictly positive for any positive species count.
The proof composes Dirac-trace positivity with `(4π)²` positivity. -/
theorem a0_dirac_pos {N_f : ℝ} (h : 0 < N_f) : 0 < a0_dirac N_f := by
  unfold a0_dirac
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) h) fourPiSqInv_pos

/-- `a_0` is linear in `N_f`: doubling species doubles the coefficient. -/
theorem a0_dirac_linear (k N_f : ℝ) :
    a0_dirac (k * N_f) = k * a0_dirac N_f := by
  unfold a0_dirac
  ring

/-! ## §3. Einstein-Hilbert coefficient `a_2` -/

/-- The Seeley-DeWitt `a_2` coefficient *of the Ricci scalar `R`* for
`N_f` free Dirac fermions in 4D:

  `a_2(x) = a2_R_coefficient(N_f) · R(x), `
  `a2_R_coefficient(N_f) = - N_f / (3 (4π)²).`

Derivation, Vassilevich Eq. (4.27): `a_2 = (4π)^{-n/2} (1/6) ∫ tr_V{6E + R}`.
The Lichnerowicz endomorphism for `D̸² = -∇² + R/4` is `E = -R/4`, so
`6E + R = -R/2`; the fibre trace over the spinor bundle is
`tr_V 𝟙 = 4 N_f` for `N_f` four-component Dirac species — the **same**
factor `a0_dirac` carries. Hence `(1/6)(4 N_f)(-1/2) = -N_f/3`.

Sign: the spin-1/2 Lichnerowicz convention yields the minus sign;
integrating Λ² · a_2 against `R √g d⁴x` produces the positive
Einstein-Hilbert prefactor `+1/(16π G_N)` (after the
trace-of-EH-Lagrangian sign flip).

⚠️ Corrected 2026-08-15. This coefficient previously read `-N_f/12`,
the value obtained when the fibre trace is *omitted* (`tr_V 𝟙 = 1`)
while `a_0` took it. `a2_R_coefficient_eq_gilkey_trace` now binds the
two, so the pair cannot silently disagree again. -/
def a2_R_coefficient (N_f : ℝ) : ℝ := -(N_f / 3) * fourPiSqInv

/-- **Trace-convention reconciliation (Vassilevich Eq. 4.27).** The
`a_2` Ricci-scalar coefficient is the Gilkey/Vassilevich assembly
`(1/6)·(6·E_R + 1)` applied to the **same** fibre trace `a_0` carries,
where `E_R = -1/4` is the coefficient of `R` in the Lichnerowicz
endomorphism `E = -R/4`.

This is the load-bearing anti-drift statement of the module: `a_0` and
`a_2` are coefficients of one expansion for one operator, so they must
agree about whether `tr_V` has been taken. Stating the relation
*through* `a0_dirac` rather than through the literal number `4 N_f`
means a future edit to either coefficient alone breaks this theorem. -/
theorem a2_R_coefficient_eq_gilkey_trace (N_f : ℝ) :
    a2_R_coefficient N_f
      = (1 / 6) * (6 * (-(1 : ℝ) / 4) + 1) * a0_dirac N_f := by
  unfold a2_R_coefficient a0_dirac
  ring

/-- `a_2` coefficient is strictly negative for positive species count. -/
theorem a2_R_coefficient_neg {N_f : ℝ} (h : 0 < N_f) :
    a2_R_coefficient N_f < 0 := by
  unfold a2_R_coefficient
  have h3 : (0 : ℝ) < N_f / 3 := by positivity
  have := mul_pos h3 fourPiSqInv_pos
  linarith

/-- `a_2` is linear in species count. -/
theorem a2_R_coefficient_linear (k N_f : ℝ) :
    a2_R_coefficient (k * N_f) = k * a2_R_coefficient N_f := by
  unfold a2_R_coefficient
  ring

/-- `a_2` vanishes iff there are no fermion species. Substantive
because: (a) the coefficient becomes 0 exactly when `N_f = 0`,
(b) elsewhere it is strictly nonzero (sign-fixed). -/
theorem a2_R_coefficient_eq_zero_iff (N_f : ℝ) :
    a2_R_coefficient N_f = 0 ↔ N_f = 0 := by
  unfold a2_R_coefficient
  have hpi : fourPiSqInv ≠ 0 := ne_of_gt fourPiSqInv_pos
  constructor
  · intro h
    have hsplit : -(N_f / 3) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact (hpi h2).elim
    have hdiv : N_f / 3 = 0 := by linarith
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    exact (div_eq_zero_iff.mp hdiv).resolve_right h3
  · intro h
    rw [h]
    ring

/-! ## §4. Tracked-hypothesis structure: Dirac heat-kernel asymptotic -/

/-- **Tracked-hypothesis structure.** A witness for the Dirac
heat-kernel asymptotic on a 4D Riemannian background, encoding:

  - The trace `Tr exp(-τ D̸²)` as a function of proper-time `τ > 0`
  - Positivity (heat-kernel traces are non-negative)
  - The leading coefficient `a_0` matches the standard textbook
    `4 N_f / (4π)²`
  - The Ricci-scalar coefficient `a_2_R_coef` matches the standard
    textbook `-N_f / (3 (4π)²)` (Vassilevich Eq. (4.27) *with* the
    Dirac fibre trace)

The PDE-level existence of the asymptotic expansion (Vassilevich 2003
Theorem 4.1, requires manifold + spin-bundle infrastructure) is a
*tracked external hypothesis*: the Lean module consumes this structure
to derive the Sakharov-Adler calibration without re-proving the
Gilkey-Vassilevich machinery in-line. Mathlib does not yet provide
the underlying diff-geom theory.

Substantive content: any user instantiating this structure has
**committed to the traced Gilkey-Vassilevich coefficient table** — the
Lean type system enforces that the coefficients used in downstream
calibration theorems agree with the textbook values, and
`a2_R_coefficient_eq_gilkey_trace` enforces that `a_0` and `a_2` share
one trace convention. -/
structure DiracHeatKernelAsymptotic (N_f : ℝ) where
  /-- Heat-kernel trace `Tr exp(-τ D̸²)` as a τ-only function (manifold
  + metric absorbed). -/
  trace : ℝ → ℝ
  /-- Positivity of the heat-kernel trace at each `τ > 0`. -/
  trace_nonneg : ∀ τ, 0 < τ → 0 ≤ trace τ
  /-- Leading coefficient. -/
  a0 : ℝ
  /-- Standard Dirac value. -/
  a0_value : a0 = a0_dirac N_f
  /-- Ricci-scalar coefficient (per unit `R`). -/
  a2_R_coef : ℝ
  /-- Standard Dirac value. -/
  a2_R_value : a2_R_coef = a2_R_coefficient N_f
  /-- Species-count positivity. -/
  N_f_pos : 0 < N_f

/-- Given a `DiracHeatKernelAsymptotic`, the bundled `a_0` is positive.
**Substantive cross-bridge** — consumes both `N_f_pos` and
`a0_value` from the structure, then dispatches to `a0_dirac_pos`. -/
theorem DiracHeatKernelAsymptotic.a0_pos {N_f : ℝ}
    (hk : DiracHeatKernelAsymptotic N_f) : 0 < hk.a0 := by
  rw [hk.a0_value]
  exact a0_dirac_pos hk.N_f_pos

/-- Given a `DiracHeatKernelAsymptotic`, the bundled `a_2` coefficient
of R is strictly negative. **Substantive cross-bridge** — consumes
both `N_f_pos` and `a2_R_value`. -/
theorem DiracHeatKernelAsymptotic.a2_neg {N_f : ℝ}
    (hk : DiracHeatKernelAsymptotic N_f) : hk.a2_R_coef < 0 := by
  rw [hk.a2_R_value]
  exact a2_R_coefficient_neg hk.N_f_pos

/-! ## §5. Sakharov-Adler calibration (correctness-push anchor) -/

/-- Newton constant from integrating the Λ²·a_2 mass-dimension term
of the heat-kernel effective action against `R √g d⁴x` and matching
the Einstein-Hilbert coefficient `-1/(16π G_N)`:

  `1/(16π G_N) = N_f Λ² / (3 (4π)²) = N_f Λ² / (48 π²)`,

so

  `G_N = 3 π / (N_f Λ²).`

This is the Decision Gate E.2 anchor. The matching rule is unchanged
from the module's original formulation — only `a2_R_coefficient` moved,
by the Dirac fibre-trace factor of four, and `G_N` moved inversely with
it (`12 π → 3 π`). -/
def G_N_from_a2 (Λ N_f : ℝ) : ℝ := 3 * Real.pi / (N_f * Λ ^ 2)

/-- `G_N_from_a2` is positive when both arguments are positive. -/
theorem G_N_from_a2_pos {Λ N_f : ℝ}
    (hΛ : 0 < Λ) (hN : 0 < N_f) :
    0 < G_N_from_a2 Λ N_f := by
  unfold G_N_from_a2
  apply div_pos
  · linarith [Real.pi_pos]
  · exact mul_pos hN (sq_pos_of_pos hΛ)

/-- **Correctness-push anchor (Decision Gate E.2), corrected
2026-08-15.** The Newton constant derived from the *traced* heat-kernel
`a_2` coefficient is exactly **one quarter** of the Sakharov-Adler
induced-gravity Newton constant stated in Phase 6a.1: `3π/(N_f Λ²)`
against `12π/(N_f Λ²)`.

The factor is not a tolerance and not a convention gap — it is the
Dirac index trace `tr_V 𝟙 = 4`. Phase 6a.1's `G_N_sakharov` is stated
independently (Adler RMP 54, 729 (1982), Eq. (3.3)) and is deliberately
left untouched by this correction, so the discrepancy is recorded here
as an *exact ratio* rather than hidden: whichever of the two carries
the trace correctly, the quotient is 4 and this theorem says so.

This replaces the former `G_N_from_a2_eq_G_N_sakharov`, which asserted
equality and is false under the traced `a_2`.

**Substantive cross-bridge:** the proof body invokes
`SKEFTHawking.LinearizedEFE.G_N_sakharov` by name — drift-protection
per `feedback_python_lean_refs_drift.md` (P6 cross-module bridge
integrity). -/
theorem G_N_from_a2_eq_quarter_G_N_sakharov (Λ N_f : ℝ) :
    G_N_from_a2 Λ N_f
      = (1 / 4) * SKEFTHawking.LinearizedEFE.G_N_sakharov Λ N_f := by
  unfold G_N_from_a2 SKEFTHawking.LinearizedEFE.G_N_sakharov
  ring

/-- **Substantive structure-consuming calibration.** Given the
`DiracHeatKernelAsymptotic` tracked hypothesis, the structure-side
Ricci-scalar coefficient `hk.a2_R_coef` is identically the closed
form `-(N_f / 3) / (4π)²` — a non-vacuous use of the structure
invariant `a2_R_value`. This is the bridging lemma between the
PDE-level structure data and the `G_N_from_a2` calibration: any
downstream proof relating `G_N_from_a2 Λ N_f` to `G_N_sakharov Λ N_f`
under the structure consumes this lemma to convert the `hk.a2_R_coef`
input to the closed-form integrand. -/
theorem DiracHeatKernelAsymptotic.a2_eq_closed_form {N_f : ℝ}
    (hk : DiracHeatKernelAsymptotic N_f) :
    hk.a2_R_coef = -(N_f / 3) * fourPiSqInv := by
  rw [hk.a2_R_value]; rfl

/-! ## §6. Quantitative anchor at fiducial parameters -/

/-- **Quantitative anchor (substantive — not pure rfl).** At the
fiducial GUT-scale parameters `(Λ_UV, N_f) = (10¹⁶ GeV, 15)`, the
*inverse* heat-kernel Newton constant equals `15 · 10³² / (3 π) ≈
1.59 · 10³² GeV²`. This is the EH-action coefficient anchor: the
closed-form inversion of `G_N_from_a2` exposes the load-bearing Λ²
scaling that makes the heat-kernel calibration drift-detectable
against off-by-one errors in the `(4π)²`/3 normalization. The proof
clears the nested division via `one_div_div`, exposing the EH
prefactor directly. -/
theorem G_N_from_a2_at_GUT_inverse :
    1 / G_N_from_a2 (10 ^ 16 : ℝ) 15 =
      15 * (10 ^ 16 : ℝ) ^ 2 / (3 * Real.pi) := by
  unfold G_N_from_a2
  rw [one_div_div]

/-- **Quantitative anchor (norm_num falsifier).** The reciprocal
`1/G_N` at the GUT anchor is *strictly* less than `M_Pl²` evaluated
at `Λ_UV = 10¹⁶`. This is the mean-field-validity diagnostic: at
GUT-scale `Λ_UV`, the induced `M_Pl_emerg` falls below the observed
`M_Pl ≈ 10¹⁹ GeV`; the natural fiducial parameters pull `Λ_UV` toward
the Planck scale, not the GUT scale. -/
theorem G_N_from_a2_inverse_at_GUT_below_planck_squared :
    (1 / G_N_from_a2 (10 ^ 16 : ℝ) 15) < (10 ^ 19 : ℝ) ^ 2 := by
  unfold G_N_from_a2
  rw [one_div_div]
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hπ_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h3π_pos : 0 < 3 * Real.pi := by linarith
  rw [div_lt_iff₀ h3π_pos]
  -- Reduce to: 15 · 10³² < 10³⁸ · 3π.
  -- Sufficient: 15 · 10³² < 10³⁸ · 9 (since 3π > 9 because π > 3).
  have h_rhs_lower :
      (10 ^ 19 : ℝ) ^ 2 * 9 < (10 ^ 19 : ℝ) ^ 2 * (3 * Real.pi) := by
    apply mul_lt_mul_of_pos_left _ (by positivity)
    linarith
  have h_easy : (15 : ℝ) * (10 ^ 16 : ℝ) ^ 2 < (10 ^ 19 : ℝ) ^ 2 * 9 := by
    norm_num
  linarith

/-! ## §7. Higher-curvature `a_4` basis -/

/-! ### The Dirac `a_4` triple

Vassilevich Eq. (4.28) reads
`a_4 = (4π)^{-n/2} (1/360) ∫ tr_V{60 E_{;kk} + 60 R E + 180 E² + 30 Ω_ij Ω^ij
+ (12 R_{;kk} + 5R² − 2 R_ij R^ij + 2 R_ijkl R^ijkl)·𝟙}`.

For one four-component Dirac species (`tr_V 𝟙 = 4`, `E = -R/4`,
`tr(Ω_ij Ω^ij) = -(1/2) R_ijkl R^ijkl`), dropping total derivatives:

| structure | `60 R E` | `180 E²` | `30 tr Ω²` | bare × `tr_V 𝟙` | total |
|---|---|---|---|---|---|
| `R²`      | `−60`    | `+45`    | —          | `+20`           | `+5`  |
| `Ric²`    | —        | —        | —          | `−8`            | `−8`  |
| `Riem²`   | —        | —        | `−15`      | `+8`            | `−7`  |

so `a_4 = (4π)^{-2}(1/360)[5R² − 8Ric² − 7Riem²]` per species, i.e.
`(+30, −48, −42)/(12·180)` in this module's units.

**Independently:** Vassilevich Eq. (4.35) with the spin-1/2 row of his
Table 1, `(a,b,c,d) = (−7/2, −11, 6, 0)`, gives the same triple, and the
Weyl-basis decomposition returns the textbook Dirac conformal-anomaly
coefficients `c = 1/20`, `a = 11/360` exactly (see
`HigherCurvatureStructure.a4_beta` / `a4_gamma`).

⚠️ Corrected 2026-08-15. These read `(−5, +7, −12)/(12·180)` before —
values that are not proportional to the published triple (two of three
signs differ), that do not decompose consistently in the Weyl basis, and
that give a non-zero independent `R²` Stelle coefficient for a field
that is conformal. -/

/-- `a_4` coefficient of `R²` for the free Dirac fermion in 4D vacuum:

  `c_{R²} = + 30 N_f / (12 · 180 · (4π)²) = + N_f / (72 (4π)²).`

Christensen-Duff spin-1/2 values as collected in Vassilevich Eq. (4.28)
/ Eq. (4.35) + Table 1. -/
def a4_R_sq_coef (N_f : ℝ) : ℝ :=
  N_f * (30 / (12 * 180)) * fourPiSqInv

/-- `a_4` coefficient of `R_μν R^μν`:

  `c_{Ricci²} = − 48 N_f / (12 · 180 · (4π)²) = − N_f / (45 (4π)²).` -/
def a4_Ricci_sq_coef (N_f : ℝ) : ℝ :=
  N_f * (-48 / (12 * 180)) * fourPiSqInv

/-- `a_4` coefficient of `R_μνρσ R^μνρσ`:

  `c_{Riem²} = − 42 N_f / (12 · 180 · (4π)²) = − 7 N_f / (360 (4π)²).` -/
def a4_Riemann_sq_coef (N_f : ℝ) : ℝ :=
  N_f * (-42 / (12 * 180)) * fourPiSqInv

/-- For positive `N_f`, the `R²` coefficient is positive.

Restated 2026-08-15: this was `a4_R_sq_coef_neg` under the pre-correction
triple. The published Dirac value is `+30/(12·180)`, so the strict sign
is now positive. -/
theorem a4_R_sq_coef_pos {N_f : ℝ} (h : 0 < N_f) :
    0 < a4_R_sq_coef N_f := by
  unfold a4_R_sq_coef
  have h1 : 0 < N_f * (30 / (12 * 180)) := by positivity
  exact mul_pos h1 fourPiSqInv_pos

/-- For positive `N_f`, the `R_μν²` coefficient is negative.

Restated 2026-08-15: this was `a4_Ricci_sq_coef_pos` under the
pre-correction triple. The published Dirac value is `−48/(12·180)`. -/
theorem a4_Ricci_sq_coef_neg {N_f : ℝ} (h : 0 < N_f) :
    a4_Ricci_sq_coef N_f < 0 := by
  unfold a4_Ricci_sq_coef
  have h1 : 0 < N_f * (48 / (12 * 180)) := by positivity
  have h2 : 0 < fourPiSqInv := fourPiSqInv_pos
  nlinarith

/-- For positive `N_f`, the `R_μνρσ²` coefficient is negative.  This is
the one sign of the three that the 2026-08-15 correction left standing. -/
theorem a4_Riemann_sq_coef_neg {N_f : ℝ} (h : 0 < N_f) :
    a4_Riemann_sq_coef N_f < 0 := by
  unfold a4_Riemann_sq_coef
  have hpi := fourPiSqInv_pos
  nlinarith

/-- **Gauss-Bonnet sanity identity.** The combination
`R² − 4 R_μν R^μν + R_μνρσ R^μνρσ` of the `a_4` coefficients
evaluates to a specific rational + π combination. We compute the
"coefficient-side" GB identity:

  `c_{R²} − 4 c_{Ricci²} + c_{Riem²} = +180 N_f / (12 · 180 · (4π)²) = + N_f / (12 (4π)²)`.

This is **NOT zero** at the coefficient level — the topological
identity is at the *integrated* level, where the `R² − 4 Ricci² +
Riem²` density combination integrates to 32π² χ(M) on a closed
4-manifold. The Lean theorem checks only the local algebra; the
global topological vanishing requires manifold-level integration
(deferred to 6f.1).

Restated 2026-08-15: the combination was `−45/(12·180)` under the
pre-correction triple; with the published `(+30, −48, −42)` it is
`+180/(12·180)`, both value and sign. -/
theorem a4_gauss_bonnet_combination (N_f : ℝ) :
    a4_R_sq_coef N_f - 4 * a4_Ricci_sq_coef N_f + a4_Riemann_sq_coef N_f
      = N_f * (180 / (12 * 180)) * fourPiSqInv := by
  unfold a4_R_sq_coef a4_Ricci_sq_coef a4_Riemann_sq_coef
  ring

/-! ## §8. Correctness-push biconditional -/

/-- **Decision-Gate-E.2 calibration biconditional, corrected
2026-08-15.** The heat-kernel-derived Newton constant agrees with the
linearized ADW emergent Newton constant (`LinearizedEFE.G_N_emerg`)
iff the dimensionless ADW coefficient `α_ADW` equals **`1/4`** —
*exactly*, with no tolerance.

The locus moved from `α_ADW = 1` to `α_ADW = 1/4` because the traced
`a_2` gives `G_N_from_a2 = 3π/(N_f Λ²)`, one quarter of the
`G_N_sakharov = 12π/(N_f Λ²)` that `G_N_emerg` rescales. The
biconditional is exactly as sharp as before — a single point in `α` —
and it is now the *true* one. The former statement
(`a2_matches_GNemerg_iff_alpha_ADW_unity`, `↔ α = 1`) is false under the
correction and is replaced, not weakened: this version still pins `α` to
a unique value and still consumes both cross-module definitions.

Forward (→): if the two Newton constants agree, then
`3π/(N_f Λ²) = α · 12π/(N_f Λ²)`, forcing `α = 1/4` (using `Λ, N_f > 0`).

Backward (←): at `α = 1/4`, `G_N_emerg = (1/4) · G_N_sakharov` and the
heat-kernel result is `(1/4) · G_N_sakharov` by
`G_N_from_a2_eq_quarter_G_N_sakharov`, so they agree.

Substantive cross-bridge: invokes `LinearizedEFE.G_N_sakharov_pos` and
`LinearizedEFE.G_N_emerg` by name. -/
theorem a2_matches_GNemerg_iff_alpha_ADW_quarter
    {Λ N_f α : ℝ} (hΛ : 0 < Λ) (hN : 0 < N_f) :
    G_N_from_a2 Λ N_f =
      SKEFTHawking.LinearizedEFE.G_N_emerg Λ N_f α ↔ α = 1 / 4 := by
  have hG : SKEFTHawking.LinearizedEFE.G_N_sakharov Λ N_f ≠ 0 :=
    ne_of_gt (SKEFTHawking.LinearizedEFE.G_N_sakharov_pos hΛ hN)
  rw [G_N_from_a2_eq_quarter_G_N_sakharov]
  unfold SKEFTHawking.LinearizedEFE.G_N_emerg
  constructor
  · intro h
    -- h : (1/4) * G = α * G, with G ≠ 0
    exact (mul_right_cancel₀ hG h).symm
  · intro hα
    rw [hα]

end SKEFTHawking.HeatKernelExpansion

end
