# 10.D — Identifying the reservoir rate from a calibrated complex density response

The independent adversarial review on 2026-11-22 accepted the derivation as written. The reviewed source note has SHA256 `5a4956cbece48be6335377d91fff673ee17f49a0574772685fe71841d843c3da`. The accepted source-model packet `E1_DYNAMIC_DARK_RESERVOIR.md` has SHA256 `a78229756aea77e084b6c0aef59a462027760400b786283579997eee2aebb62c`. The underlying model follows the laboratory-frame reservoir equation in [Falque et al., arXiv:2311.01392v2, Appendix B.1](https://arxiv.org/html/2311.01392v2#A2.SS1). The source PDF is held in the repository literature corpus.

Use `E1_DYNAMIC_DARK_RESERVOIR.md`, equations (3), (7), and (9), on a locally homogeneous, stationary probe configuration. At a declared real laboratory angular frequency ω>0, write E=A_BdG−B, N=2n0 E, Q0=Z²−ES, and α(ω)=α0 g/(g−iω), with g=γ_R>0 and α0>0. Calibrate the transfer from the applied potential to microscopic density well enough to report complex χ=δn/V with an absolute complex-plane error bound. A transmitted intensity or a fitted peak location alone is not this measurement. The drift shifts Z; it does not shift ω in the material reservoir factor.

## Identification and interval

When E≠0 and the stationary response is finite and nonzero, recover α=(Q0−N/χ)/(2E). Since Re α>0 and Im α>0,

    g = ω Re α / Im α.

This identity does not require a separate α0 calibration. Retaining α0 as an independently known quantity supplies the consistency circle |α−α0/2|=α0/2. A single measurement is enough for identification in the exact one-pole model. Several frequencies and signed phase controls are needed to test that model against backgrounds, transfer phase errors and additional poles.

With fixed calibrated n0,E,Q0, a complex estimate χ̂ and |χ−χ̂|≤εχ<|χ̂|, the inferred α̂ satisfies

    |α−α̂| ≤ εα := n0 εχ / [|χ̂| (|χ̂|−εχ)].

This uses the inverse difference exactly before applying the triangle bound. Damping, flow, dispersion, density, detuning and other covariance or model errors require a separate propagated bound. For example, if |Q0−Q̂0|≤εQ, |N−N̂|≤εN, |E−Ê|≤εE<|Ê|, and χ's lower bound above is r_min=|χ̂|−εχ, form Ŵ=Q̂0−N̂/χ̂. One sufficient total bound is

    |α−α̂| ≤ [εQ + εN/r_min + |N̂| εχ/(r_min|χ̂|)] / [2(|Ê|−εE)]
             + |Ŵ| εE / [2 |Ê| (|Ê|−εE)],

where α̂=Ŵ/(2Ê). This is a conservative bound with no assumption of independent uncertainties. Positive Re/Im margins imply the following certified interval:

    g_- = ω(Re α̂−εα)/(Im α̂+εα),
    g_+ = ω(Re α̂+εα)/(Im α̂−εα).

Use the total error in place of εα when background terms vary. If either margin fails, the interval need not certify a positive finite rate. A necessary operational input is an actual calibrated χ̂ with a useful phase and amplitude error, not an assigned α̂.

## Frequency and required precision

For first design, if each real and imaginary component has error bounded by an equal absolute εα and the true positive components are x,y, the linear relative condition number is 1/x+1/y. With t=ω/g and α0 fixed, x=α0/(1+t²), y=α0 t/(1+t²), so this number is (1+t²)(1+1/t)/α0. Its minimum is near t=0.6573, the unique positive zero of 2t³+t²−1; both very small and very large t are ill-conditioned. This is a local design heuristic and assumes the quoted errors actually remain comparable across the sweep. Exact error and interval certification use the inequalities above. A nominal frequency sweep around the earlier top-hat fit may guide design, while the shaped flowing-horizon rate remains uncalibrated until the data and transfer are matched.

A simple conservative requirement for a polariton density-response comparison with nominal g_* is to compute the reviewed endpoint envelope from [g_-,g_+] and require

    2|E| max_{g ∈ {g_-,g_+}} |α(g)−α(g_*)| ≤ δ |D_*|/(1+δ),

with fixed other comparison inputs, D_*≠0 and δ the target fractional susceptibility tolerance. On a frequency/wavevector band this must hold uniformly (or carry each jointly varying input explicitly). The independently derived rate-free tests are preferable where their margins already pass. A partial or divergent confidence interval should be reported as such rather than used to certify a band. This rate measurement does not provide the noise covariance, thermal state, physical receiver transfer or DKM locality/growth assumptions.

## What the later ballistic experiment supplies

[Falque’s thesis, HAL tel-05238306v1](https://theses.hal.science/tel-05238306v1), is held as `Lit-Search/Phase-5w/primary-sources/FalqueThesis2025-tel-05238306v1.pdf` with SHA256 `cfcec7587ceb2633da1db8fc41d4f0a27571fadedb471341091efda98d9842ea`. Section 2.4 carries the dynamic reservoir equations (2.78)–(2.79). Section 4.4.2 fits the dispersion using the static ratio $g_r n_r\approx1.84gn$ from prior same-sample work. Section 5.2.2 reuses that ratio for the upstream fit in the later ballistic configuration. Figure 5.7 reports interaction fits in the two regions. These sections leave the reservoir rate itself uncalibrated.

Sections 5.1.2 and 5.2.4 demonstrate phase-sensitive optical reconstruction at the driven probe frequency. The reference at that frequency filters out the conjugate sideband. Section 5.2.3 supplies its distinct intensity-spectrum evidence. Sections 5.2.4 and 5.3 identify residual-field effects and leave the quantitative scattering matrix open. Chapter 6’s balanced-detection correlations are on a static homogeneous fluid at a different working point. The ballistic optical data can constrain field amplitudes and phase at the probe frequency. Applying the rate specification above also requires the calibrated physical forcing and the associated complex **density** response on the chosen stationary branch. This could use jointly calibrated field sidebands, or a separately validated reconstruction from the accessible channels with propagated error. Report the resulting error on the complex response before applying the rate interval and band test.

The independent source review verified these locators and the pinned PDF. The journal article’s verified citation is [Phys. Rev. Lett. 135, 023401](https://doi.org/10.1103/t5dh-rx6w).

## Rate identification from one calibrated complex optical sideband

Independent adversarial review accepted this conditional inverse. The reviewed note has SHA256 `a274fd15eccc09f9ce318e0eb651b84eae55d08bd4d60cef9aa1a0a0cc327e2f`.

Falque thesis tel-05238306v1 §§5.1.2 and 5.2.4 describes complex optical field reconstruction at the injected frequency. Use the accepted homogeneous B1/B2 inverse (E1_DYNAMIC_DARK_RESERVOIR.md, Eq.6) to test what such a channel can identify. This is an optical-forcing inverse problem, distinct from applying the potential-probe density formula directly to an optical signal.

At a nonzero real laboratory angular frequency ω, suppose the complex energy-equation source (f_s,f_t,0) is known after optical input calibration, material coefficients Z,E,S are known, and the measured complex intracavity particle-sideband amplitude u is calibrated after accounting for direct optical background and output transfer. Use the source-defined rotating frame, mean-field phase, and s=u+v_h, t=u−v_h. The two reduced stationary equations are

    Z s − E t = f_s,
    −(S+2α)s + Z t = f_t,
    α=α0 g/(g−iω), α0>0, g>0.

Assume the model is valid on this branch and the relevant response is finite. There is no forced reservoir source in this setup. With P=Z+E, an actual positive damping η and real E ensure P≠0. More generally require P≠0 explicitly. Reconstruction is

    s=(f_s+2E u)/P,   t=2u−s,
    α=(2Z u−f_t)/(2s) − (Z+S)/2,

provided s≠0. Thus one complex sideband plus the calibrated forward coefficients can recover the hole component within this model, despite its absence from that interferogram. For a real chosen mean field, δn=√n0 s. The exact rate is g=ω Re α/Im α, at ω≠0 with the model's nonzero α0 and g. No separate fit of α0 is required to identify g from this ratio.

This is a local homogeneous-response identification. The ballistic horizon reconstruction contains inhomogeneous and residual-field terms that must be bounded or excluded. The same symbol u must not refer to raw transmitted optical field before removing direct reflection/input mixing and identifying the intracavity amplitude. Both complex source components and their relative phase must be specified. A drive with only a particle-sideband source in the original two Nambu equations has f_s=f_t, but actual optics must show that coupling before using the simplification. A source that drives the reservoir directly requires using the full three-component inverse with that source, rather than the formulas here. Optical intensity alone supplies no complex u. Sections 5.2.4 and 5.3 report residual and incomplete scattering normalization, so the thesis does not already populate this uncertainty budget.

### Exact measurement error for fixed forward coefficients

Let û be the measured intracavity estimate with |u−û|≤ε_u, let ŝ=(f_s+2E û)/P, and set e_s=|2E/P| ε_u. With e_s<|ŝ|, define X̂=2Z û−f_t. Exact subtraction gives

    α(u)−α(û)=(2Z ŝ−X̂ (2E/P))(u−û)/(2 s ŝ)
             =(Z f_s+E f_t)(u−û)/(P s ŝ).

Hence a rigorous coefficient error is

    |α(u)−α(û)| ≤ |(Z f_s+E f_t)/P| ε_u / [|ŝ| (|ŝ|−e_s)].

At fixed f_s=f_t, the numerator prefactor becomes |f_s|. If Z f_s+E f_t=0 and the reduced inverse is nonsingular, then s=0 and the method supplies no identification. That zero-overlap control must be checked. Errors in the source phase, transfer, pump branch, Z,E,S and model reduction require a jointly propagated budget; the fixed-input bound does not cover them.

For ω>0 use the positive Re/Im interval rule in the existing reservoir measurement specification with ε_α from this calculation or a verified total budget. Negative laboratory frequencies give the reflected imaginary sign as a diagnostic control. A nonempty band still needs independent calibration, stability, finite-window/noise error and model validity. This identification supplies neither a horizon-run rate estimate nor a microscopic DKM transport or receiver certificate on its own.

In the compensated case `E=0` with `f_s≠0`, the density component is `s=f_s/Z` and the fixed-input error becomes `|Z|² ε_u/|f_s|`. This optical source can still identify the rate on the admitted branch.

An independent matrix solve reproduced the feedback and rate in 1,200 synthetic one-sideband cases, with 1,200 fixed-input error checks and 600 zero-overlap controls. The maximum scaled feedback and rate residuals were 1.44e-14 and 2.28e-13. A separate 7,776-case source-model comparison checked the full three-component adjugate, density-probe response and flowing poles. These calculations used controlled synthetic inputs.
