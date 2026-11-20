# D1 crossover: common-unit construction in the existing WKB branch

ROOT manual construction for the existing D1 numerical-source/WKB obligation. Source is immutable commit `5a5d36fed74a83dcf4746e95b8f7673309e11d27`; exact source hashes and retained canonical-value arithmetic are in the adjacent JSON. No candidate source edits, project imports, Lean/native execution or physical model selection occurred. This is an independent-review candidate, not accepted scientific closure. L1 remains publication lead.

## Three temperatures must not be identified

1. `HawkingUniversality`'s defined parameter record and D1 `eq:teff-fields` use `T_parameter/TH = 1 + delta_total` at their stated order.
2. `src/wkb/connection_formula.py::effective_surface_gravity` uses `T_thermal/TH = 1/(1 + delta_total(omega))`. This sets the exponential of the thermal component. The older `src/second_order/wkb_analysis.py` instead uses exponent proportional to `1-delta_total` and a first-order `1+delta_total` temperature expression. This is a real first-order convention/model mismatch; this construction does not decide which expression follows physically from the action.
3. `src/wkb/bogoliubov.py::modified_bogoliubov_coefficients` returns `T_eff = omega/log(1+1/n_total)`, inverting the TOTAL occupation including the noise floor. That is a brightness temperature, not the thermal exponential parameter when the floor is nonzero. `SpectrumPoint.T_eff` inherits it. At a thermal/floor crossover, `n_total=2*delta`, so `T_brightness/T_thermal = log(1+1/delta)/log(1+1/(2*delta)) > 1`. Retained factory arithmetic gives about 1.070, 1.120 and 1.066; these are not rounding differences.

No generator, sentence or plot may switch between these meanings by spelling them all T_eff. Original physical derivation/matching remains owed, rather than being discharged by naming.

## Exact conditional common-unit theorem

Consider only the existing natural-unit BEC `PlatformParams` factories, with kappa=c_s=1, xi=D, positive delta=gamma_dim, and `0 < 2*delta < 0.999` so the Bogoliubov decoherence cap is inactive. Set `TH=1/(2*pi)` and `a=1+delta_disp+delta`, and require `a>0`.

The factories impose `gamma_2_2=-gamma_2_1`; with the implemented acoustic shell k=omega/c_s their retained second-order correction vanishes as an exact real expression. Each third-order coefficient equals `delta*D^2/3`; their sum gives

    delta_higher(omega) = delta*D^2*omega^4.

This is the supplied-coefficient third-order branch actually passed by `compute_spectrum`, not a claim about unknown higher EFT orders. `perturbative_spectrum` passes only second-order coefficients, so it corresponds here to dropping this quartic term.

Let `L=log(1+1/delta)`, `y=omega/TH`, and `eta=delta*D^2/(2*pi)^4 >= 0`. Below the implementation's UV-suppression switch, at zero environmental temperature, the original modified-unitarity normalization gives `n_H = 1/(exp(omega/T_thermal(omega))-1)` and `n_noise=delta`. Therefore the crossover equation in COMMON bare-TH units is

    F(y) = a*y + eta*y^5 - L = 0.

For y>=0, `F'(y)=a+5*eta*y^4>0`, while F(0)=-L<0 and F(y) tends to positive infinity. Hence exactly one positive root y_star exists. The positive-temperature fallback in the source is never used on this domain. If delta=0, no finite thermal/floor crossover exists; the logarithm is not a finite result. Negative coefficients or loss of a>0 are outside this theorem, not automatically repaired by the source's fallback.

Put `y0=L/a` and `epsilon=(eta/a)*y0^4`. Then

    y0/(1+epsilon) <= y_star <= y0.

Proof: F(y0)=eta*y0^5>=0. With z=y0/(1+epsilon), z<=y0 and
`a*z+eta*z^5 <= a*z*(1+(eta/a)*y0^4)=a*y0=L`, so F(z)<=0. Strict monotonicity proves the bracket. It also gives `(y0-y_star)/y0 <= epsilon/(1+epsilon)`. This bounds the retained quartic correction relative to the leading expression WITHIN THIS BRANCH; it is not a physical EFT truncation/remainder certificate.

## Retained factory instances and UV consistency

Using only retained canonical D, delta and delta_disp values (adjacent JSON):

| Factory | Common-unit crossover bracket y_star | epsilon | y0/(omega_max/TH) |
|---|---:|---:|---:|
| Steinhauer | [10.647696537, 10.647696877] | 3.195e-8 | 0.092562 |
| Heidelberg | [6.434260822, 6.434262395] | 2.444e-7 | 0.053147 |
| Trento | [11.168162466, 11.168162764] | 2.665e-8 | 0.101988 |

All upper endpoints are below HALF the implemented cutoff. `exact_connection_formula` sets its UV factor to one up to that half-cutoff switch, so the preceding Planck/noise calculation is self-consistent within the actual implemented branch. This does not assert that a sharp model switch is a derived physical transmission law. The present generator's log-only `omega_cross_over_TH` values remain mislabeled/misnormalized even though its qualitative below-cutoff outcome happens to agree for these factory instances.

These decimal bounds are explanatory floating-point arithmetic on retained producer results, not outward-rounded interval-arithmetic certification. The analytic bracket is exact under the stated real hypotheses. A future numerical implementation must verify actual producer binding, domain, finite arithmetic/residual/error requirements and every consumer, not take this displayed table as its runtime certificate.

## Repair and acceptance boundary

The next source repair can expose the log as `omega_cross_over_Tthermal`, calculate the bare-TH frequency with an actual common-unit witness (or a certified model bracket), and use that same normalization for cutoff/accessibility. Any compatibility treatment of the legacy key must preserve its documented meaning and actual consumer contracts; no code/API change is specified or accepted by this manual result. Preserve the original Planck law and full noise floor, do not restore ln(2/delta) or delta/2.

The complete physical temperature convention must still be derived/matched across the action, the two WKB implementations and the universality record. Brightness temperature must retain its own meaning. The canonical generator, manuscript, spectra/plots and physical error band all remain consumers of that obligation. Retained quartic smallness cannot stand in for uncomputed higher-order, greybody or device calibration bounds. This construction neither closes original D1 physics nor authorizes the wider numeral migration; the wrong polariton-to-Trento substitution and graphene point/velocity/band obligations retain their independent holds.

Before a new Lean task, follow statement/type/import/history discovery through the Lean4 skill and admitted LSP. No claim that these lemmas are absent is made here; no LSP or kernel proof has been performed. This manual construction requires independent mathematical/source review before application, and later ordinary numerical/native/publication gates remain required.
