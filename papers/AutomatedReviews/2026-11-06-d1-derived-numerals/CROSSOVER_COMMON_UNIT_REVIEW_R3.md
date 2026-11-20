# Independent D1 common-unit crossover construction review R3

**ACCEPT the manual mathematical/source construction only.** The common-unit equation, unique-root proof, analytic bracket, retained arithmetic and three-temperature distinction are correct for the explicitly selected natural-unit factory WKB branch. No source/API implementation, physical temperature convention, unknown-order EFT remainder, numerical interval certificate, default spectrum sampling, canonical closure or publication acceptance is established. Wider numeral migration remains HOLD and original physical BUILDs remain full strength.

## Authority and immutable source

Initial continuity check from the cumulative checkout was fresh, changed=[]. Cumulative packet HEAD is5ffb68b3ac298b211b320fc172f13a8f887050b6. All scientific source reads were read-only git show against immutable main commit5a5d36fed74a83dcf4746e95b8f7673309e11d27, not concurrent live scientific files. All six committed source SHA256 values in the proposal match exact commit blobs. The retained OPERATING_POINT_R1.json blob SHA256 matchesd06a90dd7ad91367f514c354ce977ba0b175fef2e0c78f136ba009ea30d5b1b0. Reviewed current referenced notebook and queue, retaining ROOT's L1 lead and ongoing full-profile freeze; no concurrent project imports/execution, graph, Lean/build/native work or process interactions occurred. Standard-library arithmetic on retained values and file/hash/source inspection only.

## Complete source-to-occupation flow

PlatformParams factory returns natural kappa=c_s=1, xi=D, gamma1=gamma2=delta/2, gamma22=-gamma21, and each gamma3 coefficient=delta*D^2/3. With acoustic on-shell k=omega, the canonical second-order numerator cancels in exact real arithmetic; the third-order sum isdelta*D^2*omega^4. This relies on the supplied factory coefficients and acoustic shell, not a derived physical dispersive-shell cancellation or physical coefficient measurement. Cancellation need not be bit-exact for separately evaluated IEEE expressions; no floating implementation proof is claimed.

compute_spectrum passes all three gamma3 coefficients through exact_connection_formula into effective_surface_gravity. The latter computes delta_total=delta_disp+delta+delta*D^2*omega^4 and kappa_eff=1/(1+delta_total) when its denominator is positive. Stokes geometry is computed as metadata and does not modify the exponent. exact_connection_formula uses exp(-2*pi*omega/kappa_eff), multiplies by a UV factor, and forms delta_k=2*Gamma_H/kappa=2delta from the leading horizon damping. It does not use the frequency-dependent quartic term as an additional decoherence rate. That is the implemented contract, not a new physical identification.

For0<2delta<0.999 the min(delta_k,0.999) cap in modified_bogoliubov_coefficients is inactive. On the positive-frequency unsuppressed branch letb=exp(-omega/T_thermal), so0<b<1. Then

    alpha_sq=(1-2delta)/(1-b)
    beta_sq=b*(1-2delta)/(1-b)
    n_H=beta_sq/(1-2delta)=b/(1-b)=1/(exp(omega/T_thermal)-1).

The full normalization is indispensable; leaving a residual factor1-2delta would give a different equation. WithT_env=0 the actual fdr_noise_floor givesdelta_k/2=delta. Thusn_total=n_H+delta. These quantities are not pure-state amplitudes or a detector temperature. At the rootb=delta/(1+delta), strictly between0 and1, so the source's deep-thermal b>=1 sentinel branch is not used in the real model. The capped and dk>=1 fallbacks are also inactive. This argument establishes real-expression source correspondence, not arbitrary machine-exponent/underflow behavior.

perturbative_spectrum calls the same effective_surface_gravity but passes only gamma2 coefficients, leaving allgamma3 defaults zero. It also omits noise/decoherence/UV suppression. It therefore has the same leading thermal denominator here, with the quartic term dropped; it is not numerically identical to the total spectrum. Its docstring's reference to the older wkb_analysis route does not override actual call flow.

## Common-unit equation, existence and bracket

Use positive bareTH=1/(2pi), y=omega/TH, delta>0, a=1+delta_disp+delta>0 and eta=delta*D^2/(2pi)^4>=0. The supplied factory instances haveD>0, hence positive finite cutoffU=omega_max/TH=2pi/D^(2/3). This explicitD>0 specialization is appropriate for their cutoff interpretation; the polynomial theorem itself only requireseta>=0.

The denominator is a+delta*D^2*omega^4, positive for every realomega. Therefore kappa_eff is positive and the positive-temperature denominator fallback is inactive. The exponent magnitude is

    omega/T_thermal=2pi*omega*(a+delta*D^2*omega^4)=a*y+eta*y^5.

WithL=log(1+1/delta)>0 the exact unsuppressed crossover equation isF(y)=a*y+eta*y^5-L=0. Continuity, F(0)=-L<0 and F(y)→infinity prove existence on positive reals. SinceF'(y)=a+5eta*y^4>0, the positive root is unique. This remains true foreta=0; theny_star=L/a exactly. Delta=0 has no finite thermal/floor crossover, and negative damping or a<=0 is outside this construction.

For y0=L/a>0 andepsilon=eta*y0^4/a>=0, F(y0)>=0. Setz=y0/(1+epsilon)>0. Sincez<=y0,

    a*z+eta*z^5 <= a*z+eta*z*y0^4
                         =a*z*(1+epsilon)=a*y0=L.

ThusF(z)<=0 and strict monotonicity yieldsz<=y_star<=y0. Consequently0<=(y0-y_star)/y0<=epsilon/(1+epsilon). The proposal's proof is valid, including the zero-quartic equality case. This is an exact real-model inequality; its small coefficient is not a bound on omitted physical EFT orders or microphysical error.

The source UV factor equals1 foromega<=0.5omega_max and otherwise switches toexp(-(omega/omega_max)^3). Requiringy0<U/2 guarantees the entire analytic bracket/root is inside the unsuppressed branch, not merely below the nominal cutoff. This is stronger and necessary for the displayed Planck equation to describe that implemented branch. All retained instances satisfy it with ample margin. No physical validity of the sharp switch is inferred.

## Independent arithmetic and temperature meanings

Recomputed every JSON row field using standard-library arithmetic on the exact retained receipt: a,L,eta,y0,lower/upper bracket,epsilon,cutoff ratio and brightness ratio match within2e-14 relative tolerance. This is a consistency comparison of explanatory floating values, not outward-rounded certification.

| Factory | Root bracket in bareTH units | y0/U | Brightness/thermal at crossover |
|---|---:|---:|---:|
| Steinhauer |[10.647696536808606,10.647696876991713]|0.09256181473325803|1.0696332242061677|
| Heidelberg |[6.434260821752808,6.43426239452117]|0.05314656629149211|1.1202191959444299|
| Trento |[11.168162466374516,11.168162763965412]|0.10198847865481295|1.0661760136773768|

The JSON fieldrelative_retained_quartic_bound storesepsilon, not the slightly tighterepsilon/(1+epsilon). This remains a valid conservative bound and matches the Markdown table labelled epsilon; no scientific correction is required, but future numerical consumers must not confuse these meanings. Neither decimal endpoint is promised outward rounding for the true real factory values.

The three temperatures are distinct. The manuscript eq:teff-fields and HawkingUniversality.universalEffectiveTemp parameter record useT_parameter/TH=1+delta_total at their declared order. The selected WKB exponent usesT_thermal/TH=1/(1+delta_total(omega)). The old second_order/wkb_analysis.py executable exponent uses1-delta_total, yieldingTH/(1-delta_total) on its normal branch, with the first-order1+delta_total form appearing in its description/fallback. The opposite first-order signs between old and current WKB are real convention/model debt, not repaired by assigning names.

modified_bogoliubov_coefficients instead returnsT_eff=omega/log(1+1/n_total), inherited bySpectrumPoint.T_eff. This is brightness temperature of the total occupation includingfloor. At crossover n_H=n_noise=delta, n_total=2delta, hence

    T_brightness/T_thermal=L/log(1+1/(2delta))>1.

The retained ratios are correct; for Heidelberg the difference is about12%, not rounding. No caller may replaceT_thermal in the crossover exponent withSpectrumPoint.T_eff. The manual proposal keeps this distinction properly and does not decide which convention follows from a physical action/state.

## Consumer and acceptance limits

The present hierarchy generator's log-only legacyomega_cross_over_TH is a thermal-normalized coefficient, while its cutoff is bareTH-normalized. The manual construction supplies a conditional common-unit mathematical witness; it does not change the generator's current result, pass its consumers or close the historical physical crossover finding. Any later generator/spectrum/manuscript/plot application needs actual producer/domain/error/control/consumer verification through existing owners.

An additional consumer limit: compute_spectrum defaults toomega_max_factor=5, whereas all three accepted real-model roots exceed5TH. Therefore default spectrum sampling does not reach these crossovers. A caller requesting an extended band must also verify its grid/coverage, UV branch and error regime; acceptance of the manual result is not evidence of an actual resolved crossover plot or numerical root. No default API change is proposed or authorized here.

All load-bearing hypotheses are accounted for in the scoped construction: natural factory coefficient relations, real finite inputs, positive-frequency root,delta>0,2delta<0.999,a>0,T_env=0 and upper bound below halfcutoff. For the stated finite factory applicationsD>0 is verified from the retained values. These hypotheses establish the implemented real-model branch, not physical applicability or full floating arithmetic safety. The physical bath/state/dispersion/temperature convention, higher EFT remainder, greybody/device calibration, experimental bounds and actual numerical integration remain owed. Wider numeral migration retains the wrong-companion and Dean operating-point/velocity/transverse-band holds. No absent-Lean claim, LSP/proof search, native proof or kernel acceptance is made.

Wrote only/tmp/d1-common-unit-crossover-review-r3.md and.json. No repository, notebook, registry, Git, runtime, cache or slot changes, and no interaction with the live full-profile process. Final same-packet continuity check must remain fresh before delivery. This is independent ACCEPT of the manual construction only; original physical BUILD stays OPEN and canonical closure is not performed.
