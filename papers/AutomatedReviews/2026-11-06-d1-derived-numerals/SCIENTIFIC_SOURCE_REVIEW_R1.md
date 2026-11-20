# Independent bounded D1 scientific source review R1

Overall **REVISE / application HOLD**. The fixed-material scaling paragraph is scientifically acceptable within the declared model, and most source bindings are appropriate. One proposed companion binds the wrong platform and physical quantity. The existing crossover predicate compares different temperature normalizations. The Dean operating point and bilayer velocity/thermal-length conflict remain unresolved. No whole-paper, physical BUILD, numerical ceiling, publication or runtime acceptance is granted. L1 remains ROOT's publication lead; this is shared numerical-debt enabling review only.

## Authority, identities and method

Initial continuity check was fresh with changed=[]; the same packet is checked again at completion. Main delivery HEAD is 6505d01b4f7781d738408b91dc9c55fdc8cce157, primary is 4fca5970f4f4cb0b408ea33243076c72058f6e56, cumulative is 0fe8f21c7f83fa4d626ab04742bd3b871fd1ce1f. Proposal candidate89a5d6d3eb233f4ffe03bd845b12f95d966ea18f is historical; the scientific draft/formulas/generator hashes are unchanged in the current packet. Main status contains only the already present untracked D1 finding/evidence directory; this reviewer did not create it.

Read CLAUDE.md, WAVE execution/scientific contracts, claims-reviewer persona, continuity contract, referenced notebook and existing disposition/charter queue, retained proposal and finding, producer sources and retained ROOT probe/Verify receipts. This is the explicitly bounded family review, not the persona's whole-manuscript sentence walk. No project modules, tests, Lean, builds, extraction or native runtime were run. Standard-library JSON/AST/hash/file inspection and arithmetic on retained receipt values only. No repository/notebook/registry/Git/runtime/slot/cache changes. No new routing ledger or finding closure.

The final JSON records exact proposal hashes, all38 site contexts/classifications, all23 proposed SCALARS identifiers, the22 counted site substitutions, and every uncounted companion. ACCEPT below is acceptance of the conditional scientific source binding, not application or physical validation. Original D1 Aug15 1.1 noise/crossover BLOCKER,2.8 velocity mismatch and all dispersion/damping/readout BUILDs retain their owners and full strength.

## Fixed-material scaling — ACCEPT

D1 Eq:delta-diss and formulas.py give Gamma_H=(gamma1+gamma2)*(kappa/c_s)^2 and delta_diss=Gamma_H/kappa=(gamma1+gamma2)*kappa/c_s^2. Eq:delta-disp gives delta_disp=-(pi/6)*(kappa*xi/c_s)^2. For kappa>0,c_s>0,xi>0 and fixed nonnegative material transport coefficients, delta_diss is linear, delta_disp quadratic, and

    delta_diss/abs(delta_disp)=6*(gamma1+gamma2)/(pi*xi^2*kappa).

With positive damping this decreases as1/kappa; with zero damping it stays identically zero (the proposed phrase “decreases inversely” can be read as the nonzero regime). Units cancel: gamma/(xi^2*kappa) is dimensionless. The proposed replacement correctly distinguishes the rate from its dimensionless correction.

The adopted microscopic estimate Gamma_Bel=sqrt(n1D*a_s^3)*kappa^2/c_s gives the same rate/correction distinction at fixed n1D,a_s,c_s. Its coefficient is an adopted UV-matching model, not a microscopic derivation supplied by the algebra. ROOT's retained operating-point receipt rc0 reports doubling ratios Gamma4,delta_diss2,abs(delta_disp)4,gamma1/gamma2 unchanged, ratio0.5. Its fixed-material probe uses upstream c_s,xi while the hierarchy D is horizon-derived; these are deliberately different numerical constructions with the same fixed-input exponent, not two evaluations of the same dispersion number.

The existing canonical finding is review:2026-11-06-d1-derived-numerals:D1:1.1. Its retained original Verify rc1 first passes production Gamma/delta assertions and then fails on contradictory prose. This is actual expected RED evidence, not this review's execution. No duplicate finding/closure. The replacement's sweep caveat is essential: changing a_s changes EOS, sound speed, healing length, microscopic coefficients and possibly density/flow/horizon derivative. Fixed geometry alone does not fix kappa. Recompute the background before assigning sweep exponents or identifiability.

## Crossover normalization — REVISE exact predicate; conditional qualitative ACCEPT

The full Planck equation is n_H=1/(exp(omega/T_eff(omega))-1), with n_noise=delta_diss=Gamma_H/kappa, not delta_diss/2. For delta_diss>0 the dimensionless equation is x=ln(1+1/delta_diss), where x=omega_cross/T_eff(omega_cross). For a frequency-dependent dressed temperature this is an implicit physical-frequency equation; the log is not by itself a solved omega. At delta_diss=0 there is no finite crossover; a finite logarithm is not defined. Require positive T_eff and the perturbative modified-unitarity regime2*delta_diss<1 plus control of the expansion on the chosen band.

compute_bec_hierarchy stores this x in misleading legacy omega_cross_over_TH. PlatformParams.T_H=kappa/(2*pi) is bare, and omega_max_over_TH=omega_max/T_H=2*pi/D^(2/3). Therefore cross_below_cutoff=x<U compares coefficients with different normalizing temperatures. The mathematically correct test is

    x*[T_eff(omega_cross)/T_H] < U,  U=omega_max/T_H.

The manuscript's listing6.44T_eff versus121T_H is not an equality of scales; the ordering needs the ratio. It is justified as a small-correction approximation only with its hypothesis stated, not as an exact consequence of the current boolean. The existing WKB source and D1 Eq:bogo-ratio use T_eff/T_H=1/(1+delta_total). Earlier D1 Eq:teff-fields instead defines T_eff/T_H=1+delta_disp+delta_diss; those differ already at first correction order (opposite sign), not merely by dropping quadratic terms. Do not silently treat both as the same physical temperature. This convention reconciliation is already part of the original charter's crossover/WKB obligations, not a new pipeline or closure requirement invented here.

Under the explicitly leading, frequency-independent WKB truncation delta_total=delta_disp+delta_diss, arithmetic on ROOT's retained values gives:

| Platform | T_eff/T_H | omega_cross/T_H | omega_max/T_H | upper bound on T_eff/T_H needed for ordering |
|---|---:|---:|---:|---:|
| Steinhauer |1.000061555|10.647696877|115.033363463|10.804256141|
| Heidelberg |0.998482992|6.434262395|121.066380079|18.787347176|
| Trento |1.000084788|11.168162764|109.504160776|9.805860443|

Thus a ratio even bounded by2 would preserve these orderings. This demonstrates the wide conditional margin; it does not supply that bound for the actual physical system. D1's broad statement that both cutoff and gradient-expansion control are checked is not established by the generator, which never computes T_eff or a higher-order remainder. PlatformParams has nonzero higher-order coefficients; their negligible effect at omega_cross must be evaluated/bounded if invoked, not inferred from a horizon-only delta. Retain full Planck law/floor semantics and correct stale docstring/CLI ln(2/delta), delta/2 labels through the existing producer owner; do not regress to them.

## Wrong-quantity companion — REVISE

REPLACEMENTS.json and proposal uncounted_BEC_companions include source_line1215,column64,literal110:

    LKB polariton (steep, $D=0.94$) & $\sim134$ mK & $-46\%$ & $110\%$ & neither

The proposed replacement is input{tables/trento_cutoff_over_th.tex} followed by unskip in that110% cell. Original physical quantity is polariton Gamma_pol/kappa, represented as percent (110%=1.10, dimensionless damping validity ratio). Producer quantity is Trento omega_max/T_H=109.504160776..., a dimensionless frequency/temperature ratio rounded to110. Numerical equality after rounding is not platform/source/quantity identity; it would become an undetectably wrong provenance even while rendering110%. Delete this occurrence from the replacement package. Retain the actual Trento cutoff occurrence at line1263,column48 in “omega_max=121T_H,115T_H and110T_H respectively.” No source was applied; this is a concrete proposal defect only.

## Dean operating point and reduction — HOLD

ROOT's actual retained results establish three distinct routes: gradient2e12s^-1 gives canonical T_H2.4313249424140624K and angular omega_H318309886183.79065s^-1; rounded2.4K gives314208814097.29535s^-1; c_s/L=(4.4e5)/(200nm) gives2.2e12s^-1. The proposed registered-gradient chain is a reasonable prospective choice consistent with provenance's stated rounded origin, but is not automatically the physical geometry or a measurement. Relative frequency change from rounded route is about1.3%, above the project's0.5% arithmetic tolerance. A source-level operating-point decision must precede integration, with coherent caption/figure/band/greybody/error consumers and explicit geometry uncertainty. Do not silently overwrite registered constants or adopt2.2e12.

Keep exact theorem literals at sites22/23 unchanged. The quoted statement proves its fixed-literal inequality and does not automatically certify the revised physical point. As elementary arithmetic, using geometric2.2e12 raises4omega_H to about1.40056e12s^-1, above pi*4.4e5/1e-6≈1.38230e12s^-1: the claimed four-omega integration band is sensitive to this choice, even though the registered2e12 route remains below threshold. This reinforces the need for explicit operating-point evidence and uncertainty rather than treating10% gradient difference as harmless rounding.

The51nm scale uses retained monolayer v_F1e6 in hbar*v_F/(k_BT), while D1 explicitly identifies bilayer v_FL≈6.2e5m/s. The profile term assumes that thermal scale is l_ee and a physical error envelope; its evaluation is not derivation of a bilayer collision mean free path. With the bilayer number the scale/term would change, but this review does not adopt that alternate model or resolve original2.8. Proposed zeroing of the other additive term is algebraically appropriate for isolating contributions; maintain hypotheses and distinguish omega=omega_H estimate from the full[0,4omega_H] band. The evanescent contribution scales asomega^2, so the quoted≈1.5% atomega_H is not a uniform two-percent bound over that band (factor16 at4omega_H).

## Remaining scientific families and numerical closure limits

Lorenz Sommerfeld constant, adopted conductance conversion/Johnson current PSD and polariton inverse-lifetime/linewidth conversions have valid proposed source bindings. Their measurement/model status and units must be retained. A converted scalar does not validate the excess PSD shape, greybody applicability, integration-time claim, physical noise state or bath. Existing D1 peak-at50GHz language is not justified by a constant-greybody omega/(exp(a*omega)-1) spectrum: this positive-frequency excess decreases from its low-frequency plateau. Do not expand the JN family's ACCEPT to those original obligations. Preserve approximate inverse8ps/80micro-eV routes, which are not numerically identical; preserve polariton nonperturbative scope/adverse-device result.

Sites13,32,38 remain binding gaps. Do not replace a bilayer velocity derivation withsqrt(2)c_s or a noise-state derivation with a temperature-shaped number. No missing Lean theorem or global absent-producer claim is made. There is no admitted LSP in this assignment; Lean LSP/type/import/history completeness is explicitly NOT ESTABLISHED. Exact constants and existing Lean citations are preserved; no proof discovery, weakening, rebuilding or absence inference occurred.

check_d1_hierarchy_table currently reads raw draft text and parses numeric cells and digit-only crossover coefficients. Generated input snippets fail that consumer contract; moving a table into input removes its raw tabular. This is an integration HOLD distinct from scientific source validity, not permission to weaken the check, duplicate numbers, invent parser infrastructure or change the debt ceiling. ROOT must resolve through the existing owner and run actual scoped producer/check/control/render verification after source decisions. No139→117 claim follows from this review:22 substitutions are prospective, not accepted current census reduction.

## Next substantive repairs

1. Remove the wrong polariton110 companion; retain every other BEC companion by platform, quantity, context and normalization, not numeral matching.
2. Apply/review the exact model-qualified scaling correction under its existing canonical finding; preserve fixed-material/sweep distinction and original full BUILD.
3. Reconcile dressed-temperature conventions through the existing WKB/crossover owner; put crossover/cutoff in common units and retain implicit-frequency/higher-order regime obligations. Current predicate cannot be an exact witness.
4. Adjudicate Dean source point and bilayer mean-free-path assumptions with source/physical evidence; propagate the chosen point coherently to physical consumers without rewriting exact quoted theorem constants. Evaluate the integration window and uncertainty, not just the central frequency.
5. Bind the remaining producer gaps or retain HOLD, preserve measured inputs, then execute existing scoped scientific/consumer checks and independent rendered review through ROOT. None of these steps alone discharges original physical dispersion, damping, noise/readout or whole-publication acceptance.

## Complete per-family disposition

- **ACCEPT — BEC hierarchy values, sites 1,2,3,4,5,6,7,8,9,10,11:** Canonical dimensionless horizon corrections and floor, conditional on adopted smooth background, T=0 Beliaev matching, pi/6 normalization. Source binding is scientifically appropriate; application remains on compatibility/evaluation hold.
- **ACCEPT — Dean adopted sound speed, sites 12,16,18,26:** Retain source/adopted c_s=4.4e5 m/s; do not back-compute from monolayer velocity.
- **HOLD — Dean bilayer velocity, sites 13:** Derived hbar*sqrt(pi*n)/m*, distinct from monolayer 1e6 m/s; producer/input binding unresolved. Do not substitute sqrt(2)*c_s as a new derivation. Original D1 2.8 owner retained.
- **HOLD — Dean quasi-1D, sites 14,15:** Proposed additive producer isolates canonical terms correctly but retains monolayer thermal-length assumption and prospective gradient. Both hypotheses and physical envelope derivation remain owed.
- **ACCEPT — Sommerfeld Lorenz reference, sites 17:** Existing (pi^2/3)*(k_B/e)^2 producer, V^2/K^2. This is a reference constant, not measured Lorenz enhancement or physical Hawking validation.
- **HOLD — Dean temperature/frequency, sites 19,20,27:** No operating point adopted by this review: registered gradient2e12, geometry2.2e12 and rounded2.4K routes differ. Adopted-gradient proposal is defensible only after explicit source/consumer reconciliation.
- **ACCEPT — Dean transverse threshold, sites 21:** pi*c_s/W at n=0 in assumed Dirichlet strip, angular s^-1. Conditional source binding accepted; physical band conclusion must use accepted omega_H and justified boundaries.
- **ACCEPT — Exact theorem constants, sites 22,23:** Retain exact literals in quoted theorem: c_s=4.4e5 m/s and omega_H=3.14e11 s^-1. No numerical generation/replacement and no new native proof acceptance.
- **ACCEPT — Dean conductance/Johnson PSD, sites 24,25:** Existing sigma=4e^2/h conversion in S and 4k_BT sigma current PSD in A^2/Hz. Cross-device conductance assumption and PSD convention must remain explicit; noise shape/time claims not accepted.
- **ACCEPT — Polariton measured/adopted inputs, sites 28,29,30,31,34,35,37:** Retain source/adopted surface gravities, mass and linewidths with citation/provenance. Site30 is SI representation of source input, not a physical model prediction.
- **HOLD — Polariton noise temperature, sites 32,38:** m*c_s^2/k_B is algebraically dimensioned as K; no accepted producer/physical noise-state binding established by proposal. It is a mean-field scale, not detector or bath temperature. No absent-code/proof assertion.
- **ACCEPT — Polariton decay conversion, sites 33,36:** Inverse adopted Paris8ps and Penn linewidth/HBAR conversion have the proposed source/units. Preserve approximate lifetime/linewidth equivalence and separate channels; do not promote perturbative validity for these adverse devices.

All38 original classifications are accepted as bounded source/quantity classifications:25 derived,11 measured/source/adopted,2 exact theorem quotes. The25 derived occurrences contain22 prospective substitutions and3 binding gaps. The23SCALARS comprise6 BEC corrections,3 crossover coefficients,3 cutoff coefficients,1 Heidelberg ratio and10 non-BEC scalars; this is distinct from22 counted occurrences. Every scalar and companion is listed in the JSON. Of14 companion occurrences,13 have coherent BEC quantity identity; one polariton occurrence is REVISE. Source compatibility and physical conditions remain holds as stated.
