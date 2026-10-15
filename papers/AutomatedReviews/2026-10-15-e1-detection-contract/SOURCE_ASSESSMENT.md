# E1 source and algebra assessment

Base: `e9518f5b`. No new physical prediction, numerical formula, API or constants change. The manuscript makes its existing ideal gain/readout model conditional on measurements the model itself does not supply.

## Noise and apparatus

The held Falque2025 PDF, experimental implementation on printed p.4, reports coherent-probe intensity about two orders below the pump, intensity modulation at 5 MHz, and photodiode selection with a zero-span spectrum analyzer at 300 Hz resolution bandwidth. These are actual apparatus settings. They do not by themselves give an in-band background PSD, phase-noise rejection ratio or shot-noise-limited detection efficiency. The paragraph describing those settings was read in full, not inferred from a search hit.

The generated scalar `m*c_s^2/k_B=0.81K` is an energy expressed in temperature units. An energy identity does not specify a statistical state, mode occupation or measured PSD. No equality to either the FDR occupation floor defined by NoiseFloorPrediction or the modified-unitarity WKB occupation is asserted. The previous source-pinned carrier/statement assessment remains applicable; no new Lean result is claimed.

Amelio and Carusotto's public author preprint v2, Sec.IV.C printed pp.7–8, evolves coherent polaritons and a dark reservoir with paired deterministic equations15–16. Its comparison holds effective parameters fixed and shows reservoir-induced vortex motion and reduced coherence in a disordered flow. That supports the narrowly stated possibility of instability/coherence loss. It does not calibrate Falque's detector, prove a flat noise PSD or imply only shot noise remains. The final publisher page verifies bibliographic identity, but the 2020 revised article body was not acquired. The manuscript bibliography explicitly links the earlier preprint used for the model claim.

## Source acquisition provenance

Primary metadata checked at https://journals.aps.org/prb/abstract/10.1103/PhysRevB.101.064505 and https://arxiv.org/abs/1905.05855 . The latter identifies latest v2, dated2019-06-13, with related final DOI10.1103/PhysRevB.101.064505 and journal reference PRB101,064505(2020). Publisher title differs from preprint title; the registry preserves the final title and records the version distinction.

Existing `back_fill_primary_sources.py` exact-bibkey writer acquired https://arxiv.org/pdf/1905.05855v2 successfully. Its PDF leg validated magic before writing. The linked-checkout caller bound the writer's provenance root to its existing canonical `find_workspace()` result; writer source was not changed. The writer's sidecar records arxiv-pdf, actual URL, size and cache path. Every other sidecar entry is JSON-value identical to the base. The registry's existing Amelio2020 entry alone is reconciled, including actual E1 usage; no unrelated bibkeys changed.

Actual saved artifact: `Lit-Search/Phase-5w/primary-sources/Amelio2020.pdf`, 2136611bytes, 10pages, SHA256 `d0d48fa5c6f9b87c4e0483f853bf8cb039156fe6a4ff78470d57188f67977781`. PDF text includes the v2 identifier and June2019 date; relevant full paragraphs and equations were read from these saved bytes. Existing fidelity classifier returns `full` for this acquired preprint. The old metadata JSON remains preserved. This is not a manual fulltext upgrade or a claim that the final revision was read.

The corpus citation-source check still FAILS with13 missing registry keys; unrelated abstract/metadata tiers remain visible. A read-only acquisition-register render from this linked checkout also mislocates actually held sources because its WORKSPACE is PROJECT_ROOT.parent; that broad output was not retained or repaired under this exact-bibkey scope. No global source-readiness claim is made.

## Gain, band and identifiability

For Gamma=1, setting the adopted gain to1/2 yields omega_half/kappa_eff=ln(3)/(2pi). Dimensional omega_half still scales with kappa_eff. Even constant nonunit Gamma yields ln(1+2Gamma)/(2pi); allowing Gamma(omega) to vary can alter shape. Independent greybody, transfer and background calibration is therefore needed before a discrepancy can be assigned to the thermal factor.

The0.30 upper working-band choice is not backed here by a hydrodynamic/greybody error bound. The manuscript and plot use the same omega/kappa_eff coordinate, and call it an adopted working band. The model divergence atzero does not establish an accessible experimental interval. The lifetime threshold is necessary for the declared weak-loss expansion, not sufficient for actual signal detection.

## Figures and executable scope

The two exact figure functions were delegated as one owned package. Existing canonical platform records supply positions; only the Paris comparison is shown. The spectrum uses the same effective-frequency coordinate as the gain equation and states Gamma=1 and ideal readout assumptions. Exact2E1PNG exports honor the declared700x500 canvases at scale3, yielding2100x1500; actual pixels were inspected by author and lead. The compiled page3 places both without clipping. Source changes outside those exact functions were checked by AST; all executable formula AST is unchanged. The gain docstring alone is corrected to the fixed-positive-greybody lowfrequency asymptote Gamma/(2pi*omega/kappa), which diverges.
