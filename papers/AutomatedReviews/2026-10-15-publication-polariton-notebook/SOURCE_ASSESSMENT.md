# Polariton notebook source and saved-output evidence

Evidence assessment against `0b984829`. This assessment combines direct reading of all current notebook sources and saved text/MIME structure with the lead's actual execution, numerical-comparison and pixel-inspection receipt. The evidence author did not execute a notebook, change output payloads, acquire sources or inspect browser-rendered HTML. Independent final whole-notebook review accepted the bounded scope; see SCOPED_REVIEW.md. The separate ledger audit accepted the exact two closures; see SCOPED_REVIEW.md.

## Source and model scope

`notebooks/Phase5d_Polariton_Technical.ipynb` retains 15 cells in their original order. Its local Paris-only view reads canonical inputs from `src/core/constants.py`, calls `src/core/formulas.py`, and displays the two canonical figure functions from `src/core/visualizations.py`. Penn's placeholder horizon parameters are excluded from the numerical device tables. No new parameter registry, formula, physical derivation or formal proof-count claim is introduced.

The held Falque author preprint is [arXiv:2311.01392v2, 5 July 2024](https://arxiv.org/abs/2311.01392v2), distinct from its 2025 publication metadata. The lead read its relevant pp.4–7. Its spectral reconstruction includes the reservoir; it measures fluid profiles and excitation dispersions, while the discussion predicts Hawking emission. It does not establish an observed thermal Hawking flux, a matched reservoir-free speed comparison or a measured spectrally flat detected noise floor.

The notebook now treats the entire quadratic dispersive law and the ideal shot-noise readout as adopted models. A 300 ps projection meets the declared necessary weak-decay criterion only; this does not establish control of dispersion or omitted terms. The reported approximately 4 K cryostat is a device condition. The final occupation calculation hypothetically assumes equilibrium at that temperature and omega=kappa; it is not a measured mode population and is not inferred from mean-field energy.

## Existing execution route and actual generated outputs

The lead first verified the existing `sk-eft-hawking` kernel through a bounded native context probe: project Python 3.14.8, notebook-directory working context and constants/formulas loaded from the assigned candidate. A sandbox loopback PermissionError was environmental; the authorized native probe succeeded without kernel provisioning, installation or configuration repair. That probe was context evidence, not the notebook output writer.

The standard nbformat writer updated source while preserving cell order. Existing `jupyter nbconvert --execute --inplace` executed all eight code cells with the existing project kernel and candidate source path, errors disallowed and private runtime/configuration directories. Execution counts are sequential 1–8 and there are no saved error outputs. Notebook language metadata reports Python 3.14.8.

The first actual execution generated Plotly MIME only; the HTML exporter omitted those plots. A second actual nbconvert execution used the existing `plotly_mimetype+png` renderer and generated both Plotly JSON and PNG representations from the two `fig.show()` calls. No output payload was manually written. Subsequent Markdown-only qualifications preserved every generated output payload exactly; the existing HTML exporter was rerun afterward.

Actual saved outputs inspected in the notebook:

| Quantity | Saved result and interpretation |
|---|---|
| Paris inputs | c_s=4e5 m/s, xi=3.4e-6 m, kappa=7e10 s^-1; D=0.595 |
| Decay criterion | Standard 8 ps: 1.786, false; projected 100 ps: 0.143, false; projected 300 ps: 0.048, true for Gamma_pol/kappa<0.1 |
| Ratio and model temperature | Ratio 0.8146, fractional shift −0.1854, conditional T_eff 69.3 mK, applied once |
| Gain coordinate | omega/kappa_eff=0.05,0.1,0.2,0.3,0.5,1,2 gives 2.7092,1.1436,0.3978,0.1790,0.0452,0.0019,0.0000 at displayed precision, unit greybody |
| Ideal readout | At omega=0.1*kappa_eff, 100 probe photons give SNR 11.4 for one shot and 114.4 for 100 shots; conditional model values |
| Energy illustration | T_mf 0.81 K; standard gradient scale 85.1 mK; energy-scale ratio 9.5, not background-to-signal ratio |
| Hypothetical population | Equilibrium occupation 7.0 at T=4 K and omega=kappa; explicitly not measured |

The lead independently recomputed the ratio 0.8146329434688122 and conditional 69.32230880287678 mK from canonical raw inputs and constants. Saved gain values match the independent Bose-factor calculation within printed precision; SNR values match square-root probe/shot scaling, including the factor 10 for 100 shots. Both saved Plotly data/layout payloads exactly match the current canonical figure JSON. These checks concern model evaluation, not measured gain or detection sensitivity.

## Actual saved figure artifacts and review boundary

The notebook itself stores both PNG images and Plotly JSON. The lead extracted the saved PNG bytes without editing the notebook and inspected their actual pixels:

| Notebook cell | Dimensions | PNG bytes | SHA256 |
|---|---|---:|---|
| 6: stimulated gain | 700×500 | 56710 | `b10d150f227fc12ee1205e388f71e1e159f091563bc3c94bc6a0d05055cf6ac8` |
| 13: regime map | 700×500 | 51171 | `fb7bb5c2528b1393830c9f7382f25c7d7270708ffaec34b15e582e3a2078656a` |

The gain figure labels kappa_eff, unit greybody and conditional ideal SNR/control requirements. The regime figure distinguishes measured/projected points and shows the 0.1 criterion and 143 ps crossing. The lead found the actual saved annotations legible. No canonical figure code or standalone figure assets changed.

The existing HTML exporter includes both saved PNGs but reports two missing-alt-text warnings. This is a QA export, not accessible-publication certification. Browser preview of the local-file URL was blocked by browser security policy. The safer completed review uses full notebook source/text/MIME structure and actual saved PNGs. No browser-rendered whole-HTML layout acceptance is claimed, and no HTTP or alternate-browser workaround was attempted or is proposed.

## Validation, preservation and remaining acceptance

Existing `TestPolaritonPredictions` plus `tests/test_e1_publication_figures.py` report eleven passing focused tests. The original scalar-ratio finding's declared Verify actually failed at the base with AssertionError. The new qualification guard also actually failed at the base; its current equivalent passes in the lead's receipt. Both exact declared report commands passed through the normal parsed-command route in lead and independent review.

Original `2026-08-15-dispersive-coefficient-normalization/infra.md` finding 1.1 owns the ratio-arithmetic defect. The corrected source computes T_H times the returned ratio exactly once; saved cell 10 now displays current D, ratio, fractional shift and conditional model scale. Actual source/output evidence supplements the old negative guard. This report creates no duplicate ratio finding. Supported closure follows the accepted review and separate ledger audit.

Shared formulas, constants, all Lean files, source caches, manifests, metadata/stages and the existing ledger are unchanged by this notebook package. No tests, production checker or new runner were implemented. Broad/seeded tests, Lean builds and canonical extraction were not run here. Existing check coverage is limited: notebook_exec evaluates in memory, and stored_outputs_current excludes this Phase5d notebook; neither certifies these persisted outputs. Actual execution and artifact inspection provide the bounded evidence described above.

Independent whole-notebook scientific/source/output/pixel review is accepted; the separate closure audit accepted preservation of all prior records and the exact two supported additions. Earlier combined-head gates must not be relabeled as evidence for this notebook increment.
