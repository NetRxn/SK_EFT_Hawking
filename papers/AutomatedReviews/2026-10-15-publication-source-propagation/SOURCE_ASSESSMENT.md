# Source standing and bounded validation

Author evidence record, based on the lead's acquisition/validation receipt and direct primary-body assessments. Final independent review of the acquired artifacts, final E2 trim, hygiene change and complete claim set is recorded in `SCOPED_REVIEW.md`. This document neither closes a finding nor certifies publication readiness.

## Actual acquired artifacts

The lead used the existing exact-bibkey acquisition writer, retaining truthful author-preprint provenance. The following are the actual saved artifacts recorded in the acquisition receipt, not a claim that a metadata cache became full text by editing its status.

| Bibkey | Held workspace-relative artifact | Bytes / pages | SHA256 |
|---|---|---|---|
| Coutant2014 | `Lit-Search/Phase-1-and-Background/primary-sources/Coutant2014.pdf` | 640599 / 6 | `96299d47d06bff45b3754ed5f74ae81077ac75d38b4558e0fe93301fcda236d2` |
| CoutantWeinfurtner2018KdV | `Lit-Search/Phase-1-and-Background/primary-sources/CoutantWeinfurtner2018KdV.pdf` | 1349807 / 23 | `7119b9564fa4fa9dda866f9843148c4be7d2e2643673080d423f8ae722664abb` |

- **Coutant2014:** [arXiv v2 PDF](https://arxiv.org/pdf/1402.2514v2), header dated 15 November 2014; [primary record](https://arxiv.org/abs/1402.2514) links PRD 90, 121501 (2014), DOI 10.1103/PhysRevD.90.121501. The dynamic TeX date June 2021 is not the version date. The lead inspected the saved pp.2–3: finite locally linear region; momentum-space WKB neglecting left-mover coupling; small kappa/Lambda and omega/Lambda. Eq.(10) supplies thermal mixing within that approximation; Eq.(11) limits its spatial interpretation. It does not establish a globally exact all-orders temperature or derive the adopted quadratic law. The final journal body was not read.
- **CoutantWeinfurtner2018KdV:** [arXiv v2 PDF](https://arxiv.org/pdf/1707.09651v2), header dated 12 January 2018; [publisher record](https://doi.org/10.1103/PhysRevD.97.025005) identifies *Low-frequency analogue Hawking radiation: The Korteweg–de Vries model*, PRD 97, 025005 (2018). The dynamic TeX date October 2021 is not its version date; 2017 is submission year. Saved p.13 Eqs.(39–40), reread by the lead, give a profile-specific low-frequency temperature ratio tanh(pi*q_r) and exponentially small smooth-limit departure; p.18 discusses the distinction from polynomial behavior. Co-propagating coupling is neglected in the weak-dispersive KdV treatment. This is not evidence for a nonzero leading local-D-squared temperature term. A loose quadratic upper bound would not supply that leading term. The final journal body was not read.

The full quadratic ansatz and coefficient are now identified as adopted in E1/E2/D1 and shared documentation. Algebraic factorization and positivity of the defined expression remain valid; they do not derive a device-specific response. Old `2026-08-15-dispersive-coefficient-normalization/infra.md` finding 2.2 owns the two-source acquisition/assessment obligation. Its original OR-cache Verify is insufficient by itself; both identities, actual artifacts and substantive assessment must be accepted. No duplicate acquisition finding is created here.

## Reservoir and earlier-horizon attribution

The retained Falque author preprint, arXiv:2311.01392v2 (July 2024), p.4 §III, adopts beta = 1.84 in the Eq.(7) spectral fit; p.5 §IV.A reports about 0.40 micrometre/ps. This supports reservoir inclusion in its reconstruction, not a matched reservoir-free 1.0 micrometre/ps comparison. It is preprint-body evidence, not verification of the final 2025 body.

[Claude2023 author preprint](https://arxiv.org/pdf/2211.12373v1), p.4 Eqs.(9–12), pp.7–8/Fig.5, separates condensate interactions from reservoir blueshift and reports alpha ≈ 0.59. The fixed-total-detuning inverse speed factor is approximately 1.69, not 2.5. [Stepanov2019 published body](https://www.nature.com/articles/s41467-019-11886-3.pdf), pp.5–6 Eqs.(3–4), distinguishes static and finite-frequency responses; its two working-point ratios do not establish Falque's calibration. [Estrecho2021 preprint](https://arxiv.org/pdf/2004.12339v2), pp.1,4 and supplement pp.6–7, studies an off-resonantly pulsed box-trapped condensate with time-dependent reservoir fractions. These sources support device-dependent reservoir effects. Reading them online did not upgrade their local caches.

[Nguyen2015 preprint](https://arxiv.org/pdf/1410.0238), supplement p.3 §V Eqs.(S5–S6), estimates about 3 K hydrodynamically for its measured 100 mW parameters; it does not establish E1's old 0.1–1 K range or an observed Hawking temperature. [Gerace2012 preprint](https://arxiv.org/pdf/1206.4276), p.6 Eq.(18) and discussion, treats configurations with different gradient energies and a convention requiring reconciliation before comparison. E1 removes the combined range and requests the profile/convention explicitly; it does not replace it with an unqualified 3 K number.

## Measured scope and preservation

The lead's receipt records executable `formulas.py` AST unchanged from 953dbfc7 after docstring removal, and the entire Lean noncomment byte stream unchanged. Only three prose fields in EFT.DISPERSIVE_C1 changed. Registry and acquisition sidecar changes are confined to the two keys above, preserving other entries. Sixteen existing KappaScaling tests passed.

Actual isolated compilation and existing length measurements:

| Bundle | Pages | TeX errors / unresolved | Overfull boxes | Existing length / abstract proxy |
|---|---:|---|---:|---|
| E1 | 4 | 0 / 0 | 0 | 3408/3750 word equivalents; 581/600 characters |
| E2 | 4 | 0 / 0 | 1 | 3747/3750 word equivalents; 550/600 characters |
| D1 | 20 | 0 / 0 | 15 | Below advisory 24-page floor |

E2/D1 exact `953dbfc7` input baselines compiled with the same page/overfull counts as the final versions. Their existing overfull defects remain unwaived. E2's initial correction exceeded its limits before a bounded prose trim; independent review accepted that final trim. These are repository measurements, not publisher-side certification. E2 ceiling provenance remains unverified.

Only measured metadata change is D1 compiled_pages 11→20 through the compile writer. Last-lift and stale/pending review fields are preserved. Corpus citation, abstract and prose failures remain; no full-green result, Lean build, canonical extraction, external submission or merge readiness is claimed.

The slow extractor test still fails on 10 stubs and reports 3 orphans. Its report now uses pytest temporary storage; all three original assertion ASTs are preserved. Output isolation fixes repository pollution while retaining the actual citation failure. The new reports' Verifies are regression floors that must be executed before closure, alongside independent review of the stronger source/artifact evidence.
