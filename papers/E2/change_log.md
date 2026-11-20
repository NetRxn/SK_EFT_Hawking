# Bundle E2 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-companion from `paper16_graphene_sk_eft` (§1)

- Source title: Graphene Dirac-fluid SK-EFT
- Lift action: Lift-companion
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: E2 PRL/PRR experimental letter: Dean-Kim-Lucas bilayer-graphene Dirac-fluid analog Hawking + Wiedemann-Franz violation + closed-form noise spectrum from Keldysh FDT + Landauer-Buttiker

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper16_graphene_sk_eft experimental physics first-claims softened ('first measurement of analog Hawking radiation in an electronic system' -> 'a measurement ...'; 'first observation ...' -> 'an observation ...'). No physics claims changed; only the primacy framing dropped.

## 2026-10-15 — Propagation of the adopted dispersive law

- Scoped the quadratic law and its benchmark shifts as phenomenological choices; retained the exact positivity statement as arithmetic about the definition. Removed Finazzi2012 as a derivation of this law and its now-unused bibliography entry.
- Qualified abstract, comparison and conclusion consistently. Coefficient changes can move the crossover; the fourteen-percent polariton comparison now identifies the projected 100 ps cavity at Falque's smooth-horizon parameters.
- Trimmed the corrected passages without removing these qualifications: four-page compile, 3747/3750 word-equivalents and abstract 550/600 characters. The existing abstract-ceiling provenance remains unverified. The one overfull box also occurs in the exact 953dbfc7 baseline. No formula, numerical benchmark, stage/freshness field or last_lift was changed.
- This is propagation of the E1 source correction, not a new paper review or submission acceptance. Focused evidence is in `papers/AutomatedReviews/2026-10-15-publication-source-propagation/`; independent final review and merge gates remain separate.


## 2026-10-15 — Infrared source and conditional electrical-readout model

- Replaced the E2 greybody attribution with the distinct Anderson et al. PRD 90, 104044 (2014), held arXiv:1404.3224v3, Eq. (36). Stated its infrared, constant-flow/density hydrodynamic BEC scope and asymptotic sound speed; graphene matching and finite-frequency roll-off remain adopted.
- Corrected Gamma0 rounding to 0.99994 and the adopted roll-off suppression at four Hawking frequencies to 26.3 percent. Distinguished the leading Planck plateau (approximately 1.0e-26 A2/Hz) from the corrected numerical illustration (approximately 1.2e-26 A2/Hz); the 1.6-frequency half-height applies only to the leading constant-transmission model.
- Regenerated the stale local noise figure through the existing canonical function. Its numerical traces are unchanged from the canonical producer; only crowded minor y-axis labels are hidden for export. The caption identifies its corrected occupation and heuristic shaded SNR band. Shared executable modules and other figures are unchanged.
- Qualified related abstract, geometric-transfer inference, detection/extraction discussion and conclusion: electrical response is adopted, and inference requires transmission, detector-transfer, operating conductivity and background calibration. Ideal timing numbers establish no achieved sensitivity. Removed unsupported priority and universal amplifier assertions.
- Actual isolated compile: four pages, zero TeX errors/unresolved references/dropped options, one existing overfull box unwaived. Measured 3629/3750 word-equivalents and 482/600 abstract characters; abstract-ceiling provenance remains unverified. No stage, stale, last_lift or manifest field changed. Focused source/model/pixel review and supported closure are recorded separately in `papers/AutomatedReviews/2026-10-15-e2-greybody-readout/`; this is not publication or submission acceptance.
