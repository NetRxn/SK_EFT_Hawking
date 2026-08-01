# Bundle D12 — Change Log

_Initial bookkeeping created 2026-07-30T21:42:57Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-07-30 — Lift-section from `D12_initial_draft` (§1)

- Source title: Kernel-Verified Detector & Readout Metrology
- Lift action: Lift-section
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Sourceless synthesis: substrate is 13 Lean modules across Phases 6EA (Poisson/Gaussian discrimination floors, shot noise), 6EB (ENBW/NEP/matched-filter floors), 6EC (electrothermal detector physics), 6EE (two-level control + composite readout ceilings); no per-paper-draft sources. First content-lift of the 2026-07-27-authorized D12 bundle.

- 2026-08-01 — **REVISION** required by completion of Phases 6EA–6EE (all closed 2026-08-01).
  D.3 branch per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`. The bundle was drafted 2026-07-30 while
  its source phases were still in flight, so each subsequent wave arrived as a late absorption
  and triggered a mandatory Stage-F re-review. With Stage A now satisfiable for every source,
  the bundle is re-lifted once from complete sources.
  Structural: two-layer posture + rational-enclosure technique promoted from an intro paragraph
  to §2; refutations returned to §3/§4/§5 rather than headlining the paper; §1 gains the
  stack-position and roadmap; composite ceilings consolidated into a new §7 from subsections
  previously split across §5 and §6. Scope: the Poisson floor is recorded as the classical
  Le Cam two-point bound at Poisson (Fuchs–van de Graaf 1999); novelty scoped to the
  kernel-verified statement and framing. Stage-F re-review required.
