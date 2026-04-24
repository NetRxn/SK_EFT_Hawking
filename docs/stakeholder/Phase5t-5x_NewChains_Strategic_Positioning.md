# Phase 5t/5w/5x: Three New Proof Chains — Strategic Positioning

*Last updated: 2026-04-24-1515.*

## Competitive Landscape

**Quantum information (Chain 7 / Paper 18).** Berry-phase and symmetry-protected two-qubit gates are an active experimental frontier in neutral-atom and Fermi-Hubbard hardware — Kiefer *et al.* (arXiv:2507.22112, Nature 2026) is the target we formalize — but no formally verified version of any geometric quantum gate exists elsewhere, as best we can determine. Paper 18's abstract explicitly invites correction if prior work exists in Isabelle/HOL (AFP), Coq (QuantumLib / QWIRE), or Agda quantum libraries; none has been located. The nearest comparable formal work in Lean is the project's own Fibonacci-braiding universality proof (Chain 3), which protects gates via topological order rather than chiral symmetry. The two are **complementary, not competing**: Paper 18 documents symmetry-protected protection at the algebraic-core level; Chain 3 documents topological protection at the full MTC level. Together they give the project two distinct machine-checked protected-gate mechanisms, covering both branches of the current industry landscape (anyon-based at Microsoft; transmon/Fermi-Hubbard/neutral-atom at Google, IBM, ETH).

**Experimental platforms (Chain 8 / Paper 16a).** The Dean group at Columbia (Geurs *et al.* 2509.16321, Sept 2025) realized the first electronic sonic horizon in bilayer graphene. That is the single most actionable new analog-gravity experimental fact since Steinhauer's BEC horizon. Andrew Lucas (CU Boulder, co-author) has deep SK-EFT engagement — he co-authored the original Crossley–Glorioso–Liu papers this project's EFT framework is built on. Nobody else is combining **SK-EFT + graphene analog gravity + formal verification**. Carusotto (Trento), Snoke (Pittsburgh), and the LKB Paris group are active on the polariton side; none of them has a graphene extension. Paper 16a claims the **first graphene-Dirac-fluid analog-Hawking formalization with a Keldysh + Landauer–Büttiker noise formula** (per the README "Representative formal-verification firsts" list). The 92% theorem-reuse from the 1+1D WKB machinery means this lead is defensible: anyone replicating the result has to redo the entire `WKBConnection.lean` / `HawkingUniversality.lean` pipeline first.

**Dark sector (Chain 9 / Paper 17).** Machine-checked Gibbs–Duhem-type structural obstructions on emergent-vacuum dark-energy frameworks are new (the Phase 5y closure, cross-referenced by Chain 9). The SFDM cluster-merger forecast fills a confirmed literature gap: Berezhiani–Khoury's 2025 Physics Reports review (arXiv:2505.23900, 118 pages) has no quantitative merger forecast — Paper 17 supplies one.

---

## Publication Targets

| Work | Venue | Timeline | Status |
|------|-------|----------|--------|
| Paper 18 — Fermi-Hubbard geometric quantum gate (Phase 5t) | TBD | TBD | Draft complete; all P1 claims-reviewer + figure-reviewer + adversarial-reviewer findings cleared (session-9 FINAL+++) |
| Paper 16a — Graphene Dirac fluid SK-EFT + analog Hawking (Phase 5w) | TBD | TBD | Draft complete; reviewed by 3 independent Opus agents (claims + figures + adversarial) |
| Paper 17 — Dark-sector connections (Phase 5x/5y integrated) | TBD | TBD | Draft complete |

Venues and submission dates are not yet locked down in any roadmap source consulted; all three are marked TBD pending the arXiv-voucher prerequisite and the Phase 5v readiness-gate process. What *is* settled: none of the three requires further Lean work to reach submission-readiness — the bottleneck is the submission pipeline itself, not the underlying verification.

---

## IP and Priority

**Paper 16a** has a specific priority window: the Dean-group sonic-horizon realization was September 2025, and the window before the natural follow-up groups (Lucas, Kim, Carusotto collaborators) write their own Hawking-radiation proposals is narrow. Submitting before the Dean group publishes a Hawking-detection attempt — or before a competing theory group frames the noise spectrum — is the priority-asserting move.

**Paper 18** is timely given 2025–2026 quantum-computing hardware activity around symmetry-protected gates; Kiefer *et al.*'s Nature 2026 experimental paper is the reference benchmark, and the formal-verification companion is a natural co-citation. No competing formalization exists in any proof assistant (as best determined).

**Paper 17** priority is more externally gated. The SFDM merger forecast is time-decoupled from submission timing — the predictions land against Euclid × Roman data that accumulates over years. The **DESI DR3 release (2026–2027)** is the decisive external milestone for the DE obstruction side: the paper is structured to accommodate either DR3 outcome (strengthening-away-from or retreat-toward `(w₀, wₐ) = (−1, 0)`), so submission timing is flexible.

---

## Experimental Collaboration Targets

- **Dean group (Columbia, bilayer graphene sonic horizon)** — primary target for Paper 16a; has the realized sonic-horizon device
- **Lucas group (CU Boulder, transport theory)** — co-author on Dean paper, deep SK-EFT engagement; natural theory-side collaborator
- **Kim group (Harvard, noise thermometry)** — has the current-noise instrument required to read `ΔS_I(ω)` predicted by `GrapheneNoiseFormula.lean`
- **Falque / LKB Paris (polariton programmable horizons)** — Chain 1 polariton track, reservoir-corrected predictions from Paper 12 remain actionable; referenced here for cross-platform context
- **Kiefer group (ETH, Fermi-Hubbard dimer)** — experimental referent for Paper 18 (arXiv:2507.22112); collaboration motivation is methodological (their experiment, our formal verification) rather than joint-experiment
- **Euclid + Roman weak-lensing consortia (SFDM cluster-merger stacking)** — observational partner for the Paper 17 money plot; stacking ≥ 30 canonical radio-relic mergers is the stated 3.5–5.7σ target
- **DESI DR3 analysis team** — relevant for the dark-energy obstruction sub-chain cross-referenced from Phase 5y

---

## Risks and Gaps

**Paper 16a** detection depends on the device-specific greybody factor `Γ(ω)` — the framework derivation is complete, but the transverse transmission coefficient is sample-geometry-specific and sets the final detection bandwidth. Without an experimentalist collaborator, the predicted noise excess (`ΔS_I ≈ 10⁻²⁶ A²/Hz` across 0.5–85 GHz, ~1% of thermal Johnson–Nyquist background) cannot be narrowed into a specific device-specific SNR. A secondary gap: the Paper 16a figure-set had a pre-existing `validate.py` advisory for paper16 figures unresolved as of the Phase 5x Wave 8 closure. **Paper 17**'s SFDM money plot is explicitly forecast-level — the 3.5–5.7σ stacked prediction is gated on Euclid × Roman actually collecting ≥ 30 canonical radio-relic mergers, and the condensate-fraction complication (10¹⁵ M☉ clusters 0% superfluid vs 10¹³ M☉ groups ~96%) means group–cluster mergers may be better targets than the five canonical fiducial cases. DESI DR3 is the decisive milestone for the paired DE obstruction. **Paper 18**'s W8 Target B (full Aharonov–Anandan / Berry-connection formalism over a parameterized eigenbundle, adiabatic following, gauge-fixed phase computation over the loop) remains explicitly deferred to Phase 6; the current formalization delivers the minimal geometric content (sign flip + vanishing dynamical phase) without parallel transport on an eigenbundle. None of these three risks is a correctness risk for the machine-checked content — each is a scope or timing risk on the downstream experimental or observational consequence.
