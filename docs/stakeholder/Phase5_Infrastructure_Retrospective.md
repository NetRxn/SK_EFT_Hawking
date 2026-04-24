# Phase 5 Infrastructure Retrospective: Enabling Machinery for the Research Chains

**Purpose:** Consolidated retrospective for four Phase 5 infrastructure / process sub-phases (5g, 5o, 5u, 5v). These phases did not produce new physics chains or new papers — they shipped the machinery that the research phases (5a–5e, 5f–5j, 5k–5p, 5q–5s, 5t–5y) depend on. Written as a single memo rather than Implications / Strategic-Positioning pairs because the standard template doesn't fit infrastructure work cleanly.

---

## Why infrastructure phases matter

The research phases are highly visible: new physics chains, new formal modules, new papers. Infrastructure is load-bearing but invisible. When a Monte Carlo run finally fits on workstation hardware at L=12, when a Mathlib-ready library lifts categorical theorems out of this project and into a community codebase, when a paper's dimensional bug is caught before submission, when a knowledge graph exposes every drifted count and every orphan citation — all of that is infrastructure work. This memo exists so the stakeholder reader can see what enables the verified chains.

---

## Phase 5g — Matrix-free Monte Carlo + Mathlib PR + Submission

Phase 5g opened three tracks that each address a different program-level bottleneck: computation, community credibility, and publication.

**Track A — matrix-free staggered Dirac operator.** The vestigial Monte Carlo work (Chain 6) relies on solving linear systems against a staggered fermion matrix. The dense form is prohibitive at realistic lattice sizes: ~220 GB at L=12. Phase 5g Waves 1–2 replaced the dense path with a matrix-free stencil in `src/vestigial/stencil_dirac.py`, built around `torch.roll()` and precomputed 8×8 hopping blocks. The stencil operator agrees with the dense reference to <1e-13 at L=2 and L=4; memory drops to ~42 MB at L=12 — a savings of over 4000× that unlocks L=12 production on workstation hardware without specialised infrastructure. The CG solver, multi-shift solver, and force computation all accept the matrix-free callable while remaining backward-compatible with the dense path. 19 tests cover correctness, antisymmetry, PSD, CG convergence, and multi-shift integration.

**Track A — L=12 production status.** Wave 3 (the actual L=12 RHMC production run) is blocked: the worker pool is currently occupied by the L=8 scan, and L=12 should wait until those workers free up. The capability is in place; the schedule is the constraint.

**Track B — Mathlib PR pipeline.** The categorical infrastructure built for quantum groups and modular tensor categories (PivotalCategory, SphericalCategory, RibbonCategory, FusionCategory, and related typeclasses) is of interest well beyond this project. Phase 5g scoped the contribution pathway: Mathlib style adaptation (100-char lines, trailing-prime naming, aesop_cat auto-params, module docstrings), the Zulip-first social protocol, and the PR sequencing plan (PivotalCategory first, because Mathlib's `Rigid.Basic` explicitly marks it as future work; then Spherical, CategoricalTrace, Ribbon in dependency order). The VecGMonoidal heartbeat overhead that would have blocked a first PR was eliminated via `@[local instance]` caching. Zulip engagement itself has not yet begun.

**Track C — paper submission.** Phase 5g documents the arXiv voucher requirement (first submission from a new author needs endorsement) and the formatting work for the first papers in the submission queue (Paper 12 polariton and Paper 11 quantum group). No papers have been submitted yet; this track is deliberately paced against the chain-stabilization strategy rather than rushing a premature first submission.

---

## Phase 5o — Community-value extraction

Phase 5o asked a deliberate question: we've built a verified pipeline from quantum groups to topological quantum computation; how do we maximise its value for others?

**Wave 4 — `lean-tensor-categories` library.** The single largest community artifact. Extracted to `/OpenSourceContrib/MathLib/lean-tensor-categories/`: 20 files, 2026 lines, 114 theorems, 78 definitions and classes, zero sorry, zero warnings. The library covers the full categorical hierarchy (Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular), the Hopf-algebra layer (QuasitriangularBialgebra, RibbonHopfAlgebra, DiagonalAction), decidable number-field arithmetic (QSqrt2, QSqrt5, QCyc5, QCyc16, QCyc5Ext, and a ComputableAdjoinRoot bridge), and concrete instances (SU(2)_k for k=1–4, Ising MTC, Fibonacci MTC, Verlinde formula verification for k=1,2). This is an upstreamable Lean library, not a research prototype — it depends on Phase 5g Track B for the social side of the contribution.

**Wave 3 — experimental-prediction bridging.** Ten prediction functions in `formulas.py` — interferometric visibility, thermal Hall conductance, topological entanglement entropy, quasiparticle charge, ground-state degeneracy, and associated distinguishing-observables tables — connect the verified braiding data (Ising R-matrices, Fibonacci R-matrices, Gauss sums, total quantum dimensions) to laboratory observables. Banerjee 2018's κ_xy/T = 2.5κ₀ at ν=5/2 is the confirmed anchor; Fibonacci predictions at ν=12/5 await experiment. Three figures (`fig_ising_braiding_data`, `fig_fibonacci_braiding_data`, `fig_experimental_predictions`) render the predictions alongside 24 tests.

**Wave 2 — literature error audit.** A systematic sweep of 13 major braiding papers against the project's own native_decide infrastructure found **zero genuine errors**. Every apparent disagreement reduced to either chirality convention (Fibonacci R-matrix sign, e^{±4πi/5}), gauge freedom (R^{σψ}_σ = ±i is a Z₂ vertex gauge), or the number-field obstruction (√φ ∉ Q(ζ₅), only addressed explicitly by Rowell-Stong-Wang 2009; this project's QCyc5Ext is the first formalisation). The honest finding is that the Ising/Fibonacci MTC literature is self-consistent as stated — the task was to check, not to produce errors.

**Wave 1 — Kazhdan-Lusztig bridge.** Verlinde formula verified at the data level for k=1 and k=2 inside the extracted library. The full categorical KL equivalence is a ~200-page analytic proof and remains out of scope; the data-level verification (k=3 exhaustive check next) is the tractable deliverable.

---

## Phase 5u — Paper revision cycle (April 2026)

Phase 5u responded to the April 2026 Perplexity review round. Seven automated review documents (10 April citation/comprehensive/LKB-Paris/IndependentVerification; 12 April deep review of Paper 10 plus master systematic checklist) surfaced substantive issues across four tracks. The substantive track closed 2026-04-15.

**Track A — Paper 1 dimensional bug.** The most serious finding. `compute_dissipative_correction` in `src/core/transonic_background.py` had been treating Beliaev transport coefficients γ₁, γ₂ (units [m²/s]) as if they were damping rates (units [s⁻¹]) since its first commit (`d72f197`). The missing factor is k_H² = (κ/c_s)² — roughly ~10⁷ in magnitude for physical parameters. The fix introduced new Lean theorems (`GammaH`, `gammaH_def`, `gammaH_via_kH`, `gammaH_nonneg`, `deltaDissFromTransport`, `deltaDissFromTransport_eq`, `deltaDissFromTransport_zero_iff`) in `SecondOrderSK.lean` to anchor the identification Γ_H = (γ₁+γ₂)(κ/c_s)² formally — the root cause of the bug's longevity was the absence of a Lean theorem pinning this identity. Eight new tests in `TestBeliaevChainConsistency` catch the exact dimensional shape. Paper 1 Table 1, main-text equations, the damping-regime paragraph, and three figures were all regenerated; the claims-reviewer passes numerically within 1%. A secondary discovery: at Heidelberg parameters, post-fix δ_diss exceeds δ_disp by ~20×, inverting the universal "dispersive dominates" narrative for one platform. The paper's framing was updated honestly — Heidelberg is now identified as the strongest detection target, which strengthens rather than weakens the thesis.

**Track B — Paper 12 Falque reconciliation.** An LLM-driven provenance reread of Falque PRL 135, 023401 (2025) resolved a three-day-old inconsistency: the 2026-03-31 provenance entry claimed Falque did not report surface gravity κ, while a 2026-04-10 LKB audit reported three measured values (0.07, 0.08, 0.11 ps⁻¹). Third-LLM reread against the full text (arXiv:2311.01392v2) confirmed Falque does report κ. The smooth-horizon red trace value κ = 7×10¹⁰ s⁻¹ was adopted as the `Paris_long` default; the steep-horizon κ = 1.1×10¹¹ s⁻¹ is quoted as the platform's upper bound. Paper 12's "programmable simulators" framing was re-attributed (from Falque to Giacobino 2025 lecture notes where the phrase actually originates) and the "inside horizon" phrasing was tightened to "supersonic region" to match Falque's own language.

**Track C — textbook-fact errors.** Three corrections in prose. Paper 3's "Z₂ × Z₂ for SO(4k)" was wrong — Z₂ × Z₂ is the centre of Spin(4k), not SO(4k); the line was rewritten to separate SO-group centres from Spin-group centres. Paper 10 attributed the ℤ₁₆ classification to "time-reversal symmetric topological superconductors", but class D has particle-hole symmetry only and no time reversal; Kitaev's 16-fold way is specifically the free-fermion ℤ reducing to interacting ℤ₁₆ in class D, with the Fidkowski-Kitaev 2010 reference added. The "16 = 8 × 2 (Bott period × Pfaffian factor)" numerology in Paper 10 was removed and reframed via the Wang 2024 Smith homomorphism, which is the actual mechanism connecting the four appearances of 16 in the ℤ₁₆ story.

**Track D — bibliography corrections.** ABP1967 page 256 → 271 (plus title added); Kitaev2009 end page added; BeaudryCampbell page 1 → 89 (plus end page); Adler 2024 page 87 → 80; diFrancesco CFT added for the Casimir / framing-anomaly interpretation. Stolz 1993 was removed after the cited coordinates could not be verified. Three additional Lean docstring updates (for `sixteen_convergence_full`, which enumerates four 16s but does not unify them; and `dai_freed_spin_z4`, which is an `Equiv.refl` placeholder for the ℤ₁₆ cobordism identification) explicitly label those theorems' status so papers can cite them accurately as "formally recorded" rather than "formally verified".

The honest framing: the dimensional bug was a real physics-correctness error that slipped through the 12-stage pipeline for the project's entire history. Tests passed because they asserted only `|δ_diss| < 0.1`, which any formula satisfies for small inputs. Phase 5u fixed the specific papers; Phase 5v was chartered to harden the pipeline against the same class of failure. The Phase 5u process track (Waves 14–22 — claims-reviewer extensions, Invariants 11 and 12, citation registry reconciliation, constants audit) was deferred into Phase 5v where it fits more naturally.

---

## Phase 5v — Knowledge-graph foundation + readiness state machine

Phase 5v was chartered by the same review round that triggered Phase 5u: the April findings exposed thirteen distinct failure modes the existing pipeline could not catch, and a silent undercount of Lean declarations was discovered in the knowledge graph.

**Wave 0 — short-name collision fix.** `build_graph.extract_lean_declaration_nodes` keyed Lean-node IDs on the last namespace component, so ~42% of Lean declarations were being silently dropped whenever two declarations shared a short name in different namespaces. The fix reshaped node IDs to full names, added autogen-helper filtering (noConfusion, casesOn, recOn — ~2,145 noise declarations), and restored the short-name → full-name index for edge extraction. Declaration-node count went from 3,317 to 3,619 — **+302 substantive declarations silently recovered**, plus one real collision (`tpf_evasion_margin`) surfaced, logged, and renamed.

**Wave 1 — foundation fixes.** The recovered `tpf_evasion_margin` collision was renamed into two distinct theorems (`tpf_evades_at_least_two` and `tpf_violation_surplus`), each matching its own statement. `update_counts.py` was wired into `validate.py` as CHECK 15b; a new CHECK 17 `count_literals` warns on raw count strings in papers that don't `\input{counts.tex}`; Paper 15 was retrofitted as the reference implementation. Auto-discovery extractors replaced hand-maintained dicts for papers, figures, and `\includegraphics` resolution; paper-node coverage went 9/15 → 15/15, figure-node coverage 76 → 104.

**Wave 2 — schema extension.** Eight new node types (ProseClaim, PythonTest, ReviewFinding, ProductionRun, PlaceholderMarker, Contradiction, CountMetric, ReadinessGate) plus eight new edge types (VERIFIES, FLAGS, SUPERSEDES, PRODUCES, REPORTS, SUPPORTS, CONTRADICTS, IMPACTED_BY) were registered in the graph schema and wired through extractors. PythonTest extraction alone classified 1,831 tests by shape (515 bounds-only / 772 identity / 177 golden / 6 roundtrip / 361 unknown) — revealing that 23 formulas are covered only by bounds-only tests, the exact test-shape that let the dimensional bug through.

**Readiness-gate taxonomy.** The eleven gates are the core deliverable. Eight correctness gates: **CitationIntegrity** (every `\bibitem` and author-name string resolves), **CrossPaperConsistency** (same construct described consistently across companion papers), **ParameterProvenance** (every parameter traceable to a primary source with human-verified date), **ComputationCorrectness** (every formula has at least one test beyond bounds-only), **LeanProofSubstance** (no trivial-body Lean theorem cited as "verified"), **AssumptionDisclosure** (every hypothesis a cited theorem depends on named explicitly in the paper), **NarrativeGrounding** (every prose claim has a formal support edge or an explicit interpretive tag), **ProductionRunHealth** (every run-dependent paper claim links to a successful run). Three UX gates: **CountFreshness** (count literals resolve through macros to current `counts.json`), **FirstClaimVerification** (every "first in any proof assistant" claim has a ledger entry), **FixPropagation** (every resolved ReviewFinding has a SUPERSEDES chain and landed in every impacted paper). 15 papers × 11 gates = 165 gate instances. The first live evaluation marks all 15 papers red — expected, because the April findings are encoded as open blockers; the gate colours will move green as remediation lands.

**Waves 6 and 7 — Stage 13 adversarial reviewer, Stage 14 QI register.** Stage 13 adds an internal adversarial-reviewer agent (fresh-context Opus, red, with DOI and arXiv lookup tools) to the pipeline. Its output flows through `extract_review_finding_nodes` into the graph automatically; citation findings are BLOCKER severity at submission time. Stage 14 is the meta-process layer: `scripts/qi_register.py` auto-generates `docs/QI_REGISTER.md` by clustering ReviewFindings across gates and papers. The April round seeded 56 findings → 7 quality-improvement patterns; the biggest cluster is CitationIntegrity with 20 findings across 7 papers.

**What's deferred.** Phase 2 of the original knowledge-graph spec — PG+AGE as source of truth, Cypher-queried dashboard endpoints, write-back for human gate reviews (Wave 3 here) — is scoped but not started. JSON-LD / W3C PROV export and the notebook `trace_claim` helper (Wave 8) are scoped. The readiness dashboard (Wave 5) is partially done: the heatmap and per-paper focus sidebar are live at `localhost:8050/?tab=readiness`, but the trend chart and action buttons depend on the PG migration.

---

## How these phases enable the research chains

Phase 5g's matrix-free Dirac operator is the precondition for Chain 6 (vestigial MC) reaching L=12 without institutional computing. Phase 5o's `lean-tensor-categories` library is the upstreaming path for Chain 3's (quantum-group) categorical infrastructure — once the Mathlib PR lands, every downstream formalisation in Lean inherits it. Phase 5u keeps Paper 1's analog-Hawking numerics honest (Chain 1: SK-EFT Hawking) and Paper 12's polariton parameters anchored to Falque's primary source (Chain 7: polariton platform). Phase 5v backstops every chain: the eleven readiness gates are the pre-submission checklist that determines whether a paper's claims actually match what the code, the Lean proofs, the parameters, and the cited literature say.

---

## What's deferred to Phase 6

- Phase 5g Wave 3 (L=12 RHMC production) — gated on L=8 worker availability.
- Phase 5g Waves 4–10 (Mathlib PR + paper submissions) — pending Zulip engagement and arXiv voucher.
- Phase 5o Wave 1 (Kazhdan-Lusztig data-level at k=3) — tractable, not yet executed.
- Phase 5u Waves 14–22 (claims-reviewer extensions, citation registry sweep) — absorbed into Phase 5v's Stage 13 + QI register pattern; surface-level items remain.
- Phase 5v Waves 3, 5b, 5c, 8 (PG+AGE migration, dashboard write-back, graph-tab readiness integration, JSON-LD export, notebook helper).

---

*Last updated: 2026-04-24-1510.*
