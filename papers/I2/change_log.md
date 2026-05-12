# Bundle I2 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01T16:30Z — Phase 7a sub-wave 7a.3 initial draft

I2 fresh-authored as a synthesis-driven new composition from
Lean-module substrate. Per `docs/PAPER_DRAFT_MAPPING.md`, I2 has
zero per-paper-draft sources (it is sourceless in the per-paper
mapping sense); per `docs/PAPER_STRATEGY.md` §2.4 the content
substrate is Phase 5c VerifiedJackknife + Phase 5o Wave 4
lean-tensor-categories + Phase 5o Wave 5 Mathlib upstream
coordination.

Section structure (9 sections / 820 lines):

- §1 Introduction — split-audience framing (applied physics +
  formal-verification readers); contributions list.
- §2 VerifiedJackknife — 7 definitions (sampleMean, deleteOneSum,
  jackknifeMeanStat, jackknifeVariance, autocovariance,
  intAutocorrTime, effectiveSampleSize) + 4 theorems
  (jackknifeVariance_nonneg, autocovariance_zero_nonneg,
  intAutocorrTime_uncorrelated, intAutocorrTime_ge_half).
  Probability-theory-free framing: estimators are deterministic
  functions on finite samples, not random variables.
- §3 Categorical hierarchy — 4 modules (KLinearCategory,
  FusionCategory, SphericalCategory, RibbonCategory) covering
  Pivotal → Spherical → Balanced → Ribbon → Fusion → Modular.
  First-formalization claim: BalancedCategory + RibbonCategory +
  ModularTensorData are the first formalizations in any proof
  assistant.
- §4 Hopf algebra extensions — 4 modules (QuantumGroupHopf,
  Uqsl2Hopf, Uqsl2AffineHopf, Uqsl3Hopf), 86 declarations.
  First-formalization claim: U_q(sl_2) is the first non-trivial
  Hopf algebra in any proof assistant; U_q(ŝl_2) the first
  affine quantum group; U_q(sl_3) the first rank-2 quantum group.
- §5 Decidable algebraic number fields — 9 modules (QSqrt2,
  QSqrt3, QSqrt5, QCyc3, QCyc5, QCyc5Ext, QCyc15, QCyc15SqrtPhi,
  QCyc16), 162 declarations. First-formalization claim:
  decidable-cyclotomic-plus-quadratic-extension infrastructure
  with composable decidable equality.
- §6 Concrete MTC instances — 11 modules (SU2kFusion, SU2kMTC,
  SU2kSMatrix, SU3kFusion, SU3k2SMatrix, SU3k2FSymbols,
  IsingBraiding, IsingGates, FibonacciBraiding, FibonacciMTC),
  265 declarations. First-formalization claim: SU(2)_k fusion
  (k=1..5) computed *from* a quantum group rather than postulated;
  SU(3)_k=2 first rank-2 level-k formalization; Ising +
  Fibonacci as ModularTensorData instances.
- §7 Mathlib upstream coordination — R1/R2/R3
  relationship-building gate (Zulip introduction +
  AI-tool-assistance disclosure + PR-strategy discussion); 4-PR
  atomic sequence (PR-1 QSqrt2/ComputableAdjoinRoot bridge → PR-2
  PivotalCategory/RibbonCategory → PR-3 QuasitriangularBialgebra/
  RibbonHopfAlgebra → PR-4+ MTC instances). Software-only
  fallback path documented for Mathlib-acceptance delay.
- §8 Reusability — design choices supporting general reuse (zero
  physics-specific imports, Mathlib-pinned-not-HEAD-dependent,
  composable decidable arithmetic). Downstream applications:
  topological-QFT formalization, fault-tolerant QC certification,
  lattice statistics, emergent-MTC BH entropy, anomaly
  classification.
- §9 Discussion — related work (Steinberg pivotal-Coq, Agda cubical
  MTC partial impl, Isabelle/AFP Tensor Networks); limitations
  (no Drinfeld center yet, no RT 3-manifold construction yet, no
  probability-theory layer for VerifiedJackknife yet); future
  extensions (Drinfeld center, SU(2)_k k=6,7,8,
  LinearAlgebra.Eigenvalues.Concrete extension).

Bookkeeping: `bundle_metadata.json` `last_lift` set to
2026-05-01T16:30:00Z; `stage13_redo_required: true`; all stage
statuses pending. `append_log.json` initialized with single
synthesis event referencing 28 Lean modules.

Stage-13 redo required: yes. Reviewer triple (Stage 9/10/13) to be
invoked next; per user directive 2026-05-01 they run as
background processes against the bundle target I2.

## 2026-05-06 — Lift-section from `_phase6n_W1b_lean_only` (§5)

- Source title: SymTFT audit substrate
- Lift action: Lift-section
- Insertion point: §5
- Stage-13 redo required: yes
- Notes: D.2 sidebar: Phase 6n W1b lean-tensor-categories companion (SymTFTAudit substrate is Mathlib-grade in-program build; Phase 5o W5 cross-bridge)

## 2026-05-11 — Stage-13 fix-pass (papers/AutomatedReviews/2026-05-11-1550-bundle-stage13/I2.md)

Closed 17 of 20 findings (8 BLOCKER + 6 REQUIRED + 3 RECOMMENDED) and accepted 3 (7.4 + 1.1 registry-bookkeeping; 5.7 redundant with 5.1-5.3 removal pass). 20 supersession-ledger entries appended to `docs/review_finding_supersessions.json` (entries 633-652).

Substantive fixes:

- **BLOCKER 3.1** Verlinde scope: §6.1 prose corrected from "for the cases up to k=5" to k=1,2 only with explicit theorem enumeration (matches SU2kSMatrix.lean module docstring).
- **BLOCKER 3.2** FibonacciBraiding hexagon: §6.4 rewritten — pentagon reattributed to FibonacciMTC.lean (`fib_pentagon`, line 106, native_decide); hexagon claim retracted, no "in flight" hedge per discipline override.
- **BLOCKER 3.3** RibbonCategory inheritance: §3.1 corrected to match actual class declaration ("extends BalancedCategory (with RigidCategory as typeclass parameter)" rather than fabricated "extends BalancedCategory, PivotalCategory"); future Pivotal-aligned refactor flagged as separate task.
- **REQUIRED 3.4** SU(3)_k=2 hexagon scope: §6.2 softened to "F-matrix on Fibonacci sub-block (F^2 = I involution proven; full F-symbol catalog + hexagon/pentagon deferred)".
- **BLOCKER 5.1/5.2/5.3** First-claim removal (10 instances + cleanup): all 10 enumerated instances + abstract's 5-item packaging + §9.1 "to the best of our knowledge" packaging + §1 "have never been formally verified in any proof assistant" softened to neutral scope description / "as of our 2026 prior-art sweep" framing. Zero "first" priority-claims remain (verified via grep).
- **REQUIRED 5.4** IsolatedHorizonHypotheses paragraph: "Phase 6j Wave 1" wave-history jargon removed; bundle D3 substituted for broken sec:reusability flagship cross-paper ref; public-facing description of gauge assumptions added.
- **REQUIRED 5.5** Fault-tolerant QC certification overclaim: section bullet lead softened from "certification" to "infrastructure"; FibonacciUniversality.lean cited with explicit non-shipped-named-theorem flag.
- **RECOMMENDED 5.6** "in preparation" / "in active development": abstract + §9.3 rephrased to neutral forward-looking.
- **BLOCKER 7.1/7.2/7.3** Count drift: all 9 number-field per-module counts + cumulative 164→207 + Hopf-layer 101→114 + 4 Hopf per-module counts + abstract ~640→~695 refreshed against canonical Lean source (grep-verified).
- **REQUIRED 6.1** intAutocorrTime_uncorrelated window-bound: §2.2 enumerated theorem reads "W with W+1 < n" matching Lean theorem statement at VerifiedJackknife.lean:109-114.
- **REQUIRED 8.1** tau_int illustrative value: §1 tagged "(a worked-example value, not a measured one in this paper)".
- **RECOMMENDED 4.1** turaev2010 bibitem aligned with CITATION_REGISTRY (`V.~G.~Turaev`).
- **RECOMMENDED 7.5** wolff2004 bibitem amended with arXiv:hep-lat/0306017.

Accepted as Stage 14 QI candidates (registry/source-maintenance only, no paper change):

- **RECOMMENDED 7.4**: VerifiedJackknife.lean:138 docstring "1 sorry" is stale (file is sorry-clean); paper does not reproduce this stale string. Stage 14 QI: `lean_docstring_audit.py`.
- **RECOMMENDED 1.1**: wolff2004 + mathlib4 CITATION_REGISTRY entries missing `arxiv_verified=True` / `doi_verified=True` bookkeeping fields; non-paper finding.
- **REQUIRED 5.7**: prior-art ledger absence — resolved by 5.1+5.2+5.3 first-claim removal pass; no first-claims remain.

QI candidates surfaced (Stage 14 candidates):

- `scripts/lean_docstring_audit.py` — flag "FIRST", "first formalization", "N sorry" patterns and cross-check sorry counts against actual file content.
- `scripts/update_counts.py` per-bundle macros — extend to emit `\iiNumberFieldDecls`, `\iiHopfDecls`, `\iiCategoricalDecls`, `\iiInstancesDecls`, etc., for I2-class count-heavy bundles. Closes the count-drift class for good.

LaTeX compile clean (14 pages, 1200339 bytes). validate.py citation_primary_sources_present PASS (no new bibitems added; all references registry-resident). Stage-13 redo: re-runnable; expect GREEN.
