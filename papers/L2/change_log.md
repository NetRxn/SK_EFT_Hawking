# Bundle L2 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-letter from `paper10_modular_generation` (§1)

- Source title: Modular generation constraint
- Lift action: Lift-letter
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: L2 PRL splash initial lift: three generations from modular invariance (paper10 source); 24|c₋ chain + Ext over A(1) computation + N_f≡0 mod 3 derivation

## 2026-05-01T22:10Z — First-pass content draft authored

3-page PRL twocolumn paper (`revtex4-2 prl twocolumn`) fresh-authored as a synthesis-driven new composition; not a copy from paper10. Six sections: Introduction; Chiral central charge from SM fermion content (Weyl table + with/without ν_R); Framing anomaly from Dedekind eta function (η T-transformation + 24|c_- + figure cube-roots-of-unity); Machine-checked Ext computation over A(1) (1,2,2,2,3,4 dimensions through deg 5 + change-of-rings); 16-convergence and the role of ν_R (with/without ν_R combined-constraint table); Conclusion. 12 bibitems matching paper10 source. 2 figures lifted from paper10 (fig75 modular invariance phase, fig73 SM generation constraint). LaTeX compile clean (`pdflatex` 2 passes, no errors, 3 pages, 393 KB).

## 2026-05-01T22:30Z — Stage 9 round 1: 0 FAIL / 2 MINOR

YELLOW. fig75 caption-range mismatch (caption said N_f=1..9; figure annotates groups N_f=1..12). fig73 right-margin dashed-line labels clipped against N_f=9 bar top.

## 2026-05-01T22:40Z — Round 1 fixes

(1) fig75 caption rewritten to N_f=1..12 with explicit modular-invariant set {3,6,9,12} and excluded set {1,2,4,5,7,8,10,11}. (2) `src/core/visualizations.py:fig_sm_generation_constraint`: dropped `annotation=` kwarg from the three `add_hline(y=24/48/72)` calls; added explicit `tickvals=[0,8,16,24,32,40,48,56,64,72]` so y-axis ticks convey threshold grid. fig73 PNG regenerated. LaTeX recompiled clean (3 pp / 394 KB). 2 supersession-ledger entries appended.

## 2026-05-01T22:45Z — Stage 9 round 2: GREEN

2 PASS / 0 FAIL / 0 MINOR. Both round-1 MINORs verified resolved. Caption-figure consistency restored on fig75; fig73 right-margin clipping eliminated, no new artifacts.

## 2026-05-01T22:50Z — Stage 10 round 1: GREEN

24/24 PASS / 0 FAIL / 0 WARN direct GREEN (no rounds-of-fixes needed; pre-flight Lean module + theorem name + bibitem verifications during authoring paid off). Verifications: 9 Lean modules resolved (A1Ring, A1Resolution, A1Ext, ChangeOfRings, SMFermionData, ModularInvarianceConstraint, GenerationConstraint, RokhlinBridge, WangBridge); 10 load-bearing theorem names resolved (`fermion_count_gives_central_charge`, `central_charge_fractional_without_nu_R`, `qParam_shift`, `framing_anomaly_constraint`, `sixteen_convergence_full`, `z16_anomaly_always_cancels_with_nu_R`, `constraints_without_nu_R`, `rokhlin_strictly_stronger`, `total_components_with_nu_R`, `generation_mod3_constraint`); 12 bibitems present in CITATION_REGISTRY; library counts (5229/243/1/0) exact-match `docs/counts.json`; Ext dimensions 1,2,2,2,3,4 match `A1Ext.lean` `ext_dim_*` theorems; arithmetic identities (`c_-=8N_f`, `24|c_-⇒3|N_f`, `lcm(16,3)=48`, `c_-=15/2 ∉ ℕ`, cube-roots-of-unity phase cycle) all verified; toolchain pins (Lean v4.29.0, Mathlib commit `8850ed93`) verified.

## 2026-05-01T22:55Z — Stage 13 round 1: GREEN

Tier-2 PRL profile sweep across 8 finding classes. Verdict: 0 BLOCKER / 1 RECOMMENDED / 2 ADVISORY. Spot-check passes:
- 5/5 load-bearing bibitems verified in registry + arXiv IDs match bibitem text
- Numerical claims internally consistent (Ext dims, library counts, arithmetic, axiom name)
- 10/10 Lean theorem name references resolve
- L2-paper10 source clean; L2-D2 cross-bridge advisory (D2 not yet drafted; forward-compatible)
- First-claim hedge present in body §IV ("We are not aware of any prior...")
- N/A production-run claims (theory paper)
- Freshness clean (`last_lift` current)
- Tracked-hypothesis discipline in place: 3 textbook hypotheses (ko cohomology, ASS convergence, ABP splitting) explicitly disclosed as non-axioms; single project axiom (`gapped_interface_axiom`) explicitly disclosed as unused in this chain

Stage 13 review doc: `papers/AutomatedReviews/2026-05-01-2200-bundle-stage13/L2.md`.

## 2026-05-01T23:00Z — Bundle L2 CLOSED at GREEN

Phase 7b sub-wave 7b.3 ledger entry: <0.5 person-day effort for fresh first-pass + 3 reviewer-triple stages with deterministic recheck (Stage 9 needed 1 round-of-fixes; Stages 10 + 13 GREEN direct). 3-page Tier-2 PRL splash bundle (target PRL) at GREEN at all three reviewer-triple stages. Bundle ready for arXiv-voucher submission per `PAPER_STRATEGY.md` §3 sequencing. 6 of 13 bundles now reviewer-triple-closed (L2 + D5 + I1 + I2 + L1 + L3); 7 source-only-green still need first-pass drafting (F + D1 + D2 + D3 + D4 + E1 + E2).

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper10_modular_generation (L2's sole source paper) had abstract + conclusion + body first-claims rewritten to descriptive prose. L2 bundle content remains aligned.

## 2026-06-10 — External-review prose fix (L2-Y2)

- Source: (none — direct prose revision per review-2026-06-05 findings)
- Lift action: Prose-revision (direct edit, no content lift)
- Insertion point: abstract + §Ext (textbook-bridge paragraph)
- Stage-13 redo required: no (epistemic-labeling clarification; no claims added/removed)
- Notes: L2-Y2 — epistemic-status label added to the three textbook topology results (ko cohomology, ASS convergence, ABP splitting): all established results in the algebraic-topology literature, tracked pending Mathlib formalization — "a library gap, not an open problem". "Commentary" framing KEPT after load-bearing verification against Lean ground truth: H1/H3/H4 Props live only in `ExtBordismBridge.lean`, are consumed only by the bridge-documentation theorem `generation_constraint_chain` (where they are cleared before the arithmetic), and the kernel-pure headline `SmoothSpinManifold4.rokhlin` (16|σ via Hasse-Minkowski + theta-modularity classification route) does not depend on them — anti-circularity note in `src/core/constants.py` HYPOTHESIS_REGISTRY confirms ABP is deliberately NOT used. pdflatex ×2 clean, 0 undefined refs.

## 2026-06-10 — Prose-revision-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-06-10 freshness reconciliation. L2's only flagged source is paper10_modular_generation (RESTRICTED — owned by active Phase 5q.B session with 6 open adversarial findings; its 16|sigma/Rokhlin deltas are NOT reconciled by this event). Verification-only on source side: paper10's post-2026-05-12 commits (f6048c48 + 6ac6ef89, 2026-06-08) edited L2 in tandem, and 1bb62842 (2026-06-10) applied the L2-Y2 epistemic-label fix — L2 prose already matches paper10's current committed framing (TPFConjecture tracked-Prop note, counts.tex macros, v4.29.1/5e932f97 pins; CHECKs 24/25/26 PASS). No non-paper10 divergence found. ONE bundle edit this event per docs/DISCLOSURE_TEXT.md: standard Variant-B 'Methods and tools disclosure' block installed before bibliography (was clearly absent; register verdict L2=Variant B), and the stale acknowledgments blurb 'Automated proofs by the Aristotle theorem prover (Harmonic).' removed per DISCLOSURE_TEXT.md §2 advisory (L2 uses no Aristotle-proved theorems; lake-build sentence kept). Boilerplate only — no scientific claims added/removed; stage13 redo NOT required. pdflatex x2 clean (4 pp, 0 errors, 0 undefined refs). freshness_stale deliberately RE-SET to true after this event: paper10 substantive reconciliation remains pending Phase 5q.B.

## 2026-08-15 — Deregister-lean-modules

- Modules deregistered: `Schellekens.Chain`, `Schellekens.HolomorphicVOAc24`, `Schellekens.NiemeierLattice`
- Stage-13 redo required: no (no content changed — this records a dependency the
  draft already does not have)
- Rationale: The redraft hands the holomorphic-VOA reading of 24 | c_- to the companion paper on anomaly constraints on Standard-Model particle content, which owns that derivation. The Letter now states the reading in one Discussion sentence citing Schellekens and Moller-Scheithauer as published work, and rests no claim on the Schellekens.* Lean modules: it does not name them and cites none of their theorems. They were registered when this Letter was expected to carry the Niemeier-lattice chain itself. Keeping the citations alive purely to hold the coverage ratchet green is the failure mode ADR-015 D1 was written for, so the registration is withdrawn instead and LEAN_MODULE_ABSENT_CEILING is lowered by three in the same commit.

## 2026-08-15 — Stage-10 full redraft

- Source: (none — full re-authoring from the Lean substrate and the primary sources)
- Lift action: Redraft
- Insertion point: whole manuscript
- Stage-13 redo required: yes
- Findings filed: `papers/AutomatedReviews/2026-08-15-l2-stage10-redraft/L2.md`
  (2 BLOCKER, 8 REQUIRED, 6 RECOMMENDED)
- Notes: Manuscript re-authored end to end against a `prose-reviewer` pre-drafting
  instruction and a second pass on the finished text. Six sections became five;
  the standalone Ext section was folded into the right-handed-neutrino section,
  where the number 16 first does work. Abstract 2454 -> 588 characters against
  the declared 600 ceiling. Both hand-written tabulars and the second figure cut
  (fig73 duplicated fig75's divisibility in a second visual grammar); the
  four-occurrence "16-convergence" enumeration cut to one Discussion sentence;
  the project-wide library census cut from abstract and conclusion.
  TWO BLOCKER-class corrections, both found by re-reading the primary sources
  and the Lean statements rather than the prior manuscript.
  (1) The right-handed-neutrino conclusion. The prior draft concluded that
  modular invariance is a formal argument for nu_R. Wang Sec. IV.2 supplies a
  Pfaffian-like non-Abelian quantum Hall sector carrying the missing c_- = 3/2,
  and Garcia-Etxebarria and Montero Sec. 4.6 state that Dai-Freed constraints
  are altered by coupling to a suitable topological field theory without
  changing the local degrees of freedom. The Letter now states the disjunction.
  (2) The lcm(16,3) = 48 "combined without-nu_R constraint" is wrong: 3 | N_f
  follows from c_- = 8 N_f, which is the 16-component spectrum. At 15 components
  c_- = 15 N_f / 2 and modular invariance gives 16 | N_f, the same condition as
  the Z_16 anomaly. The minimum is 16, not 48, and each condition excludes
  N_f = 3 on its own.
  Ext material CUT from the manuscript. It was grounded first on
  `A1ExtSubstantive.lean` rather than `A1Ext.lean`'s arithmetic proxies, and
  the priority claim was then dropped because no categorical Ext appears in any
  Lean statement and exactness of the free complex is not proved in tree. With
  the priority claim withdrawn the paragraph had no argumentative job: the Ext
  computation is the Adams route to Rokhlin, which this paper obtains from the
  lattice interface instead. Rokhlin survives as a compressed scope paragraph
  justifying why the divisor is 16 and not 8, with an explicit statement that
  the headline 3 | N_f rests on Secs. II and III alone and carries no such
  assumption. `native_decide` remains disclosed in the artifact-availability
  section. The two A1.* apex entries and the charter lede still declare the
  cut contribution; filed as REQUIRED, not fixed here, because
  `bundle_counts.tex` derives from the apex closure and ExtractDeps does not
  run in this worktree.
  Citations: AlvarezGaumeWitten1984, Rademacher1973 and diFrancesco1997 dropped
  (no primary source held; the c = 1/2 coefficient and the zeta(-1) origin of
  the 24 are now grounded on Wang Eqs. (6)-(11), (15), (16) and n. 9, read at
  page level). Kitaev2009 and FidkowskiKitaev2010 dropped (the prior draft's
  Z -> Z_16 class-D attribution is wrong on dimension, symmetry class and
  group). Niemeier1973 dropped with the enumeration. The companion-paper
  bibitem no longer exposes internal bundle codes.
  Compile clean: 4 pp, 0 tex errors, 0 unresolved refs, 0 overfull.
