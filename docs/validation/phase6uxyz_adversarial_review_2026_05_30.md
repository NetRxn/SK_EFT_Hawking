# Phases 6u / 6x / 6y / 6z — full adversarial review (2026-05-30)

Four independent fresh-context **Opus** adversarial reviewers, one per phase, each handed its full phase
roadmap as the intended-implementation yardstick (read-only, no-web, no edits/commits). Mandate: find
gaps between intended and actual scope, overclaims, strengthening-discipline tautologies (P2–P5),
kernel-impurity (axioms / sorry / native_decide / maxHeartbeats), and dishonest labeling.

## Headline result

**No BLOCKING findings in any of the four phases.** All headline theorems checked are kernel-pure
(`{propext, Classical.choice, Quot.sound}`, plus the documented allowlisted KMM/MA `native_decide`
cores in 6x); the load-bearing density / SK / lower-bound results are substantive (not P2–P5
tautologies); and the sensitive honesty watch-items (SK length exponent, conditional-vs-unconditional,
density-vs-span, empirical-vs-proven) hold up. Findings are all RECOMMENDED-level (documentation
drift / labeling nuance), not substance.

| Phase | Verdict | Kernel purity | Notable finding |
|---|---|---|---|
| 6u | GREEN-WITH-RECOMMENDED | pure; 0 native_decide | SK length conjunct decoupled from the actual compiled word (documented as CP2 R2) |
| 6x | GREEN-WITH-RECOMMENDED | pure + 4 allowlisted KMM native_decide cores; Item-L files 0 native_decide | roadmap L.C prose stronger than the parametric Lean reality (FIXED) |
| 6y | GREEN-WITH-RECOMMENDED | pure; 0 native_decide (1 kernel-`decide` w/ maxRecDepth) | roadmap STALE (density witnesses shipped but roadmap says "pending") |
| 6z | GREEN | pure; **0 native_decide anywhere in 6z** | CCZ-essentiality converse ~~not formalized~~ **now FORMALIZED (Phase 6x′ `cliffordOnly_not_dense`, Stage-13 GREEN, 2026-05-30)**; dead seed scaffolding pruned |

## Phase 6u (Clifford+T SU(2) density + generic SK substrate) — GREEN-WITH-RECOMMENDED

- Density genuine (true ε-density over all SU(2) via kernel-proved `H_of_G = ⊤`; NOT a mislabeled finite
  subgroup — the infinite-order proof is load-bearing). SK exponent honest: `log 5/log(3/2) ≈ 3.97`.
- All headline theorems kernel-pure; **0 axiom / 0 sorry / 0 native_decide / 0 maxHeartbeats**.
- **REC-1 (the substantive one):** the "bundled-strict" headline's LENGTH conjunct bounds a closed-form
  `skLength` function of `ε` and is **decoupled from the actual returned word** — the genuine
  word-coupled bound (`skApproxC_generic_freeGroup_length_le_skLength`) exists but requires a
  `BaseFinder_length_bounded` hypothesis NOT discharged for the actual `cliffordTBaseFinder`
  (`Classical.choose`, no length control). So the shipped unconditional Clifford+T compiler has no
  theorem bounding its output word length. Self-flagged as CP2 R2 but framed as a minor follow-up; the
  docstrings read as if length constrains the output. Honesty-of-framing, not a false theorem.
- REC-2: `skLengthBaseCase := 100` etc. are honestly-labeled unverified artifact constants.

## Phase 6x (additional-alphabet instantiations + Mathlib upstreaming + Tier-2 G/H/I/L) — GREEN-WITH-RECOMMENDED

- Tier-2 G/H/I + Item-L (MVP + the 2026-05-30 L.A/L.B/L.C continuation) genuinely clean. `nonempty_kmmReduction`
  is in fact UNCONDITIONAL (stronger than the "deterministic-branch" claim, which applies only to the
  front-end grid finder's ∀-completeness). Item I = honest soundness + empirical pygridsynth completeness.
  Item G = honest KMM `N₃+4·sde` length. Item H = genuine sound+complete biconditional. Item-L L.C honestly
  PARAMETRIC. **The work caught and corrected an error in its own DR source-of-truth** (the Q2.3 "no lower
  bound follows" claim) — the telescoping `T^of ≥ sde₂` argument was independently re-derived as sound.
- Kernel-pure + the 4 allowlisted KMM/MA `native_decide` cores; 0 declared axioms; 0 sorry; no maxHeartbeats;
  Item-L files use NO native_decide.
- **REC-1 (FIXED 2026-05-30):** roadmap L.C closure prose called `toffoliCost_ge_measure` "the genuine
  `T^of ≥ sde₂` bound" while it is a parametric skeleton (in-file docstrings were already honest); tightened
  the roadmap sentence to the skeleton/PARAMETRIC framing.
- REC-2: Item C's M-track "Mathlib PR" mixes real extractions with alias re-exports (the 2026-05-26
  failure-mode #3 pattern); substance exists beneath. Out of core Tier-2 scope.
- REC-3: `synth_CCZ_correct` is a choice-from-existence near-tautology, honestly labeled (correctness, not
  minimality); the substantive Item-L content is in `mukGen_Z_eq_CCZ`/`mukGen_sq`/the L.A channel-rep layer.

## Phase 6y (SU(d) Solovay–Kitaev cascade) — GREEN-WITH-RECOMMENDED

- The two highest-overclaim-risk watch-items are CLEAN: SK length exponent single-sourced at the honest
  `log 5/log(3/2)` (with `skLengthPolylogBound_sud` genuinely discharged, not predicate-only); the (B)
  super-quadratic bound is UNCONDITIONAL concrete-radius (NO `h_regime` hypothesis). Density witnesses
  genuinely proved (engine + SU(4)/SU(8) instantiation both shipped as discharged theorems). Headlines
  kernel-pure; 0 native_decide / 0 sorry / 0 maxHeartbeats (one kernel-`decide` with maxRecDepth, permitted).
- **REC-1:** `Phase6y_Roadmap.md` is STALE — still describes the (D) ClosureDenseWitness as "the SOLE
  substantive frontier / tracked Props / multi-session remaining," but the witnesses shipped (2026-05-28)
  and the SU(4)/SU(8) per-alphabet headlines are already UNCONDITIONAL. Doc drift, not overclaim.
- REC-2: roadmap references `*_tight` headline identifiers that don't exist (actual names differ); cosmetic.
- REC-3: the SU(8) instance ships *Clifford+T at SU(8)* — CCZ is present in the 10-token alphabet but
  VERIFIED UNUSED in witness construction (0 references). Honestly disclosed at the definition site. Flag for
  the paper-bundle Stage-13 reviewer if any draft cites this as "CCZ-essential compilation" (the faithful
  literal Clifford+CCZ density is Phase 6z's deliverable, not 6y's).

## Phase 6z (literal ⟨H,S,CNOT,CCZ⟩ dense in SU(8), CCZ-essential, no T) — GREEN

- Density genuine SU(8) ε-density (NOT a span/subgroup mislabel; `H_of_G = ⊤ ↔ closure = univ`). Seed
  infinite-order genuinely proved via an algebraic-integer trace obstruction (`tr = u·(1/√2) ∉ 𝒪`) and
  load-bearing. Irreducibility = genuine representation theory (Pauli twirl + character orthogonality), NOT
  brute-force decide. d=8 von-Neumann engine actually wired.
- **ZERO `native_decide` in any 6z module** (refutes the watch-item premise) — the density headline rests on
  the kernel; the only `maxRecDepth` gates a kernel `decide` on a finite 63-label orbit (permitted, stronger
  than allowed). All headlines `lean_verify` → `{propext, Classical.choice, Quot.sound}`.
- REC-1: CCZ-essentiality — the POSITIVE direction (CCZ is mechanistically the source of the irrationality)
  is genuinely shown; the CONVERSE (Clifford-only ⟨H,S,CNOT⟩ is finite/non-dense) is asserted in docstrings
  but NOT formalized. Recommend softening the "essential" wording or adding a `Nat.card (Clifford) < ∞` lemma.
- REC-2: dead scaffolding — the roadmap insists the operative seed is DR2's `(H₃·CCX)²` (eigenvalues
  `(−3±i√7)/4`), but the shipped proof uses the cleaner DR1 seed `CCZ·H₁H₂H₃` (trace `1/√2`); the
  `seedEigenvalue` block in `CliffordCCZSU8Irrationality.lean` is unused. Recommend pruning/annotating + fixing
  the roadmap's "operative seed" wording.

## Disposition

All four phases pass adversarial review. The cross-phase RECOMMENDED items (6u length-coupling honesty;
6y roadmap staleness; 6z CCZ-converse + dead scaffolding; 6x M-track aliases) are documentation/labeling
follow-ons in already-closed phases — none blocks. The 6x roadmap-prose item (the only finding originating
in the 2026-05-30 session) was fixed.

## Remediation (2026-05-30, all findings — green-lit by the principal, substance-preferred)

All five advisories addressed. Feasibility note: the *big* substantive fixes (a length-bounded ∀-coverage
base finder for 6u; a formalized 3-qubit Clifford-finiteness theorem for 6z) are NOT cheaply feasible —
each is a genuine multi-increment project gated on the same deep deferred residuals (the grid-completeness
∀-coverage that also gates Item I; the per-generator channel-rep / Pauli-normalization analysis that is
the 6x Fact-3.9 residual). Where substance was feasible it was shipped; otherwise the honest re-framing
(claim only what is proved, name the residual) was applied. Counts after remediation: 9837 theorems / 0
axioms / 0 sorry / 742 modules; build clean; counts_fresh + axiom_closure_allowlist PASS.

- **6u (`f5f664c`) — SUBSTANCE.** Added `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_at_basefinder`:
  the generic word-coupled 3-conjunct headline instantiated at the ACTUAL Clifford+T compiler — error +
  abstract-length UNCONDITIONAL, the CONCRETE output-word-length conjunct conditional on the single explicit
  `BaseFinder_length_bounded` hypothesis (the one irreducible residual; the existential ε₀-net finder provably
  carries no length control). Corrected both decoupled-headline docstrings to label the length conjunct as the
  SK recursion-LEVEL count and cross-reference the new theorem + residual.
- **6z (`fe79c09`) — SUBSTANCE (doc-correctness) + honest re-framing.** Corrected the false "operative seed"
  claim (module docstring + roadmap): the shipped proof uses the DR1 trace-route seed `CCZ·H₁H₂H₃`
  (`tr=u·(1/√2)∉𝒪`), not the DR2 eigenvalue seed — which is a correct, RETAINED alternative obstruction off
  the critical path (kept, not deleted; it is a valid completed Wave-1 deliverable). Softened the
  CCZ-essentiality docstrings to the proved positive direction (CCZ supplies the trace-irrationality),
  attributing the unproved Clifford-only-finiteness converse to the standard fact.
- **6y (`841187c`) — doc refresh (substance already shipped).** Replaced the stale "SOLE frontier / tracked /
  multi-session" block with an AS-SHIPPED UPDATE naming the actually-shipped unconditional witnesses/headlines
  (the stale `*_tight` names don't exist); carried the SU(8)=Clifford+T (CCZ present-but-unused) scope note.
- **6x (`426831b` roadmap prose; `841187c` M-track).** Roadmap L.C prose tightened to PARAMETRIC framing
  (done in the review commit). Added an HONEST SCOPE note to `SU2CompactnessMathlibPR.lean` distinguishing the
  alias/packaging layer from genuine-extraction PRs (M.1).

**Documented substantive follow-ons (NOT done — disproportionate, gated on deep residuals):** (i) a
length-bounded ∀-coverage Clifford+T base finder (constructive finite ε₀-net / Ross-Selinger) to discharge
`BaseFinder_length_bounded` unconditionally; (ii) a formalized 3-qubit Clifford-group finiteness theorem to
prove the CCZ-essentiality converse. Both are tracked as optional, the same class as the existing Item-I
grid-completeness and 6x per-generator channel-rep residuals.

**Scoped 2026-05-30 — Phase 6x′** (`docs/roadmaps/Phase6x_prime_Roadmap.md`) is the staged blueprint for
the per-generator Clifford/CCZ channel-rep analyses, which retire follow-on (ii) [the 6z CCZ-essentiality
converse, via the finite signed-permutation image — Phase 1] plus the 6x Lemma 3.10 + the unconditional
Item-L `T^of ≥ sde₂` bound [Phase 2]. Follow-on (i) (the 6u ∀-coverage finder) and full MITM minimality
remain separately out of scope.

**UPDATE 2026-05-30 — Phase 6x′ Phase 1 SHIPPED, Stage-13 GREEN; Phase 2 off-ramped.** Follow-on (ii) is
**CLOSED**: `SKEFTHawking.FKLW.MukhopadhyayCCZ.cliffordOnly_not_dense` (`MukhopadhyayCliffordNotDense.lean`,
commit `838d96ff`) proves `¬ IsDenseInSUd_gs cliffordOnlyGeneratingSetSU8` — `⟨H,S,CNOT⟩` (no CCZ) is not
dense in SU(8), the genuine CCZ-essentiality converse, via the finite signed-permutation channel-rep image
(Fact 3.9) + channelRep continuity + the infinite-order seed. A fresh-context Opus adversarial Stage-13
review returned **GREEN (no findings at any severity)**: faithful, non-vacuous, CCZ-free, non-circular,
kernel-pure `{propext, Classical.choice, Quot.sound}`, zero new `native_decide`. The 6z `CliffordCCZSU8Density`
docstrings were flipped from "standard fact, not formalized" to cite the theorem (so the `NOT formalized`
note in the 6z row above is now superseded). Phase 2 shipped C.1 (the CCZ diagonal-conjugation identity,
`MukhopadhyayCCZConjugation.lean`, commit `2db6f6c3`) and, per the roadmap off-ramp, kept the 6x Lemma 3.10
+ unconditional Item-L `T^of` as a documented residual (the `hC` half substantiated; `hCCZ` gated on the
64-Pauli Theorem-3.8 entry table + an `sde₂`-on-ℂ matrix measure — disproportionate for a non-tight bound).
Counts after Phase 6x′: 9879 theorems / 0 axiom / 0 sorry / 747 modules; counts_fresh +
axiom_closure_allowlist GREEN.
