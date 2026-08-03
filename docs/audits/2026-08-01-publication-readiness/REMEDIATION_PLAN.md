# Remediation Plan — substance-first

**Date:** 2026-08-01
**Supersedes:** `SYNTHESIS.md` §6 Phase 1, which was mis-posed (see §0).
**Governing posture:** [[feedback-remediation-build-dont-walkback]], as refined by the operator 2026-08-01:

> *"If, while reviewing, there's ever something we could do in order to improve (i.e., fix with substance
> rather than prose) that's my default posture. We'd start by flagging and planning — if we need items that
> are deferred in a given roadmap to strengthen, it's OK to defer publication pending the completion of
> the work."*

**The publication schedule is the flexible variable, not the claim strength.**

---

## 0. Why the first plan was wrong

`SYNTHESIS.md` §6 framed Phase 1 as *"every one is a false statement in a manuscript, and each is cheap to
fix once acknowledged."* That sentence encodes the walk-back default: it treats *narrowing the claim to fit
the weak substrate* as the fix, and prices the work accordingly ("cheap").

The correct question for each Class-1 finding is **"can we build the substrate that makes this claim true?"**
— and only if the answer is a demonstrated no does the claim get revisited, by the operator.

**This failure mode has already cost the project once.** `AnalogHawkingDemarcation.lean:31–39` carries an
"Honesty scope (remediation B-04, 2026-07-17)" block stating the theorem is *"NOT a proof of classical
simulability or a quantum-advantage lower bound."* That block **is** the B-04 walk-back, which the standing
memory records as **RETRACTED** pending the genuine follow-up (build real bipartite acyclicity + the
BP-convergence-on-trees theorem). The build never happened. The Lean was narrowed, the manuscript kept the
strong claim, and D7 has been self-contradictory ever since. **One abandoned remediation, not two errors.**

---

## 1. Triage buckets

Every Class-1 finding sorts into exactly one:

| Bucket | Definition | Action |
|---|---|---|
| **BUILD** | The claim is plausibly true; the substrate is absent or vacuous. | Build it. Defer publication as needed. |
| **CORRECT-TO-SUBSTRATE** | The Lean is right; the prose misdescribes it. | Fix the prose. **Not a walk-back** — the claim isn't being narrowed, the description is being made accurate. |
| **FACTUAL** | A claim about the external record or project history. No substrate can change it. | Correct it. Building is not an option. |

The distinction matters most for **L1**, which has one finding in BUILD and one in FACTUAL. You cannot build
your way out of a misattribution — what Volovik wrote is a fact. You *can* build your way out of a stipulated
parameter window, and doing so makes the result stronger.

---

## 2. BUILD queue

Ordered by (value to the claim) × (existing substrate leverage). "Roadmap" column shows whether an authorized
item already specs the work — where one exists, this is **unexecuted authorized work**, not new scope.

| # | Finding | What must be built | Existing leverage | Roadmap | Est. |
|---|---|---|---|---|---|
| B1 | **D10** HK / Levy–Lieb claimed as "first formalization"; files are 66-line order-theory stubs | Real HK uniqueness + Levy–Lieb constrained search over an actual many-body Hamiltonian, on PhysLib spectral theory | `CoulombRelativeBound.lean` (2,492 lines) — the Kato half is **done** | **`Phase6BB_Roadmap.md` — specs exactly this** | M |
| B2 | **D7** demarcation theorem disclaimed by its own Lean; topological axis vacuous | (a) real bipartite acyclicity + BP-exactness-on-trees; (b) a genuine Chern class, replacing `categoricalChernExpansion`'s linear `c0+c1x` | `AnalogHawkingDemarcation.lean` (286 lines) | B-04 follow-up (retracted walk-back) | M–L |
| B3 | **L1** χ_vest window stipulated, not derived | Carry out the RPA bubble integral with the stated `O(Λ²/16π²)` normalisation, so `[0.1,10]` is a **result** | `VestigialSusceptibility.lean` (382 lines) already has `χ_RPA = χ₀/(1−γ⋆χ₀)` | — | S–M |
| B4 | **D2** H2 "discharged" by `rank = rank` | The genuine Hom-tensor / change-of-rings adjunction | `ChangeOfRings.lean` (167 lines); Mathlib has `Algebra.TensorProduct` adjunctions | — | M |
| B5 | **D6** end-to-end claim with no composite theorem; §2 compiler link empty | The composite theorem chaining code → measurement → compiler → universal logic | all four component layers exist | — | M |
| B6 | **D9** `fdt_quantum_noise_floor` — Johnson term cancels; content is `0 < E0/2` | A real fluctuation–dissipation statement with the thermal→quantum crossover regime | — | — | M |
| B7 | **D4** "central QEC theorem" = `Real.log_pos_iff` on a `codeDistance` *defined* as a log | `codeDistance` from the actual code (min weight of a nontrivial logical operator), then the relation as a theorem | `QECHolographyBridge.lean` (381 lines) | — | M–L |
| B8 | **I3** predicates named for theorems they don't state | `IsNovikovCondition` as the actual Novikov condition; separate Cramér upper/lower bounds | — | — | L; may hit a genuine Mathlib gap → then document as a buildable-absent gap per rule (2) |

**Rule (2) applies throughout:** where a build proves genuinely infeasible, the output is a
*decomposition-backed infeasibility finding* — the precise construction required and its size — surfaced for
the operator, **not** a pre-drafted reframe.

---

## 3. CORRECT-TO-SUBSTRATE queue

The Lean is correct here; the manuscripts misdescribe it. Fixing the prose is not narrowing a claim.

- **D5 §12** — paper lists 8 labels (0,a,b,c,d,e,f,g) for a "7-class" taxonomy; Lean has 7 constructors and
  (e),(f),(g) don't exist. Real classes (b′),(b″) are missing from the paper. Fix the paper to the Lean.
  *Open build question:* whether the taxonomy should be **extended** — Track C's f(R)/Lovelock candidates
  live in (b′),(b″) and are currently unrepresented in the narrative.
- **D12** — abstract claims photon-counting/bolometric device results; §2 correctly says no theorem is a claim
  about any device. §2 is right.
- **D11** — correction narration (`:328`, `:459`, the 23-line counting-rules digression). The *corrections* are
  right; only the telling-the-reader-about-them is wrong.
- **D3 §6** — carries L1's framing; follows L1's resolution.
- **F `:1957`** — "all 17 bundles Stage-13 GREEN" is now false on its face.

---

## 4. FACTUAL queue

No substrate can make these true; they are statements about the external record.

- **L1 `:78`** — *"Volovik's 2024 vestigial-fluid review proposes this directly."* arXiv:2312.09435v2 does not
  contain the graviton = second-sound identification. `Volovik2022Counting` **is** correctly cited for the spin
  counting; that citation stays. Strongest correct framing: lead with the measure result
  (GW170817-compatible window has measure ≈1.2 × 10⁻¹⁴), which kills the whole class of order-unity
  identifications and does not depend on attribution. With B3 done, the falsified object becomes a
  *project-derived* prediction — a legitimate and stronger target.
- **L1 abstract `:33`** — *"Several emergent-gravity programs identify…"* generalises to an unnamed plurality
  behind a single citation.
- **I1** — *"All nine sub-lemmas closed in a single Aristotle priority batch."* No entry in
  `ARISTOTLE_THEOREMS` (322 entries, 34 runs, zero `EWBaryogenesis`), no run ID. Either the run exists and must
  be identified, or the sentence is false.
- **D10 / I2 / D2 / D8 priority claims** — "first in any proof assistant" formulations; resolve against the
  now-reachable AFP and GitHub prior-art sources (egress unblocked 2026-08-01).

---

## 5. Program-level item: `native_decide` — defer to Phase 6GA

**This is known, categorized, and already scoped. Do not re-derive it.**
Canonical source: [`docs/roadmaps/Phase6GA_Roadmap.md`](../../roadmaps/Phase6GA_Roadmap.md).

*Correction to an earlier figure of mine:* I reported "1,541 sites across 828 files" from a raw grep. That
swept comments and docstrings and is wrong. The project's own measured surface (`docs/counts.json`, ADR-002
ratchet) is **546 decl-closure over 494 real tactic sites in 43 files**, clustered `anyon_mtc` 327 /
`number_field_qgroup` 154 / `other` 53 / `lattice_signature` 12.

6GA is the `native_decide → decide +kernel` ratchet, with a verified spike: **90 of 494 sites converted with
zero errors**, cost from negligible to ~7×. Its guardrails already cover the failure modes I was going to
raise — never raise heartbeats to force a conversion; statements stay byte-identical; the ratchet is a floor,
not a target. It also records a known negative (the private braid-word corpus does **not** convert).

**The only publication-side action here** is ordering, not scope: **6GA should prioritise the clusters that
back promoted manuscript claims** — D4's trefoil / figure-eight / hexagon / ribbon invariants sit in
`anyon_mtc`, the largest cluster. Until those convert, no bundle may assert or imply axiom-freedom for a
result whose closure contains `ofReduceBool`.

**No operator decision needed.** My earlier "tier 1 vs tier 2 boundary" question is answered by 6GA's own
wave structure.

---

## 5b. The lineage instrument already measures Class 1 — nothing gates on it

`scripts/chain_canonicalize.py --report` resolves every claims-reviewer chain link against the live graph.
Run 2026-08-01, whole corpus: **3,442 links — 87% resolved, 121 `theorem-absent`, 112 `invalid-target`,
84 `formula-absent`.**

`theorem-absent` is precisely Class 1's mechanical core: **a manuscript sentence whose chain-of-backing names
a Lean theorem that does not exist.** D7's phantom `analog_hawking_quantum_advantage_demarcation` is one of
121, not an isolated slip.

Per-bundle (`--paper <bundle>`), resolved / absent / invalid:

| Bundle | resolved | **absent** | invalid | Note |
|---|---|---|---|---|
| **D7** | 12 | **15** | 0 | **more absent than resolved** — worst ratio in the portfolio |
| **I1** | 61 | **24** | 1 | highest absolute; includes the Aristotle-batch claim |
| **D12** | 200 | 18 | 0 | best coverage (the 148-finding Stage-10 walker ran here) |
| **L1** | 50 | 16 | 0 | |
| **D2** | 75 | 13 | 6 | |
| **D8** | 43 | 10 | 0 | |
| **D11** | 226 | 6 | 14 | highest resolved count — most disciplined bundle |
| **D1** | 23 | 6 | 6 | |
| **D4** | 30 | 5 | 5 | |
| **E1 / E2** | 20 / 63 | 5 / 4 | **17 / 19** | highest invalid — the triplicated Phase-6w block's targets (`grep_theorem_count_phase6w`) |
| **D3 / L2 / D5 / D10 / I2 / L3** | 19 / 36 / 28 / 25 / 98 / 59 | 0 / 0 / 1 / 1 / 1 / 3 | 0 / 4 / 0 / 0 / 2 / 2 | |
| **D6, D9** | — | — | — | **no `claims_review.json` at all** — Stage 10 never ran |
| **F, I3** | 0 | 0 | 0 | file exists, **zero links** — no chain-of-backing whatsoever |

**Three independent confirmations fall out.** D6/D9's missing Stage-10 (third source now). F's "31 prose
bullets, 5 with theorem names" — mechanically, the flagship has *no lineage at all*. And D7's severity
ordering: it is quantitatively the worst bundle, matching its F grade and four placeholder sections.

**Consequence for Phase 0 — and a caution about this whole section.** `SYNTHESIS.md` §6 item 4 proposed
building `bundle_headline_theorem_resolves`. **That would have duplicated an instrument that already exists
and already works.** That near-miss is the reason the operator has withdrawn clearance to build
infrastructure without approval (2026-08-01), and it applies to *every* item in `SYNTHESIS.md` §6, not just
item 4. See §6a below.

**Caveat on the 121 figure — do not quote it as settled.** The `--report` run emits many
`Ambiguous Lean name '<short>' resolves to N candidates — edges skipped` warnings (`zero` → 12 candidates,
`ext` → 19, `A`/`F` → 8 each). Some fraction of `theorem-absent` is therefore a **name-resolution artifact,
not a missing theorem**. The per-bundle ordering is likely still informative (D7's absent > resolved is
extreme enough to survive a large correction), but the absolute counts are unverified pending the
exploration in §6a.

---

## 6a. ⛔ Phase 0 is NOT authorized as written

**Operator ruling, 2026-08-01:** *"you aren't cleared to build new infrastructure without approval for that
reason. you must explore, or use explore agents to fully understand our existing system before you consider
making changes. This is a defect analysis & remediation layer, and possibly an update to our late wave
absorption protocol/procedure."*

`SYNTHESIS.md` §6 Phase 0 listed six checks to build. **That list is withdrawn.** It was written before the
existing system was mapped, and the `chain_canonicalize` case proves the failure mode is live: one of the six
was a reimplementation of a working instrument.

**What this engagement actually is:** a *defect analysis and remediation layer*, plus — where the analysis
shows the process itself produced the defect — an *amendment to the existing lift procedure and/or late-wave
absorption protocol*. Both are document changes over existing machinery.

**Standing rule for the rest of this work:** for every proposed check or gate, the sequence is

> **(1)** identify the defect class → **(2)** establish what existing machinery covers it, by reading the code
> → **(3)** if a genuine residue remains, describe it and **request approval** → **(4)** only then build.

Never (4) before (3). "The dial doesn't exist" must be demonstrated, not assumed — the audit's own systemic
finding is that dials existed and were disconnected, which is a *wiring* problem, not a *building* problem,
and the two have very different costs.

Exploration of the three subsystems (validate.py check inventory; provenance/lineage stack;
bundle-lifecycle + absorption machinery) is in flight. Phase 0 will be re-authored against its results as a
**defect → existing coverage → residue** table, with the residue column being the only thing that could
become a build request.

**Outcome so far (2026-08-03).** The exploration confirmed the withdrawal was right: of the seven defect
classes Phase 0 proposed building for, **four already have working machinery wired to `passed=True`**, and
one (`prose_theorem_reference_coverage`) is a functioning hard gate that item 4 would have duplicated. The
instrumentation work is therefore *repair and wiring*, not construction, and it is now governed by
**[ADR-009](../../adrs/ADR-009-validation-suite-modularization.md)** (validation-suite modularization + the
mutation-test obligation), with execution detail in
`docs/architecture/.working-docs/validation-module-migration-notes.md`. Only two defect classes are
genuinely uncovered — Lean-module→bundle coverage, and prose figure/table counts — and neither is authorized
for construction.

---

## 6. Revised sequencing

Phase 0 is **suspended pending §6a**. The sequencing below is otherwise unchanged.

Phase 1 is now **flag → plan → build**, and it gates publication rather than being gated by it:

1. **Phase 0** — instrumentation (§6 of `SYNTHESIS.md`, unchanged).
2. **Phase 1a** — CORRECT-TO-SUBSTRATE + FACTUAL queues. Fast, and they stop the portfolio actively
   *misstating* things while the builds run.
3. **Phase 1b** — BUILD queue, B1–B8, dispatched across worktree slots. **Publication of any bundle with an
   open B-item is deferred until that item lands or is proven infeasible.**
4. **Phase 2–4** — deduplication, mechanical sweep, structure/length (unchanged), runnable in parallel with 1b
   since they touch disjoint material.
5. **Phase 5** — process repair, including the lift-procedure changes and the D11 rule (*correct claims
   silently*).

**Consequence to state plainly:** no Tier-1 bundle ships on the previous timeline. B1, B2, B5, B6, B7 each gate
a headline. That is the intended trade — per the governing posture, the schedule moves and the claims don't.

The nearest-term submittable candidates are the ones whose findings are *not* in the BUILD queue: **L3**
(`revision`), **L2** (`revision`, needs the PRL abstract cut from 2,804 chars), and **L1** once B3 lands and
the FACTUAL items are corrected.
