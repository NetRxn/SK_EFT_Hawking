# PR review pass 3 — consolidated findings register

**Branch:** `infra/adr-009-validation-modularization` · **Reviewed at:** `db430c65` ·
**Date:** 2026-08-05 · **8 reviewers, 6 defect-dimension + 2 architectural, one worktree each.**

| reviewer | dimension | verdict | C | M | I | Min |
|---|---|---|---|---|---|---|
| [R1](reviewer-reports/R1-population-reach.md) | population reach | **NO** | 2 | 4 | 3 | 3 |
| [R2](reviewer-reports/R2-new-fixes.md) | the four newest commits | **NO** | 1 | 4 | 3 | 8 |
| [R3](reviewer-reports/R3-ratchets.md) | ratchets & baselines | YES-WITH-FIXES | 1 | 2 | 3 | 5 |
| [R4](reviewer-reports/R4-test-efficacy.md) | can the tests fail | **NO** | 2 | 3 | 5 | 3 |
| [R5](reviewer-reports/R5-docs-accuracy.md) | docs vs code | **NO** (docs only) | 0 | 6 | 7 | 14 |
| [R6](reviewer-reports/R6-adr010-verification.md) | ADR-010 numbers | YES-WITH-FIXES | 3 | 5 | 6 | 3 |
| [H1](H1-goal-fit.md) | does the infra serve the goal | thesis **SUPPORTED, reframed** | — | — | — | — |
| [H2](H2-plugin-and-seams.md) | plugin fit & seams | parts sound, **seams unenforced** | — | — | — | — |

---

## 1. The architectural finding — one sentence, from two independent reviewers

H1 and H2 arrived at the same axis from opposite ends.

> **H1 (what is measured):** every content-facing predicate is universally quantified over a
> population *the draft itself supplies* — `∀x ∈ S(draft). P(x)`. None is existential or
> cardinality-bounded. **Every universal over ∅ is true**, so the system cannot distinguish
> *correct* from *contains nothing to be wrong about*. It is **monotone in emptiness**: a
> one-paragraph draft with no citations, no Lean references and no numbers is a clean run of all
> 60 checks *and* a clean review from all three LLM agents.
>
> **H2 (what is wired):** the **derived** spine — `lean_deps.json` → `atlas_view.json` → frontier
> → SessionStart injection — is a genuinely coherent closed loop and cannot drift. The
> **hand-maintained** half is accretion, *"with the two exceptions (`KERNEL_NOGO_REGISTRY`,
> `HYPOTHESIS_REGISTRY`) being exactly the two that acquired a validate gate."*

Together: **the infrastructure is excellent at proving that what exists is consistent, and has no
construct for proving that enough exists.** That is not an omission to be patched check-by-check;
it is a property of the predicate form, and it is why 60 green checks coexist with a portfolio the
2026-08-01 audit graded C−.

**The confirming instance:** the portfolio's only GREEN bundle, **D9, is 12 pp against a ~40 pp
charter, references 3 Lean modules, and never had Stage 10 run.**

### Coverage against severity — inverted

| category | checks |
|---|---|
| consistency/agreement | 12 |
| resolution/existence | 13 |
| freshness | 7 |
| process/ledger | 9 |
| build & trust | 7 |
| Lean-statement substance | 5 |
| physics/numerics | 4 |
| presentation | 2 |
| aggregate | 1 |
| **content sufficiency** | **0** |
| **substrate attachment** | **0** |

Drift prevention = 32 of 60 = 53 %, and it is genuinely first-rate. But the least severe audit
defect class carries ~12 instruments and the three most severe carry between zero and one.

---

## 2. The recurring implementation flaw — enumerate instead of derive

Found independently by R1, R2 and R6, in four unrelated instruments:

| instrument | enumerates | missed | status |
|---|---|---|---|
| `prose_theorem_reference_coverage` | `\texttt` → `\lean` → `\verb` → `\thm`/`\mthm` | **900 references** in one day across three shapes | **FIXED** `39e7ac3a` — replaced with brace-matched bodies + alias fixpoint; 671 → **1 280** |
| `ExtractDeps` → `lean_deps.json` | what the root aggregate imports | **27 modules**, 16 never compiled; ~15 checks + counts + atlas + graph all blind | OPEN |
| `cluster_detect.py` | `startswith('paper')` | **all 19 bundle** `claims_review.json` → `bundle_consistency` verifies zero bundle members | OPEN |
| `paper_tables/sources.py` | neutralized `\input` only | any other control sequence → **broke paper15's build** | **FIXED** `39e7ac3a` — inverted to an allowlist |
| `readiness_gates.py:430` | `\texttt` only | Gate 5 LeanProofSubstance blind to D6/D8/D9's own references | OPEN |
| `_PROSE_REF_ALLOWLIST` registry tier | 606 registry keys resolve *before* `lean_deps.json` | incl. the 14 dead Aristotle keys the branch's own ratchet certifies name nothing | OPEN |

**The pattern is the finding.** Two prior review passes read these checks and judged them
well-constructed — which they were, on their own terms. Reading a check establishes whether it is
well-built; only measuring the corpus independently establishes whether it is *pointed at the
right set*. All three verbatim holes were found that second way, none the first.

---

## 3. CRITICAL findings

| id | finding | source | status |
|---|---|---|---|
| C1 | `\thm`/`\mthm` wrapped alias — 336 refs unscanned while reporting PASS | R1 R2 R6 | **FIXED** `39e7ac3a` |
| C2 | 27 project Lean modules absent from `lean_deps.json`; 16 never compiled. `ExtractDeps.lean:9` claims the root transitively imports all project modules — **verified false** | R1 | OPEN |
| C3 | `parameter_provenance` cannot see a **10× drift in ℏ** — 169 of 206 entries silently skipped, and `max(abs(actual), 1e-30)` makes the relative test absolute. Invariant #8 unenforced for value agreement | R4 | OPEN |
| C4 | `bundle_source_freshness` **writes to nine tracked production files on every run**, including from pytest — it writes its own verdict into the artifact the absorption protocol reads as its trigger | R4 | OPEN |
| C5 | prose check resolves **606 registry keys before consulting `lean_deps.json`**, including 14 known-dead Aristotle keys. Proved with a one-character control | R3 | OPEN |
| C6 | ADR-010 "D11 and D12 reference zero Lean declarations" is **false** — D12 → 160 declarations / 13 modules, D11 → 125 / 25 | R6 R2 | ADR CORRECTION PENDING |
| C7 | ADR-010's "the audit's ~340 is low by 4–5×" is a **unit swap** — the audit said 162 `PinPlus*.lean` **modules** (reproduced at 164); the re-measurement counted **declarations** and graded the audit ❌ for the difference. The `2 914` count is also ~30 % inflated by 748 structure/inductive companions | R6 | ADR CORRECTION PENDING |

---

## 4. Seam findings (H2) — the plugin question

1. **Three of four gates have no caller.** `gate_precheck` defines s9 / s10 / s13 / submission;
   only **s13** is invoked (`wave-close/SKILL.md:34`). `wave-close` step 2 then dispatches
   `claims-reviewer` **directly, bypassing the s10 gate built specifically to guard that
   dispatch**. `BUNDLE_LIFT_PROCEDURE.md` contains zero occurrences of "precheck".
2. **Plugin prompts drift against code at 19.7 % (26 of 132 references), with zero enforcement** —
   two dead `validate.py --check` names, a nonexistent `data/` path, a **14-code bundle roster
   against the canonical 21** (so D6–D12 and I3 are invisible to *both* bundle-aware reviewers),
   and `coach.md` telling the human-proxy to apply "Core PD-0..PD-4" when **PD-5 is an
   operator-set decision sitting inside Core**. The repo enforces docstring↔code cross-references
   for Python↔Lean and does not enforce the same for plugin↔code.
3. **The deterministic/LLM loop runs one way only.** Agent output flows *into* the suite through a
   real typed pipeline; **nothing consumes `validate.py --json`** — a frozen contract with no
   counterparty. So `claims-reviewer` Classes TN and TP re-implement
   `prose_theorem_reference_coverage` and `paper_toolchain_pin_drift`; the latter's own docstring
   calls itself the *"structural mirror"* of the agent class it duplicates.
4. **The 5 554-test pytest suite is in no gate at all** — a wave can close with it red.
5. **`gate_precheck s13` currently cannot pass on any wave, pure-Lean included**, because of
   paper-corpus reds. This is exactly the sharp edge `VALIDATION_GATE_TOPOLOGY.md` §2 predicted,
   now live. **The scoping fix is ~60 LoC because ADR-009 already partitioned the checks by
   domain.**

---

## 5. What is already fixed at `39e7ac3a`

- C1 — verbatim detection is now structural (brace-matched bodies + alias fixpoint), not an
  enumeration. **671 → 1 280** candidate references; two genuine unresolved D12 references
  surfaced, both verified as real Mathlib names in the pinned source.
- The paper15 build regression this branch introduced, fixed **at the generator** by inverting
  `\input`-only neutralization into a safe-macro allowlist.

## 6. Open, by owner

**Substrate integrity (highest):** C2 — 27 invisible modules is a hole under the whole derived
spine, including the atlas H2 identifies as the system's one coherent loop.

**Instrument correctness:** C3, C4, C5; R3's `CI_SKIP` runs-then-discards; R2's freshness fix keys
on directory *existence* rather than *measurability* (an empty directory restores the vacuous
verdict); the `LEGACY_DRAFT_UNRESOLVED_REF_CEILING` is **environment-dependent** — 79 with PhysLib
built, 83 without, so the ratchet and its zero-headroom test both go red in a fresh clone.

**ADR-010:** C6, C7 — two published claims to correct. **What survives adversarial
re-derivation: M1 page counts, M4a's 78 shared theorems (the D6+D9 merge case), M5, M6.**

**Documentation:** R5's 27 findings, 6 load-bearing.

**Architecture:** H1's five already-computed-but-discarded signals (`compile_bundle_pdf` computes
`pages` then drops it; `bundle_metadata.lean_modules_referenced` written `[]` and read by nothing;
`chain_canonicalize`'s 121 `theorem-absent`; `PAPER_DEPENDENCIES`; the bundle anchor lists), and
H2's five seams.
