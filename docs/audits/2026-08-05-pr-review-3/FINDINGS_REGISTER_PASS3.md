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

---

# REMEDIATION — closed 2026-08-06

Every CRITICAL and MAJOR is closed. Each was **re-verified by the lead before being
fixed** — three did not reproduce as filed, and two of those were the reviewer measuring
the right defect with the wrong mechanism.

## CRITICALs

| id | resolution | commit |
|---|---|---|
| C1 `\thm`/`\mthm` alias — 336 refs unscanned | Verbatim detection is now **structural**: brace-matched macro bodies plus a fixpoint over aliases-of-aliases. 671 → **1 280** candidate references. | `39e7ac3a` |
| C2 27 modules outside the build graph | 2 broken modules repaired, 25 imported, 1 deleted (below). New `lean_modules_in_build_graph` joins the filesystem to the import graph; exe-root allowlist **parsed from `lakefile.toml`**. **Zero exceptions.** | `566c0fa1` `ffb64183` |
| C3 `parameter_provenance` blind to a 10× ℏ drift | Denominator was `max(abs(actual), 1e-30)` — an absolute test below 1e-30. Now genuinely relative; the 169 un-comparable entries are counted and ratcheted instead of skipped in silence. | `37cf835a` |
| C4 freshness check mutated 9 tracked files | `check()` is **pure by default**; the CLI passes `write_metadata=True`. R4's specific reproduction did not hold — the writes are content no-ops while values agree — but the mechanism was real and was proved directly. | `37cf835a` |
| C5 606 registry keys whitelisting non-existent theorems | Dead `ARISTOTLE_THEOREMS` keys withdrawn, derived by intersecting the registry against the live index. Ceiling 79 → 80, cause recorded. *(R3 said "before `lean_deps`"; it is after — the finding stands regardless.)* | `21724ad1` |
| C6 ADR-010 "D11/D12 reference zero" | **FALSE** — an extraction artifact. D11 = 95 declarations, D12 = 132. Claim withdrawn. | `ef866bda` |
| C7 ADR-010 "audit's ~340 low by 4–5×" | **A UNIT SWAP.** The audit said 162 `PinPlus*.lean` **modules**; there are **164**. The audit was right. | `ef866bda` |

## MAJORs

`compute_lean_hash` blind to the root aggregate · `cluster_detect` excluding all 19 bundles
(*and the freshness guard watching it carried the same predicate*) · `readiness_gates` Gate 5
`\texttt`-only (105 names seen vs 778) · `paper_latex_compiles` bundle-only (14 of 43 legacy
drafts fatally broken while it reported 21/21) · `CI_SKIP` running checks then deleting results ·
the self-sealing CI-floor test · `gate_precheck s13` unable to pass for any wave · plugin roster
13 codes vs 21 · 2 dead `--check` names in a reviewer prompt.

## Found during remediation, not by any reviewer

- **The pre-commit `sorry` guard was INERT.** It matched `declaration uses 'sorry'` with straight
  quotes; Lean v4.32.0 emits backticks. Verified by running the guard's own expression against a
  log that genuinely contained the warning: no match. `main` carries the same bug. (`8a08889e`)
- **The project's only live `sorry`** sat in `SingularConnSquareCrossReal`, a duplicate of an
  already-proven theorem on the route `SETTLED_FORKS` bans and `3ea6b739` hard-reverted. It
  survived that revert **only because it was orphaned** — the revert could not see it for the same
  reason no instrument could. Deleted after reading both candidate files in full; the sibling
  `CloseUncond` was **kept**, because reading it showed two general reusable lemmas the earlier
  delete-both recommendation would have destroyed.
- **The counts regen costs 3 min 14 s, not the "~30 min"** asserted in four places and used to
  defer regeneration.
- **Nothing enforced plugin↔code references.** New `tests/test_plugin_prompt_code_refs.py`.

## Instrument errors by the lead, recorded

Four times a probe returned the wrong answer and was caught by re-checking rather than accepted:
a non-leaf module whose import removal left it transitively reachable; a LaTeX defect seeded after
`\end{document}`; an advisory check used as a negative control; and a script-path test that
resolved only against the repo root when prompts legitimately reference the plugin's own.

## State at close

| | |
|---|---|
| `pytest` | **5 588 passed / 5 skipped / 0 failed** |
| `validate.py` | **59/61**, `✓ SUBSTRATE: clean` |
| remaining reds | `bundle_metadata_matches_graph`, `readiness_submission_gate` — both paper-corpus, both ADR-010 work **on this branch** |
| `lake build` | 0 errors, **0 sorries**, 2038 modules = 2036 reachable + 2 exe roots |
| tree | clean, 132 commits ahead, **unmerged** |

**Open, deliberately:** R5's remaining MINOR doc items; the 14 broken legacy drafts (frozen by
`LEGACY_DRAFT_LATEX_BROKEN_CEILING`); H1's absent content-sufficiency and substrate-attachment
checks. All are paper-corpus work, which lands on this branch so the infrastructure is validated
by use before it is merged.
