# ADR-006 — Aristotle submission rewrite: minimal-closure partial submission + verify-then-graft, archiving the full-project process

- **Status:** **PROPOSED (2026-06-25).** Drafted on branch `feature/aristotle-process-rewrite` (off `main` @ `b8add28c`), pending user review of this ADR before implementation. Supersedes the *active-tooling* posture of the Aristotle reference doc ([docs/references/Theorm_Proving_Aristotle_Lean.md](../references/Theorm_Proving_Aristotle_Lean.md)) and Stage 4 of [WAVE_EXECUTION_PIPELINE.md](../WAVE_EXECUTION_PIPELINE.md) §172–257 for **new** submissions; the prior full-project process is **archived, not deleted** (it is the Methods of record for prior papers — see Consequences). The Aristotle **provenance/attribution layer** (`ARISTOTLE_THEOREMS`, disclosure variants, `SORRY_GAPS` historical registry) is **preserved unchanged**. Blast radius mapped by three read-only impact-assessment agents (2026-06-25); anchors below are verified against the working tree.

---

## Context

### What the old process is, and why it was fine then

Aristotle (Harmonic) is the project's Stage-4 fallback automated theorem prover for Lean 4 `sorry` gaps. The active tooling — `scripts/submit_to_aristotle.py` + `src/core/aristotle_interface.py::AristotleRunner` — was built when the Lean substrate was **~76 `.lean` files**. Its design choices were reasonable at that scale:

- **`AristotleRunner.submit_and_wait` hardcodes `--project-dir self.lean_dir`** ([aristotle_interface.py:1942](../../src/core/aristotle_interface.py)) — every submission uploads the **entire** Lean project. The script says so explicitly ([submit_to_aristotle.py:9-12](../../scripts/submit_to_aristotle.py)): *"Every submission sends the ENTIRE Lean project to Aristotle. The prompt only guides where Aristotle focuses."*
- **`integrate_proofs` is a blind whole-file copy** ([submit_to_aristotle.py:196-207](../../scripts/submit_to_aristotle.py)): it `shutil.copy2`-overwrites **every** returned `.lean` file that differs from ours, with no merge intelligence and no verification gate beyond a suggested `lake build`.

### Why it is now a foot-gun

The substrate has grown ~15×, to **1,172 `.lean` files / 17 MB / 312,915 lines** (measured 2026-06-25). The two design choices above are now actively dangerous:

1. **Full-project upload** ships all 17 MB on every run — slow, wasteful, and maximally exposed to the **toolchain mismatch** (below). The `--priority`/`--target` flags do *not* mitigate this: `submit_priority_batch` filters only the *prompt hint*, never the upload scope ([aristotle_interface.py:2009-2038](../../src/core/aristotle_interface.py)) — a dangerously misleading name.
2. **Blind whole-file `--integrate`** can overwrite *any* of the 1,172 files Aristotle returns — not just the target — silently compromising the substrate. It performs **no kernel-purity / axiom audit**, **no `validate.py` run**, **no test gate**. This contradicts the project's matured standards: kernel-purity bar `{propext, Classical.choice, Quot.sound}`, no `native_decide` regressions, no un-signed-off axioms (CLAUDE.md; ADR-002; ADR-004).

Additional latent foot-guns found in the surface scan: `--force` permits parallel duplicate uploads; the pre-flight running-job check greps CLI text and fails open if the format changes; submission **manifests are write-only** (the intended dedup at [submit_to_aristotle.py:13](../../scripts/submit_to_aristotle.py) was never implemented — manifests are saved but never read); `AristotleResult.sorries_filled/remaining` are declared but never populated.

### The two-layer distinction (the key framing)

The "Aristotle machinery" is **two layers**, and only one is dangerous:

- **(A) Active tooling layer — the foot-guns.** `submit_to_aristotle.py`, `AristotleRunner`'s submission/integration methods. **This ADR rewrites layer A.**
- **(B) Provenance / attribution layer — load-bearing, not dangerous.** `ARISTOTLE_THEOREMS` (the append-only run-ID ledger, [constants.py:980-1374](../../src/core/constants.py)), the `SORRY_GAPS` historical registry ([aristotle_interface.py:71+](../../src/core/aristotle_interface.py)), the locked disclosure Variant A/B + S1/S2 applicability rule ([docs/DISCLOSURE_TEXT.md](../DISCLOSURE_TEXT.md)), `aristotle_usage_by_bundle.py`, `ATTRIBUTION.md`. **This ADR preserves layer B unchanged**, and the new tooling must keep feeding it.

### What the blast-radius assessment found

Three read-only agents mapped the impact (claims/disclosure · automated processes · tooling/pipeline). Load-bearing findings:

- **The count `322` is hard-asserted in two places** — `constants.py:1372` (`assert ARISTOTLE_PROVED_COUNT == 322`) and `validate.py:1172` (CHECK 5). Registering a new run requires bumping **both** in the same commit. `TOTAL_THEOREMS = ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)` ([constants.py:1371-1374](../../src/core/constants.py)).
- **Archive-not-delete is already a coded invariant.** `tests/test_lean_integrity.py:174-176` requires `len(SORRY_GAPS) >= 45` *"as provenance."* Deleting historical registry entries would fail an existing test.
- **Prior papers describe the old process verbatim.** `papers/I1/paper_draft.tex:256-264,1119` and `papers/paper15_methodology/paper_draft.tex:100,110,121` state *"the entire Lean project is submitted."* `papers/D1/paper_draft.tex:835-851` is a case study on an Aristotle-discovered counterexample (run `270e77a0`). These Methods sections, and every cited run-ID, are an **immutable record** of how prior results were produced.
- **Only three code sites import the tooling module** — `src/core/__init__.py:40-44/59-62`, `scripts/submit_to_aristotle.py:50`, `tests/test_lean_integrity.py:168` — all importing the **data layer** (`SorryGap`, `SORRY_GAPS`, `AristotleResult`, `AristotleRunner`). Archiving must keep the data layer importable.
- **Toolchain mismatch is a known, tolerated risk.** Our pin is `leanprover/lean4:v4.29.1` ([lean/lean-toolchain](../../lean/lean-toolchain)); Aristotle is confirmed **still on 4.28.0** (re-checked 2026-06-25 — unchanged since we last looked). One cross-version submission since moving to 4.29.x **succeeded** (cherry-picked rather than `--integrate`d — the very foot-gun this ADR removes). The mismatch is therefore real but empirically survivable; the verify-then-graft gauntlet (D2) is the safety net, not a mandatory pre-flight build (see D6).

---

## Decision

Replace the active Aristotle **submission + re-incorporation** tooling (layer A) with a **safe-by-construction** process, archive (not delete) the old full-project process, and leave the provenance/attribution layer (layer B) untouched. The new process **slides into the same seam** with minimal architectural change.

### D1 — Partial submission by minimal-closure staging (never the full project)

New submissions stage a **minimal Lean project** = a `lakefile` + `lean-toolchain` + the **transitive `SKEFTHawking` import-closure** of the target `sorry` file(s) only, with only the target file(s) editable and the rest supplied as Aristotle *context* files. The full ~1,172-file upload path is removed from the default flow.

*Worked basis:* the two open L2 `sorry` files (`SingularConnSquareCloseNC.lean`, `SingularOpenDualityMVConnSquareCore.lean`) have a transitive closure of **138 modules / 1.39 MB / 23,518 lines ≈ 8 % of the substrate** — a ~92 % upload reduction, and it excludes the other ~1,030 modules entirely.

### D2 — Verify-then-graft re-incorporation (never blind whole-file copy)

The new retrieve path is **retrieve → review diff → hand-graft only the target theorem bodies → verification gauntlet → keep-or-reject**. It never `shutil.copy2`-overwrites our tree. The gauntlet, run before anything is kept, is:

1. `lake build` clean, zero new `sorry`;
2. **axiom/kernel-purity audit** (`lean_verify` / `validate.py --check axiom_closure_allowlist`) — reject any closure escaping `{propext, Classical.choice, Quot.sound} ∪ AXIOM_METADATA`, any new `native_decide` (ADR-002), any un-signed-off `axiom`;
3. `validate.py` green;
4. relevant tests green.

A returned proof that fails any gate is rejected, not grafted.

### D3 — Archive, do not delete, the old full-project process

The old tooling is **prominently labeled DEPRECATED / full-project-oriented and archived**, kept functional only for reproducing prior papers' Methods, and gated so it cannot run by accident:

- `scripts/submit_to_aristotle.py` → archived (relocated and/or banner-guarded so an unguarded invocation refuses and points to the new tool). No internal module imports it, so this is low-risk.
- `AristotleRunner`'s full-project submission/integration methods → retained in place but banner-deprecated and guarded (an explicit, documented escape hatch is required to run the archived full-project path).
- The **data layer** (`SorryGap`, `SORRY_GAPS`, `AristotleResult`) stays importable so the three import sites and the provenance tests keep working.

### D4 — Preserve the provenance/attribution layer and its registration chain

Layer B is unchanged. A newly Aristotle-proved theorem flows through the **existing** registration chain, which the new tooling must drive: add to `ARISTOTLE_THEOREMS` + bump the two `322` asserts → set the `SORRY_GAPS` entry `filled=True` → `update_counts.py` (→ `counts.json` / `\aristotleproved`) → `build_graph.py` (dedup by run-ID) → `aristotle_usage_by_bundle.py` re-derives disclosure Variant A/B → `ATTRIBUTION.md` count → `validate.py`. Disclosure Variant A/B wording and the S1/S2 applicability rule remain locked (user decision 2026-06-10).

### D5 — Attachment seam (minimal architectural change)

- New module `src/core/aristotle_submit.py` (`SafeAristotleRunner`): `stage_minimal_closure(target) → Path`, `submit_safe(closure_dir, prompt, …)`, `retrieve_review(run_id)`, `graft_targeted(...)`, `run_verification_gauntlet(...)`. It **reuses** `AristotleResult` / `SorryGap` from the preserved data layer.
- New CLI `scripts/aristotle_submit.py` is the user-facing entry; it requires **explicit user authorization** before any submission (Stage 4 already mandates "user gets first & last call") and reads manifests on start to refuse duplicate-closure resubmission (fixing the write-only-manifest gap).
- `WAVE_EXECUTION_PIPELINE.md` Stage 4 and the Aristotle reference doc are updated to describe the new process and point to the archived one.

### D6 — Toolchain mismatch is a documented known-risk, not a mandatory pre-build gate

Aristotle runs **Lean/Mathlib 4.28.0**; we run **4.29.1** (confirmed unchanged 2026-06-25). This cross-version mismatch is real but empirically survivable — one submission since moving to 4.29.x succeeded. We therefore do **not** require a formal local 4.28.0 test-build before submitting. The **verify-then-graft gauntlet (D2) is the safety mechanism**: any returned proof that does not `lake build` + kernel-verify on our 4.29.1 is rejected, so a toolchain-induced failure costs a *run*, not substrate integrity. A local staged-closure test-build remains an **optional diagnostic** — worth doing only if a submission fails or the closure is unusually 4.29-API-heavy — never a gate that blocks an attempt.

---

## Overlap reconciliation with prior ADRs (keep the ADR set one system)

- **ADR-002 (native-decide policy):** the D2 gauntlet's axiom/kernel-purity audit **enforces** ADR-002 at the re-incorporation boundary — a returned proof introducing `native_decide` is rejected. This ADR adds teeth at a new boundary; it does not change the policy.
- **ADR-004 (substrate integrity gates):** D2 is the same "shift-left, verify-before-accept" philosophy applied to *external* (Aristotle-returned) proofs. The gauntlet runs the existing R-gates (`axiom_closure_allowlist`, etc.) rather than inventing parallel checks.
- **ADR-005 (derived proof atlas):** the new minimal-closure staging consumes the **same dependency graph** the atlas derives (`lean_deps.json` / import closure). The closure computation should reuse atlas machinery rather than a bespoke import walker where practical.
- No conflict with the disclosure framework (DISCLOSURE_TEXT 2026-06-10): D4 preserves it verbatim.

---

## Consequences

**Preserved (immutable / must-keep-working):**
- `ARISTOTLE_THEOREMS` is append-only — entries are never deleted or renamed (prior-paper provenance).
- `SORRY_GAPS` retains ≥45 historical entries (enforced by `test_lean_integrity.py:174-176`).
- Prior papers' Methods prose (I1, paper15, D1) and all cited run-IDs are **never edited** — they correctly describe the *archived* process that produced prior results. New/future work describes the new process.
- Disclosure Variant A/B + S1/S2 rule remain locked.

**Changed:**
- Default submission is partial (minimal closure); default re-incorporation is verify-then-graft. The full-project upload and blind `--integrate` are removed from the default flow and survive only as a guarded, banner-deprecated archived path.
- New `src/core/aristotle_submit.py` + `scripts/aristotle_submit.py`; Stage 4 + reference doc rewritten; the three import sites updated if/as the old module is relocated.

**Invariants touched / added:**
- A new registered run bumps the hardcoded `322` in **both** `constants.py:1372` and `validate.py:1172`, in the same commit.
- Candidate new invariant (optional, implementation-time): assert `len(set(ARISTOTLE_THEOREMS.values())) == counts.json::aristotle_runs` to keep run-dedup honest.

**Risks / open items:**
- **Toolchain (known risk, accepted):** Aristotle's 4.28.0 vs our 4.29.1, mitigated by the D2 gauntlet (reject-on-fail) with empirical precedent (one successful cross-version run). The L2 closure is heavy custom homological algebra — the code most exposed to 4.28↔4.29 Mathlib API drift — so a failed run is plausible; that costs a submission, not the substrate.
- **Closure completeness:** the import-closure staging must be exact, or the minimal project won't build on Aristotle's side; reuse ADR-005 graph machinery and test the staged build locally first.
- **Count drift — `ARISTOTLE_THEOREMS` is the source of truth.** `ATTRIBUTION.md:26` says "307 theorems … across 43+ submissions" while the registry holds 322 (319 machine + 3 manual); the 307 simply predates the last submission. The registry is canonical; `ATTRIBUTION.md` is reconciled to it (and, where cheap, made registry-derived to prevent re-drift) as part of the D4 attribution-wiring work — not left as a standalone nit.

---

## Alternatives considered

1. **Harden the full-submission path in place (keep full upload, only fix `--integrate`).** Rejected: still ships 17 MB, still maximally exposed to the toolchain mismatch, and leaves the misleading `submit_priority_batch`/`--force` foot-guns. Treats the symptom, not the cause.
2. **Delete the old process outright.** Rejected by user directive and by the codebase: prior papers' Methods (I1, paper15, D1) describe it verbatim and `test_lean_integrity.py` enforces historical-registry retention — deletion would break published-work provenance and an existing test.
3. **Hard-deprecate + guard only, no new safe tool.** Rejected: removes the foot-guns but delivers no usable path for the pending L2 work; the project still needs Stage-4 fallback.
4. **Chosen: archive + build the safe partial-submission + verify-then-graft path** that slides into the existing seam, preserving the provenance/attribution layer. Best balance of safety, provenance integrity, and minimal architectural disruption.
