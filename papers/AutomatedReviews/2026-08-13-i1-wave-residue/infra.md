# Residue from the I1 remediation wave — 2026-08-13

**Found by** the first end-to-end run of the ADR-012 loop: three `lean-worker`s in three
worktree slots, plan → dispatch → verify → close → ratchet. The wave itself closed clean (I1
38 → 34, escapes 5 → 0). These are the things it surfaced *while* closing — two found by the
workers inside their own targets, one by the lead in the orchestrator that dispatched them.

⚠️ **All three are defects the wave's own success would have hidden.** A green ratchet says the
population shrank; it says nothing about what the work touched on the way.

---

## Findings

### 1 — 🟠 The orchestrator's disjointness covers declared TARGETS, not the files a fix writes

**✅ FIXED IN-SESSION 2026-08-13**, recorded here because the mechanism is worth reading. The
fix is option 2 below: `SHARED_REGISTRIES` + `registry_note()`, so every dispatched unit in a
registry-writing lane carries the one-writer rule on its face, and lanes that do not write them
carry no rule at all — a rule that applies to everything reads as boilerplate.

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/orchestrate.py::target_files`
- **Observed:** wt2 and wt3 were dispatched as disjoint units — their findings named disjoint
  Lean files. Both then edited `src/core/constants.py` and `src/core/aristotle_interface.py`,
  because a substrate repair that changes a theorem's provenance *must* touch the registries.
  Neither file appears in any finding's `Location:`, so the planner could not see the conflict
  and dispatched them concurrently.
- **Evidence:** `git diff --name-only main...worktree-wt2` and `...worktree-wt3` share both
  paths. They auto-merged only because the two workers happened to edit different regions —
  git's line-level merge, not the guarantee the orchestrator advertises.
- **Expected:** the concurrency guard reasons about **write scope**, not target scope.
- **Fix:** ⚠️ **Write scope cannot be known before the work is done**, so a bigger static
  analysis is the wrong shape. Two candidates, and the second is preferred:
  1. Declare the registries as *shared resources* every substrate/lean unit implicitly holds —
     correct but serialises the whole lane, since nearly every fix touches them.
  2. **Workers do not edit registries at all; they report the needed registry change and the
     lead applies it at merge.** This matches the `close_finding.py` doctrine already in force —
     a registry has one writer — and keeps the fan-out wide.
- **Verify:** `uv run python -m pytest tests/test_orchestrate.py -q`

### 2 — 🟠 `hawking_universality` is registered `anchored` on a witness description that is false

- **Severity:** major
- **Lane:** substrate
- **Gate:** `LeanProofSubstance`
- **Location:** `lean/SKEFTHawking/HawkingUniversality.lean`, `src/core/constants.py`
  (`EXISTENTIAL_WITNESS_REGISTRY`)
- **Observed:** the entry reads *"teff, EQUATED to the effective-temperature expression"*. The
  proof witnesses `delta_disp := 1` and `delta_diss := if γ₁ = 0 ∧ γ₂ = 0 then 0 else 1`, and
  discharges the inner `∃ C > 0, |δ_disp| ≤ C·D²` with `C := 1/D²` — **literally the escape
  repaired as finding §2 of the statement-substance review, nested inside the `∃ teff`.** Only
  the `T_H` field is genuinely equated.
- **Evidence:** found by the wt1 worker while repairing §2/§3 in the same module, and annotated
  in-source with a ⚠️ note. It is a third instance of the pattern, currently counted as
  **anchored** — i.e. as a disclosure that holds.
- **Expected:** either the statement is repaired the way §2/§3 were (equate the two correction
  fields to their definitions), or the registry entry is downgraded to `escape` and the
  ceiling raised **only with an explicit operator decision**.
- ⚠️ **Do not simply re-label it.** `EXISTENTIAL_ESCAPE_CEILING` is now 0; moving this to
  `escape` breaches it, which is the correct pressure. Repair is the intended route.
- **Fix:** restate against the correction definitions, following `dispersive_correction_bound`
  as repaired — same module, same shape, already done once.
- **Verify:** `uv run python scripts/validate.py --check existential_witness_disclosure`

### 3 — 🔵 A cluster of `rfl`-true theorems in `OnsagerAlgebra.lean`

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `LeanProofSubstance`
- **Location:** `lean/SKEFTHawking/OnsagerAlgebra.lean`
- **Observed:** `davies_AA_coeff : (4:ℤ) = 4`, `dg_generator_count : (2:ℕ) = 2`,
  `davies_roan_classification : True`, and neighbours. Each is a theorem whose statement is
  decidable by `rfl` and carries no project content — the same class as the placeholder
  population, in a module that was just strengthened.
- **Evidence:** found by the wt3 worker while building the Onsager model. Not filed by it
  (out of its brief), not fixed.
- **Expected:** statements that constrain the algebra, or deletion. A named theorem asserting
  `4 = 4` reads as a verified result in any count that reaches a draft.
- **Fix:** per theorem — restate against `onsagerAlgebra` / `onsagerDavies` (both now exist and
  are proved), or delete. ⚠️ Check `VACUOUS_STATEMENT_BASELINE` first: if any is baselined,
  removing it must lower the baseline in the same commit, since that ratchet may only shrink.
- **Verify:** `uv run python scripts/validate.py --check vacuous_statement_audit`
