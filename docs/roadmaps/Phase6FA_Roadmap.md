# Phase 6FA — Mathlib Upstream Packaging: the confirmed-gap quartet + Pfaffian

**Status: PLANNED (namespace authorized 2026-07-29).** First phase of the `6F*` series
(*upstream contribution*). Independent of every other active phase; consumes nothing, blocks nothing.

**Series framing (`6F*` = upstream contribution).** A namespace for work whose deliverable leaves
this repo. It is a different *kind* of work from the `6A*`–`6E*` research phases: no bundle target,
no Stage-13 claims review, no new mathematics. The deliverable is a **Mathlib PR** — which means
external cadence (Zulip coordination, maintainer review, Mathlib style conformance) and a success
criterion this repo does not control. Kept out of the research namespaces so a stalled upstream
review never reads as a stalled research phase. Room to grow: `6FB` (Kronecker spectral theory →
`LinearAlgebra.Matrix.Kronecker`), `6FC` (PhysLib `QuantumInfo` — the negativity/PPT ladder and
diamond-norm cluster), `6FD+` as the disposition assigns them.

**Thesis.** The repo has carried Mathlib-PR-packaged modules (Apache-2.0 headers,
Mathlib-namespaced presentations, target-path mirrors) since Phase 6f. The mathematics has landed:
the Fable portfolio records the matrix-log/BCH quartet as complete, with *"remaining work is
packaging/upstream review, not a Fable theorem program"*. The
[2026-07-29 re-validation](../assessments/UpstreamDisposition_Revalidation_2026-07-29.md) §2
confirmed **every one of these is still a genuine Mathlib gap at v4.32.0 `81a5d257`**. Nothing
blocks the packaging except deciding to spend the bandwidth.

**Substrate (verified 2026-07-29 — all kernel-pure, zero sorry).**

| module | decls | target |
|---|---|---|
| `MatrixExpLocalHomeomorphMathlibPR` | 14 | `Matrix.exp_isLocalHomeomorph_zero` |
| `SU2CompactnessMathlibPR` | 4 | `specialUnitaryGroup` compactness + instance |
| `MatrixBCHCubicMathlibPR` | 4 | `Matrix.BCH` order-2 + `linftyOpNorm_reindex` |
| `FKLW/GenericSUdMatrixMercatorLog` | 19 | concrete-radius matrix log |
| `MathlibAux/Pfaffian` | 21 | Pfaffian + `Matrix.IsSkewSymmetric` |

> **⚠️ GUARDRAIL — verify the gap immediately before each PR, not from this table.** Every entry
> here is a *capability claim about upstream Mathlib*, and the class that a version bump can
> silently flip (re-validation §0). Mathlib moves weekly; this table was true at `81a5d257` on
> 2026-07-29. Re-confirm with `lean_local_search` + a direct grep of the pinned source **and** a
> `by exact?`/`infer_instance` probe before opening any PR — a grep alone gave a false negative
> twice during the re-validation.

> **⚠️ GUARDRAIL — upstream style is not our style.** Mathlib will not take
> `Authors: …, Claude (Anthropic)` co-author lines without a norms check (disposition §6 open
> decision 3), nor project-local naming. Expect real rewriting: namespace placement, `variable`
> blocks, docstring conventions, deprecation aliases. Budget the port, not just the proof.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.**
> 1. **Bootstrap reads:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` →
>    `docs/WAVE_EXECUTION_PIPELINE.md` → `docs/assessments/UpstreamDisposition_Revalidation_2026-07-29.md`
>    (the gap evidence) → `docs/assessments/UpstreamContributionDisposition.md` (routing + the
>    withdrawn Track R3 banner).
> 2. **This phase ships no new theorems.** If a port needs new mathematics, that is a scope
>    change — stop and re-scope, do not quietly grow the phase.
> 3. **User gets first and last call on every PR submission**, same posture as Aristotle.
>    Nothing leaves the repo without explicit sign-off.
> 4. Kernel-purity, zero sorry, no new axioms (#15), no `maxHeartbeats` (#10) still apply to
>    anything touched in-tree.

**Standing invariants:** kernel-pure; no new axioms; never push; never open a PR without sign-off.

---

## Wave 1 — Gap re-confirmation + port order

**Goal.** For each of the five, re-verify the upstream gap at the *current* Mathlib HEAD (not our
pin — a PR lands against HEAD), and fix the port order by ascending friction.

**Done (AC).**
- [ ] A dated gap-verification table: per module, the search performed, the result, and the
      Mathlib file the declaration would land in.
- [ ] Any entry that has since been filled upstream is **struck from the phase**, with the
      upstream declaration cited — that is a success, not a loss.
- [ ] Port order frozen. Prior read (disposition §3.3): matrix-exp homeomorphism is the
      smallest/cleanest, SU(d) compactness next (it also discharges the explicit hypothesis in
      `FKLW/ConstructiveEpsilonNet.lean`), BCH and Mercator log after.

## Wave 2 — Port the first module to Mathlib style

**Goal.** One module, fully ported: upstream namespace, `variable` blocks, docstrings, naming.
Builds against a Mathlib checkout, not against this repo.

**Done (AC).**
- [ ] Builds clean in a Mathlib worktree at upstream HEAD.
- [ ] No dependency on any `SKEFTHawking.*` declaration (a port that needs our substrate is not
      upstreamable as-is — record what it needs and re-scope).
- [ ] Author-line question resolved with the user before submission.

## Wave 3 — Zulip coordination + PR

**Goal.** Announce on the relevant Mathlib Zulip stream, get a maintainer read on placement, submit.

**Done (AC).** PR open, link recorded here, review comments tracked as a checklist.

---

## Open UNKNOWNs

- **UNKNOWN-1:** author-line norms (disposition §6 decision 3) — resolve before the first PR.
- **UNKNOWN-2:** whether `SU2CompactnessMathlibPR` should generalize `SU(2) → SU(d)` before
  submission. Mathlib will likely ask; our `ConstructiveEpsilonNet` consumer only needs SU(2).
  Decide at Wave 1, do not discover it in review.
- **UNKNOWN-3:** whether `MathlibAux/Pfaffian` belongs in this phase at all — it was vendored as
  in-tree infrastructure, and the disposition never routed it explicitly. Confirm intent first.
