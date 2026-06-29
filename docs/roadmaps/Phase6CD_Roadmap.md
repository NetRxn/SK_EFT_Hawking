# Phase 6CD — Non-Hermitian Topology / Exceptional Points

**Status: PLANNED (authorized 2026-06-29).** Non-Hermitian Bloch Hamiltonians, exceptional-point (EP) degeneracies via Jordan-block coalescence, and PT-symmetry / real-spectrum criteria. Clean physics whitespace. Distinct phase in the `6C*` materials series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP `loogle`):**
- **Reuse (exists):** PhysLib `Mathematics/SchurTriangulation.lean` — `Matrix.schur_triangulation` (`A = U·T·star U`), `schurTriangulationUnitary`, `schurTriangulation`, `IsUpperTriangular`, `UpperTriangular` (over `RCLike` + `IsAlgClosed`, i.e. ℂ); Mathlib `Module.End.eigenspace` + `LinearAlgebra.Eigenspace.Triangularizable` (Schur's own import); PhysLib `…/SpectralTheory/Symmetric.lean` `numericalRange` (Toeplitz–Hausdorff); project `CGLTransform`/`HigherOrderSK`/`SecondOrderSK` (dissipative SK-EFT algebra); project `QuantumNetwork/NumericalBounds.expNeg_enclosure`.
- **Absent → build (confirmed `loogle`):** `JordanNormalForm` returns **No results found** in Mathlib; `exceptionalPoint`/`ExceptionalPoint` 0 in PhysLib + project.
- **New content:** the non-Hermitian Bloch Hamiltonian + the **EP = defective-eigenvalue** criterion — algebraic mult > geometric mult, read off `Module.End.eigenspace` dimensions over the Schur form. **Full JNF is NOT required** — only the eigenspace-dimension comparison (Isabelle AFP's JNF is a reference cross-check only). Plus PT-symmetry + EP order.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target **D11** (authorized 2026-06-29 in `PAPER_STRATEGY`) — record it; the `papers/D11/` + `_VALID_BUNDLE_TARGETS` scaffolding is created at **first content-lift** (`BUNDLE_LIFT_PROCEDURE` step 2), not before. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)**. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** the EP is a **defective eigenvalue** — algebraic mult > geometric mult via `Module.End.eigenspace` dims over `Matrix.schur_triangulation`. **Full JNF is NOT required** (it's `loogle`-confirmed absent from Mathlib *and* unnecessary here) — build only the eigenspace-dimension comparison.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D11** (authorized 2026-06-29; §non-Hermitian), shared with 6CA/6CB/6CE. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — non-Hermitian Bloch + exceptional point
- **Goal:** a non-Hermitian 2-band Bloch Hamiltonian on Schur; the **exceptional point** = simultaneous eigenvalue + eigenvector coalescence (a defective block); the EP/defectiveness primitive (eigenspace-dimension comparison — **not** full JNF). **Verdict: reachable** — finite-dim linear algebra on Schur.
- **Why:** EPs are the defining feature of non-Hermitian band physics; the defectiveness primitive is reusable infrastructure.
- **Bricks:** PhysLib `Matrix.schur_triangulation`; Mathlib `Module.End.eigenspace`; project dissipative algebra.
- **Done (AC / `/goal` condition):**
  - [ ] `NonHermitianBloch.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] non-Hermitian 2-band Bloch Hamiltonian on Schur; `exceptional_point_defective` (alg. mult > geom. mult via `Module.End.eigenspace` dims — **not** full JNF) proven

## Wave 2 — PT-symmetry + EP order
- **Goal:** the PT-symmetric real-spectrum criterion; EP-order classification (EP2/EP3); the square-root spectral splitting near an EP. **Verdict: reachable.**
- **Why:** PT-symmetry breaking is the experimentally salient transition; EP order sets the sensing response.
- **Bricks:** W1; characteristic-polynomial discriminant.
- **Done (AC / `/goal` condition):**
  - [ ] `ExceptionalPoint.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `pt_symmetric_real_spectrum_iff` (biconditional) + EP-order (EP2/EP3) classification proven

## Wave 3 — skin effect + certified EP-proximity bound
- **Goal:** (optional) non-Hermitian winding / the skin effect; a certified EP-proximity bound (enclosure on the spectral-gap closing). **Verdict: reachable.**
- **Why:** the skin effect is the bulk topological signature; the proximity bound is the certificate-grade output.
- **Bricks:** W1/W2; `expNeg_enclosure`.
- **Done (AC / `/goal` condition):**
  - [ ] `NonHermitianWinding.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `ep_proximity_enclosure` (`norm_num`-backed) proven; (optional) skin-effect / winding

## Sequencing
W1 (EP/JNF primitive) → W2 (PT + order) → W3 (skin/proximity). Independent of 6CA/6CB/6CC/6CE; one of the two fast materials phases (with 6CB).

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; the finite-dim JNF/EP primitive flagged as Mathlib-PR-eligible; D11 §non-Hermitian row staged for first-lift; roadmap status updated.
