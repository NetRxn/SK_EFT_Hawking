# Rokhlin `topo` Discharge — POINTER (see Phase 5q.C)

> # ⛔ NO-GO (2026-06-13): the Arf-bridge approach this pointer describes is MATHEMATICALLY FALSE
> Both this plan and Phase 5q.C aimed to relocate `topo : 2∣σ/8` → `topo' : Arf(q̄)=0` and prove the bridge
> `σ/8 ≡ Arf(q̄) (mod 2)`. **That bridge is FALSE.** `Arf(q̄)` (the lattice Arf of `redQuad` on `L/2L`) is
> identically 0 on every even unimodular lattice (E₈: `Arf = 0`, `σ/8 = 1`), so the relocation is vacuous and
> does NOT capture `2∣σ/8`. The residual stays the *geometric* `topo : 2∣σ/8` (Guillou–Marin Arf on a
> characteristic surface, NOT the lattice Arf). Refuted in `lean/SKEFTHawking/RokhlinArfNoGo.lean`. **Do NOT
> pursue the relocation.** See the 5q.C top banner + ADR-003 + the no-go memory.

> **Superseded as a standalone plan (2026-06-13).** The authoritative roadmap for the Rokhlin `topo`
> discharge is **[`Phase5qC_ArfBridge_Roadmap.md`](Phase5qC_ArfBridge_Roadmap.md)** ("Arf-bridge hardening",
> created 2026-06-08, governed by [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md)).
> It already contains the full, in-repo-grounded plan (Waves C.1–C.4) + a ready-to-run `/goal`, and its
> 2026-06-13 STATUS banner records the LIVE-board #1 ranking, the entry-state re-verification, and the fresh
> leanprover-community ecosystem re-check.

This doc was an independent re-derivation written during the 2026-06-13 substrate-weakness reconciliation
before 5q.C was re-located; the two converged on the same approach (relocate `topo : 2∣σ/8` → `topo' :
Arf(q̄)=0` + prove the bridge `σ/8 ≡ Arf(q̄) (mod 2)` via `Arf.gaussSum_genus_g` + the classification) —
**which has since been REFUTED (2026-06-13): the bridge is FALSE, the relocation vacuous (see top banner).**
5q.C is more complete (it cites the verified in-repo bricks — `EvenLattice.redQuad` already exists), and it
now carries the matching NO-GO banner. **Go to 5q.C — but only to read its NO-GO; do NOT execute the bridge.**

~~Honest framing (both docs agree): this RELOCATES the irreducible topological hypothesis to its sharpest form
(`Arf(q̄)=0`, the Freedman–Kirby vanishing) and PROVES the algebraic bridge — it does **not** make `16∣σ`
unconditional (E₈ is the algebraic counterexample).~~ **⛔ FALSE (2026-06-13):** the relocation to `Arf(q̄)=0`
does NOT preserve `2∣σ/8` — the lattice `Arf(q̄)` is identically 0, so `Arf(q̄)=0` is vacuous, not "the
Freedman–Kirby vanishing." The Freedman–Kirby vanishing lives on a *geometric characteristic surface*, a
different invariant. The residual stays the geometric `topo : 2∣σ/8`. The "16∣σ unconditional" phrasing in the
5q.B roadmap header + the older `next-session-phase5qb-resume` memory remains an overstatement (only `8∣σ` is
algebraic + unconditional); corrected in both 5q.C's banner and the memory's CORRECTION banner.
