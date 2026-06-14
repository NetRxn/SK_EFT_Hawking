# Rokhlin `topo` Discharge — POINTER (see Phase 5q.C)

> **Superseded as a standalone plan (2026-06-13).** The authoritative roadmap for the Rokhlin `topo`
> discharge is **[`Phase5qC_ArfBridge_Roadmap.md`](Phase5qC_ArfBridge_Roadmap.md)** ("Arf-bridge hardening",
> created 2026-06-08, governed by [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md)).
> It already contains the full, in-repo-grounded plan (Waves C.1–C.4) + a ready-to-run `/goal`, and its
> 2026-06-13 STATUS banner records the LIVE-board #1 ranking, the entry-state re-verification, and the fresh
> leanprover-community ecosystem re-check.

This doc was an independent re-derivation written during the 2026-06-13 substrate-weakness reconciliation
before 5q.C was re-located; the two converged on the same approach (relocate `topo : 2∣σ/8` → `topo' :
Arf(q̄)=0` + prove the bridge `σ/8 ≡ Arf(q̄) (mod 2)` via `Arf.gaussSum_genus_g` + the classification). 5q.C is
more complete (it cites the verified in-repo bricks — `EvenLattice.redQuad` already exists, so no symplectic
reduction need be built). **Go to 5q.C.**

Honest framing (both docs agree): this RELOCATES the irreducible topological hypothesis to its sharpest form
(`Arf(q̄)=0`, the Freedman–Kirby vanishing) and PROVES the algebraic bridge — it does **not** make `16∣σ`
unconditional (E₈ is the algebraic counterexample). The "16∣σ unconditional" phrasing in the 5q.B roadmap
header + the older `next-session-phase5qb-resume` memory is an overstatement, corrected in both 5q.C's banner
and the memory's CORRECTION banner.
