# D9 apex retrofit (backfill) — a claimed consumption that no declaration supports, and D6∩D9 = 0

**Date:** 2026-08-07 · Backfill: D9 declared its apexes before this retrofit began, so it had no
FINDINGS doc. Written now so **DONE item 2 holds for all 21 bundles**. This completes the set.

**Read IN FULL before anything was written,** per ADR-010 C4: `papers/D9/paper_draft.tex`
(1,318 lines, every line, including the appendix's verification-status statement),
`bundle_metadata.json`, and the full `QuantumNetwork` declaration index.

---

## 1. What is declared

**25 apexes → 623 declarations across 68 modules, depth 12, 6 private truncations.**

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Quantum-network and device-characterization practitioners — simulator authors, error-budget writers, and vendors quoting `T₁`/`T₂`/readout numbers. Secondarily the formal-methods-for-QI community, for the methodology. |
| **Venue** | PRX Quantum \| Quantum, per the metadata. Appropriate: certification substrate plus a methodological claim. |
| **The claim only this container can make** | **A strict two-layer posture, enforced corpus-wide, as a contribution in its own right** — the formula layer is kernel-checked, and *every* identification of a formula with a physical quantity is a named, cited hypothesis inside the theorem statement. The paper says this outranks any individual theorem, and its documented walls (Caves, CV channel capacity, DEJMPS asymptotics) are the posture applied to itself. No sibling makes a methodological claim about *how to scope* a formalization. |
| **Substrate** | 68 modules, 623 declarations, depth 12 — the `QuantumNetwork` family plus its Mathlib-facing supports. |
| **Honest size vs charter** | 1,318 lines against ~40pp. Mid-range, and dense: five layers with a per-layer contribution list. |
| **Boundary failure?** | **No inbound.** `D9 ∩ D10 = 50`, `D9 ∩ D8 = 14`, `D9 ∩ D12 = 3` — D9 *supplying* diamond-norm infrastructure, which its §Relationship paragraph says explicitly (*"the operator-norm-to-diamond conversion [D8] consumes lives in the present corpus"*). ⚠️ But two of the three relationships it claims are not in any declaration — §2 and §3. |

---

## 2. ⚠️ D9 says it consumes I3's LDP foundations. No declaration does — and I3 agrees.

D9 §4.2 states its rare-event tails are *"consuming the large-deviation foundations of the I3
bundle"*, and §1's companion paragraph repeats it: *"The stochastic-calculus bundle (I3) owns the
large-deviation foundations that the rare-event tails of Sec. 4.2 consume."*

**Measured three ways, all negative:**

| probe | result |
|---|---|
| `D9 ∩ I3` closure | **0** |
| `fdt_rare_event_tail`'s direct `name_deps_project` touching `LDP.*` or `Itô.*` | **none** |
| `fdt_gallavotti_cohen`'s, likewise | **none** |

Both theorems live in `QuantumNetwork.FDTNoiseFloor` and reach nothing in either I3 namespace.

✅ **And I3's own draft says the same thing from the other side**, unprompted: *"The I3 cross-bridge
is designed but not yet consumed at release time … no D3, D5, or E1 Lean module currently invokes
`LDPCompatibleSKEFT` or any of the Itô-substrate predicates."* I3's retrofit measured its closure as
intersecting **nothing** in the portfolio.

**So the two drafts disagree, and the substrate sides with I3.** D9's consumption claim is prose.
The honest repair is D9's own two-layer vocabulary: the LDP reading of those tails is an
*identification-layer* statement, not a formula-layer dependency — which is exactly the distinction
D9 invented and applies rigorously everywhere else. Filed as **TODO-D21**.

⚠️ **Note what makes this finding safe rather than a probe artifact:** it is corroborated by an
independent source — the *other* bundle's prose — and by two different measurements (closure
intersection, and direct dependency lists). Per the V26/V37 rule, an absence needs a probe proven
able to show presence: the same dependency probe returns **50** for `D9 ∩ D10` and **14** for
`D9 ∩ D8`.

---

## 3. ⚠️ ADR-010 §D4, D6+D9: the two bundles proposed for merger share ZERO declarations

D9's §Relationship paragraph draws the line: *"The fault-tolerant-computation bundle (D6) owns the
logical layer — codes, measurement, gauging; the device envelopes of Sec. 4 characterize the
physical layer beneath it, and the abstract code-distance suppression theorems included here
(Sec. 4.4) are **the interface between the two**."*

**`D9 ∩ D6 = 0`.** The stated interface — `logicalErrorBound_antitone_distance`,
`logicalErrorBound_tendsto_zero` — appears in D9's closure and in no shared declaration with D6.

**This is new evidence for a merge question the ledger already records**, and it points the same
way as what was there: the §D4 row had D6+D9 as *supported-but-RELOCATED* on the grounds that the
content F attributes to D6 is actually D8's, with `D4 ∩ D6 = D8 ∩ D6 = 0`. **Now `D9 ∩ D6 = 0`
too.** D6 shares no declaration with D4, D8, or D9.

**Recorded, not decided.** A zero intersection is not by itself an argument against merging — two
containers can be adjacent in subject and disjoint in substrate, which is precisely what a
physical-layer/logical-layer split *should* look like. It does mean **a D6+D9 merge would be
motivated by narrative adjacency alone, with no substrate overlap to consolidate.** Added to
`EVIDENCE.md` §2.

---

## 4. What D9 gets right — and the two-layer posture is the reason

- **The posture is stated as the headline and then honoured**: every floor and ceiling carries its
  identification as a named hypothesis, and §5.3 *Documented walls* lists five things the verified
  layer does **not** contain, each with the reason.
- **The Caves bound is the worked example of the posture**: `A ≥ ħω/2` *"requires the bosonic
  commutation relation `[a,a†] = 1` … absent from PhysLib and Mathlib at our pin. It is carried as
  the explicit hypothesis `hcaves` … **never as an axiom**."*
- **A non-monotonicity counterexample is shipped as an honesty witness**:
  `dejmps_single_step_can_decrease` — the draft calls it *"the honesty witness"* — proving that
  `λ₀₀ > ½` does *not* guarantee a single-step increase.
- **No decimal is asserted where the proof gives a root**: the BB84 crossover is produced by the
  intermediate-value theorem, and *"the conventional ≈ 11% threshold is recovered as the implicit
  root … no decimal is asserted in the formal layer."* The figure caption repeats it.
- **Exactness is claimed only where earned**: covariant channels get exact diamond distances;
  amplitude damping gets *"honest two-sided brackets in place of unsupported exact claims"*, with
  §5.3 recording that the exact optimum *"requires an eigenvector witness the corpus documents but
  does not claim."*
- **A cited conjecture is explicitly not claimed**: the Fortescue–Lo `D/(D+1) → 1` limit is proven,
  *"the optimality of 1 is the cited open conjecture … and is not claimed."*
- **The overall novelty claim is deflationary and specific**: *"Almost every theorem in this corpus
  formalizes known mathematics, and we state that plainly"*, followed by four circumscribed
  exceptions.
- **Adoption is preferred to re-derivation, and said so**: the PhysLib bridge means *"bridging
  beats re-deriving"*, with the derived Callen–Welton floor and thermal occupancy as the
  demonstrations.

---

## 5. Verified, and one count that is off by one

| D9 says | measured |
|---|---|
| *"over 900 kernel-checked theorems"* in `QuantumNetwork` | **969** author-written theorem declarations ✓ — true and conservatively stated |
| *"no `native_decide` compiled-evaluation trust escapes"* | **0** carriers in the whole `QuantumNetwork` family ✓ (instrument seeded at 19 in D4's closure) |
| *"axiom set `{propext, Classical.choice, Quot.sound}`, no project-local axioms"* | the family's `axiom_deps_core` union is exactly those three; **zero** declarations of kind `axiom` project-wide ✓ |
| *"103 Lean modules"* | **104** ⚠️ off by one, hand-maintained — the same class as TODO-D10/D15, and the fix is L3's: a bundle-scoped derived macro |

⚠️ **Not verified, stated per C4:** the appendix's claim that the corpus's PhysLib-touching
theorems are *"verified by axiom audit not to depend on the one sorried declaration present in that
library at our pin."* Checking it means auditing a dependency's internals; not done, and building a
probe for it would be new infrastructure under §6a. **Recorded as unverified, not as wrong.**

**Pin drift** (`v4.29.1`, `5e932f97`) is already reported by the registered
`paper_toolchain_pin_drift` check at **D9:1074**. Existing coverage; nothing filed.

---

## 6. Ledger

| artifact | change |
|---|---|
| `docs/audits/2026-08-07-d9-retrofit/FINDINGS.md` | **created** — DONE item 2 now holds for **all 21 bundles** |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | §2 gains `D9 ∩ D6 = 0` |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | **TODO-D21** (D9's I3-consumption claim); TODO-D10/D15 gain D9's module count |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V41 |

No metadata changed: D9's 25 apexes were already declared and all resolve.
