# D12 apex retrofit — and what it measured about D6/D9

**2026-08-06.** Fourth bundle retrofitted under ADR-010 §D5a / `PUBLICATION_INTAKE_SHAPE.md` §3b.
Ceiling 18 → 17.

## Why D12 was chosen

ADR-010 §What-remains item 2 lists the **D6+D9+D12 → D6★** merge as **untested**, on the stated
grounds that *"D11 and D12 reference zero Lean declarations, so a merge argument for them cannot be
built from substrate overlap."* That premise was **withdrawn 2026-08-06** (D12 = 132 declarations /
13 modules; the zero was a `\thm{}` extraction artifact). With D6 and D9 already declared, D12 makes
the three-way overlap computable for the first time.

## The retrofit

11 apexes, one per claim of the abstract, each verified `kind == theorem`, kernel-pure
(`{propext, Classical.choice, Quot.sound}`, **zero project axioms**), and cited in the draft.
Closure: **147 declarations / 14 modules, depth 6, 3 private truncations.**

Substrate namespaces: `Detection.*`, `Electrothermal.ETFModel.*`, `Control.*`. Exactly **one** of
D12's 164 draft references reaches `QuantumNetwork` (`IsBinaryPOVM`).

⚠️ **Method note.** `grep` for these theorem names in the draft returns **0** — the draft escapes
underscores (`avgError\_ge\_affinity\_sq`) inside `\thm{}`. This is the same class of extraction
artifact that produced ADR-010's withdrawn "D11/D12 reference zero declarations" and its
"D6 ∩ D9 = 0". **Do not verify a reference claim with a bare grep on this corpus.**

## The measurement — the merge hypothesis does not survive as stated

Apex-closure overlap:

| pair | shared | Jaccard |
|---|---:|---:|
| D6 ∩ D9 | **0** | 0.000 |
| D6 ∩ D12 | **0** | 0.000 |
| D9 ∩ D12 | 3 | 0.004 |

**D12 is not part of a three-way merge.** Its substrate is disjoint from D6's and touches D9's at
3 declarations (2 modules: `QuantumNetwork.NumericalBounds`, `QuantumNetwork.ReadoutRelaxationBound`)
— which is exactly the *interface* the draft describes in prose: *"these floors are the layer
beneath the channel- and device-level envelopes of quantum-network certification."* The manuscript
already states its own boundary correctly, and the closure confirms it.

## But D6 ∩ D9 = 0 is NOT a refutation of the D6+D9 merge — it relocates the finding

The audit's **78 shared theorems** reproduce **exactly** on a third independent route (85 shared
resolved references, 78 of them theorems). The 0 is a statement about *declared apexes*, not about
substrate. The two numbers measure different things, and the gap between them is the finding:

| | D6 | D9 | D12 |
|---|---:|---:|---:|
| resolved draft references | 172 | 169 | 160 |
| covered by its OWN apex closure | **33 (19 %)** | 65 (38 %) | 46 (29 %) |
| references in `QuantumNetwork.*` (D9's namespace) | **133 (77 %)** | — | 1 |
| …of those, inside **D9's** apex closure | **69** | — | — |
| …of those, inside **D6's** apex closure | **0** | — | — |

**D6's manuscript is 77 % built out of D9's namespace, while D6 claims a small FaultTolerance core**
(51 declarations, 4 modules, depth 3). That is ADR-010 **§D2**'s boundary-failure criterion in its
exact stated form — *"a target whose purpose cannot be stated without reference to another target's
substrate"* — and it is a sharper diagnosis than "the two duplicate each other":

- **Duplication** would mean two bundles independently claiming one substrate. Measured, they claim
  **disjoint** substrates.
- What is actually true is **borrowing**: D6 cites D9's results extensively and claims almost none
  of them.

The remedies differ. Concatenation (the audit's D6+D9) is one; so is re-pointing D6 to cite D9 as
companion work and stating D6's claim at the size of its real core; so is **giving D6 more substrate
of its own**, which is the only option consistent with §C5 (*the schedule moves, the claims do not*)
if D6's charter is to stand. **This does not decide between them** — that is §D4, and it needs the
manuscripts read for intent, not just the closure.

## The reusable instrument this produced

**Apex-closure coverage** — what fraction of a bundle's own citations its own claims reach — is a
continuous, checkable signal of the kind ADR-010 **§D3** demands (*"a control is acceptable only if
it is checkable"*). A bundle at 19 % is not making the claim its manuscript is built on. It is
derived, needs no new hand-maintained input, and is a candidate for the content floor §D3 asks for.

Not built. Recorded per `REMEDIATION_PLAN.md` §6a — identify the class, state the residue, request
approval, **then** build.

## Not done

- D11's retrofit (the other untested merge, D10+D11).
- The §D4 recommendation for D6 — needs the manuscripts read, per §C4.
