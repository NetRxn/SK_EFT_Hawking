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

## ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

*Added 2026-08-07 to close DONE item 3, after reading `papers/D12/paper_draft.tex` (829 lines) in
full — the class-option note, the scope section, the disclosed-hypotheses paragraph and the
annotated bibliography included.*

| field | statement |
|---|---|
| **Audience** | Detector and readout engineers — photon counting, bolometry, lock-in filtering, TES electrothermal feedback — and, separately, the formalization community, for whom the draw is a stack nobody has formalized rather than a result nobody has proved. |
| **Venue** | PRX Quantum \| Quantum \| Phys. Rev. Applied, per the metadata. **Phys. Rev. Applied is the closest fit** and the draft's content says so: this is instrument metrology, not quantum information. Its sibling D9 is the PRX-Quantum-shaped one. |
| **The claim only this container can make** | **That three criteria in current engineering use are provably wrong, and that the surviving floors compose end to end.** The folklore photon-counting floor `e^{-N_diff}` fails in *two opposite directions* — false-strict as a miss bound, exponentially fail-open as an average-error screen; a magnitude-only electrothermal stability criterion inverts the physics on the unstable branch; and the sign-free characterization of matched-filter saturation is false. No sibling refutes working practice. D9 certifies channels *given* a detector error; **D12 is where that error comes from**, and it says so. |
| **Substrate** | 13 root-imported modules, 132 declarations: `Detection.*`, `Electrothermal.*`, `Control.*`. Kernel purity established *"from the project's extracted axiom closures for **every** declaration in all thirteen modules — not from spot checks."* |
| **Honest size vs charter** | 829 lines against a Tier-1 ~40pp charter — **under**, and unusually so for this portfolio. The compression is real: the draft carries five layers plus a composite capstone. |
| **Boundary failure?** | **No.** `D12 ∩ D9 = 3` and `D12 ∩ D4 = 3` are `PauliMatrices` infrastructure. The one substantive dependency — the POVM/Helstrom layer — is disclosed and correctly attributed: *"The POVM layer we do consume is our own project's network-certification substrate"*, i.e. D9's, and D12 says which of its claims that does and does not license. |

### ⚠️ D12 is the only pin-current bundle in the portfolio — and the pin check flags it anyway

D12 §1 scopes every library claim to *"Lean toolchain `v4.32.0`, Mathlib revision `81a5d257` and
PhysLib revision `c4843367`."* All three match `lean-toolchain` and `lakefile.toml` **exactly**.
Every other bundle measured in this retrofit quotes a stale pin.

**But `paper_toolchain_pin_drift` reports `papers/D12/paper_draft.tex:129 — c4843367` as drift.**
Read rather than assumed: `_tp_scan_lines` (`scripts/validation/checks/papers_prose.py`) collects
every hex literal on a line whose *context* matches `_TP_MATHLIB_CTX_RE`, and compares each against
the single `live_rev` that `_tp_live_pins()` reads from **Mathlib's** `rev`. D12's sentence names
Mathlib and PhysLib together, so the PhysLib hash is tested against Mathlib's — and a **current**
pin is reported stale. `papers/D11/paper_draft.tex:546` is the same false positive.

**Filed as TODO-D22; nothing built** (§6a). The residue is that the check has no PhysLib pin input;
the fix shape is to read PhysLib's `rev` alongside Mathlib's and accept a hex that matches *either*.
That needs approval.

⚠️ **And a scope correction to my own reporting:** at E1's and E2's retrofits I quoted the check's
*"29 pin-drift sites across 65 drafts"* as a clean corpus figure. **At least two of those 29 are
false positives.** The figure should be quoted as *"29 reported sites, of which ≥2 are the PhysLib
false positive"* until TODO-D22 lands.

---

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

---

## What D12 gets right — the corpus's strongest epistemic discipline (added 2026-08-07)

Reading the whole draft for the §D2 statement, D12 is the most disciplined manuscript measured, and
the evidence is that **it corrects itself in public, four times, naming what it previously got
wrong**:

- **The class-option note corrects its own first version**, at the top of the file: *"⚠️ CORRECTION
  2026-07-31 … That was wrong, and I asserted it without compiling both. Compiling both gives
  IDENTICAL extracted text (same md5)."*
- **The provenance line corrects itself**: it *"previously claimed ALL names were project-local,
  which was false for the four Mathlib names cited in the scope section."*
- **The γ paragraph corrects two predecessors**: *"both of this paragraph's predecessors were wrong:
  one compared the two figures across conventions … and its replacement asserted that no PSD
  reduction near 30 % was available, which is false at r = 1.19."*
- **The hypothesis list refuses to claim completeness, having twice been wrong about it**: *"Two
  earlier drafts of this paragraph asserted completeness at 'four' and then at 'six'; both were
  wrong, and the second was wrong in **both** directions … We deliberately do not claim this list is
  complete"* — deferring to the Lean statement as the authority.

Other instruments worth carrying to other bundles:

- **`\thm{}` vs `\mthm{}`** — two macros that render identically, existing *"so the provenance line
  above is checkable rather than asserted."* A project-local declaration and a Mathlib one are
  distinguishable in the source. **This is TODO-D18's problem solved independently, in the draft.**
- **Absence is scoped to evidence, not asserted**: *"We phrase this as the limit of our evidence
  rather than as an absence claim, because for the ecosystems named in the next paragraph we have no
  evidence either way."* Two prior-art checks are flagged **blocking**, and unassessed ecosystems are
  named (Isabelle AFP, Coq `infotheo`, HOL4, PVS, Mizar, Agda).
- **A citation discloses why it could not be inspected**: the `TestingLowerBounds` bibitem records
  that *"both its repository host and its blueprint host lie outside the network policy under which
  this work was carried out"*, and names the single source that was verified. **The egress policy is
  disclosed as a limit on the evidence** — nothing else in the corpus does this.
- **Two sources are marked read-in-abstract-only / DOI-record-only**, with the attribution
  explicitly *"provisional"*.
- **A refutation is scoped to its class**: the sign-free saturation refutation is stated *"within the
  admissible class, since refuting a universally quantified statement is not the same as refuting its
  class-restricted form."*
- **A limitation is shipped as a theorem**: `trace_blind_to_rotation_direction` *"records a real
  limitation: the trace does not distinguish rotation direction, so a trace-only calibration check
  cannot detect a sign error."*
- **The direction of an error is worked out rather than guessed**: the γ = 1 floors *overstate*, so
  they yield false **refutations** rather than false admissions — *"the mirror image of the fail-open
  failure of Section 3, not an instance of it."*

**This is the manuscript the other twenty should be read against.** TODO-D12 (D10's undisclosed
definitional encodings) and TODO-D19 (proved-but-unnamed) are both defects D12 does not have.

