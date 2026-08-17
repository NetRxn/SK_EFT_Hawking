# Bundle D9 — Change Log

_Initial bookkeeping created 2026-06-10T20:39:59Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-06-10 — Synthesize from `D9_initial_draft` (§1-§6)

- Source title: Kernel-Verified Quantum-Network and Device-Characterization Certification Sub...
- Lift action: Synthesize
- Insertion point: §1-§6
- Stage-13 redo required: yes
- Notes: D9 initial lift (sourceless synthesis): QN + device-characterization certification substrate — authorized 2026-06-10

## 2026-06-10 — Initial draft authored (sourceless synthesis, §3b)

- Full draft authored fresh: §1 introduction + two-layer posture, §2
  diamond-norm program, §3 entropy/majorization corpus, §4 network
  envelopes, §5 device-characterization envelope family, §6
  rational-enclosure technique + library contributions + documented
  walls, §7 scope, appendix verification status. ~870 lines, 10pp
  compiled.
- Every cited Lean name (170 distinct) verified on disk against
  `lean/SKEFTHawking/QuantumNetwork/` (one is the hypothesis binder
  `hcaves` of `fdt_noise_floor_amplifier`, verified by direct read).
- Disclosure: standard Variant B block installed (register-derived:
  S1 — no `ARISTOTLE_THEOREMS` entry resolves to a QuantumNetwork
  module; S2 — whole-word sweep of the draft against all 322 registry
  keys is empty).
- Bibliography: 41 in-draft `\bibitem` entries (thebibliography); all
  bibkeys are NEW to the bundle and flagged for CITATION_REGISTRY
  follow-up (not yet registered).
- LaTeX compile gate: `pdflatex` ×2, zero errors, clean 10-page PDF.
- `bundle_metadata.json` finalized per D8 field shape:
  stage{9,10,13}=pending, stage13_redo_required=true (never
  reviewed), freshness_stale=false, headline_theorems +
  contributing_phases + §3b sourceless note recorded.
- TOOLING ADAPTATION (documented per BUNDLE_LIFT_PROCEDURE §3b): the
  `bundle_append.py` / `bundle_source_manifest.py` /
  `bundle_migration.py` bundle registries predate D9
  (`_VALID_BUNDLE_TARGETS`, `_TIER_OF`, `_BUNDLE_TITLES`,
  `_BUNDLE_TARGET_JOURNAL`, `_BUNDLE_SUBPHASE`, and the
  `_DEST_BUNDLE_RE` regex `D[1-8]`). The initial lift was executed
  by running the real `bundle_append.append()` in-process with those
  registries patched at runtime (no script files were modified).
  FOLLOW-UP REQUIRED: register D9 in `scripts/sentence_state.py`,
  `scripts/bundle_source_manifest.py`, `scripts/bundle_migration.py`
  (regex), `scripts/datastar_bundles.py`, and
  `scripts/aristotle_usage_by_bundle.py` so the standard tooling and
  CHECK 22 freshness tracking see the bundle.

---

## 2026-08-17 — Stage-10 full redraft (branch `redraft/D9`)

Manuscript rebuilt from a five-layer inventory onto the certification chain itself as its
spine. Findings filed at `papers/AutomatedReviews/2026-08-17-d9-stage10-redraft/D9.md`
(17 live: 2 critical, 12 major, 2 minor, 1 advisory; F12 withdrawn by re-measurement;
F17 filed as roster evidence rather than as a defect).

**Claims corrected in this pass** (the manuscript states the corrected version and does not
narrate the correction; this entry is the record):

- The randomized-benchmarking "two-sided certificate" is withdrawn (F1). The corpus proves a
  LOWER bound on the diamond distance from `avgGateFidelity` and nothing in the other
  direction; `avgGateFidelity_diamondDist_two_sided` two-sides the entanglement
  distinguishability, not the diamond distance. The manuscript now states the lower bound and
  carries the impossibility as Negative result 1. `bundle_metadata.json`'s apex `claims`
  string for that theorem was false in the same way and is corrected.
- The §5.2 paragraph asserting that `fdt_rare_event_tail_is_ldp_certified` states both halves
  for one object is retired (F2); the certification half has been a separate theorem,
  `linearResponseRateFunctionCentered_is_ldp_certified`, since 2026-08-09.
- The erasure/PLOB "mutual consistency" cross-link is cut, not restated (F3): the two are
  capacities of different channels.
- The `logNegB_ncopy_localKraus_le` scope is corrected from "the per-n form of E_D <= E_N" to
  the one-sided-local specialization it is (F4); LOCC is now named as an open library gap.
- `diamondDist_genAmpDamp_bracket` is reported as a lower bound; its proven upper endpoint is
  the universal range bound (F5). Metadata `claims` string corrected likewise.
- The Kronecker operator-norm bound is ceded by citation to the compilation manuscript, which
  holds it in its apex set (F6).
- The `fig:wghz` caption no longer calls 1 "the GHZ_3 rate" (F7); Fortescue--Lo p.2 gives 0.64
  for the random-pair GHZ rate, and 1 is a specified-pair figure of merit.
- The opening motivation no longer leans on a simulator disagreement (F8): Chung et al. report
  AGREEMENT on fidelity, which is D9's own domain.
- Hardcoded 103 modules / "over 900" theorems removed (F9); counts now come from
  `bundle_counts.tex`, with the counted population named.
- `fdt_noise_floor_amplifier` is reported as a disclosure, not a result (F10).
- Two unheld primary sources (Audenaert 2007, Nielsen 2002) carry `% TODO:` markers (F11) and
  correctly hold the bundle off green.
- Entropy-unit notation disambiguated (F13); `teleport_useful_over_chain_unconditional` now
  cited in place of its conditional sibling (F14).
- NEW in this pass, not previously filed anywhere: the rate side of the chain does not
  terminate in the kernel (F15). The enclosure technique covers the exponential only, so the
  claim "every envelope is evaluable" was false for every logarithmic quantity. The manuscript
  now works the fiber chain to the point where it stops and names the missing bracket.
- Reader-facing internal taxonomy removed (F16): companions are cited as papers by title.

**Structural:** new sections for the chain diagram, the benchmark impossibility, a worked
certification against published transmon parameters, the results the formalization owns, the
failure taxonomy, and related formalizations. Cut: the five-layer framing, the QEC interface
subsection, the library-contribution appendix. Compiles clean at 14 pages (advisory floor 24).
