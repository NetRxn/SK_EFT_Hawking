# Attributed Mertens cancellation backport

`MertensCancellationBackport.lean` adapts selected Apache-2.0 PNT+ source at
revision `a5154676af9aa3095150ee410cdda80555aa0642`. The original license is
preserved in `LICENSE.Apache-2.0`; `source-manifest.json` records exact upstream
URLs, file hashes, retained prefixes, exclusions and compatibility changes.
Independent source, extraction, provenance and kernel-axiom reviews pass.
The authoritative aggregate build passed at `fc283951` on unchanged local pins;
canonical inventory and final cycle gate acceptance remain pending.

The endpoint `M_isLittleO` proves unconditional sublinear growth of the inclusive
real summatory Moebius function. Its route uses a proved Wiener-Ikehara theorem
and the weak prime number theorem. It supplies no fixed power saving,
square-root bound or RH conclusion.

The extraction keeps nine conservative supporting modules or prefixes through
the required theorems. Three unused alternative declarations from `Wiener.lean`
are excluded: global `prelim_decay_2`, `prelim_decay_3`, and `decay_alt`.
The first two contain unfinished proofs; the third depends on those alternatives.
These names are global declarations, not members of a `Wiener` namespace.
Architect metadata is made inert and project imports are replaced by retained
source in dependency order. Exact retained mathematical code was independently
reconciled; no theorem statement or mathematical proof was modified.

All 1,002 retained constants were enumerated and axiom-audited in the same Lean
session: 365 upstream-authored declarations, 12 explicit constructors/projections
and 625 other generated helpers. Every closure uses only ordinary core axioms.
The authored items comprise 235 lemmas, 48 theorems, 57 definitions, five
abbreviations, 17 instances and three structures. Two local coercion instances
are explicitly disclosed and audited. These are backported upstream results,
not newly authored mathematical results of this project.

Candidate `b3fd5848` was integrated unchanged as `5b4bf9f1`, with source SHA256
`82fa59c8cddbd59e438548a53f80530ec7b2487e3b7ed99bac9ffddaab4e9fff`.
No toolchain upgrade, publication or broader number-theory claim is included.
