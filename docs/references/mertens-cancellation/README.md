# Bounded Mertens cancellation compatibility assessment

This candidate adapts selected source from the Apache-2.0 PNT+ project at
revision `a5154676af9aa3095150ee410cdda80555aa0642`. The original license is
preserved in `LICENSE.Apache-2.0`; exact upstream URLs and source hashes are
recorded in `source-manifest.json`. Compatibility on the existing local pins
passed standalone source checks. Independent source and kernel-axiom review pass;
authoritative aggregate, inventory and final gate acceptance remain pending.

The selected endpoint is upstream `M_isLittleO`, stating unconditional
sublinear growth of the inclusive real summatory Moebius function. Its route
uses a proved Wiener-Ikehara theorem and the weak prime number theorem.
Sublinear cancellation supplies no fixed power saving or square-root bound.

The extraction retains conservative supporting source and prefixes ending at
the required theorems. Unused unfinished alternative Fourier decay arguments
are excluded. Architect metadata is removed explicitly; project-local imports
are replaced by the retained source in dependency order. Exact extraction and
compatibility modifications must be reconciled before acceptance. Textual
dependency inspection alone does not establish a kernel-pure theorem closure.

The source candidate passes independent mathematical/extraction review and
matching-pins diagnostics. All 1,002 retained constants were enumerated and axiom-
audited within the same Lean session: 365 authored declarations, 12 explicit
constructors/projections and 625 other generated helpers. Every closure uses
only ordinary core axioms. The 365 source declarations comprise 235 lemmas,
48 theorems, 57 definitions, five abbreviations, 17 instances and three structures.
These are backported upstream declarations, not independently authored new
mathematical results. Two local coercion instances are explicitly disclosed and
audited. No mathematical proof or theorem statement was modified.

Authoritative aggregate build, canonical reconciliation and final gate acceptance
remain required. No toolchain upgrade, publication or broader number-theory claim
is included.

Source candidate `b3fd5848` is integrated unchanged as `5b4bf9f1`. The
aggregate now imports the selected module; its authoritative build is pending.
