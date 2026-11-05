# Independent numerical repair review

ROOT authored the repair. Independent reviewer `/root/l1_transport`
reproduced the original defect, checked the mathematical interval
and scalar input behavior, and accepted the final four-path code
and test composition. Its second review confirmed the documented
invalid-cap and overflow behavior and the corrected test semantics.

For small caps, compensated evaluation avoids rounding the
intermediate `1±τ` before squaring. Above cap one-half and below
one, direct squaring uses the stable subtraction near one. At
and above cap one the nonnegative lower endpoint is zero.
The exact width is `4τ` through cap one. D3 computes that
quantity directly for its ratio. Rounded endpoint subtraction
retains an unavoidable quantization error.

The deviation calculation uses the equivalent rationalized
expression and promotes scalar precision to at least binary64
while retaining wider NumPy arithmetic before the float return.
The independent reviewer found zero classification mismatches
on 210 distinct near-boundary binary64 values. ROOT's separately
generated exact-rational boundary control also contains 210
distinct inputs and zero mismatches.

The canonical uv verification command passed 69 cases using the
existing prepared environment in offline, no-sync mode. D3's
existing writer regenerated all sixteen scalar snippets with no
tracked TeX byte change. The existing figure producer regenerated
the accepted L1 PNG byte for byte. The manuscript changes only
the test count from 49 to 69 and compiles to four pages. Pages
one through three are pixel-identical to the prior accepted
render. ROOT inspected page four; the six inherited overfull
boxes remain.

The sentence-review artifact retains its physical BUILD
obligations and H1 attribution failure. Native/full-tree gates,
complete figure propagation to other manuscripts, physical
calibration and final human approval remain open.

The existing counts writer records 6,911 collected project cases,
up by the twenty added cases. Its Lean counts are unchanged.
The focused count-freshness suite passes fourteen checks.
The canonical planner resolves this finding to the four actual
Python/test/producer paths and marks its declared verification
command as available. The sentence writer ingests 114 current
records with zero automatic finding closures and five prior
reconciliation candidates.
