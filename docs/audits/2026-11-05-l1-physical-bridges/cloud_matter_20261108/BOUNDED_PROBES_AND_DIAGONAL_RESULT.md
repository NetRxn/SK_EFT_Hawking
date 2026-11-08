# Bounded representative probes and a further diagonal subfamily

This increment continues issue121 and draft PR125 under the existing numbered execution plan and W0–W4 roadmap. It admits no complete harder-channel traversal or larger lattice simulation. Local physics remains paused. The scientific archive remains pinned to the earlier accepted closed four-site source; the exact consumed archive and adapter hashes are recorded in `representative_probe_run/summary.json`. The old failed high-arity and Dirac-loop receipts are preserved.

## Executed representative experiment

From this directory, the lead executed:

```sh
PYTHONDONTWRITEBYTECODE=1 timeout 720s python -B representative_probes.py --output-dir representative_probe_run
```

Exit0 means the bounded sample was recorded, not that every contraction completed. Whole wall time was196.324094s; the once-only cold controls took175.333822s. All six prospectively fixed cases were attempted exactly once, each from a fresh fork of the same prepared single-threaded parent. Source hashes remained unchanged and each child began at the same recorded cache baseline. The original controls, full producer/ordering controls, 1716 degree-six coordinate multisets and their reversals, and seven independent actual-source fixtures per case passed. The frozen sample and explicit omissions are documented in `representative_probe_design.md`.

| Case | Exact scope | Outcome | Wall s including assembly/controls | Child wait4 high-water KiB | Source candidate products | Completed join products |
|---|---|---|---:|---:|---:|---:|
| A | G02², anchors00, one degree-six link | Aggregate3,000,000 join-product guard; incomplete |2.525|119460|26688|418932|
| B | G02², anchors00, two degree-six links |120001 live rows against120000; incomplete|2.624|181220|26688|1232812|
| C | G02², anchors01, maximum degree four |Exact individual raw word0, imaginary0|1.315|80352|131328|222988|
| D | G02², anchors11, maximum degree four |Exact individual raw word6561/8, imaginary0|4.498|85216|623616|194768|
| E | G02G12, anchors02, maximum degree six |120001-row failure preserved; shutdown monitoring unavailable|3.640|117904|131328|808016|
| F | G02G12, anchors12, maximum degree six |120001 live rows against120000; incomplete|6.367|128280|623616|484208|

The fractions are bare anchor-resolved contributions to the raw g2^6 numerator, with the original repetition factorial included; they are neither normalized covariances nor complete source-anchor sums. C's exact zero applies only to that completed contribution. No amplitude was obtained from A/B/E/F. A's failed join was stopped before admitting product2581069 against its remaining2581068 budget. Failed joins' unfinished work is not included in completed counters.

Case E has two retained facts: the child wrote its concrete row-cap exception and exited10; the supervisor additionally recorded `memory-observation-unavailable` during shutdown. This is not evidence of OOM or a measured RSS overrun. Missing required RSS fails closed after an exit-race recheck. No failed case was retried.

The largest child wait4 high-water RSS was181220KiB; the largest sampled conservative parent-plus-child RSS was252.289MiB, below the declared sampled384/512MiB stops. Shared pages are double-counted in that sum. Polling and wait4 maxima are distinct; sampling does not prove an instantaneous ceiling. Every per-case30s, cumulative warm180s, whole700s/internal720s/external, row120000, aggregate join3000000 and separate source-candidate3000000 budget was retained. Detailed per-join/resource/phase/cache records and complete stdout are in `representative_probe_run/`.

## Further diagonal trace computation

The original both-unused-source Dirac-loop pilot failed its120000-row guard. Its source and failure are preserved in `both_unused_trace.py` and `both_unused_trace_control_r0_failure.txt`. It was not rerun unchanged. A changed representation integrates the unfixed product-Haar variables before tree fixing and uses exact local endpoint projections:

- SAME4 keeps all three Kronecker pairings with coefficient1/32.
- Independent TWO2 keeps only the pairing matching the actual equal-origin occurrence positions, also with coefficient1/32. Crossed pairings vanish in that separate tensor, not by assumption.
- The physical source Q is invariant, top(Q²)=108, and private curvature averaging gives the local factor18 including its own2! exactly once.
- The original full commutator fourth moments and central multiplicity factorials1/4/24 remain. No Wick replacement is made.

The design,35-quartet cubature/identity controls,100 TWO2 tensor checks, private-pair controls and actual occurrence matching for all22 words were independently accepted before execution. The independent single-word anchor is1161/5. The lead then ran:

```sh
PYTHONDONTWRITEBYTECODE=1 timeout 60s python -B both_unused_trace_reduced.py --all > both_unused_trace_reduced_result.txt 2>&1
```

Exit0;22 words in8 orbits completed in7.789351s, with2104188 charged products (1956732 exterior plus147456 conservative scalar upper charge),198 peak rows and58580KiB process high-water RSS. The selected exact raw numerator is

`N_22/g2^6 = 37152/5`.

With the matching closed `Z=1252309350145403/2123366400 * g2^8`,

`g2² A_22 = 15777461698560/1252309350145403`.

All selected action source charges vanish, so their fixed-bare raw first/second j jets vanish. Full denominator differentiation is retained. With h=2sqrt(2)j, the normalized second h jet is

`g2² A_22,hh = -1882252020491427168387072000/142570791678327415714294730219`.

Independent mathematical replay exited0 in7.759927s, reproduced every orbit/fraction/jet and the same2104188-product/198-row counters, and measured58472KiB RSS. Its complete receipt is `both_unused_trace_reduced_replay.txt`. This completes this22-word family only.

## Partial scalar insertion and remaining work

The previous128-word diagonal subset and this disjoint22-word family give150of310 words, raw133839/10. The remaining160 words are explicitly unknown. Their sum is not inferred from sign, symmetry or cancellation. The combined normalized contribution and second h jet are

`g2² A_150 = 28418923560960/1252309350145403`,

`g2² A_150,hh = -1951195376342291865521356800/142570791678327415714294730219`.

Only the old128-word subset contributes the raw second j numerator47628; the new22 contributes zero. The lead evaluated independently reviewed `diagonal_150_kernel.py` with `timeout10s`, exit0 in0.305s. `diagonal_150_kernel.json` preserves exact four-momentum values for the known D/H/trace part. Define d_remaining = g2² times the normalized160-word diagonal contribution. The coefficient multiplying d_remaining remains(-61/360,-257/360,-257/360,-9/8). The same coefficients multiply its unknown second source jet. Other active/mixed contributions remain explicit unknowns. No full propagation, cone, positivity or B3 result follows.

The measured degree-four cases are feasible individual contributions; they do not admit all omitted profiles. The tested failing words need a reviewed reduction or elimination-order change before retry; their failures do not prove that every word in their profiles fails. The next bounded action is a source-resolved reduction/design for the precise failing joins, checked against the retained controls and with new predeclared resource estimates. The160 diagonal words likewise need a prospective partition and bounded reduction; the22-word identity must not be extended without proving its hypotheses. Active(a,b,c,t) covariance blocks and remaining local mixed combinations are still required for the full kernel. Physical body/scale/source/state matching and real-time/locality obligations remain unchanged. Publication retains its original N4/16-site c0 lanes; no such campaign was restarted.

## Independent gates and verification

Mathematical/code/resource reviewer: `/root/math_review`; physics/source reviewer: `/root/physics_review`. Both accepted the six-case design before execution and accepted post-result receipt scope; both accepted the22-word representation before execution. Mathematics additionally performed the independent22-word replay. Both accepted the exact partial-kernel algebra before its cheap execution.

Frozen hashes:

- Representative script249e3db814b4f9c69627d31663dcec1efd724208f6370609764e33bba49642c9; design df8096e4f7efa2683b2d6ab2eed8dd347b11915da4b70023fd7dd79242226399.
- Reduced22 producer bc5659d561dc9dd9a181f77499276a3f6c4699ae0b66ab05fb5a2e8598b01f47; design2fa9c452a2fe6c09b8b67742a26b738914b09840523c590e4531006d32e86af9.
- Independent22 receipt82ce4fd84133abeef758f9b230b6777af2b61e43be8c013e96b9028b3d726d31.
- Partial-kernel script f4711a592ed664473a2e5c6b5353ca18a16aef9c9cc50a841690c0f3b84a65aa.

These are scoped scientific audit gates, not full-tree/native/wave or publication acceptance. The branch remains draft and unmerged. Existing roadmap/repair map/issue121 retain routing and ownership. This report extends the numbered execution record rather than creating a new ledger.

Filing checks: `git diff --check`, AST parsing of the seven new audit scripts, and parsing every new JSON receipt passed. `PYTHONDONTWRITEBYTECODE=1 python -B scripts/verify_scope.py` exited0 and explicitly reported no applicable mechanical gate / NOT CERTIFIED for everything; no Lean, Python suite or merge-floor claim is made.
