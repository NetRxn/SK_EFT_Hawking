# Prospective bounded representative covariance probes

This design authorizes no execution by itself. The new script requires independent
mathematical and source review before its scientific entry point runs. It preserves
the accepted archive, failed high-arity adapter, accepted loop adapter, and all prior
receipts. No complete harder-channel or larger-lattice campaign is admitted.

## Frozen sample and scientific conventions

The six cases below were selected before their amplitudes. Within each named
stratum choose the minimum `(sum of unfixed link degree squared, S2 index tuple)`.
The indices refer to the actual archive-bound `C.S.TERMS`, never a separately
imported geometry module. Source origin is site0; each metric contracts its own
internal index. Each listed source anchor pair `(z,w)` means four frame anchors
`((z,0),(w,0))`. Distinct occurrences retain distinct quaternion legs and common
physical links meet the unchanged joint two-chiral-sphere Haar chains.

| Case | Source, anchors | Stratum | Sorted action indices | Unfixed histogram | Repetition divisor |
|---|---|---|---|---|---:|
| A | G02²,00 | exactly one degree6 link | 16,16,28,28,45,45 | 2:6,4:4,6:1 | 8 |
| B | G02²,00 | exactly two degree6 links | 17,17,28,28,45,45 | 2:6,4:3,6:2 | 8 |
| C | G02²,01 | maximum degree4 | 18,19,26,26,39,39 | 2:8,4:4 | 4 |
| D | G02²,11 | maximum degree4 | 19,19,26,26,39,39 | 2:8,4:4 | 8 |
| E | G02G12,02 | maximum degree6 | 18,21,33,33,39,48 | 2:10,4:2,6:1 | 2 |
| F | G02G12,12 | maximum degree6 | 19,21,33,33,39,48 | 2:10,4:2,6:1 | 2 |

The full word labels and physical incidence are derived and preserved in the
case manifest and verified before contraction. Sources have Grassmann degrees
`(6,2,0,0)` or `(6,1,1,0)`; action degrees are `(2,6,8,8)` or `(2,7,7,8)`.
The original tree `(0,0),(0,1),(1,1)` and full I4 substitutions are unchanged.
Each word has sixteen physical frame quarters and six loop curvature vertices,
with zero remaining curvature quarters. Divide by `4^16`, one Haar common
denominator per unfixed used physical link, and the repetition divisor above.
Do not add source factorials, normalize by Z8, subtract means, or force an
individual imaginary numerator to vanish. Retain exact real and imaginary
fractions; these are individual anchor-resolved raw word coefficients.

Free source occurrences/coarse source mask-row bounds are A/B:2/50176,
C:3/401408, D:4/3211264, E:3/917504, F:4/7340032. Bounds above the row cap
are not actual row counts and do not prove infeasibility.

## Controls and child isolation

One single-threaded parent runs the original physical controls and loop controls
once under the original 600-second cold limit. Extract the nested `sphere` and
`sequence` functions exactly by AST from the archive-bound `controls.moments`;
run all1716 degree-six coordinate multisets and their reversals against the
existing actual Haar-chain producer, including all1596 zero multisets. Record
source and transported-AST fingerprints. This adds coverage without rewriting
the reference formula or Haar assembly.

Fork each case sequentially from this same prepared parent. Children build fresh
factors; no child caches or scientific globals return to the parent. Cache
snapshots before/after each case and parent baseline permit checking this
isolation. The parent must remain single-threaded before every fork.

Before its contraction each child evaluates the generated first/source factor
at four archived full Spin(4) matrix fixtures and three coordinate-polarization
fixtures selected from its first three nonzero table keys. Compare the complete
Gaussian mask polynomial against explicit independent bilinear coframe formulas
for the actual component and anchor geometry. Polarizations use the union of
coordinates selected on each physical link, respecting repeated occurrences;
they are algebra fixtures, not normalized Spin(4) samples. Tree links use full
I4. The direct control never calls the frame/source producer to obtain its
expected polynomial. Keep all quaternion legs and actual endpoint masks.

## Bounds and failure semantics

One cold preparation allowance is at most600 seconds. The aggregate warm budget
is `min(180 seconds,700 seconds minus cold elapsed time)`; every case has at
most30 seconds including factor assembly, new source controls, and contraction.
The internal whole-run ceiling is700 seconds; the external supervisor must keep
the existing720-second ceiling. No per-case timer may reset the aggregate clock.

The original120000 live-row cap and3000000 per-join compatible-product cap
remain. Each child wraps the unchanged join with a stricter aggregate3000000
compatible-product budget, passing at most the remaining budget to the original
guard. A failed join is preserved and never read as zero; its partial product
count is not invented. Source-factory input candidate products have a separate
aggregate3000000 budget checked before the original bounded wedge.

Monitor only the owned fork child via `/proc/<pid>/status` every50ms. Stop and
reap that child when observed RSS exceeds384MiB, or conservative parentRSS plus
childRSS exceeds512MiB. Record samples, observed overshoot, VmHWM and exact
wait4 CPU/ru_maxrss evidence. Parent-plus-child RSS double-counts shared pages;
it is a conservative stopping rule, not unique physical memory accounting.
Missing required child or parent VmRSS triggers a second nonblocking wait4 to
resolve an exit race. If the child is still live, stop/reap only that child with
`memory-observation-unavailable`; unknown observations never become zero RSS.
Report polling overshoot and wait4 high-water overshoot separately. If no valid
RSS sample was observed, its polling maximum and overshoot remain null.
Polling has sampling/allocation overshoot and is not an exact instantaneous
RSS enforcement guarantee. Child RLIMIT_AS768MiB is a separate virtual-address
safety limit, not a substitute for RSS monitoring; Linux RLIMIT_RSS is not used.

After cap, time, or resource failure, proceed only to another already declared
independent case. Never retry the same case. A scientific AssertionError halts
the entire sample. Only the owned child may be killed. Reap before proceeding.
Preserve per-join rows/products/timings, source-factory output, phase durations,
complex raw values where complete, source identities, cache snapshots, stdout,
failure status and resource causes. Write case JSON atomically and rename each
stdout partial file only after reaping. Summary lists attempted cases and
explicitly records incomplete and unattempted cases; sample termination is not
physics closure.

## Coverage boundary

This compares degree4 and degree6 action interfaces, one versus two degree6
links, and two/three/four free source occurrences. It omits all G02² anchor10,
degree6 cases at anchors01/11, G02G12 anchor10, most degree-histogram profiles,
and nearly every word within selected profiles. Six outcomes cannot establish
runtime or memory scaling for all780 G02² or48 G02G12 support entries. They
cannot admit a complete campaign without further evidence and review.

Prospective invocation after independent review:

```sh
python -B representative_probes.py --output-dir <fresh-output-directory>
```

Only syntax/static support checks are permitted before that review gate.
