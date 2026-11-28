# Fixed-dose multibath reachability and channel calibration

The same-dose affine reset model extends to finitely many labelled
baths. The reachable terminal weights are exactly the convex hull of
contiguous block orders. Every weight vector in that hull has one
deterministic finite realization. For three baths the construction
uses at most 35 slices. The equal-dose and held-out unequal-dose
replays use 15 and 27 slices, respectively.

The exact same-total-dose diamond distance is one half the trace
norm of the accumulated-target difference. The Lean proof covers
normalized Kraus realizations of arbitrary finite equal-dose
schedules. On every stabilized density input the trace distance
takes this same value. The analytic argument also gives the induced
trace-norm bound on arbitrary complex joint matrices with a spectator
of any finite size.

A three-level control has identical level-A data in two different
bath orders, with diamond distance $1/32$. A second occupation
detector resolves the control. For the two-level bounded-noise
example the compatible interval midpoint halves the per-datum
worst-case error from $1/16$ to $1/32$. The example uses the
previous bath targets and a specified new calibration input and datum.

The weight polytope, detector count, and bounded-noise minimax result
are established by the analytical derivation. The numerical replay
tests the finite construction and channel comparisons with product,
entangled and arbitrary complex inputs. It does not model calibration
drift, dose uncertainty or laboratory implementation.

From the repository root, use the project Python environment.

```bash
dir=docs/roadmaps/phase6bc_multibath
tmp=$(mktemp -d)
python -B "$dir/CheckBounds.py" > "$tmp/Exact.json"
cmp "$tmp/Exact.json" "$dir/Exact.json"
python -B -O "$dir/replay.py" --repo . > "$tmp/Replay.json"
```

The calculation verifies its pinned source and reference inputs.
Across installations, use the replay's declared absolute tolerance
for the floating-point diagnostics.

[Derivation](Derivation.md) · [Frozen protocol](Protocol.md) ·
[Reference replay](Replay.json) ·
[Lean distance proof](../../../lean/SKEFTHawking/FiniteGibbsResetScheduleDiamond.lean)
