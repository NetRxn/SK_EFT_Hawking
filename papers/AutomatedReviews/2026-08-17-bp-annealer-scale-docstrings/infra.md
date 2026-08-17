---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-17T00:00:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Lean docstrings attribute the annealer comparison to the wrong experiment scale

## Summary

**1 MINOR.** Found while correcting the Kibble-Zurek exponent family; same class as that
defect — a docstring naming a source's result as something the source does not report.

### 1.1 — 🟡 MINOR — "matches the D-Wave Advantage2 annealer at 300+ qubits" is not what the source compares

- **Severity:** MINOR
- **Lane:** lean

**Where:** `lean/SKEFTHawking/BeliefPropagation.lean:81`;
`lean/SKEFTHawking/BPLDPSimulability.lean:28-29,116`.

Tindall, Mello, Fishman, Stoudenmire and Sels (Science **392**, 2026) put the annealer
comparisons at 8x8 cylinders and ~50-qubit 3D lattices (pp. 4-5). The 300+ qubit run is the
Kibble-Zurek correlation-length extraction, a different experiment in the same paper. The
docstrings fuse the largest number in the paper to the comparison claim.

These are **docstrings only** — no theorem statement changes, and D7's apex closure is
untouched, so a correction cannot disturb the bundle. The scale claim reaches a reader
through the module header, which is where a fresh agent forms its picture of what the
substrate is entitled to say.

**Bar:** state the scale each claim actually carries — annealer comparison at 8x8
cylinders / ~50-qubit 3D lattices; 300+ qubits for the Kibble-Zurek extraction.

Verify: `cd "$REPO" && grep -rn "300+ qubits\|Advantage2" lean/SKEFTHawking/BeliefPropagation.lean lean/SKEFTHawking/BPLDPSimulability.lean`

*What it asserts:* no line fuses the annealer comparison to the 300+ qubit figure.
