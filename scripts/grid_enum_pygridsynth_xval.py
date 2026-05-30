"""Phase 6x Item H — cross-validate the Ross-Selinger upright grid ENUMERATION vs pygridsynth.

The Lean `gridSolutions1D lo hi lo' hi'` (RossSelinger/GridEnum.lean) enumerates all (m, n) ∈ ℤ²
with the ℤ[√2] value `m + n√2 ∈ [lo, hi]` AND its Galois conjugate `m − n√2 ∈ [lo', hi']`, via the
upright scan: `m ∈ [⌈(lo+lo')/2⌉, ⌊(hi+hi')/2⌋]`, and per m, `n ∈ [⌈max((lo−m)/√2,(m−hi')/√2)⌉,
⌊min((hi−m)/√2,(m−lo')/√2)⌋]`. `gridSolutions1D_mem_iff` proves membership ⇔ the four real bounds
(correctness + completeness).

pygridsynth (MIT) ships the SAME one-dimensional grid problem as `odgp.solve_ODGP(I, J)`: enumerate
ZRootTwo (= ℤ[√2], `a + b√2`) elements with value in interval I and conjugate in J. This harness
re-implements the Lean enumeration in Python (verbatim: same ceil/floor m- and n-ranges) and checks
its solution SET equals pygridsynth's `solve_ODGP` set across a suite of boxes — the literal Item-H
roadmap deliverable "cross-validate vs pygridsynth". Set equality across the suite confirms the
formalized enumeration is both SOUND (no spurious solutions) and COMPLETE (no missed solutions)
against the reference, matching `gridSolutions1D_mem_iff`.

Boxes use non-lattice-aligned bounds (rational offsets) so no solution sits exactly on a box edge —
floating ceil/floor then agrees with pygridsynth's exact (mpmath) arithmetic without edge ambiguity.
"""
from __future__ import annotations

import math

import mpmath
from pygridsynth.odgp import solve_ODGP
from pygridsynth.region import Interval

S2 = math.sqrt(2)


def lean_grid1d(lo: float, hi: float, lop: float, hip: float) -> set[tuple[int, int]]:
    """Verbatim Python port of the Lean `gridSolutions1D` upright enumeration (the (m,n) set)."""
    out: set[tuple[int, int]] = set()
    m_lo = math.ceil((lo + lop) / 2)
    m_hi = math.floor((hi + hip) / 2)
    for m in range(m_lo, m_hi + 1):
        n_lo = math.ceil(max((lo - m) / S2, (m - hip) / S2))
        n_hi = math.floor(min((hi - m) / S2, (m - lop) / S2))
        for n in range(n_lo, n_hi + 1):
            out.add((m, n))
    return out


def ref_grid1d(lo: float, hi: float, lop: float, hip: float) -> set[tuple[int, int]]:
    """pygridsynth reference: solve_ODGP(value-interval, conjugate-interval) → {(a, b) : a + b√2}."""
    sols = solve_ODGP(Interval(mpmath.mpf(lo), mpmath.mpf(hi)),
                      Interval(mpmath.mpf(lop), mpmath.mpf(hip)))
    return {(int(z.a), int(z.b)) for z in sols}


def build_boxes() -> list[tuple[float, float, float, float]]:
    """A suite of upright boxes (value-interval × conjugate-interval), non-lattice-aligned bounds."""
    boxes: list[tuple[float, float, float, float]] = []
    offs = 0.37  # irrational-ish offset to keep solutions off the box edges
    for w in (1.0, 2.5, 4.0, 6.0, 9.0):          # value half-width-ish
        for wp in (1.0, 3.0, 5.0, 8.0):          # conjugate half-width-ish
            for c in (0.0, 1.3, -2.1):           # value-interval centre
                for cp in (0.0, -0.8, 2.4):      # conjugate-interval centre
                    lo, hi = c - w + offs, c + w + offs
                    lop, hip = cp - wp - offs, cp + wp - offs
                    boxes.append((lo, hi, lop, hip))
    return boxes


def main() -> int:
    boxes = build_boxes()
    n_match = 0
    n_total = len(boxes)
    n_sols = 0
    fails: list[str] = []
    for (lo, hi, lop, hip) in boxes:
        mine = lean_grid1d(lo, hi, lop, hip)
        ref = ref_grid1d(lo, hi, lop, hip)
        n_sols += len(ref)
        if mine == ref:
            n_match += 1
        else:
            missing = ref - mine
            spurious = mine - ref
            fails.append(f"[{lo:.2f},{hi:.2f}]x[{lop:.2f},{hip:.2f}] "
                        f"missing={sorted(missing)[:3]} spurious={sorted(spurious)[:3]}")
    print(f"Item H — gridSolutions1D vs pygridsynth.solve_ODGP: {n_total} upright boxes")
    print(f"  exact solution-set match (sound + complete):  {n_match}/{n_total}")
    print(f"  total grid solutions enumerated across suite:  {n_sols}")
    if fails:
        print(f"  mismatches: {fails[:6]}{' …' if len(fails) > 6 else ''}")
    assert n_match == n_total, f"only {n_match}/{n_total} boxes matched pygridsynth exactly"
    assert n_sols >= 50, f"suite enumerated only {n_sols} solutions (need a non-trivial suite)"
    print(f"PASS: the Lean upright enumeration matches the MIT pygridsynth solve_ODGP reference set")
    print(f"exactly on all {n_total} boxes ({n_sols} solutions) — empirical corroboration of")
    print("gridSolutions1D_mem_iff (soundness + completeness of the formalized enumeration).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
