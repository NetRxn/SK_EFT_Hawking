#!/usr/bin/env python3
"""ℤ[ω] reference oracle for the KMM Clifford+T exact-synthesis Lean formalization.

Phase 6x Tier-2 Item F (M4). A small, dependency-free reference implementation of
the ring ℤ[ω] (ω = ζ₈ = e^(iπ/4), ω⁴ = −1) matching the Lean
`SKEFTHawking.RossSelinger.ZOmega` convention EXACTLY, used to numerically
validate the load-bearing KMM lemmas BEFORE formalizing them in Lean (the
"correctness over expediency / validate-before-formalize" discipline).

Lean convention (lean/SKEFTHawking/FKLW/RossSelinger/ZOmega.lean):
    ⟨a, b, c, d⟩  =  a·ω³ + b·ω² + c·ω + d      (a = ω³-coef, …, d = constant)
    mul, conj (= σ₇ complex conjugation), √2 = ω − ω³ = ⟨−1,0,1,0⟩, ω = ⟨0,0,1,0⟩.

KMM (arXiv:1206.5236) facts validated here (run as a script):

  * Lemma 4 — for a unitary column (z,w) with cleared numerators x = z·√2^a,
    y = w·√2^a (so |x|²+|y|² = 2^a) and √2 ∤ x, √2 ∤ y, the squared-modulus gde
    satisfies gde(|x|², √2) ∈ {0,1} (and = gde(|y|²)).

  * Lemma 3 (THE reduction lemma) — for such a realizable column at sde(|z|²) ≥ 4,
    the achievable set { gde(|x+ωᵏy|²) − gde(|x|²) : k ∈ {0,1,2,3} } EQUALS {1,2,3}.
    Hence:
      - s = −1 (reduce sde(|z|²) by 1): pick the k with Δgde = 3, since
        sde(|z'|²) − sde(|z|²) = 2 − Δgde  (z' = (z + ωᵏw)/√2).

  * IMPORTANT (a corrected mental model): the reduction tracks the gde of the
    *squared modulus* |·|², NOT divisibility of the element x+ωᵏy itself. The
    naive condition "2 ∣ (x + ωᵏy)" is FALSE in general for realizable pairs —
    there is no finite mod-2 `decide` shortcut; the gde-valuation arithmetic
    (KMM Lemma 5 + Prop 1 + the gde(|x|²)∈{0,1} case split) is irreducibly
    required.

This oracle is the Lean side's numerical cross-check (cf. the dossier's
pygridsynth oracle for the Ross-Selinger H/I tracks).
"""

from __future__ import annotations
import itertools

Z = tuple[int, int, int, int]


def mul(x: Z, y: Z) -> Z:
    """ℤ[ω] product, Lean ZOmega.Mul convention (ω⁴ = −1)."""
    a1, b1, c1, d1 = x
    a2, b2, c2, d2 = y
    return (
        a1 * d2 + b1 * c2 + c1 * b2 + d1 * a2,   # ω³
        -a1 * a2 + b1 * d2 + c1 * c2 + d1 * b2,  # ω²
        -a1 * b2 - b1 * a2 + c1 * d2 + d1 * c2,  # ω
        -a1 * c2 - b1 * b2 - c1 * a2 + d1 * d2,  # constant
    )


def conj(x: Z) -> Z:
    """Complex conjugation σ₇ : ⟨a,b,c,d⟩ ↦ ⟨−c,−b,−a,d⟩ (Lean ZOmega.conj)."""
    a, b, c, d = x
    return (-c, -b, -a, d)


def add(x: Z, y: Z) -> Z:
    return tuple(x[i] + y[i] for i in range(4))  # type: ignore[return-value]


def norm_sq(x: Z) -> Z:
    """|x|² = x · conj x (a real element of ℤ[√2] ⊂ ℤ[ω])."""
    return mul(x, conj(x))


WPOW: list[Z] = [(0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0), (1, 0, 0, 0)]  # ω⁰..ω³


def divides_sqrt2(z: Z) -> bool:
    """√2 ∣ z criterion (Lean ZOmega.dividesSqrt2): a ≡ c, b ≡ d (mod 2)."""
    a, b, c, d = z
    return (a - c) % 2 == 0 and (b - d) % 2 == 0


def div_sqrt2(z: Z) -> Z:
    """z / √2 (valid when √2 ∣ z), Lean ZOmega.divSqrt2."""
    a, b, c, d = z
    return ((b - d) // 2, (a + c) // 2, (b + d) // 2, (c - a) // 2)


def gde_sqrt2(z: Z, fuel: int = 80) -> int:
    """gde(z, √2): greatest m with √2^m ∣ z (peel until indivisible)."""
    g = 0
    while fuel > 0 and z != (0, 0, 0, 0) and divides_sqrt2(z):
        z = div_sqrt2(z)
        g += 1
        fuel -= 1
    return g


def is_pow2_int(r: Z) -> int | None:
    """If r = 2^k as a pure integer ⟨0,0,0,2^k⟩ (k ≥ 0) return k, else None."""
    a, b, c, d = r
    if a != 0 or b != 0 or c != 0 or d <= 0:
        return None
    n, k = d, 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k if n == 1 else None


def _validate(coord_range: int = 3) -> None:
    rng = range(-coord_range, coord_range + 1)
    pts = [(a, b, c, d) for a in rng for b in rng for c in rng for d in rng]

    # sanity
    assert mul((-1, 0, 1, 0), (-1, 0, 1, 0)) == (0, 0, 0, 2), "√2² ≠ 2"
    assert mul(WPOW[1], WPOW[1]) == (0, 1, 0, 0), "ω² ≠ i"
    assert norm_sq((0, 0, 0, 1)) == (0, 0, 0, 1) and norm_sq(WPOW[1]) == (0, 0, 0, 1)

    total = lemma3_ok = full_ok = 0
    gde_vals: set[int] = set()
    for x in pts:
        if divides_sqrt2(x):
            continue
        nx = norm_sq(x)
        gx = gde_sqrt2(nx)
        for y in pts:
            if divides_sqrt2(y):
                continue
            s = add(nx, norm_sq(y))
            kp = is_pow2_int(s)
            if kp is None or kp < 2:  # |x|²+|y|² = 2^a with a ≥ 2  ⟹  sde(|z|²) ≥ 4
                continue
            total += 1
            gde_vals.add(gx)
            diffs = {gde_sqrt2(norm_sq(add(x, mul(WPOW[k], y)))) - gx for k in range(4)}
            if 3 in diffs:
                lemma3_ok += 1
            if {1, 2, 3} <= diffs:
                full_ok += 1

    print(f"realizable columns (|x|²+|y|² = 2^a, a≥2, √2∤x,y): {total}")
    print(f"  Lemma 4  gde(|x|²) ∈ {sorted(gde_vals)}            (expect ⊆ {{0,1}})")
    print(f"  Lemma 3  ∃k Δgde=3 (s=−1 reduce): {lemma3_ok}/{total}")
    print(f"  Lemma 3  {{1,2,3}} ⊆ Δgde-set:     {full_ok}/{total}")
    assert gde_vals <= {0, 1}, "Lemma 4 violated"
    assert lemma3_ok == total, "Lemma 3 (s=−1) violated"
    assert full_ok == total, "Lemma 3 (full {1,2,3}) violated"
    print("ALL KMM Lemma 3/4 numerical checks PASS.")


if __name__ == "__main__":
    _validate()
