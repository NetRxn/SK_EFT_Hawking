#!/usr/bin/env python3
"""Validate-before-formalize: characterize the MA `ma_step` reducing syllable.

Phase 6x Tier-2 Item F (𝕊₃ coverage, ma_step crux). Companion to
`kmm_ma_coverage_validation.py`.

`ma_step` (the crux remaining for the MA base-coverage recursion): for a realizable
matrix `M` with `kSO3 M ≥ 1`, there is a unique syllable `s ∈ {T, HT, SHT}` whose
strip `stripMat s M = adjoint(interp s)·M` satisfies `kSO3 (stripMat s M) = kSO3 M − 1`.
(Already confirmed unique + decreasing in `kmm_ma_coverage_validation.py`.)

To formalize the existence/selection by `native_decide` (kmm_lemma3-style), the
selector must be a FINITE RESIDUE function. This script determines the residue
MODULUS + which residue determines the reducing syllable:

  - U(2) residue: the cleared matrix numerators mod 2 (16 bits) — would let us
    reuse the existing `coordOf`/ZOmega bridge machinery.
  - + denominator-exponent parity `k mod 2` if 16 bits alone is too coarse.
  - Bloch residue (the 3×3 SO(3) image mod 2) as a fallback.

Output: for each candidate residue function, whether `residue ↦ {reducing syllables}`
is well-defined (consistent across all realizable μ≤3 non-Clifford matrices). The
coarsest consistent residue is the one to formalize.
"""

from __future__ import annotations
import sys, os, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kmm_n3_bfs import normalize, sde_z00sq  # noqa: E402
from kmm_ma_coverage_validation import full_bfs, kso3, strip, clifford_set  # noqa: E402


def res_u2_mod2(M):
    """Cleared matrix numerators mod 2: 16 bits (4 entries × 4 ZOmega coords)."""
    ents, _ = normalize(M)
    return tuple(c % 2 for e in ents for c in e)


def res_u2_mod2_k(M):
    """U(2) mod-2 residue + denominator-exponent parity."""
    ents, k = normalize(M)
    return (tuple(c % 2 for e in ents for c in e), k % 2)


def res_u2_mod2_kfull(M):
    """U(2) mod-2 residue + full denominator exponent."""
    ents, k = normalize(M)
    return (tuple(c % 2 for e in ents for c in e), k)


def res_u2_mod4(M):
    """Cleared matrix numerators mod 4."""
    ents, _ = normalize(M)
    return tuple(c % 4 for e in ents for c in e)


def reducers(M):
    """The set of syllables s with kSO3(strip s M) = kSO3 M − 1."""
    n = kso3(M)
    return frozenset(s for s in ('T', 'HT', 'SHT') if kso3(strip(s, M)) == n - 1)


def check(name, resfn, items):
    """Is `resfn ↦ reducers` well-defined over `items`?  Report consistency."""
    table = {}
    consistent = True
    nclasses = 0
    for M, red in items:
        r = resfn(M)
        if r in table:
            if table[r] != red:
                consistent = False
        else:
            table[r] = red
            nclasses += 1
    # also: is the reducer always a singleton?
    singleton = all(len(red) == 1 for _, red in items)
    print(f"  {name:22s}: consistent={consistent!s:5s}  "
          f"#residue-classes={nclasses:5d}  reducer-always-singleton={singleton}")
    return consistent


def main():
    print("Building orbit + kSO3 (this takes ~1 min) ...")
    dist = full_bfs(14)
    cliffs = clifford_set()
    # realizable μ≤3 non-Clifford matrices, with their reducing-syllable set
    items = []
    for M in dist:
        if sde_z00sq(M) <= 3 and M not in cliffs:
            items.append((M, reducers(M)))
    print(f"  non-Clifford μ≤3 matrices: {len(items)}")

    print("\nResidue-determines-syllable consistency (coarsest consistent wins):")
    check("U(2) mod 2 (16 bits)", res_u2_mod2, items)
    check("U(2) mod 2 + k%2", res_u2_mod2_k, items)
    check("U(2) mod 2 + k", res_u2_mod2_kfull, items)
    check("U(2) mod 4", res_u2_mod4, items)

    # Distribution of reducing syllable by kSO3 level (sanity)
    bylev = collections.defaultdict(collections.Counter)
    for M, red in items:
        bylev[kso3(M)][tuple(sorted(red))] += 1
    print("\nReducing-syllable distribution by kSO3 level:")
    for lev in sorted(bylev):
        print(f"  kSO3={lev}: {dict(bylev[lev])}")


if __name__ == "__main__":
    main()
