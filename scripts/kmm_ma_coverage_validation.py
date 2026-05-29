#!/usr/bin/env python3
"""Validate-before-formalize: the Matsumoto-Amano (MA) base-coverage route.

Phase 6x Tier-2 Item F (𝕊₃ coverage). Companion to `kmm_n3_bfs.py` +
`kmm_zomega_reference_oracle.py`.

The deep-research verdict (Lit-Search/Phase-6x/"Phase 6x Tier-2 Item F — DR-
formalizing the 𝕊₃ base-case COVERAGE in Lean 4.md") is: prove `coverage` via
the **Matsumoto-Amano normal-form route**, not BFS. MA reads a single-qubit
Clifford+T unitary as

      U = (T | ε)(HT | SHT)* C          (Giles-Selinger arXiv:1312.6584, Conv 7.9)

with C a Clifford and #syllables = T-count = k_SO3 (GS Lemma 4.10). The DR
skeleton defines the decreasing measure via the SO(3) Bloch map. THIS SCRIPT
TESTS A BLOCH-FREE VARIANT that would be far cheaper in Lean:

  * recursion MEASURE  = μ(M) := sde(|z₀₀|²)  (already computable in Lean), AND
                         the matrix sde, AND the (oracle) T-count — test all three
  * recursion BASE     = decidable membership "M is a Clifford" (finite set)
  * recursion STEP     = strip the leading MA syllable s ∈ {T, HT, SHT}:
                         M' := interp(s)⁻¹ · M

Make-or-break questions answered here:

  Q-A. Bridge:    does μ(M) ≤ 3  ⟹  T-count(M) ≤ 3 ?  (and what is the max T-count
                  over the whole 𝕊₃ orbit?)
  Q-B. Strip:     for every NON-Clifford μ≤3 matrix M, is there a syllable
                  s ∈ {T, HT, SHT} whose strip M' = interp(s)⁻¹·M satisfies
                  T-count(M') = T-count(M) − 1 ? Is it UNIQUE (MA)? Does the same
                  hold with the cheaper measure μ (strict decrease)? matrix-sde?
  Q-C. Closure:   does the greedy strip recursion stay inside μ≤3 (so the base
                  finder never leaves the finite orbit), and terminate at a
                  Clifford?
  Q-D. Length:    what is the worst-case total emitted word length
                  (#syllables·(≤3) + clifford-tail)?  Must be ≤ 22 (DR) — and
                  ideally we learn the true max.
  Q-E. Clifford:  how many Cliffords are in the orbit, and what is the max
                  clifford-tail word length (the "+13" constant)?

If Q-A..Q-D pass with the μ measure, the Lean build is Bloch-free: recurse on
muMeasure, decidable Clifford base, decrease + syllable-choice are finite residue
facts (native_decide), correctness by the strip algebra. If μ fails but T-count
works, we fall back to the SO(3)/Bloch measure (DR option b verbatim).
"""

from __future__ import annotations
import sys, os, collections
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kmm_zomega_reference_oracle import (  # noqa: E402
    mul as zmul, add as zadd, norm_sq, divides_sqrt2, div_sqrt2, gde_sqrt2)
from kmm_n3_bfs import (  # noqa: E402
    GENS, ID, matmul, normalize, sde_z00sq, ONE, ZERO, NEG1, OM, I, NEGI)


# ── ZOmega conjugation + matrix adjoint (= inverse for unitaries) ──────────────
def zconj(z):
    """conj(a·ω³+b·ω²+c·ω+d) = ⟨-c,-b,-a,d⟩  (ω ↦ ω⁻¹ = ω⁷ = -ω³)."""
    a, b, c, d = z
    return (-c, -b, -a, d)


def adjoint(A):
    """Conjugate-transpose of ((m00,m01,m10,m11),k)."""
    (m00, m01, m10, m11), k = A
    return ((zconj(m00), zconj(m10), zconj(m01), zconj(m11)), k)


def mat_eq(A, B):
    return normalize(A) == normalize(B)


def sde_matrix(A):
    """Matrix sde: least k with √2^k·M over ZOmega (= the normalized exponent)."""
    return normalize(A)[1]


# ── syllable matrices ─────────────────────────────────────────────────────────
def interp_word(gates):
    M = ID
    for g in gates:
        M = matmul(M, GENS[g])
    return normalize(M)


SYLLABLES = {
    'T':   ['T'],
    'HT':  ['H', 'T'],
    'SHT': ['S', 'H', 'T'],
}
SYL_MAT = {name: interp_word(gs) for name, gs in SYLLABLES.items()}
SYL_INV = {name: adjoint(M) for name, M in SYL_MAT.items()}


def strip(name, M):
    """M' = interp(syllable)⁻¹ · M."""
    return normalize(matmul(SYL_INV[name], M))


# ── Bloch / SO(3) map (DR's recommended measure k_SO3) ────────────────────────
PAULI = {
    'x': ((ZERO, ONE, ONE, ZERO), 0),
    'y': ((ZERO, NEGI, I, ZERO), 0),
    'z': ((ONE, ZERO, ZERO, NEG1), 0),
}


def den_exp(e, k):
    """Denominator exponent of a single ZOmega element e/√2^k."""
    while k > 0 and divides_sqrt2(e):
        e = div_sqrt2(e)
        k -= 1
    return k


def kso3(U):
    """k_SO3 = least-denominator-exponent of the SO(3) Bloch image
    R(U)_{ij} = (1/2)·Tr(σ_i U σ_j U†). GS Lemma 4.10: k_SO3 = T-count."""
    Ud = adjoint(U)
    m = 0
    for si in PAULI.values():
        for sj in PAULI.values():
            (a00, a01, a10, a11), k = matmul(si, matmul(U, matmul(sj, Ud)))
            tr = zadd(a00, a11)            # numerator of Tr(...)
            m = max(m, den_exp(tr, k + 2))  # /2 = /√2², so +2 to the exponent
    return m


def entry_denExp(M, i):
    """denExp(normSq(entry i)) for entry index i∈{0:m00,1:m01,2:m10,3:m11}."""
    ents, _ = normalize(M)
    e = ents[i]
    ns = norm_sq(e)            # real ZOmega
    # sde(|e|²) = 2·matrix_k − gde(|e|²); but for a single entry use the
    # squared-modulus least-denom-exp analogous to sde_z00sq:
    _, k = normalize(M)
    return max(0, 2 * k - gde_sqrt2(ns))


# ── full-group BFS (μ≤3 orbit) ────────────────────────────────────────────────
def full_bfs(maxlen=14):
    start = normalize(ID)
    dist = {start: 0}
    q = deque([start])
    while q:
        M = q.popleft()
        d = dist[M]
        if d >= maxlen:
            continue
        for G in GENS.values():
            N = normalize(matmul(G, M))
            if N not in dist:
                dist[N] = d + 1
                q.append(N)
    return dist


# ── T-count via 0-1 BFS (Clifford gens cost 0, T cost 1) ──────────────────────
CLIFFORD_GENS = {k: v for k, v in GENS.items() if k != 'T'}


def tcount_bfs(maxt=6):
    """Min #T gates (forward T only, matching our generating set), capped at
    T-count ≤ maxt. The Clifford+T group is INFINITE, so the T-level cap is
    mandatory; maxt=6 cleanly distinguishes T-counts 0..3 (μ≤3 region) plus
    headroom for strips. Implemented as level-by-level: at each T-level, take
    the Clifford-closure (cost-0), then one T-edge to seed the next level."""
    start = normalize(ID)
    tc = {start: 0}

    def clifford_closure(frontier):
        """Expand `frontier` (a set) under cost-0 Clifford edges, recording any
        newly-seen matrix at the current T-level."""
        q = deque(frontier)
        while q:
            M = q.popleft()
            for G in CLIFFORD_GENS.values():
                N = normalize(matmul(G, M))
                if N not in tc:
                    tc[N] = tc[M]
                    q.append(N)

    clifford_closure({start})
    level = {M for M in tc}          # all T-count-0 matrices
    for t in range(1, maxt + 1):
        nxt = set()
        for M in level:
            N = normalize(matmul(GENS['T'], M))
            if N not in tc:
                tc[N] = t
                nxt.add(N)
        if not nxt:
            break
        clifford_closure(nxt)
        level = {M for M, d in tc.items() if d == t}
    return tc


def clifford_set():
    """All Cliffords = T-count 0 = reachable using only Clifford gens."""
    start = normalize(ID)
    seen = {start}
    q = deque([start])
    while q:
        M = q.popleft()
        for G in CLIFFORD_GENS.values():
            N = normalize(matmul(G, M))
            if N not in seen:
                seen.add(N)
                q.append(N)
    return seen


def main():
    print("Building orbits ...")
    dist = full_bfs(14)
    s3 = {M for M in dist if sde_z00sq(M) <= 3}
    cliffords = clifford_set()
    tc = tcount_bfs()
    print(f"  full orbit (≤14): {len(dist)}   |   𝕊₃ (μ≤3): {len(s3)}   |   "
          f"Cliffords: {len(cliffords)}")

    # ── Q-E: clifford tail length (max shortest-word over Cliffords) ──────────
    cliff_lens = [dist[M] for M in cliffords]
    print(f"\n[Q-E] Cliffords in orbit: {len(cliffords)}; "
          f"max shortest-word (tail bound) = {max(cliff_lens)}")
    # how many Cliffords have μ≤3 (all should — Cliffords are low-μ)
    cliff_mu = collections.Counter(sde_z00sq(M) for M in cliffords)
    print(f"       Clifford μ distribution: {dict(sorted(cliff_mu.items()))}")

    # ── Q-A: bridge μ≤3 ⟹ T-count≤3 ──────────────────────────────────────────
    tc_by_mu = collections.defaultdict(list)
    for M in s3:
        tc_by_mu[sde_z00sq(M)].append(tc[M])
    print("\n[Q-A] bridge  μ → max T-count over 𝕊₃:")
    bridge_ok = True
    for mu in sorted(tc_by_mu):
        mx = max(tc_by_mu[mu])
        print(f"       μ={mu}: matrices={len(tc_by_mu[mu]):5d}  max T-count={mx}")
        if mx > 3:
            bridge_ok = False
    print(f"       bridge μ≤3 ⟹ T-count≤3 : {'PASS' if bridge_ok else 'FAIL'}")

    # ── Q-B: strip reduces measure (T-count / μ / matrix-sde), uniqueness ─────
    print("\n[Q-B] strip test over NON-Clifford μ≤3 matrices "
          f"({len(s3) - len([m for m in s3 if m in cliffords])} of them):")
    fail_tcount = []      # M with no syllable reducing T-count by 1
    fail_mu = []          # M with no syllable strictly reducing μ
    fail_sdemat = []      # M with no syllable strictly reducing matrix-sde
    nonunique_tcount = 0  # M with >1 syllable reducing T-count (MA expects exactly 1)
    leaves_s3 = []        # M where the unique T-reducing strip leaves μ>3
    for M in s3:
        if M in cliffords:
            continue
        t0 = tc[M]
        mu0 = sde_z00sq(M)
        sm0 = sde_matrix(M)
        good_t = []
        good_mu = False
        good_sm = False
        for name in ('T', 'HT', 'SHT'):
            Mp = strip(name, M)
            if tc.get(Mp, 99) == t0 - 1:
                good_t.append(name)
                if sde_z00sq(Mp) > 3:
                    leaves_s3.append((M, name))
            if sde_z00sq(Mp) < mu0:
                good_mu = True
            if sde_matrix(Mp) < sm0:
                good_sm = True
        if not good_t:
            fail_tcount.append(M)
        elif len(good_t) > 1:
            nonunique_tcount += 1
        if not good_mu:
            fail_mu.append(M)
        if not good_sm:
            fail_sdemat.append(M)
    n_noncliff = len(s3) - len(cliffords & s3)
    print(f"       T-count strip exists (=t-1): "
          f"{'PASS' if not fail_tcount else f'FAIL ({len(fail_tcount)})'}  "
          f"| non-unique: {nonunique_tcount}/{n_noncliff}")
    print(f"       μ strict-decrease strip exists: "
          f"{'PASS' if not fail_mu else f'FAIL ({len(fail_mu)})'}")
    print(f"       matrix-sde strict-decrease strip exists: "
          f"{'PASS' if not fail_sdemat else f'FAIL ({len(fail_sdemat)})'}")
    print(f"       T-reducing strip leaves μ>3: "
          f"{'never (good)' if not leaves_s3 else f'{len(leaves_s3)} cases'}")
    if fail_mu[:3]:
        print(f"       sample μ-fail matrices (μ, T-count): "
              f"{[(sde_z00sq(M), tc[M]) for M in fail_mu[:5]]}")

    # ── Q-C/Q-D: greedy recursion (MA-faithful: T-count−1 strip) termination ──
    # Choose the T-count-reducing syllable (first that works); recurse to Clifford.
    print("\n[Q-C/Q-D] greedy MA recursion (T-count measure):")
    max_syllables = 0
    max_total_len = 0
    recursion_ok = True
    for M0 in s3:
        M = M0
        syllables = []
        steps = 0
        while M not in cliffords and steps < 30:
            t0 = tc[M]
            chosen = None
            for name in ('T', 'HT', 'SHT'):
                Mp = strip(name, M)
                if tc.get(Mp, 99) == t0 - 1:
                    chosen = name
                    break
            if chosen is None:
                recursion_ok = False
                break
            syllables.append(chosen)
            M = strip(chosen, M)
            steps += 1
        if M not in cliffords:
            recursion_ok = False
            continue
        syl_len = sum(len(SYLLABLES[s]) for s in syllables)
        tail_len = dist[M]          # shortest Clifford word
        total = syl_len + tail_len
        max_syllables = max(max_syllables, len(syllables))
        max_total_len = max(max_total_len, total)
    print(f"       recursion terminates at a Clifford for all 𝕊₃: "
          f"{'PASS' if recursion_ok else 'FAIL'}")
    print(f"       max #syllables = {max_syllables}  (≤3 expected)")
    print(f"       max total emitted length = {max_total_len}  "
          f"(DR bound: ≤22; we use this to pin N₃)")

    # ── Q-F: Bloch k_SO3 measure (DR route) — equals T-count? decreases by 1? ──
    print("\n[Q-F] Bloch k_SO3 measure (DR option b):")
    kso3_eq_tcount = True
    kso3_bad = []
    for M in s3:
        if kso3(M) != tc[M]:
            kso3_eq_tcount = False
            kso3_bad.append((M, kso3(M), tc[M]))
    print(f"       k_SO3 == T-count over all 𝕊₃: "
          f"{'PASS' if kso3_eq_tcount else f'FAIL ({len(kso3_bad)})'}")
    if kso3_bad[:3]:
        print(f"       sample (k_SO3, T-count): {[(b[1], b[2]) for b in kso3_bad[:5]]}")
    # decreases by exactly 1 under the T-reducing strip?
    kso3_dec_ok = True
    for M in s3:
        if M in cliffords:
            continue
        t0 = tc[M]
        for name in ('T', 'HT', 'SHT'):
            Mp = strip(name, M)
            if tc.get(Mp, 99) == t0 - 1:
                if kso3(Mp) != kso3(M) - 1:
                    kso3_dec_ok = False
                break
    print(f"       k_SO3 decreases by exactly 1 under T-reducing strip: "
          f"{'PASS' if kso3_dec_ok else 'FAIL'}")
    kso3_max = max(kso3(M) for M in s3)
    kso3_cliff = all(kso3(M) == 0 for M in cliffords)
    print(f"       max k_SO3 over 𝕊₃ = {kso3_max} (≤3 expected); "
          f"k_SO3=0 ⟺ Clifford: {'PASS' if kso3_cliff else 'CHECK'}")

    # ── Q-G: cheap computable measures — does the T-reducing strip lower them? ──
    print("\n[Q-G] cheap computable measures vs the (unique) T-reducing strip:")
    measures = {
        'matrix-sde k':        lambda M: normalize(M)[1],
        'denExp|m01|²':        lambda M: entry_denExp(M, 1),
        'sum entry denExp':    lambda M: sum(entry_denExp(M, i) for i in range(4)),
        'max entry denExp':    lambda M: max(entry_denExp(M, i) for i in range(4)),
        'k + denExp|m00|²':    lambda M: normalize(M)[1] + sde_z00sq(M),
    }
    for mname, mf in measures.items():
        strict_dec = True
        only_treducer = True
        for M in s3:
            if M in cliffords:
                continue
            t0 = tc[M]
            m0 = mf(M)
            for name in ('T', 'HT', 'SHT'):
                Mp = strip(name, M)
                is_tred = (tc.get(Mp, 99) == t0 - 1)
                dec = (mf(Mp) < m0)
                if is_tred and not dec:
                    strict_dec = False
                if dec and not is_tred:
                    only_treducer = False
        print(f"       {mname:18s}: T-reducer lowers it: "
              f"{'YES' if strict_dec else 'no '}  | "
              f"only T-reducer lowers it: {'YES' if only_treducer else 'no'}")

    print("\n── SUMMARY ───────────────────────────────────────────────────────")
    print(f"  Bloch-free μ-measure viable : "
          f"{'YES' if (bridge_ok and not fail_mu and recursion_ok) else 'NO'}")
    print(f"  Bloch-free T-count viable   : "
          f"{'YES' if (bridge_ok and not fail_tcount and recursion_ok) else 'NO'}")
    print(f"  matrix-sde measure viable   : "
          f"{'YES' if not fail_sdemat else 'NO'}")
    print(f"  ⟹ pin coverage length bound at N₃ = {max_total_len}")


if __name__ == "__main__":
    main()
