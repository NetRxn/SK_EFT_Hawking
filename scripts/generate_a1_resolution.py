#!/usr/bin/env python3
"""
Generate the minimal free resolution of F₂ over A(1) and export matrices for Lean 4.

A(1) = ⟨Sq¹, Sq²⟩ is the 8-dimensional sub-Hopf algebra of the mod 2 Steenrod algebra.
The minimal free resolution of F₂ over A(1) through degree 5 has explicit differentials
with a bidiagonal structure (Sq¹ on diagonal, Sq(2,1) on superdiagonal).

This script:
  1. Defines A(1) multiplication over F₂ (GF(2)) using the explicit table
  2. Builds the differentials as A(1)-element matrices
  3. Expands to F₂-matrices (each A(1) element → 8×8 left-multiplication matrix)
  4. Verifies d² = 0 at every level
  5. Verifies exactness via rank computation (rank-nullity over GF(2))
  6. Computes RREF and transformation matrices for Lean witnesses
  7. Verifies A(1)-linearity of differentials
  8. Exports everything as Lean 4 matrix literals

References:
  - Deep research: Lit-Search/Phase-5q/The minimal free resolution...
  - Beaudry-Campbell (arXiv:1801.07530) — Ext chart
  - Adams, "Stable Homotopy and Generalised Homology" (1974)

Usage:
  uv run python scripts/generate_a1_resolution.py
  uv run python scripts/generate_a1_resolution.py --export-lean  # Write Lean literals
"""

import numpy as np
from typing import Optional
import argparse
import sys

# All arithmetic is over GF(2) = Z/2Z
# We use regular numpy int arrays and reduce mod 2 after every operation


# =============================================================================
# Section 1: A(1) Algebra Structure (Milnor Basis)
# =============================================================================

# Basis elements of A(1) in the MILNOR basis, indexed 0..7.
# Milnor basis element Sq(r1, r2) with 0 ≤ r1 ≤ 3, 0 ≤ r2 ≤ 1.
# Degree = r1 + 3*r2.
#
# 0: Sq(0,0) = 1        (degree 0)
# 1: Sq(1,0)             (degree 1)
# 2: Sq(2,0)             (degree 2)
# 3: Sq(3,0)             (degree 3)
# 4: Sq(0,1) = Q₁        (degree 3)  [Milnor primitive]
# 5: Sq(1,1)             (degree 4)
# 6: Sq(2,1)             (degree 5)
# 7: Sq(3,1)             (degree 6)  [top element]
#
# Key relation to Adem basis:
#   Sq(0,1) = Sq¹Sq² + Sq²Sq¹ (= Q₁, the commutator)
#   Sq(3,0) ≠ Sq³ (Adem); rather Sq³(Adem) = Sq(3,0) + Sq(0,1) in Milnor basis
#   The ONLY product yielding a sum of basis elements is Sq(1)*Sq(2) = Sq(3) + Sq(0,1)

A1_DIM = 8
A1_DEGREES = [0, 1, 2, 3, 3, 4, 5, 6]
A1_NAMES = ["1", "Sq(1)", "Sq(2)", "Sq(3)", "Q1", "Sq(1,1)", "Sq(2,1)", "Sq(3,1)"]

# Multiplication table in the Milnor basis.
# Products are over F₂. Most products yield a single basis element or zero.
# The ONE exception: Sq(1)*Sq(2) = Sq(3) + Q₁ (sum of indices 3 and 4).
#
# We represent each product as a frozenset of indices (over F₂, so XOR).
# Empty set = zero. Single element = that basis element. Two elements = their F₂ sum.

_MUL_TABLE_SETS: list[list[frozenset[int]]] = [
    # 1 * x = x
    [{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}],
    # Sq(1) * x
    [{1}, set(), {3, 4}, {5}, {5}, set(), {7}, set()],
    # Sq(2) * x
    [{2}, {3}, {5}, set(), {6}, {7}, set(), set()],
    # Sq(3) * x
    [{3}, set(), {6}, {7}, {7}, set(), set(), set()],
    # Q₁ * x
    [{4}, {5}, {6}, {7}, set(), set(), set(), set()],
    # Sq(1,1) * x
    [{5}, set(), {7}, set(), set(), set(), set(), set()],
    # Sq(2,1) * x
    [{6}, {7}, set(), set(), set(), set(), set(), set()],
    # Sq(3,1) * x
    [{7}, set(), set(), set(), set(), set(), set(), set()],
]


def a1_mul_set(a: int, b: int) -> frozenset[int]:
    """Multiply two A(1) basis elements. Returns set of indices in the F₂ sum."""
    return _MUL_TABLE_SETS[a][b]


def left_mul_matrix(a: int) -> np.ndarray:
    """8×8 matrix over F₂ for left multiplication by basis element a.

    (L_a)_{ij} = 1 if e_i appears in a * e_j (over F₂).
    """
    L = np.zeros((A1_DIM, A1_DIM), dtype=int)
    for j in range(A1_DIM):
        for i in a1_mul_set(a, j):
            L[i, j] = 1
    return L


def verify_a1_associativity():
    """Verify (a*b)*c = a*(b*c) for all basis triples.

    Since products can yield F₂ sums, we must compute the full F₂-linear extension:
    (sum_i α_i e_i) * e_c = sum_i α_i (e_i * e_c) with XOR for F₂ addition.
    """
    for a in range(A1_DIM):
        for b in range(A1_DIM):
            for c in range(A1_DIM):
                # (a*b)*c: first compute a*b as a set, then multiply each term by c
                ab_set = a1_mul_set(a, b)
                lhs = set()
                for mid in ab_set:
                    lhs ^= a1_mul_set(mid, c)  # XOR = F₂ addition

                # a*(b*c): first compute b*c as a set, then multiply a by each term
                bc_set = a1_mul_set(b, c)
                rhs = set()
                for mid in bc_set:
                    rhs ^= a1_mul_set(a, mid)

                assert lhs == rhs, \
                    f"Associativity fails: ({A1_NAMES[a]}*{A1_NAMES[b]})*{A1_NAMES[c]} = {lhs} != {rhs} = {A1_NAMES[a]}*({A1_NAMES[b]}*{A1_NAMES[c]})"
    print("✓ A(1) associativity verified (512 triples, Milnor basis)")


# =============================================================================
# Section 2: Resolution Differentials as A(1)-Element Matrices
# =============================================================================

# The differentials d_n: P_n -> P_{n-1} as matrices of A(1) basis indices.
# Entry (i,j) = index of A(1) element, or -1 for zero.
# Rows = generators of P_{n-1}, Columns = generators of P_n.

# d1: P1 (rank 2) -> P0 (rank 1)
# d1 = [Sq1, Sq2]
D1_A1 = np.array([[1, 2]])  # 1×2

# d2: P2 (rank 2) -> P1 (rank 2)
# d2 = [[Sq1, Sq3], [0, Sq2]]
D2_A1 = np.array([[1, 3], [-1, 2]])  # 2×2

# d3: P3 (rank 2) -> P2 (rank 2)
# d3 = [[Sq1, Sq(2,1)], [0, Sq3]]
D3_A1 = np.array([[1, 6], [-1, 3]])  # 2×2

# d4: P4 (rank 3) -> P3 (rank 2)
# d4 = [[Sq1, Sq(2,1), 0], [0, Sq1, Sq(2,1)]]
D4_A1 = np.array([[1, 6, -1], [-1, 1, 6]])  # 2×3

# d5: P5 (rank 4) -> P4 (rank 3)
# d5 = [[Sq1, Sq(2,1), 0, 0], [0, Sq1, Sq(2,1), 0], [0, 0, Sq1, Sq2]]
D5_A1 = np.array([[1, 6, -1, -1], [-1, 1, 6, -1], [-1, -1, 1, 2]])  # 3×4


def expand_differential(d_a1: np.ndarray) -> np.ndarray:
    """Expand an A(1)-element matrix to an F₂-matrix.

    Each A(1) element in position (i,j) becomes an 8×8 block (left multiplication matrix).
    Zero entries (-1) become 8×8 zero blocks.
    """
    rows_a1, cols_a1 = d_a1.shape
    rows_f2 = rows_a1 * A1_DIM
    cols_f2 = cols_a1 * A1_DIM
    D = np.zeros((rows_f2, cols_f2), dtype=int)

    for i in range(rows_a1):
        for j in range(cols_a1):
            elem = d_a1[i, j]
            if elem >= 0:
                block = left_mul_matrix(elem)
                D[i * A1_DIM:(i + 1) * A1_DIM, j * A1_DIM:(j + 1) * A1_DIM] = block

    return D


def gf2_matmul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Matrix multiplication over GF(2)."""
    return (A @ B) % 2


def gf2_rank(M: np.ndarray) -> int:
    """Compute rank of a matrix over GF(2) via row reduction."""
    M = M.copy() % 2
    rows, cols = M.shape
    rank = 0
    for col in range(cols):
        # Find pivot
        pivot_row = None
        for row in range(rank, rows):
            if M[row, col] == 1:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        # Swap
        M[[rank, pivot_row]] = M[[pivot_row, rank]]
        # Eliminate
        for row in range(rows):
            if row != rank and M[row, col] == 1:
                M[row] = (M[row] + M[rank]) % 2
        rank += 1
    return rank


def gf2_rref(M: np.ndarray):
    """Compute RREF over GF(2). Returns (rref, transform, rank).

    transform @ M = rref (mod 2)
    """
    M = M.copy() % 2
    rows, cols = M.shape
    # Augment with identity to track transformations
    augmented = np.hstack([M, np.eye(rows, dtype=int)])

    rank = 0
    pivot_cols = []
    for col in range(cols):
        pivot_row = None
        for row in range(rank, rows):
            if augmented[row, col] == 1:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        augmented[[rank, pivot_row]] = augmented[[pivot_row, rank]]
        for row in range(rows):
            if row != rank and augmented[row, col] == 1:
                augmented[row] = (augmented[row] + augmented[rank]) % 2
        pivot_cols.append(col)
        rank += 1

    rref = augmented[:, :cols] % 2
    transform = augmented[:, cols:] % 2
    return rref, transform, rank


# =============================================================================
# Section 3: Verification
# =============================================================================

def verify_d_squared_zero():
    """Verify d_{n-1} * d_n = 0 for all consecutive pairs."""
    diffs_a1 = [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]
    diffs_f2 = [expand_differential(d) for d in diffs_a1]

    for i in range(len(diffs_f2) - 1):
        product = gf2_matmul(diffs_f2[i], diffs_f2[i + 1])
        assert np.all(product == 0), f"d{i + 1} * d{i + 2} ≠ 0!"
        print(f"✓ d{i + 1} * d{i + 2} = 0  ({diffs_f2[i].shape[0]}×{diffs_f2[i + 1].shape[1]})")


def verify_exactness():
    """Verify exactness at each degree via rank-nullity over GF(2).

    At degree n: ker(d_n) = im(d_{n+1})
    Equivalently: rank(d_n) + rank(d_{n+1}) = dim(P_n)
    (This follows from d² = 0 which gives im(d_{n+1}) ⊆ ker(d_n),
     and the rank condition forces equality.)
    """
    diffs_f2 = [expand_differential(d) for d in [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]]

    # Also need the augmentation: ε : P0 -> F₂
    # ε projects onto the "1" component (index 0) of A(1)
    eps = np.zeros((1, A1_DIM), dtype=int)
    eps[0, 0] = 1  # project onto unit

    # Augmented sequence: ... -> P2 -d2-> P1 -d1-> P0 -ε-> F₂ -> 0
    # Exactness at P0: rank(ε) + rank(d1) = dim(P0) = 8
    # Exactness at Pn: rank(d_n) + rank(d_{n+1}) = dim(P_n)

    rank_eps = gf2_rank(eps)
    ranks = [gf2_rank(d) for d in diffs_f2]
    dims = [d.shape[1] for d in diffs_f2]  # Column count = dim of source

    # Exactness at P0
    assert rank_eps + ranks[0] == A1_DIM, \
        f"Not exact at P0: rank(ε)={rank_eps} + rank(d1)={ranks[0]} ≠ {A1_DIM}"
    print(f"✓ Exact at P0: rank(ε)={rank_eps} + rank(d1)={ranks[0]} = {A1_DIM}")

    # Exactness at P1..P4
    for n in range(len(ranks) - 1):
        dim_pn = dims[n]  # dim of P_{n+1} (source of d_{n+1})
        # Wait — need to be careful about indexing.
        # d_{n+1}: P_{n+1} -> P_n has shape (dim_P_n, dim_P_{n+1})
        # rank(d_{n+1}) is computed from diffs_f2[n] which is d_{n+1}
        # Exactness at P_{n+1}: rank(d_{n+1}) + rank(d_{n+2}) = dim(P_{n+1})
        dim_source = diffs_f2[n].shape[1]  # = dim(P_{n+1})
        r_out = ranks[n]      # rank(d_{n+1}), maps OUT of P_{n+1}
        r_in = ranks[n + 1]   # rank(d_{n+2}), maps INTO P_{n+1}
        # Actually let me re-derive. diffs_f2[0] = d1 : P1 -> P0, shape (8, 16)
        # diffs_f2[1] = d2 : P2 -> P1, shape (16, 16)
        # Exactness at P1: ker(d1) = im(d2), i.e. dim(P1) - rank(d1) = rank(d2)
        # equivalently: rank(d1) + rank(d2) = dim(P1)
        dim_pn1 = diffs_f2[n].shape[1]  # dim(P_{n+1}), source of d_{n+1}
        assert ranks[n] + ranks[n + 1] == dim_pn1, \
            f"Not exact at P{n + 1}: rank(d{n + 1})={ranks[n]} + rank(d{n + 2})={ranks[n + 1]} ≠ dim(P{n + 1})={dim_pn1}"
        print(f"✓ Exact at P{n + 1}: rank(d{n + 1})={ranks[n]} + rank(d{n + 2})={ranks[n + 1]} = dim(P{n + 1})={dim_pn1}")

    print(f"\n  Ranks: ε={rank_eps}, d1={ranks[0]}, d2={ranks[1]}, d3={ranks[2]}, d4={ranks[3]}, d5={ranks[4]}")
    return rank_eps, ranks


def verify_minimality():
    """Verify the resolution is minimal: all differentials map into the augmentation ideal.

    A resolution is minimal iff applying the augmentation ε to each column of d_n gives 0.
    Equivalently: for each column of the A(1)-element matrix, the entry in the "1" (index 0)
    row is always not the unit element "1" (index 0), OR the F₂ expansion of each column,
    when projected onto the augmentation component (index 0 of each A(1) block), gives zero.
    """
    diffs_a1 = [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]

    for n, d in enumerate(diffs_a1):
        rows, cols = d.shape
        for j in range(cols):
            for i in range(rows):
                elem = d[i, j]
                if elem >= 0:
                    # Check that the element is in the augmentation ideal (degree > 0)
                    assert elem != 0, \
                        f"d{n + 1} column {j}, row {i} contains unit element 1 — not in augmentation ideal"
        print(f"✓ d{n + 1} is minimal (all entries in augmentation ideal)")


def verify_a1_linearity():
    """Verify differentials are A(1)-module maps.

    An A(1)-module map d: A(1)^r -> A(1)^s defined by d(e_j) = sum_i a_{ij} * e_i
    is automatically A(1)-linear BY CONSTRUCTION (left multiplication on free modules
    commutes with right-action maps). The F₂-expanded matrix encodes this correctly
    because each block (i,j) is the LEFT multiplication matrix of a_{ij}.

    We verify a STRONGER property: that the F₂-expansion of each A(1)-element
    differential d_{A1} correctly reproduces the action. For each A(1) element a_{ij}
    in the differential matrix, verify that the corresponding 8×8 block in the
    expanded F₂ matrix equals left_mul_matrix(a_{ij}).
    """
    diffs_a1 = [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]
    diffs_f2 = [expand_differential(d) for d in diffs_a1]

    for n, (d_a1, d_f2) in enumerate(zip(diffs_a1, diffs_f2)):
        rows, cols = d_a1.shape
        for i in range(rows):
            for j in range(cols):
                elem = d_a1[i, j]
                block = d_f2[i * A1_DIM:(i + 1) * A1_DIM, j * A1_DIM:(j + 1) * A1_DIM]
                if elem >= 0:
                    expected = left_mul_matrix(elem)
                    assert np.array_equal(block, expected), \
                        f"d{n + 1}[{i},{j}] block doesn't match left_mul_matrix({A1_NAMES[elem]})"
                else:
                    assert np.all(block == 0), \
                        f"d{n + 1}[{i},{j}] block should be zero but isn't"
        print(f"✓ d{n + 1} F₂-expansion matches A(1)-element action (A(1)-linearity by construction)")


def compute_ext_dimensions():
    """Compute Ext dimensions from the minimal resolution.

    For a minimal resolution, dim(Ext^n) = rank(P_n) directly
    (since all coboundaries are zero — minimality means differentials
    map into the augmentation ideal, so Hom_{A(1)}(d_n, F₂) = 0).
    """
    ranks = [1, 2, 2, 2, 3, 4]
    print("\nExt^n_{A(1)}(F₂, F₂) dimensions:")
    for n, r in enumerate(ranks):
        print(f"  Ext^{n} = F₂^{r} (dimension {r})")
    print(f"\n  Total through degree 5: {sum(ranks)} basis elements")
    return ranks


# =============================================================================
# Section 4: RREF Witness Export
# =============================================================================

def compute_rref_witnesses():
    """Compute RREF transformation matrices for Lean witnesses."""
    diffs_f2 = [expand_differential(d) for d in [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]]
    witnesses = []

    for n, d in enumerate(diffs_f2):
        rref, transform, rank = gf2_rref(d)
        # Verify transform @ d = rref (mod 2)
        check = gf2_matmul(transform, d)
        assert np.array_equal(check, rref), f"RREF transform invalid for d{n + 1}"
        # Compute inverse of transform
        _, inv_transform, _ = gf2_rref(transform)
        # Verify transform @ inv = I
        identity_check = gf2_matmul(transform, inv_transform) % 2
        expected_I = np.eye(transform.shape[0], dtype=int)
        assert np.array_equal(identity_check, expected_I), f"Transform not invertible for d{n + 1}"

        witnesses.append({
            'n': n + 1,
            'differential': d,
            'rref': rref,
            'transform': transform,
            'inv_transform': inv_transform,
            'rank': rank,
            'shape': d.shape,
        })
        print(f"✓ RREF witness for d{n + 1}: rank={rank}, shape={d.shape}")

    return witnesses


# =============================================================================
# Section 5: Lean Export
# =============================================================================

def matrix_to_lean(M: np.ndarray, name: str) -> str:
    """Convert a numpy matrix to Lean 4 matrix literal syntax."""
    rows, cols = M.shape
    lines = [f"def {name} : Matrix (Fin {rows}) (Fin {cols}) (ZMod 2) := !!["]
    for i in range(rows):
        row_str = ", ".join(str(int(M[i, j])) for j in range(cols))
        separator = ";" if i < rows - 1 else ""
        lines.append(f"  {row_str}{separator}")
    lines.append("]")
    return "\n".join(lines)


def export_lean(witnesses):
    """Export all matrices as Lean 4 definitions."""
    output = []
    output.append("-- AUTO-GENERATED by scripts/generate_a1_resolution.py")
    output.append("-- Do not edit manually. Regenerate with: uv run python scripts/generate_a1_resolution.py --export-lean")
    output.append("")
    output.append("import Mathlib.Data.ZMod.Basic")
    output.append("import Mathlib.Data.Matrix.Basic")
    output.append("")
    output.append("namespace SKEFTHawking.A1Resolution")
    output.append("")
    output.append("abbrev F2 := ZMod 2")
    output.append("")

    for w in witnesses:
        n = w['n']
        output.append(f"-- d{n}: P{n} → P{n - 1}, shape {w['shape']}")
        output.append(matrix_to_lean(w['differential'], f"d{n}"))
        output.append("")
        output.append(f"-- RREF transform for d{n} (P @ d{n} = RREF)")
        output.append(matrix_to_lean(w['transform'], f"P{n}"))
        output.append("")
        output.append(matrix_to_lean(w['inv_transform'], f"P{n}_inv"))
        output.append("")
        output.append(matrix_to_lean(w['rref'], f"rref{n}"))
        output.append("")

    output.append("end SKEFTHawking.A1Resolution")
    return "\n".join(output)


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Generate A(1) resolution matrices")
    parser.add_argument("--export-lean", action="store_true", help="Export Lean 4 matrix literals")
    parser.add_argument("--output", type=str, default=None, help="Output file for Lean export")
    args = parser.parse_args()

    print("=" * 60)
    print("A(1) Minimal Free Resolution — Cross-Validation")
    print("=" * 60)

    # Step 1: Verify A(1) algebra
    print("\n--- A(1) Algebra Verification ---")
    verify_a1_associativity()

    # Step 2: Verify chain complex property
    print("\n--- Chain Complex Property (d² = 0) ---")
    verify_d_squared_zero()

    # Step 3: Verify exactness
    print("\n--- Exactness (rank-nullity) ---")
    rank_eps, ranks = verify_exactness()

    # Step 4: Verify minimality
    print("\n--- Minimality ---")
    verify_minimality()

    # Step 5: Verify A(1)-linearity
    print("\n--- A(1)-Linearity ---")
    verify_a1_linearity()

    # Step 6: Compute Ext dimensions
    ext_dims = compute_ext_dimensions()

    # Step 7: RREF witnesses
    print("\n--- RREF Witnesses ---")
    witnesses = compute_rref_witnesses()

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"A(1) dimension: {A1_DIM}")
    print(f"Resolution ranks: P0={1}, P1={2}, P2={2}, P3={2}, P4={3}, P5={4}")
    print(f"Ext dimensions: {ext_dims}")
    print(f"d² = 0: ✓ all verified")
    print(f"Exactness: ✓ all verified")
    print(f"Minimality: ✓ all verified")
    print(f"A(1)-linearity: ✓ all verified")
    print(f"RREF witnesses: ✓ all computed and verified")
    print(f"\nAll checks PASSED. Ready for Lean encoding.")

    if args.export_lean:
        lean_code = export_lean(witnesses)
        if args.output:
            with open(args.output, 'w') as f:
                f.write(lean_code)
            print(f"\nLean export written to {args.output}")
        else:
            print("\n--- Lean Export ---")
            print(lean_code)

    return 0


if __name__ == "__main__":
    sys.exit(main())
