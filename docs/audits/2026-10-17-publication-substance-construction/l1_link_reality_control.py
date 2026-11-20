"""Check simultaneous complex conjugation of the literal Spin(4) factors."""
from sympy import I, diag, eye, simplify, symbols, zeros

from l1_direct_b_haar import gamma, pauli


def quaternion(q):
    return q[0] * eye(2) - I * sum(
        (coordinate * matrix for coordinate, matrix in zip(q[1:], pauli)),
        zeros(2),
    )


def main():
    j = I * pauli[1]
    change = diag(j, j)
    inverse = change.inv()
    assert change.det() == 1
    coordinates = symbols("q0:8", real=True)
    link = diag(quaternion(coordinates[:4]), quaternion(coordinates[4:]))
    chirality = gamma[0] * gamma[1] * gamma[2] * gamma[3]
    for matrix in (*gamma, chirality, link, link.H):
        assert (matrix.conjugate() - change * matrix * inverse).applyfunc(
            simplify
        ) == zeros(4)
    print("gamma, chirality and independent chiral quaternion conjugations agree")


if __name__ == "__main__":
    main()
