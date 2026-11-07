from itertools import product
from fractions import Fraction
from l1_direct_a_haar import A, X, adj, qproduct, integral

J=range(3)
site_bits=[set(range(3)),set(range(3,6))]

def A_support(site,j):
    return site_bits[site] | {3*(1-site)+j}

def B_support(site,j):
    return {3*site+j}

assert all(A_support(0,j)^A_support(1,k)^B_support(0,l)^B_support(1,m)
           for j,k,l,m in product(J, repeat=4))
assert sum(not (A_support(0,j)^A_support(0,k)^A_support(1,l)^A_support(1,m))
           for j,k,l,m in product(J, repeat=4))==9
assert sum(not (B_support(0,j)^B_support(0,k)^B_support(1,l)^B_support(1,m))
           for j,k,l,m in product(J, repeat=4))==9
print("original direction center parity: all 81 mixed monomials vanish; A/B each retain 9 of 81")
commutator=qproduct(A,X,adj(A),adj(X))
covariance=tuple(tuple(integral(commutator[i]*commutator[j])[0]
                       for j in range(1,4)) for i in range(1,4))
assert covariance==tuple(tuple(Fraction(2,9) if i==j else 0 for j in J) for i in J)
print("direct commutator imaginary component covariance:",covariance)
