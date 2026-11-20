from fractions import Fraction
from functools import cache
from math import prod
from sympy.polys.domains import ZZ
from sympy.polys.rings import ring

R, *variables = ring(",".join(f"{name}{j}" for name in "ABXY" for j in range(4)), ZZ)
A, B, X, Y = (variables[k:k+4] for k in range(0,16,4))


def adj(q):
    return [q[0], *(-x for x in q[1:])]


def mul(q, r):
    a,b,c,d = q
    e,f,g,h = r
    # Quaternion convention U=q0 I−i q·σ. The Haar measure is unchanged
    # under sign reversal of all three vector coordinates.
    return [a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e]


def qproduct(*qs):
    accum = qs[0]
    for q in qs[1:]:
        accum = mul(accum,q)
    return accum


@cache
def haar_moment(powers):
    if any(p % 2 for p in powers):
        return Fraction(0)
    half = [p//2 for p in powers]
    numerator = prod(prod(range(1,2*k,2)) for k in half)
    denominator = prod(range(4,4+2*sum(half),2))
    return Fraction(numerator,denominator)


def integral(poly):
    value = Fraction(0)
    surviving = 0
    for powers, coef in poly.items():
        if any(p%2 for p in powers):
            continue
        surviving += 1
        value += int(coef)*prod(haar_moment(tuple(powers[k:k+4])) for k in range(0,16,4))
    return value, surviving


def run():
    q0 = qproduct(A,Y,adj(A),adj(X))
    q1 = qproduct(B,X,adj(B),adj(Y))
    # Direct vector-component squares. No sphere substitution 1−scalar²
    # or conditional averaging is used before expansion.
    r0 = sum(v*v for v in q0[1:])
    r1 = sum(v*v for v in q1[1:])
    r0r1 = r0*r1
    for name, p in (("r0",r0),("r1",r1),("r0r1",r0r1)):
        result, even = integral(p)
        print(name, "degree", max(map(sum,p)), "monomials",len(p),"even",even,"integral",result)
    both, _ = integral(r0r1)
    first, _ = integral(r0)
    second, _ = integral(r1)
    assert (first,second,both)==(Fraction(3,4),Fraction(3,4),Fraction(41,72))
    same = Fraction(9,4)*256*(2*both+2*first*second)
    diff = Fraction(9,4)*256*(4*first*second)
    assert (same,diff,(3*same+6*diff)/4)==(1304,1296,2922)
    print("same",same,"different",diff,"A contribution",(3*same+6*diff)/4)
    # An incorrect reuse of the same longitudinal link breaks the independence.
    poison_q = qproduct(A,X,adj(A),adj(Y))
    poison_sq = sum(v*v for v in poison_q[1:])
    changed, _ = integral(r0*poison_sq)
    assert changed != both
    print("shared-longitudinal-link poison",changed,"vs",both)
    rerun,_=integral(r0*r1)
    assert rerun == both
    print("original independent links repeat PASS")

if __name__ == "__main__":
    run()
