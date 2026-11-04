"""Certified rational lift of both Gaussian-integer embeddings of the cut."""
from fractions import Fraction
from math import lcm,prod,isqrt
from subprocess import check_output
from sys import argv
from concurrent.futures import ThreadPoolExecutor

def sphere_denominator(n):
    return prod(range(4,4+n,2))
H=lcm(*(sphere_denominator(a)*sphere_denominator(b)
        for a in range(0,9,2) for b in range(0,9-a,2)))
scale=24*H
# Every scaled link has polynomial row l1 norm <=8. A coframe contributes
# <=4 matrix bilinears of norm <=4*8. Closed plaquette trace <=4*8^4.
# Eighteen labels, twelve gamma pairs each.
bound=scale*(18*12*(4*8**4)*(4*4*8)**2)**4
assert bound.bit_length()<=163
def prime(x):
    return all(x%d for d in range(3,isqrt(x)+1,2))
primes=[x for x in range(65537,65000,-4) if prime(x)]
while prod(primes[:11])<=2*bound:
    raise AssertionError("insufficient lift modulus")

def residues(p):
    root=next(i for i in range(1,p) if i*i%p==p-1)
    result=[]
    for r in (root,p-root):
        output=check_output([argv[1],"2","1","1",str(p),str(r)],text=True)
        result.append([int(s.split()[2]) for s in output.splitlines() if s.startswith('coefficient ')])
    a,b=result
    return p,[(scale*(x+y)*pow(2,-1,p)%p,scale*(x-y)*pow(2*root,-1,p)%p)
              for x,y in zip(a,b,strict=True)]
with ThreadPoolExecutor(max_workers=2) as executor:
    inputs=list(executor.map(residues,primes[:12]))
M=1
x=[[0,0] for _ in range(3)]
for p,values in inputs[:11]:
    for row,target in zip(x,values,strict=True):
        for i in range(2):
            row[i]+=M*((target[i]-row[i])*pow(M,-1,p)%p)
    M*=p
assert M>2*bound
p,check=inputs[-1]
assert all((v if v<=M//2 else v-M)%p==r for row,target in zip(x,check,strict=True)
           for v,r in zip(row,target,strict=True))
print('H',H,'scale',scale,'bound bits',bound.bit_length(),'CRT bits',M.bit_length(),'withheld',p)
for h,row in enumerate(x):
    row=[v if v<=M//2 else v-M for v in row]
    assert all(abs(v)<=bound for v in row)
    raw=[Fraction(v,scale) for v in row]
    unit=[v/2**(24-4*h) for v in raw]
    print(h,'raw',raw,'unit',unit)
