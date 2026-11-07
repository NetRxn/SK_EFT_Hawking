"""Exact sparse four-center join, no modular arithmetic."""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import os
import subprocess
import sys
from l1_reduced_wedge_reference import wedge_sign

TOP=(1<<32)-1
DEN=4096*4608*(192**2*4**2*4**4)**2
AUDIT = Path(__file__).resolve().parent
GENERATORS = (
    "l1_mixed_g1_source0.py", "l1_mixed_g1_center1.py",
    "l1_mixed_g1_center2.cpp", "l1_mixed_g1_determinant_tensor.cpp",
)


def generate(directory):
    paths = []
    for name in GENERATORS:
        generator = AUDIT / name
        if generator.suffix == ".cpp":
            binary = directory / generator.stem
            subprocess.run(
                [os.environ.get("CXX", "c++"), "-std=c++20", "-O3",
                 str(generator), "-o", str(binary)], check=True,
            )
            command = [str(binary)]
        else:
            command = [sys.executable, str(generator)]
        path = directory / (generator.stem + ".rows")
        with path.open("w") as stream:
            subprocess.run(command, stdout=stream, check=True)
        paths.append(path)
    return paths


def read(path, n):
    rows=defaultdict(list)
    with path.open() as f:
        for line in f:
            data=tuple(map(int,line.split()))
            if n==3:
                c,m,r,i=data
                mode=c>>12
                a,b,y,z=((c>>shift)&7 for shift in (9,6,3,0))
            else:
                mode,a,b,y,z,m,r,i=data
            # Mode source and center = bit0+2*bit1. Determinant stored
            # as 2*axis0 anchor bit + axis1 anchor bit.
            rows[mode].append((a,b,y,z,m,r,i))
    assert sum(map(len, rows.values())) == (76800, 23936, 55296, 50176)[n]
    return dict(rows)

def index(rows,edge):
    out=defaultdict(list)
    for a,b,y,z,m,r,i in rows:
        match=(a,y) if edge==0 else (b,z)
        other=(b,z) if edge==0 else (a,y)
        out[match].append((*other,m,r,i))
    return out

def pair(left,le,right,re,swap=False):
    out={}
    L,R=index(left,le),index(right,re)
    for k,A in L.items():
        if k not in R:continue
        for a,y,m,r,i in A:
            for b,z,n,s,j in R[k]:
                if m&n:continue
                key=(b,z,a,y,m|n) if swap else (a,y,b,z,m|n)
                sign=wedge_sign(m,n)
                p,q=out.get(key,(0,0))
                out[key]=p+sign*(r*s-i*j),q+sign*(r*j+i*s)
    return {k:v for k,v in out.items() if any(v)}

def top(A,B):
    re=im=0
    matches=0
    for (a,y,b,z,m),(r,i) in A.items():
        v=B.get((a,y,b,z,TOP^m))
        if v is None:continue
        s,j=v
        sign=wedge_sign(m,TOP^m)
        re+=sign*(r*s-i*j);im+=sign*(r*j+i*s)
        matches+=1
    return re,im,matches

def replay(directory):
    S,C1,C2,D=(read(path, i) for i, path in enumerate(generate(directory)))
    total=0
    for s0,s1,t0,t1 in product(range(2),repeat=4):
        # s0/s1: shared at source edge to center1/center2, respectively.
        # t0/t1: shared at determinant edge to center2/center1.
        A=pair(S[s0+2*s1],0,C1[s0+2*t1],0)
        # Remaining boundary ordered (source-to-C2, C1-to-det).
        B=pair(C2[s1+2*t0],1,D[2*t0+t1],0)
        re,im,matches=top(A,B)
        assert not im
        f=Fraction(re,DEN)
        expected = Fraction(15, 16384) if s0 and t0 and t1 else 0
        assert f == expected
        total+=f
        print((s0,s1,t0,t1),'halves',len(A),len(B),'matches',matches,'coefficient',f,flush=True)
    assert total == Fraction(15,8192)
    print('sum representative transverse labels',total)
    print('weighted numerator at fixed composite site',-4*total)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: l1_mixed_g1_replay.py OUTPUT")
    destination = Path(sys.argv[1]).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    replay(destination)
