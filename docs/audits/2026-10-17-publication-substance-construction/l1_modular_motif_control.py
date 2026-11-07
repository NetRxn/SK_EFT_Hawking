"""Odd-prime signed cycle control on reviewed 16-site restricted motifs."""
from collections import defaultdict
from fractions import Fraction
from math import prod
import signal
from l1_extended_inter_sheet import DEN, centers, cycle_tables, setup
from l1_reduced_wedge_reference import wedge_sign

P=65537
def residue(v):
    return v.numerator*pow(v.denominator,-1,P)%P

def cycle(path,table):
    def oriented(reverse):
        return {(b,a) if reverse else (a,b):v%P for (a,b),v in table.items() if v%P}
    live=oriented(path[0][1])
    widths=[len(live)]
    for _,reverse in path[1:]:
        index=defaultdict(list)
        for (left,right),v in oriented(reverse).items():
            index[left].append((right,v))
        out=defaultdict(int)
        for (first,last),v in live.items():
            complement=255^last
            sign=wedge_sign(last,complement)
            for end,w in index[complement]:
                out[first,end]=(out[first,end]+sign*v*w)%P
        live={k:v for k,v in out.items() if v}
        widths.append(len(live))
    raw=sum(v*wedge_sign(b,a) for (a,b),v in live.items() if a^b==255)%P
    return raw*pow(DEN**len(path),-1,P)%P,widths

signal.alarm(40)
T=centers(True)
for flips,expected in [
    (set(),[Fraction(9995625,131072)]*4),
    ({0,6},[Fraction(21690819140625,34359738368)]+[Fraction(9995625,131072)]*2),
]:
    result=[cycle(path,T) for path in cycle_tables(setup(flips))]
    assert sorted(v for v,_ in result)==sorted(map(residue,expected))
    got=prod(v for v,_ in result)%P
    assert got==residue(prod(expected))
    print('restricted modular motif',sorted(flips),result,'full coefficient',got,flush=True)
large=Fraction(1057574865922986076396613,3696469150265516934764386546876416)
print('independent rational-to-residue target for 35084-orbit motif',residue(large))
signal.alarm(0)
