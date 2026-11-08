"""Exact mixed-column contraction, reweighting verified baseline blocks when proportional."""
from fractions import Fraction
from inspect import getsource
import l1_extended_overlap_scheduler as scheduler
from sys import argv
from time import perf_counter
from l1_extended_overlap_run_orbits import temporal_parity
from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import assignments,exterior,jobs,kernel,left,right

namespace = dict(vars(scheduler))
exec(getsource(kernel).replace("<= 3264","<= 9792"),namespace)
kernel = namespace["kernel"]

ordinary=exterior(argv[1])
modified=exterior(argv[2])
plan=list(selected(jobs(ordinary)))
assert len(plan)==35084
assert modified.keys()==ordinary.keys()
ratios={}
for k,rows in ordinary.items():
    other=modified[k]
    assert len(rows)==len(other)
    alpha0,r0=rows[0]
    alpha1,r1=other[0]
    assert alpha0==alpha1
    assert all(a==b for (a,_),(b,_) in zip(rows,other))
    if all(y*r0==x*r1 for (_,x),(_,y) in zip(rows,other)):
        ratios[k]=Fraction(r1,r0)
baseline={}
for path in argv[5:]:
    for line in open(path):
        n,w,c,l,v,_=line.split()
        assert int(n) not in baseline
        baseline[int(n)]=(int(w),int(c),int(l),int(v))
assert baseline.keys() == set(range(len(plan)))
pending=0
for index in range(int(argv[3]),int(argv[4])):
    (a,b,c,s,q,t,r),weight=plan[index]
    bw,bc,bl,bv=baseline[index]
    assert weight==bw and bc==len(modified[s,q])*len(ordinary[t,r])
    if not (temporal_parity(s) and temporal_parity(t)):
        assert bv==0
        print(index,weight,bc,bl,0,0.0,'parity',flush=True)
        continue
    ratio=ratios.get((s,q))
    if ratio is not None:
        value=ratio*bv
        assert value.denominator==1
        print(index,weight,bc,bl,int(value),0.0,'proportional',flush=True)
        continue
    pending+=1
    if __import__('os').environ.get('L1_COUNT_ONLY'):
        continue
    started=perf_counter()
    value,count,live,_=kernel(left(a,b),right(c,assignments(q,r,s[5],t[5]),s[7]),
                               modified[s,q],ordinary[t,r])
    assert count==bc
    print(index,weight,count,live,value,perf_counter()-started,'exact',flush=True)
print('nonproportional jobs',pending,file=__import__('sys').stderr,flush=True)
