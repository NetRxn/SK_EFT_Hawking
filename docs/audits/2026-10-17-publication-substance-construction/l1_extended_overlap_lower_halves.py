"""Exact lower column contraction after early upper-block complement pruning."""
from collections import defaultdict
from functools import cache
from itertools import product
from time import perf_counter
from l1_extended_overlap_mixed_frames import vertex
from l1_reduced_wedge_reference import wedge_sign

from l1_extended_overlap_upper_block import signed_lower_complements

def addg(out,key,r,i):
    a,b=out.get(key,(0,0))
    out[key]=a+r,b+i

def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]

@cache
def fixed(endpoint,alpha):
    out={}
    for q in (0,4):
        for k,(r,i) in vertex(endpoint,q,alpha).items():addg(out,k,r,i)
    return {k:z for k,z in out.items() if any(z)}

def fixed_pair():
    out=defaultdict(dict)
    for a,b in product(range(6),repeat=2):
        for m,z in fixed(0,a).items():
            for n,w in fixed(1,b).items():
                if m&n:continue
                r,i=mul(z,w);s=wedge_sign(m,n)
                addg(out[m|n],(a,b),s*r,s*i)
    return {m:{k:z for k,z in row.items() if any(z)} for m,row in out.items()}

def complement_project(pair, complements=None):
    U = signed_lower_complements() if complements is None else complements
    out=defaultdict(dict)
    tested=0
    for m,alpha in pair.items():
        for low,z in U.items():
            if m&low!=m:continue
            needed=low^m
            s=wedge_sign(m,needed)*z
            for k,(r,i) in alpha.items():addg(out[needed],k,s*r,s*i)
            tested+=1
    out={m:{k:z for k,z in row.items() if any(z)} for m,row in out.items()}
    out={m:row for m,row in out.items() if row}
    print('lower original × upper block',len(pair),'original masks',len(U),'upper complements',
          tested,'compatible mask pairs',len(out),'live mixed masks',
          sum(map(len,out.values())),'entries',flush=True)
    return out

def masksplit(mask):
    return tuple((mask>>s)&255 for s in (0,8,16,24))

def half_columns(K):
    index=defaultdict(list)
    for m,row in K.items():
        p,a,q,b=masksplit(m)
        index[p,q].append((a,b,row))
    halves=[]
    for endpoint in (0,1):
        H={}
        for alpha in range(6):
            for mask,z in fixed(endpoint,alpha).items():
                p,q,r,s=masksplit(mask)
                local,remote,upper=(p,q,r) if endpoint==0 else (q,p,s)
                assert (local.bit_count(),remote.bit_count(),upper.bit_count())==(2,1,1)
                for j in range(8):
                    incoming=1<<j
                    if incoming&local:continue
                    # Local vertex and incoming bit are ordered oppositely
                    # in the two blocks. The odd middle-byte swap of the
                    # standalone fixed pair cancels the endpoint-0 upper crossing.
                    sg=(wedge_sign(local,incoming) if endpoint==0
                        else wedge_sign(incoming,local))
                    for a,b,row in index.get((local|incoming,upper),()):
                        for (c,d),w in row.items():
                            re,im=mul(z,w)
                            key=(incoming,remote,a,b,alpha,c,d)
                            addg(H,key,sg*re,sg*im)
        halves.append({k:v for k,v in H.items() if any(v)})
    return halves

def direct_mask_control(P,K,H):
    # Independently reconstruct one A-endpoint mask's full six-alpha tensor
    # using both unsplit fixed vertices. Compare all retained gamma labels.
    i0=defaultdict(list);i1=defaultdict(list)
    for key,z in H[0].items():i0[key[2:4]].append((key,z))
    for key,z in H[1].items():i1[key[2:4]].append((key,z))
    assert i0 and i1
    for mask0,mask1 in [((7,16),(193,64))]:
        split={}
        for (incoming,outgoing,_,_,a,c,d),z in i0[mask0]:
            for (incoming2,outgoing2,_,_,b,e,f),w in i1[mask1]:
                if (incoming,outgoing)!=(outgoing2,incoming2):continue
                r,s=mul(z,w);addg(split,(a,b,c,d,e,f),r,s)
        unsplit={}
        pairs=[[],[]]
        for mask,row in K.items():
            a,b,c,d=masksplit(mask)
            for x,target in enumerate((mask0,mask1)):
                if (b,d)==target:pairs[x].append((a,c,row))
        for (a,c,K0),(b,d,K1) in product(*pairs):
            m=a|(b<<8)|(c<<16)|(d<<24)
            if m not in P:continue
            for (g,h),z in P[m].items():
                for (i,j),w in K0.items():
                    for (k,l),t in K1.items():
                        r,s=mul(mul(z,w),t)
                        addg(unsplit,(g,h,i,j,k,l),r,s)
        split={k:v for k,v in split.items() if any(v)}
        unsplit={k:v for k,v in unsplit.items() if any(v)}
        assert split==unsplit,(mask0,mask1,len(split),len(unsplit))
        if split:
            print('exact direct unsplit control',mask0,mask1,len(split),'nonzero alpha rows',flush=True)
            return
    raise AssertionError('no nonzero controls')

if __name__=='__main__':
    start=perf_counter()
    P=fixed_pair()
    K=complement_project(P)
    H=half_columns(K)
    direct_mask_control(P,K,H)
    for i,h in enumerate(H):
        print('factored half',i,'nonzero rows',len(h),
              'cross-bit channels',len({k[:2] for k in h}),
              'endpoint masks',len({k[2:4] for k in h}),
              'peak component',max(abs(x) for z in h.values() for x in z),flush=True)
    print("seconds", perf_counter() - start)
