"""Independent direct quartic cubature for complete mixed frames."""
from collections import Counter
from itertools import product
from l1_extended_overlap_mixed_frames import projected,L
from l1_normalization_opposed_fourth import nodes
from l1_normalization_disjoint_sector import quat,adj
from l1_equal_time_int_contract import sparse_int
from l1_direct_b_haar import R,diag,gamma,bilinear,add,scale,wedge

def vertex(U,Ud,x,a):
    out={}
    for (g,h),terms in L.items():
        for alpha,w in terms:
            if alpha!=a:continue
            G,H=gamma[g],gamma[h]
            if x==0:
                t=add(bilinear(G*Ud,0,1),scale(bilinear(U*G,1,0),-1))
            else:
                t=add(bilinear(Ud*G,0,1),scale(bilinear(G*U,1,0),-1))
            fixed=add(bilinear(H,x,x+2),scale(bilinear(H,x+2,x),-1))
            out=add(out,scale(wedge(t,fixed),-w))
    return out

def direct(p,a,b):
    out={}
    for l,r,w in nodes():
        q=tuple(l)+tuple(r)
        f=w*q[p[0]]*q[p[1]]
        if not f:continue
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        out=add(out,scale(wedge(vertex(U,Ud,0,a),vertex(U,Ud,1,b)),f))
    return {m:(r,i) for m,(r,i) in sparse_int(out).items() if r or i}

if __name__=='__main__':
    _,P=projected()
    for p in ((0,0),(0,1),(0,4),(2,7),(5,5)):
        row=P[p]
        a,b,_=next(iter(row))[:3]
        observed=direct(p,a,b)
        keys={k[2] for k in row if k[:2]==(a,b)}
        expected={m:(32*row.get((a,b,m,0),0),32*row.get((a,b,m,1),0)) for m in keys}
        assert observed==expected
        print(p,(a,b),len(keys),'nonzero exact masks',flush=True)
