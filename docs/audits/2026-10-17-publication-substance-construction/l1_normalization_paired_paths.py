from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import prod,factorial
from l1_normalization_shared_transport import (
    TERMS,component_multisets,local_pair,pair,top_product,add,wedge,scale,translate,
)
from l1_normalization_transport_cycle import ORDERED as pairs, M as weights, edge_base
from l1_normalization_six_mixed_chain import classify as mixed_chain
from l1_normalization_paired_curvature import classify
from l1_normalization_transport_cycle import pattern

def plan_for(ii):
    labels=defaultdict(list)
    for i in ii:
        labels[TERMS[i][2][0]].append(TERMS[i][2])
    slots=[]
    for x in range(4):
        (_,k,l,u,v),(_,q,r,a,b)=labels[x]
        ds=[d for d in range(4) if d not in (k,l)]
        slots.append(dict(zip(ds,((u,a),(v,b)))))
    plan=[]
    for x,row in enumerate(slots):
        out=[]
        for d,(a,b) in row.items():
            if d>=2:
                assert a==b==x
                out.append((d,-1,0))
                continue
            y=x^(1<<d)
            c,f=slots[y].get(d,(-1,-1))
            if a==b:
                assert c==f
                out.append((d,y,1) if a==c else (d,-1,0))
            else:
                assert c!=f
                out.append((d,y,2))
        plan.append(tuple(out))
    return tuple(plan)

def canonical(plan):
    ans=[]
    for shift,swap in product(range(4),(False,True)):
        def site(x):
            return shift ^ ((((x&1)<<1)|((x&2)>>1)) if swap else x)
        rows=[None]*4
        for x,row in enumerate(plan):
            rows[site(x)]=tuple(sorted((2 if d>=2 else d^int(swap),site(y) if y>=0 else y,k) for d,y,k in row))
        ans.append(tuple(rows))
    return min(ans)

@cache
def link_moment(x,d,kind):
    def move(z):
        return x ^ ((((z&1)<<1)|((z&2)>>1)) if d else z)
    return {k:translate(p,move) for k,p in edge_base(kind).items()}

@cache
def graph_component(plan,nodes):
    @cache
    def local(x,d):
        return pair(x,d) if d<2 else local_pair(x)
    @cache
    def msg(x,parent):
        children=[(d,y,k) for d,y,k in plan[x] if y>=0 and y!=parent]
        attach={}
        for d,y,k in children:
            H=link_moment(x,d,k)
            C=msg(y,x)
            attach[y]={p:add(*(wedge(H[p,q],C[q]) for q in pairs)) for p in pairs}
        out={}
        for (p,q),w in weights.items():
            ps=[]
            slot=None
            for (d,y,k),tag in zip(plan[x],(p,q)):
                if y==parent and y>=0:
                    slot=tag
                elif y>=0:
                    ps.append(attach[y][tag])
                else:
                    ps.append(local(x,d)[tag[0]][tag[1]])
            g=ps[0] if len(ps)==1 else wedge(*ps)
            out[slot]=add(out.get(slot,{}),scale(g,w))
        return out
    return msg(nodes[0],-2)[None]

def parts(plan):
    used=set();out=[]
    for x in range(4):
        if x in used:continue
        queue=[x];cur={x}
        while queue:
            y=queue.pop()
            for d,z,k in plan[y]:
                if z>=0 and z not in cur:
                    queue.append(z);cur.add(z)
        assert sum(z>=0 for y in cur for d,z,k in plan[y])==2*(len(cur)-1)
        out.append(tuple(sorted(cur)));used.update(cur)
    return tuple(out)

@cache
def scalar(plan):
    part=parts(plan)
    ps=[graph_component(tuple(row if x in nodes else () for x,row in enumerate(plan)),nodes) for nodes in part]
    if len(ps)==1:
        c=ps[0].get((1<<32)-1)
        assert c is None or c.is_ground and c.const().y==0
        t=0 if c is None else int(c.const().x)
    else:
        t=top_product(ps)
    shared=sum(y>=0 for row in plan for _,y,_ in row)//2
    private=8-2*shared
    return F(t,128**private*(96*8**4)**shared),tuple(map(len,ps))

def main():
    census=Counter()
    for comps in component_multisets():
        ii=[i for c in comps for i in c]
        if pattern(ii) is not None or len(set(ii))==4:continue
        reduced=classify(ii)
        if reduced is None:continue
        shape=tuple(sorted(map(len,comps)))
        seen=(max(shape)<=4 or (shape==(2,6) and mixed_chain(max(comps,key=len)) is not None))
        census[shape,seen,reduced.count('Haar'),canonical(plan_for(ii)),prod(factorial(n) for n in Counter(ii).values())]+=1
    print('cases',sum(census.values()),'unique plans',len({k[3] for k in census}),flush=True)
    totals=Counter();pop=Counter();maxterms=0
    for idx,((shape,seen,n,plan,factor),count) in enumerate(census.items()):
        if idx%10==0:print("evaluating census entry",idx,"of",len(census),flush=True)
        z,sizes=scalar(plan)
        p=z*2**n*F(16,9)**(4-n)/factor
        maxterms=max(maxterms,*sizes)
        totals[shape,seen]+=p*count;pop[shape,seen]+=count
    print('component cache',graph_component.cache_info(),'link cache',link_moment.cache_info(),'max exterior terms',maxterms)
    for k,n in sorted(pop.items()):print(k,'multisets',n,'exact signed sum',totals[k])
    print('additional multisets',sum(v for k,v in pop.items() if not k[1]),
          'additional coefficient',sum(v for k,v in totals.items() if not k[1]))
if __name__=='__main__':main()
