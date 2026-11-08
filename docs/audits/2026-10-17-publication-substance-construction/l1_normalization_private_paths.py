from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import prod
from l1_normalization_shared_transport import (
    TERMS,component_multisets,local_pair,pair,top_product,add,wedge,scale,translate,
)
from l1_normalization_six_transport import pairs,weights,shared_moment
from l1_normalization_six_mixed_chain import classify as mixed_chain
from l1_normalization_private_curvature import classify
from l1_normalization_transport_cycle import pattern

def plan_for(ii):
    labels=[TERMS[i][2] for i in sorted(set(ii))]
    slots=[]; use=defaultdict(list)
    for x,k,l,u,v in labels:
        ds=[d for d in range(4) if d not in (k,l)]
        for d,z in zip(ds,(u,v)):
            use[z,d].append(x)
        slots.append(tuple(zip(ds,(u,v))))
    plan=[]
    for x,row in enumerate(slots):
        plan.append(tuple((d,next((y for y in use[z,d] if y!=x),-1)) for d,z in row))
    return tuple(plan)

def canonical(plan):
    ans=[]
    for shift,swap in product(range(4),(False,True)):
        def site(x):
            return shift ^ ((((x&1)<<1)|((x&2)>>1)) if swap else x)
        rows=[None]*4
        for x,row in enumerate(plan):
            rows[site(x)]=tuple(sorted((2 if d>=2 else d^int(swap),site(y) if y>=0 else y) for d,y in row))
        ans.append(tuple(rows))
    return min(ans)

@cache
def shared_base():
    return shared_moment(0,0)

@cache
def link_moment(x,d):
    def move(z):
        return x ^ ((((z&1)<<1)|((z&2)>>1)) if d else z)
    return {k:translate(p,move) for k,p in shared_base().items()}

@cache
def graph_component(plan,nodes):
    @cache
    def local(x,d):
        return pair(x,d) if d<2 else local_pair(x)
    @cache
    def msg(x,parent):
        children=[(d,y) for d,y in plan[x] if y>=0 and y!=parent]
        attach={}
        for d,y in children:
            H=link_moment(x,d)
            C=msg(y,x)
            attach[y]={p:add(*(wedge(H[p,q],C[q]) for q in pairs)) for p in pairs}
        out={}
        for (p,q),w in weights.items():
            ps=[]
            slot=None
            for (d,y),tag in zip(plan[x],(p,q)):
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
            for d,z in plan[y]:
                if z>=0 and z not in cur:
                    queue.append(z);cur.add(z)
        assert sum(z>=0 for y in cur for d,z in plan[y])==2*(len(cur)-1)
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
    shared=sum(y>=0 for row in plan for _,y in row)//2
    private=8-2*shared
    return F(t,128**private*(96*8**4)**shared*16),tuple(map(len,ps))

def main():
    census=Counter()
    for comps in component_multisets():
        ii=[i for c in comps for i in c]
        if pattern(ii) is not None:continue
        reduced=classify(ii)
        if reduced is None:continue
        shape=tuple(sorted(map(len,comps)))
        seen=(max(shape)<=4 or (shape==(2,6) and mixed_chain(max(comps,key=len)) is not None))
        census[shape,seen,reduced.count('Haar'),canonical(plan_for(ii))]+=1
    print('cases',sum(census.values()),'unique plans',len({k[3] for k in census}),flush=True)
    totals=Counter();pop=Counter();maxterms=0
    for idx,((shape,seen,n,plan),count) in enumerate(census.items()):
        if idx%10==0:print("evaluating census entry",idx,"of",len(census),flush=True)
        z,sizes=scalar(plan)
        p=z*2**n*F(16,9)**(4-n)
        maxterms=max(maxterms,*sizes)
        totals[shape,seen]+=p*count;pop[shape,seen]+=count
    print('component cache',graph_component.cache_info(),'link cache',link_moment.cache_info(),'max exterior terms',maxterms)
    for k,n in sorted(pop.items()):print(k,'multisets',n,'exact signed sum',totals[k])
    print('additional multisets',sum(v for k,v in pop.items() if not k[1]),
          'additional coefficient',sum(v for k,v in totals.items() if not k[1]))
if __name__=='__main__':main()
