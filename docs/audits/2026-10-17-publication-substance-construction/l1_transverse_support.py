from itertools import product, combinations_with_replacement
dirs=(1,2,3)
ops=list(product('AB',range(2),dirs))
def site_bits(x, js):
    return sum(1<<(3*x+j-1) for j in js)
def data(op):
    k,x,j=op
    l,r={'A':(4,0),'B':(3,1),'H':(4,0),'D':(4,0),'S':(7,1)}[k]
    masks={'A':site_bits(x,dirs)^site_bits(1-x,[j]),'B':site_bits(x,[j]),'H':site_bits(x,[1,2]),'D':0,'S':site_bits(x,dirs)}
    return ((l,r) if x==0 else (r,l)),masks[k]
def survives(terms):
    parity=0
    n=[0,0]
    for t in terms:
        v,p=data(t); parity^=p
        for i in range(2): n[i]+=v[i]
    return n==[8,8] and parity==0
S=[('S',x,1) for x in range(2)]
for k in 'HD':
    src=(k,0,1)
    print('linear',k,'g1g2',[p for p in product(S,ops) if survives((src,)+p)],'g2^3',[p for p in combinations_with_replacement(ops,3) if survives((src,)+p)])
    for ell,y in product('HD',range(2)):
        print('quadratic',k,ell,y,'g1',[p for p in S if survives((src,(ell,y,1),p))],'g2^2',[p for p in combinations_with_replacement(ops,2) if survives((src,(ell,y,1))+p)])
