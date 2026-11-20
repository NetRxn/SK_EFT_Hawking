from l1_normalization_uniform_mixed_edge import edge
from l1_normalization_shared_transport import quat,adj,nodes,diag,gamma,bilinear,add,scale,wedge
from l1_direct_a_haar import mul,adj as qad

X=(1,1,-1,1,1,-1,-1,1)
Y=(1,-1,1,1,1,1,-1,-1)
E=edge()
for a,b,t,u in ((0,1,0,0),(0,4,0,3),(4,1,1,2),(4,5,3,3)):
    expected=add(*(scale(p,X[x[0]]*X[x[1]]*Y[y[0]]*Y[y[1]])
                   for (c,d,v,w,x,y),p in E.items() if (c,d,v,w)==(a,b,t,u)))
    ch,i=divmod(a,3);cb,j=divmod(b,3)
    xx=X[4*ch:4*ch+4];yy=Y[4*ch:4*ch+4]
    mean=-X[4*cb]*Y[4*cb+j+1]
    direct={}
    for l,r,w in nodes():
        q=(l,r)[ch]
        P=mul(mul(q,yy),mul(qad(q),qad(xx)))
        W=w*P[i+1]*mean
        if not W:continue
        U=diag(quat(l),quat(r));Ud=diag(quat(adj(l)),quat(adj(r)))
        g,h=gamma[t],gamma[u]
        T=add(bilinear(g*Ud,0,1),scale(bilinear(U*g,1,0),-1))
        S=add(bilinear(Ud*h,0,1),scale(bilinear(h*U,1,0),-1))
        direct=add(direct,scale(wedge(T,S),W))
    assert direct==scale(expected,32)
    print('conditional edge direct quartic control',a,b,t,u,'exterior terms',len(expected))
