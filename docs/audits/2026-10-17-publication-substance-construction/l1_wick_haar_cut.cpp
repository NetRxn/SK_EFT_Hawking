#include <array>
#include <cassert>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
int P=65537,I=256;
using Key=uint32_t;
using Poly=unordered_map<Key,int>;
using Ext=unordered_map<uint16_t,Poly>;
using Mat=array<array<Poly,4>,4>;
int mod(long long x){return (x%P+P)%P;}
int powm(int x,int n){int a=1;for(;n;n>>=1,x=mod(1LL*x*x))if(n&1)a=mod(1LL*a*x);return a;}
void accumulate(Poly& a,Key k,long long v){
    if(!v)return;
    auto f=a.find(k);
    if(f==a.end()){int w=mod(v);if(w)a.emplace(k,w);}
    else {f->second=mod(f->second+v);if(!f->second)a.erase(f);}
}
void add(Poly& a,const Poly& b,int s=1){for(auto [k,v]:b)accumulate(a,k,1LL*s*v);}
void addprod(Poly& a,const Poly& b,const Poly& c,int s=1){
    for(auto [k,v]:b)for(auto [l,w]:c)accumulate(a,k+l,1LL*s*v*w);
}
void add(Ext& a,const Ext& b,int s=1){for(const auto& [k,v]:b)add(a[k],v,s);}
int sign(unsigned a,unsigned b){
    unsigned s=0;for(;a;a&=a-1){unsigned t=a&(-a);s^=popcount(b&(t-1))&1;}
    return s?-1:1;
}
Ext wedge(const Ext& a,const Ext& b){
    Ext c;
    for(const auto& [k,p]:a)if(!p.empty())for(const auto& [l,q]:b)if(!(k&l)&&!q.empty())
        addprod(c[k|l],p,q,sign(k,l));
    for(auto it=c.begin();it!=c.end();)if(it->second.empty())it=c.erase(it);else++it;
    return c;
}
Mat mm(const Mat&a,const Mat&b){
    Mat c;
    for(int i=0;i<4;++i)for(int j=0;j<4;++j)for(int k=0;k<4;++k)addprod(c[i][j],a[i][k],b[k][j]);
    return c;
}
Ext bil(const Mat&a,int x,int y){
    Ext b;
    for(int i=0;i<4;++i)for(int j=0;j<4;++j)if(!a[i][j].empty()){
        unsigned u=1u<<(8*x+i),v=1u<<(8*y+4+j);
        add(b[u|v],a[i][j],sign(u,v));
    }
    return b;
}
Mat g[4],g5,U[2][4],Ud[2][4];
int fwd(int x,int d){return d==0?x^1:x;}
void setup(int active_site,int active_axis,int seed,bool dense){
    int pauli[4][2][2]={{{0,1},{1,0}},{{0,-I},{I,0}},{{1,0},{0,-1}},{{1,0},{0,1}}};
    for(int a=0;a<4;++a)for(int i=0;i<2;++i)for(int j=0;j<2;++j){
        accumulate(g[a][i][j+2],0,(a==3?1:-I)*pauli[a][i][j]);
        accumulate(g[a][i+2][j],0,(a==3?1:I)*pauli[a][i][j]);
    }
    g5=mm(mm(g[0],g[1]),mm(g[2],g[3]));
    for(int x=0;x<2;++x)for(int a=0;a<4;++a)for(int c=0;c<2;++c){
        array<Poly,4> q;
        if(x==active_site&&a==active_axis){
            for(int j=0;j<4;++j)q[j][1u<<(4*(4*c+j))]=dense?2:1;
        } else {
            if(dense){
                unsigned u=(seed+1)*2654435761u+(x+1)*16777619u+(a+1)*1140071485u+(c+1)*3525937633u;
                for(int j=0;j<4;++j){u=u*1664525u+1013904223u;q[j][0]=(u>>31)?1:P-1;}
            } else {
                int idx=(seed+x*3+a*(c+1)+c)%4;
                q[idx][0]=(seed+x+a+c)%2?1:P-1;
            }
        }
        for(int i=0;i<2;++i)for(int j=0;j<2;++j){
            auto &u=U[x][a][2*c+i][2*c+j], &v=Ud[x][a][2*c+i][2*c+j];
            if(i==j){add(u,q[0]);add(v,q[0]);}
            for(int k=0;k<3;++k){
                add(u,q[k+1],-I*pauli[k][i][j]);add(v,q[k+1],I*pauli[k][i][j]);
            }
        }
    }
}
Ext t(int x,int d,int z,int a){
    int y=fwd(x,d);
    Ext r;
    if(x==y){
        add(r,bil(mm(g[a],Ud[x][d]),x,x));add(r,bil(mm(Ud[x][d],g[a]),x,x));
        add(r,bil(mm(g[a],U[x][d]),x,x),-1);add(r,bil(mm(U[x][d],g[a]),x,x),-1);
    } else if(z==x){
        r=bil(mm(g[a],Ud[x][d]),x,y);add(r,bil(mm(U[x][d],g[a]),y,x),-1);
    } else {
        r=bil(mm(Ud[z][d],g[a]),y,x);add(r,bil(mm(g[a],U[z][d]),x,y),-1);
    }
    return r;
}
pair<Ext,Ext> center(int x){
    Ext S,D;
    Ext T[4][2][4];
    for(int d=0;d<4;++d)for(int a=0;a<4;++a){
        T[d][0][a]=t(x,d,x,a);
        if(!d)T[d][1][a]=t(x,d,x^1,a);
        if(d>=2)add(D,wedge(T[d][0][a],T[d][0][a]),d==2?1:-1);
    }
    for(int k=0;k<4;++k)for(int l=k+1;l<4;++l){
        vector<int> axes;for(int d=0;d<4;++d)if(d!=k&&d!=l)axes.push_back(d);
        int mu=axes[0],nu=axes[1];
        Mat C=mm(mm(Ud[x][l],Ud[fwd(x,l)][k]),mm(U[fwd(x,k)][l],U[x][k]));
        int sg=(k+l-1)%2?-1:1;
        for(int a=0;a<4;++a)for(int b=0;b<4;++b)if(a!=b){
            Mat tr=mm(mm(C,mm(g[a],g[b])),g5);
            Poly coeff;
            for(int i=0;i<4;++i)add(coeff,tr[i][i]);
            if(coeff.empty())continue;
            for(int z=0;z<(mu==0?2:1);++z)for(int w=0;w<(nu==0?2:1);++w){
                auto v=wedge(T[mu][z][a],T[nu][w][b]);
                for(const auto& [mask,q]:v)addprod(S[mask],coeff,q,sg);
            }
        }
    }
    return {S,D};
}
size_t count(const Ext& e){size_t n=0;for(const auto& [_,p]:e)n+=p.size();return n;}
unordered_map<Key,int> moment_cache;
int haar(Key p){
    auto f=moment_cache.find(p);if(f!=moment_cache.end())return f->second;
    int n=1,den=1;
    for(int c=0;c<2;++c){
        int sum=0;
        for(int j=0;j<4;++j){
            int e=(p>>(4*(4*c+j)))&15;
            if(e&1){moment_cache[p]=0;return 0;}
            sum+=e;
            for(int k=1;k<e;k+=2)n=mod(1LL*n*k);
        }
        for(int k=0;k<sum;k+=2)den=mod(1LL*den*(4+k));
    }
    int out=mod(1LL*n*powm(den,P-2));
    moment_cache[p]=out;return out;
}
int haar_join(const Ext& A,const Ext& B,uint64_t& products){
    int total=0;
    for(const auto& [m,p]:A){
        auto it=B.find(m^65535);if(it==B.end())continue;
        int s=sign(m,m^65535);
        for(auto [k,v]:p)for(auto [l,w]:it->second){
            ++products;
            int z=haar(k+l);
            if(z)total=mod(total+1LL*s*v*w*z);
        }
    }
    return total;
}
int main(int argc,char** argv){
    int active=argc>1?stoi(argv[1]):2,seed=argc>2?stoi(argv[2]):1;
    bool dense=argc>3?stoi(argv[3]):false;
    if(argc>4)P=stoi(argv[4]);
    if(argc>5)I=stoi(argv[5]);
    setup(0,active,seed,dense);
    array<array<array<Ext,3>,5>,2> W;
    Ext S[2],D[2];
    int factorial[5]={1,1,2,6,24};
    for(int x=0;x<2;++x){
        auto [s,d]=center(x);
        S[x]=s;D[x]=d;
        W[x][0][0][0][0]=1;
        for(int n=0;n<=4;++n){
            if(n)W[x][n][0]=wedge(W[x][n-1][0],s);
            for(int h=1;h<=2&&n+h<=4;++h)W[x][n][h]=wedge(W[x][n][h-1],d);
            for(int h=0;h<=2&&n+h<=4;++h)
                cout<<"local "<<x<<' '<<n<<' '<<h<<" terms "<<count(W[x][n][h])<<endl;
        }
    }
    array<int,3> local{};
    for(int h=0;h<=2;++h){
        int val=0;
        uint64_t products=0;
        for(int i=0;i<=4-h;++i)for(int j=0;j<=h;++j){
            int n=4-h-i,k=h-j;
            int weight=powm(factorial[i]*factorial[n]*factorial[j]*factorial[k],P-2);
            val=mod(val+1LL*weight*haar_join(W[0][i][j],W[1][n][k],products));
        }
        local[h]=val;
        cout<<"coefficient "<<h<<' '<<val<<" products "<<products<<" moments "<<moment_cache.size()<<endl;
    }
    // Independent accumulation order: global exterior exp first, then Haar.
    Ext s=S[0],d=D[0];
    add(s,S[1]);add(d,D[1]);
    for(int h=0;h<=2;++h){
        Ext p0;p0[0][0]=1;
        for(int n=0;n<4-h;++n)p0=wedge(p0,s);
        for(int n=0;n<h;++n)p0=wedge(p0,d);
        int total=0;
        for(auto [k,v]:p0[65535])total=mod(total+1LL*haar(k)*v);
        total=mod(1LL*total*powm(factorial[4-h]*factorial[h],P-2));
        assert(total==local[h]);
        cout<<"global control "<<h<<' '<<total<<" top terms "<<p0[65535].size()<<endl;
    }
}
