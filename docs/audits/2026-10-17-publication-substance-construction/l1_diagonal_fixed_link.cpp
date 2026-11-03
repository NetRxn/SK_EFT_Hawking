#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int P=65537, I=256;
int mod(long long n) {return (n%P+P)%P;}
using Mat=array<array<int,4>,4>;
using Ext=unordered_map<uint32_t,int>;
Mat unit(){Mat m{};for(int i=0;i<4;i++)m[i][i]=1;return m;}
Mat mul(Mat a,Mat b){Mat c{};for(int i=0;i<4;i++)for(int j=0;j<4;j++)for(int k=0;k<4;k++)c[i][j]=mod(c[i][j]+1LL*a[i][k]*b[k][j]);return c;}
Mat add(Mat a,Mat b,int s=1){for(int i=0;i<4;i++)for(int j=0;j<4;j++)a[i][j]=mod(a[i][j]+s*b[i][j]);return a;}
int sign(uint32_t a,uint32_t b){unsigned n=0;for(;a;a&=a-1){auto t=a&(-a);n^=popcount(b&(t-1))&1;}return n?-1:1;}
void merge(Ext &a,const Ext &b,int s=1){for(auto [u,v]:b)a[u]=mod(a[u]+1LL*s*v);}
Ext wedge(const Ext&a,const Ext&b){Ext c;for(auto [u,v]:a)if(v)for(auto [w,z]:b)if(z&&!(u&w))c[u|w]=mod(c[u|w]+1LL*sign(u,w)*v*z);return c;}
Ext bil(Mat a,int x,int y){Ext b;for(int i=0;i<4;i++)for(int j=0;j<4;j++)if(a[i][j]){uint32_t u=1u<<(8*x+i),v=1u<<(8*y+4+j);b[u|v]=mod(sign(u,v)*a[i][j]);}return b;}
int fwd(int x,int d){return d<2?x^(1<<d):x;}
Mat g[4],g5,U[4][4],Ud[4][4];
int epsilon(int k,int l,int m,int n){array<int,4>a={k,l,m,n};int s=1;for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)if(a[i]>a[j])s=-s;return s;}
void setup(int seed){
    array<array<array<int,2>,2>,4> pauli={{{{{0,1},{1,0}}},{{{0,P-I},{I,0}}},{{{1,0},{0,P-1}}},{{{1,0},{0,1}}}}};
    for(int a=0;a<4;a++)for(int i=0;i<2;i++)for(int j=0;j<2;j++){
        g[a][i][j+2]=mod((a==3?1:-I)*pauli[a][i][j]);
        g[a][i+2][j]=mod((a==3?1:I)*pauli[a][i][j]);
    }
    g5=mul(mul(g[0],g[1]),mul(g[2],g[3]));
    // Distinct rational unit quaternions mod P by stereographic parameterization.
    auto powm=[](int a,int n){int t=1;for(;n;n>>=1,a=mod(1LL*a*a))if(n&1)t=mod(1LL*t*a);return t;};
    unsigned s=seed;
    for(int x=0;x<4;x++)for(int d=0;d<4;d++){
        U[x][d]={};Ud[x][d]={};
        for(int c=0;c<2;c++){
            int q[4]={};int norm=0;
            for(int j=1;j<=3;j++){s=s*1664525u+1013904223u;q[j]=(s>>16)%61+1;norm+=q[j]*q[j];}
            int den=powm(norm+1,P-2);q[0]=mod(1LL*(1-norm)*den);
            for(int j=1;j<=3;j++)q[j]=mod(2LL*q[j]*den);
            for(int i=0;i<2;i++)for(int j=0;j<2;j++){
                int v=0;for(int a=0;a<3;a++)v=mod(v-1LL*I*q[a+1]*pauli[a][i][j]);
                U[x][d][2*c+i][2*c+j]=mod((i==j?q[0]:0)+v);
                Ud[x][d][2*c+i][2*c+j]=mod((i==j?q[0]:0)-v);
            }
        }
    }
}
Ext tt(int x,int d,int z,int a){
    int y=fwd(x,d);
    if(x==y){Mat delta=add(Ud[x][d],U[x][d],-1);return bil(add(mul(g[a],delta),mul(delta,g[a])),x,x);}
    Ext r;
    if(z==x){r=bil(mul(g[a],Ud[x][d]),x,y);merge(r,bil(mul(U[x][d],g[a]),y,x),-1);}
    else {r=bil(mul(Ud[z][d],g[a]),y,x);merge(r,bil(mul(g[a],U[z][d]),x,y),-1);}
    return r;
}
Ext source(int x){
    Ext r;for(int d=2;d<4;d++)for(int a=0;a<4;a++){
        Ext t=tt(x,d,x,a);merge(r,wedge(t,t),d==2?1:-1);}
    return r;
}
Ext action(array<int,5> l){
    auto [x,k,n,u,v]=l;
    vector<int> a;for(int d=0;d<4;d++)if(d!=k&&d!=n)a.push_back(d);
    Mat p=mul(mul(U[x][k],U[fwd(x,k)][n]),mul(Ud[fwd(x,n)][k],Ud[x][n]));
    Ext r;
    for(int c=0;c<4;c++)for(int d=0;d<4;d++)if(c!=d){
        Mat m=mul(mul(p,mul(g[c],g[d])),g5);
        int z=0;for(int j=0;j<4;j++)z=mod(z+m[j][j]);
        merge(r,wedge(tt(x,a[0],u,c),tt(x,a[1],v,d)),epsilon(k,n,a[0],a[1])*z);
    }
    return r;
}
int eval(const array<array<int,5>,6>& labels, bool verbose){
    vector<Ext> factors={source(0),source(3)};
    for(auto l:labels)factors.push_back(action(l));
    Ext a=wedge(wedge(factors[0],factors[2]),wedge(factors[3],factors[4]));
    Ext b=wedge(wedge(factors[1],factors[5]),wedge(factors[6],factors[7]));
    int t=0;for(auto [u,v]:a){auto w=~u;auto it=b.find(w);if(it!=b.end())t=mod(t+1LL*sign(u,w)*v*it->second);}
    if(verbose)cout<<"half support "<<a.size()<<" "<<b.size()<<"; scaled top residue "<<t<<"\n";
    return t;
}
void qblock(int x,int d,int c,const array<int,4>& q){
    int v[2][2]={{q[0],0},{0,q[0]}};
    v[0][0]=mod(q[0]-I*q[3]);v[1][1]=mod(q[0]+I*q[3]);
    v[0][1]=mod(-I*q[1]-q[2]);v[1][0]=mod(-I*q[1]+q[2]);
    for(int i=0;i<2;i++)for(int j=0;j<2;j++){
        U[x][d][2*c+i][2*c+j]=v[i][j];
        Ud[x][d][2*c+i][2*c+j]=mod((i==j?2*q[0]:0)-v[i][j]);
    }
}
int main(int argc,char **argv){
    int seed=argc>1?stoi(argv[1]):1;setup(seed);
    array<array<int,5>,6> labels;
    for(auto &l:labels)for(int &v:l)if(!(cin>>v))return 2;
    eval(labels,true);
    if(argc<=3)return 0;
    int x=stoi(argv[2]),d=stoi(argv[3]);
    vector<array<int,4>> nodes;
    for(int j=0;j<4;j++)for(int s : {-1,1}){array<int,4> v{};v[j]=mod(s);nodes.push_back(v);}
    for(int k=0;k<16;k++){array<int,4> v{};for(int j=0;j<4;j++)v[j]=(k&(1<<j))?32769:32768;nodes.push_back(v);}
    int t=0; for(auto l:nodes)for(auto r:nodes){qblock(x,d,0,l);qblock(x,d,1,r);t=mod(t+eval(labels,false));}
    // 576^-1 modulo P.
    int inv=1;while(mod(576LL*inv)!=1)inv++;
    cout<<"integrated-link "<<x<<" "<<d<<"; exact cubature residue "<<mod(1LL*t*inv)<<"\n";
}
