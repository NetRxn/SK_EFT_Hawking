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

using Boundary=array<int,784>;
int powm(int a,int n){int t=1;for(;n;n>>=1,a=mod(1LL*a*a))if(n&1)t=mod(1LL*t*a);return t;}
array<int,256> masks(){array<int,256> x{};x.fill(-1);int k=0;for(unsigned m=0;m<256;m++)if(popcount(m)==2)x[m]=k++;return x;}
const auto mindex=masks();
Boundary block(int x){
    auto a=action({x,0,2,x,x});
    auto b=action({x,1,2,x,x});
    auto c=action({x,2,3,x,x});
    auto ab=wedge(a,b);
    Boundary out{};
    const uint32_t center=255u<<(8*x);
    for(auto [u,v]:ab)if(v)for(auto [w,z]:c)if(z&&!(u&w)){
        uint32_t f=u|w;
        if((f&center)!=center)continue;
        int i=mindex[f&255],j=mindex[f>>24];
        if(i<0||j<0)continue;
        int at=28*i+j;
        out[at]=mod(out[at]+1LL*sign(u,w)*v*z);
    }
    return out;
}
void put(int x,int d,const array<int,4>& l,const array<int,4>& r){
    qblock(x,d,0,l);qblock(x,d,1,r);
}
void basis(int x,int d,int i){
    array<int,4> l{},r{};
    (i<4?l[i]:r[i-4])=1;
    put(x,d,l,r);
}
struct Node {array<int,4> l,r; int w;};
vector<Node> quartic_nodes(){
    vector<Node> nodes;
    array<int,4> zero{};
    int q24=powm(24,P-2),q4=powm(4,P-2),q32=powm(32,P-2);
    // Pure fourth: S3 degree-four rule. Subtract axis projections used
    // by the mixed part. Global sign can be removed in homogeneous degree four.
    for(int j=0;j<4;j++){
        array<int,4> l{};l[j]=1;
        int w=mod(2*q24-q4);
        nodes.push_back({l,zero,w});nodes.push_back({zero,l,w});
    }
    for(int k=0;k<8;k++){
        array<int,4> l{};l[0]=32769;
        for(int j=1;j<4;j++)l[j]=(k&(1<<(j-1)))?32769:32768;
        nodes.push_back({l,zero,mod(2*q24)});nodes.push_back({zero,l,mod(2*q24)});
    }
    for(int j=0;j<4;j++)for(int k=0;k<4;k++)for(int s:{-1,1}){
        array<int,4> l{},r{};l[j]=1;r[k]=mod(s);
        nodes.push_back({l,r,q32});
    }
    return nodes;
}
Boundary integrate_link(int x, int axis, const vector<Node>& nodes,int axis2=-1){
    Boundary result{};
    for(auto& n:nodes){
        put(x,axis,n.l,n.r);
        auto b=axis2<0?block(x):integrate_link(x,axis2,nodes);
        for(int i=0;i<784;i++) result[i]=mod(result[i]+1LL*n.w*b[i]);
    }
    return result;
}
int matrix_rank(vector<Boundary> a){
    int r=0;
    for(int j=0;j<784 && r<a.size();j++){
        int p=r;while(p<a.size() && !a[p][j])p++;
        if(p==a.size())continue;
        swap(a[p],a[r]);int inv=powm(a[r][j],P-2);
        for(int i=r+1;i<a.size();i++)if(a[i][j]){
            int s=mod(-1LL*a[i][j]*inv);
            for(int k=j;k<784;k++)a[i][k]=mod(a[i][k]+1LL*s*a[r][k]);
        }
        r++;
    }
    return r;
}
int main(int argc,char**argv){
    int x=argc>1?stoi(argv[1]):1;
    int axis=argc>2?stoi(argv[2]):0;
    int axis2=argc>3?stoi(argv[3]):-1;
    setup(1);
    auto nodes=quartic_nodes();
    vector<Boundary> fix,part;
    for(int a=0;a<8;a++)for(int b=0;b<8;b++){
        basis(0,2,a);basis(3,2,b);
        // integrate_link() mutates one internal link. Restore the fixed link before
        // each evaluation so all fixed slices use the same rational sample.
        setup(1);basis(0,2,a);basis(3,2,b);
        fix.push_back(block(x));
        part.push_back(integrate_link(x,axis,nodes,axis2));
    }
    auto count=[](const vector<Boundary>& m){int n=0;for(auto& b:m)for(int v:b)n+=(v!=0);return n;};
    cout<<"center "<<x<<" axis "<<axis<<" cubature nodes "<<nodes.size()<<"\n";
    cout<<"fixed matrix nonzeros "<<count(fix)<<" rank "<<matrix_rank(fix)<<"\n";
    cout<<"projected matrix nonzeros "<<count(part)<<" rank "<<matrix_rank(part)<<"\n";
}
