// Exact determinant center for the leading mixed g1 g2^5 composite/dressed source.
// Build: c++ -std=c++20 -O3 l1_mixed_g1_determinant_tensor.cpp -o /tmp/l1-det
// Replay: /tmp/l1-det > /tmp/l1-det.rows
// Receipt: four populations of 12544, largest Gaussian component 128.
// Each row is packed coordinates, global Grassmann mask, real, imaginary.
// Coordinate digits from high to low: anchor0, anchor1, i0, i1, i2, i3.
// Each anchor is a bit; the i's are base-8 chiral quaternion coordinates.
// Anchor 0 is based at site 3, anchor 1 is at the adjacent site.
// Divide each row by 4^4 for the coframes and 4^2 for singleton Haar moments.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int P=65537; int I=256;
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
Mat g[4],U[4][4],Ud[4][4];
int epsilon(int k,int l,int m,int n){array<int,4>a={k,l,m,n};int s=1;for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)if(a[i]>a[j])s=-s;return s;}
void setup(int seed){
    array<array<array<int,2>,2>,4> pauli={{{{{0,1},{1,0}}},{{{0,P-I},{I,0}}},{{{1,0},{0,P-1}}},{{{1,0},{0,1}}}}};
    for(int a=0;a<4;a++)for(int i=0;i<2;i++)for(int j=0;j<2;j++){
        g[a][i][j+2]=mod(1LL*(a==3?1:-I)*pauli[a][i][j]);
        g[a][i+2][j]=mod(1LL*(a==3?1:I)*pauli[a][i][j]);
    }
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
Ext determinant(const array<int,5>& labels){
    const int x=labels[0];
    array<int,4> p{0,1,2,3};
    Ext out;
    do {
        auto a=wedge(tt(x,0,labels[1],p[0]),tt(x,1,labels[2],p[1]));
        auto b=wedge(tt(x,2,labels[3],p[2]),tt(x,3,labels[4],p[3]));
        merge(out,wedge(a,b),epsilon(p[0],p[1],p[2],p[3]));
    } while(next_permutation(p.begin(),p.end()));
    return out;
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

Mat basis[8],basis_dagger[8];
void bases(int imaginary){
    I=imaginary;
    setup(1);
    for(int j=0;j<8;j++){
        U[3][0]={};Ud[3][0]={};
        array<int,4> q{};q[j%4]=1;
        qblock(3,0,j/4,q);
        basis[j]=U[3][0];basis_dagger[j]=Ud[3][0];
    }
}
void setbasis(int site,int axis,int i){
    U[site][axis]=basis[i];Ud[site][axis]=basis_dagger[i];
}
using Key=uint64_t;
unordered_map<Key,int> tensor(int imaginary){
    bases(imaginary);
    unordered_map<Key,int> out;
    for(int a=0;a<2;a++)for(int b=0;b<2;b++){
        int u=a?2:3,v=b?1:3;
        for(int i=0;i<8;i++)for(int j=0;j<8;j++){
            setbasis(u,0,i);setbasis(v,1,j);
            for(int k=0;k<8;k++)for(int l=0;l<8;l++){
                setbasis(3,2,k);setbasis(3,3,l);
                for(auto [mask,z]:determinant({3,u,v,3,3}))if(z){
                    if(popcount(mask>>24)!=6 || popcount((mask>>8)&255)!=1
                       || popcount((mask>>16)&255)!=1 || (mask&255)!=0)
                        throw runtime_error("bad determinant mask");
                    if(k%4==0 || l%4==0)throw runtime_error("scalar self frame");
                    Key coords=((((a*2+b)*8+i)*8+j)*8+k)*8+l;
                    out[(coords<<32)|mask]=z;
                }
            }
        }
    }
    return out;
}
int centered(int n){n=mod(n);return n>P/2?n-P:n;}
void control(Key key){
    // Check E[q_k T(q)] using independent eight-node sphere quadrature.
    // Each Spin(4) link chooses q_L=e_i, q_R=±e_i; cross chirality vanishes.
    bases(256);
    Key c=key>>32;
    int r=c&7,q=(c>>3)&7,j=(c>>6)&7,i=(c>>9)&7;
    int u=(c&(2<<12))?2:3, v=(c&(1<<12))?1:3;
    setbasis(u,0,i);setbasis(v,1,j);
    setbasis(3,2,q);setbasis(3,3,r);
    auto expected=determinant({3,u,v,3,3});
    Ext accumulated;
    for(int i=0;i<4;i++)for(int j=0;j<4;j++)for(int s:{-1,1})for(int t:{-1,1}){
        U[3][2]=add(basis[i],basis[4+i],s);
        Ud[3][2]=add(basis_dagger[i],basis_dagger[4+i],s);
        U[3][3]=add(basis[j],basis[4+j],t);
        Ud[3][3]=add(basis_dagger[j],basis_dagger[4+j],t);
        int w=(i==q%4)*(j==r%4)*(q<4?1:s)*(r<4?1:t);
        if(w)merge(accumulated,determinant({3,u,v,3,3}),w);
    }
    merge(accumulated,expected,-4); // 64 nodes / Haar denominator 16.
    for(auto [mask,z]:accumulated)if(z)throw runtime_error("Haar control mismatch");
    size_t nonzero=0;for(auto [mask,z]:expected)nonzero+=bool(z);
    if(!nonzero)throw runtime_error("trivial Haar control");
    cerr<<"nonzero independent singleton Haar control "<<nonzero<<" masks\n";
}
array<int,8> coordinates(const Mat& m){
    array<int,8> q{};
    for(int j=0;j<2;j++){
        int c=2*j;
        q[4*j]=mod(32769LL*(m[c][c]+m[c+1][c+1]));
        q[4*j+1]=mod(128LL*(m[c][c+1]+m[c+1][c]));
        q[4*j+2]=mod(32769LL*(m[c+1][c]-m[c][c+1]));
        q[4*j+3]=mod(-128LL*(m[c+1][c+1]-m[c][c]));
    }
    return q;
}
void fixed_control(const unordered_map<Key,int>& tensor){
    I=256;
    setup(1);
    for(int a=0;a<2;a++)for(int b=0;b<2;b++){
        int u=a?2:3,v=b?1:3;
        auto x=coordinates(U[u][0]),y=coordinates(U[v][1]),
             z=coordinates(U[3][2]),w=coordinates(U[3][3]);
        Ext joined;
        for(auto [key,c]:tensor){
            Key k=key>>32;
            if((k>>12)!=unsigned(a*2+b))continue;
            int factor=mod(1LL*x[(k>>9)&7]*y[(k>>6)&7]);
            factor=mod(1LL*factor*z[(k>>3)&7]*w[k&7]);
            auto& t=joined[uint32_t(key)];
            t=mod(t+1LL*factor*c);
        }
        merge(joined,determinant({3,u,v,3,3}),-1);
        for(auto [mask,n]:joined)if(n)throw runtime_error("fixed-link reconstruction mismatch");
    }
    cerr<<"fixed-link reconstruction control all four anchor pairs\n";
}
int main(){
    auto plus=tensor(256),minus=tensor(P-256);
    fixed_control(plus);
    if(plus.empty())throw runtime_error("empty determinant tensor");
    control(plus.begin()->first);
    for(auto [key,z]:minus)plus.try_emplace(key,0);
    array<size_t,4> populations{};
    int bound=0;
    for(auto [key,p]:plus){
        int m=minus[key];
        int re=centered(mod(1LL*(p+m)*32769));
        // 512^-1 mod 65537 = -128.
        int im=centered(mod(-128LL*(p-m)));
        bound=max(bound,max(abs(re),abs(im)));
        // Unit basis gives long-frame L1 <= 4 and local-frame L1 <= 8.
        // The 24 determinant terms therefore have total L1 <= 24576.
        if(abs(re)>24576 || abs(im)>24576)throw runtime_error("ambiguous coefficient lift");
        if(!re&&!im)continue;
        Key c=key>>32;
        populations[c>>12]++;
        cout<<c<<" "<<uint32_t(key)<<" "<<re<<" "<<im<<"\n";
    }
    if(populations != array<size_t,4>{12544,12544,12544,12544} || bound!=128)
        throw runtime_error("determinant receipt mismatch");
    cerr<<"exact nonzero populations";for(auto n:populations)cerr<<" "<<n;
    cerr<<"; largest Gaussian component "<<bound<<"\n";
}
