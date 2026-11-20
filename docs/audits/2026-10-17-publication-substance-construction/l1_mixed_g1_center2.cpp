// Exact closed-order mixed-curvature tensor at site 2.
// Physical denominator: 192^2 * 4^2 * 4^4. Mode bits mark shared source/determinant links.
// Output: mode, source extended coordinate, determinant extended coordinate,
// source transverse coordinate, determinant transverse coordinate, mask, real, imag.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
#include <cassert>

struct G {
    std::int64_t r{}, i{};
    G& operator+=(G b) { r += b.r; i += b.i; return *this; }
    explicit operator bool() const { return r || i; }
};
G operator+(G a,G b) { return {a.r+b.r,a.i+b.i}; }
G operator-(G a) { return {-a.r,-a.i}; }
G operator*(G a,G b) { return {a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r}; }
G operator*(std::int64_t k,G a) { return {k*a.r,k*a.i}; }
using Mat=std::array<std::array<G,4>,4>;
using Ext=std::unordered_map<std::uint32_t,G>;
using Q=std::array<int,4>;

Mat mul(const Mat& a,const Mat& b) {
    Mat z{};
    for(int i=0;i<4;++i)for(int j=0;j<4;++j)for(int k=0;k<4;++k)z[i][j]+=a[i][k]*b[k][j];
    return z;
}
Mat add(const Mat& a,const Mat& b,int sign=1) {
    Mat z{};
    for(int i=0;i<4;++i)for(int j=0;j<4;++j)z[i][j]=a[i][j]+sign*b[i][j];
    return z;
}
int sign(std::uint32_t a,std::uint32_t b) {
    int n=0;
    while(a){auto bit=a&-a;n^=std::popcount(b&(bit-1))&1;a^=bit;}
    return n ? -1 : 1;
}
Ext wedge(const Ext& a,const Ext& b) {
    Ext z;
    for(auto [m,v]:a)if(v)for(auto [n,w]:b)if(w&&!(m&n))z[m|n]+=sign(m,n)*(v*w);
    return z;
}
void merge(Ext& a,const Ext& b,G s) {
    for(auto [m,v]:b)if(v)a[m]+=s*v;
}
Ext bil(const Mat& a,int x,int y) {
    Ext z;
    for(int i=0;i<4;++i)for(int j=0;j<4;++j)if(a[i][j]){
        auto p=1u<<(8*x+i),q=1u<<(8*y+4+j);
        z[p|q]=sign(p,q)*a[i][j];
    }
    return z;
}
Mat gam[4],g5,U[8],Ud[8];
G trace_kernel[6][4][4];
void setup(){
    const G one{1,0}, i{0,1}, zero{};
    const G pauli[3][2][2]={{{zero,one},{one,zero}},{{zero,-i},{i,zero}},{{one,zero},{zero,-one}}};
    for(int a=0;a<4;++a)for(int j=0;j<2;++j)for(int k=0;k<2;++k){
        gam[a][j][k+2]=a==3 ? (j==k ? one : zero) : -i*pauli[a][j][k];
        gam[a][j+2][k]=a==3 ? (j==k ? one : zero) : i*pauli[a][j][k];
    }
    g5=mul(mul(gam[0],gam[1]),mul(gam[2],gam[3]));
    for(int z=0;z<8;++z){
        const int ch=z/4, q=z%4;
        for(int j=0;j<2;++j)for(int k=0;k<2;++k){
            const int p=2*ch+j,t=2*ch+k;
            U[z][p][t]=q==0 ? (j==k?one:zero) : -i*pauli[q-1][j][k];
            Ud[z][p][t]=q==0 ? U[z][p][t] : -U[z][p][t];
        }
    }
    for(int j=0;j<6;++j)for(int a=0;a<4;++a)for(int b=0;b<4;++b){
        if(a==b)continue;
        const int coord=(j/3)*4+j%3+1;
        auto t=mul(mul(mul(U[coord],gam[a]),gam[b]),g5);
        for(int k=0;k<4;++k)trace_kernel[j][a][b]+=t[k][k];
    }
}
Q unit(int i){Q q{};q[i]=1;return q;}
Q dag(Q a){for(int i=1;i<4;++i)a[i]=-a[i];return a;}
Q qmul(Q a,Q b){
    auto [w,x,y,z]=a;auto [W,X,Y,Z]=b;
    return {w*W-x*X-y*Y-z*Z,w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X,w*Z+x*Y-y*X+z*W};
}
int moment4(int a,int b,int c,int d) {
    int n[8]{};
    ++n[a];++n[b];++n[c];++n[d];
    for(int x:n)if(x&1)return 0;
    int left=n[0]+n[1]+n[2]+n[3];
    if(left==2)return 12; // 192 * (1/4)^2
    for(int x:n)if(x==4)return 24; // 192 * 3/24
    return 8; // 192 * 1/24
}
struct Entry {int p, i, alpha, weight;};
std::vector<Entry> projected(bool shared,int external_t,int external_transverse) {
    std::vector<Entry> out;
    const int ch=external_transverse/4;
    const Q Y=unit(external_transverse%4);
    // A collapsed local frame annihilates the scalar coordinate.
    for(int p=1;p<4;++p)for(int i=0;i<8;++i)for(int alpha=0;alpha<3;++alpha){
        int z=0;
        for(int s=0;s<4;++s)for(int t=0;t<4;++t){
            int w=shared ? moment4(i,external_t,4*ch+s,4*ch+t)
                         : 12*(i==external_t && s==t);
            if(w){
                const Q q=qmul(qmul(dag(unit(p)),dag(unit(s))),qmul(Y,unit(t)));
                z+=w*q[alpha+1];
            }
        }
        if(z)out.push_back({4*ch+p,i,3*ch+alpha,z});
    }
    return out;
}
Ext longitudinal(int axis,bool shared,int coord,int a) {
    constexpr int x=2;
    const int y=x^(1<<axis);
    if(shared){
        Ext out=bil(mul(gam[a],Ud[coord]),x,y);
        merge(out,bil(mul(U[coord],gam[a]),y,x),{-1,0});
        return out;
    }
    Ext out=bil(mul(Ud[coord],gam[a]),y,x);
    merge(out,bil(mul(gam[a],U[coord]),x,y),{-1,0});
    return out;
}
Ext action(int axis,bool shared,int ext_coord,int local_coord,int alpha) {
    Ext out;
    const Mat delta=add(Ud[local_coord],U[local_coord],-1);
    for(int a=0;a<4;++a)for(int b=0;b<4;++b){
        const G c=trace_kernel[alpha][a][b];
        if(c){
            const Ext loc=bil(add(mul(gam[b],delta),mul(delta,gam[b])),2,2);
            merge(out,wedge(longitudinal(axis,shared,ext_coord,a),loc),c);
        }
    }
    return out;
}
int main(){
    setup();
    using Key=std::array<int,5>;
    std::map<Key,Ext> cache;
    auto piece=[&](int axis,bool shared,int ext,int local,int alpha)->const Ext&{
        Key k{axis,shared,ext,local,alpha};
        auto it=cache.find(k);
        if(it==cache.end())it=cache.emplace(k,action(axis,shared,ext,local,alpha)).first;
        return it->second;
    };
    std::size_t count=0;
    for(int mode=0;mode<4;++mode)for(int s=0;s<8;++s)for(int d=0;d<8;++d)
        for(int qsource=0;qsource<8;++qsource)for(int qdet=0;qdet<8;++qdet){
        const bool shs=mode&1,shd=mode&2;
        Ext out;
        const auto A=projected(shs,s,qsource),B=projected(shd,d,qdet);
        for(auto a:A)for(auto b:B){
            // Source curvature (1,2) uses the determinant-side frame and local 3.
            // Determinant curvature (0,3) uses the source-side frame and local 2.
            // Both world epsilon factors are +1 in this representative.
            const Ext& S=piece(0,shd,b.i,b.p,a.alpha);
            const Ext& D=piece(1,shs,a.i,a.p,b.alpha);
            merge(out,wedge(S,D),{a.weight*b.weight,0});
        }
        for(auto [mask,c]:out)if(c){
            assert(std::popcount(mask&255)==1);
            assert(std::popcount((mask>>8)&255)==0);
            assert(std::popcount((mask>>16)&255)==6);
            assert(std::popcount(mask>>24)==1);
            std::cout<<mode<<' '<<s<<' '<<d<<' '<<qsource<<' '<<qdet<<' '<<mask<<' '<<c.r<<' '<<c.i<<'\n';
            ++count;
        }
    }
    assert(count == 55296);
    std::cerr<<"center 2 rows "<<count<<'\n';
}
