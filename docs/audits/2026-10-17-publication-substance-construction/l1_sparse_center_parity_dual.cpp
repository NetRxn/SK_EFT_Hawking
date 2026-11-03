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
Mat g[4],g5,U[4][4],Ud[4][4];
int epsilon(int k,int l,int m,int n){array<int,4>a={k,l,m,n};int s=1;for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)if(a[i]>a[j])s=-s;return s;}
void setup(int seed){
    array<array<array<int,2>,2>,4> pauli={{{{{0,1},{1,0}}},{{{0,P-I},{I,0}}},{{{1,0},{0,P-1}}},{{{1,0},{0,1}}}}};
    for(int a=0;a<4;a++)for(int i=0;i<2;i++)for(int j=0;j<2;j++){
        g[a][i][j+2]=mod((a==3?1LL:-1LL*I)*pauli[a][i][j]);
        g[a][i+2][j]=mod((a==3?1LL:1LL*I)*pauli[a][i][j]);
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

#include <chrono>
#include <unordered_set>
using Term=pair<uint32_t,int>;
using Poly=unordered_map<uint32_t,unordered_map<uint32_t,int>>; // mask -> packed coordinate monomial -> coefficient
Mat Q[8],Qd[8];
Ext ts[4][4][8];
int pack(const array<int,4>& a){return a[0]|a[1]<<6|a[2]<<12|a[3]<<18;}
int tracecoef(const Mat& p,int c,int d){
    auto z=mul(mul(p,mul(g[c],g[d])),g5);
    int t=0;for(int i=0;i<4;i++)t=mod(t+z[i][i]);return t;
}
Poly build(int k,int l,int ex0,int ex1,uint32_t allowed){
    vector<int> ts_axes;for(int a=0;a<4;a++)if(a!=k&&a!=l)ts_axes.push_back(a);
    int u=ts_axes[0],v=ts_axes[1];
    Poly result;
    int s=epsilon(k,l,u,v);
    // Curvature and T slots on distinct directions in each factor.
    for(int a=0;a<8;a++)for(int b=0;b<8;b++)for(int j=0;j<8;j++)for(int h=0;h<(k<2?1:8);h++){
        Mat p;
        array<int,4> q{};
        q[k]=a*8+b;
        if(k<2){
            p=mul(mul(Q[a],Q[k==0?ex0:ex1]),mul(Qd[b],Qd[j]));
            q[l]=j;
        } else {
            p=mul(mul(Q[a],Q[j]),mul(Qd[b],Qd[h]));
            q[l]=j*8+h;
        }
        for(int c=0;c<4;c++)for(int d=0;d<4;d++)if(c!=d){
            int t=tracecoef(p,c,d);
            if(!t)continue;
            for(int i=0;i<8;i++)if(!ts[u][c][i].empty())for(int j2=0;j2<8;j2++)if(!ts[v][d][j2].empty()){
                q[u]=i;q[v]=j2;
                uint32_t key=pack(q);
                for(auto [x,f]:ts[u][c][i])for(auto [y,r]:ts[v][d][j2])if(!(x&y)&&!((x|y)&~allowed)){
                    auto& z=result[x|y][key];
                    z=mod(z+1LL*s*t*sign(x,y)*f*r);
                }
            }
        }
    }
    return result;
}
int invm(int a){int t=1;for(int n=P-2;n;n>>=1,a=mod(1LL*a*a))if(n&1)t=mod(1LL*t*a);return t;}
int moment[64][8][8];
int fourth(int a,int b,int c,int d){
    array<int,8> n{};for(int x:{a,b,c,d})n[x]++;
    for(auto v:n)if(v&1)return 0;
    for(auto v:n)if(v==4)return invm(8);
    int l=n[0]+n[1]+n[2]+n[3];
    return invm(l==2?16:24);
}
int coeff(uint32_t a,uint32_t b,uint32_t c, int mode){
    long long value=1;
    for(int j=0;j<4;j++)if(mode<0||mode&(1<<j)){
        int qa=(a>>(6*j))&63,qb=(b>>(6*j))&63,qc=(c>>(6*j))&63;
        int w=j==0?moment[qa][qb][qc]:j==1?moment[qb][qa][qc]:moment[qc][qa][qb];
        if(!w)return 0;
        value=mod(value*w);
    }
    return int(value);
}
int main(int argc,char**argv){
    int ex0=argc>1?stoi(argv[1]):0,ex1=argc>2?stoi(argv[2]):1;
    uint32_t m0=argc>3?stoi(argv[3]):3,m3=argc>4?stoi(argv[4]):192;
    uint32_t allowed=0xFF00FFFF;
    auto parity=[](int q,int k,int l){
        uint32_t mask=0;
        for(int j=0;j<4;j++){
            int m=(q>>(6*j))&63;
            uint32_t z=(j==k||(k==2&&j==l))?((1u<<(m/8))^(1u<<(m%8))):(1u<<m);
            mask|=z<<(8*j);
        }
        return mask;
    };
    array<unordered_set<uint32_t>,3> support;
    array<unordered_map<uint32_t,unordered_set<uint32_t>>,3> masked;
    for(int embed:{256,65281}){
        I=embed;
    setup(1);
    array<array<int,8>,4> sample{};
    for(int j=0;j<4;j++)for(int ch=0;ch<2;ch++){
        int o=2*ch;
        auto& M=U[1][j];
        sample[j][4*ch+0]=mod((M[o][o]+M[o+1][o+1])*1LL*invm(2));
        sample[j][4*ch+1]=mod((M[o][o+1]+M[o+1][o])*1LL*invm(mod(-2*I)));
        sample[j][4*ch+2]=mod((M[o+1][o]-M[o][o+1])*1LL*invm(2));
        sample[j][4*ch+3]=mod((M[o+1][o+1]-M[o][o])*1LL*invm(mod(2*I)));
    }
    for(int i=0;i<8;i++){
        array<int,4> l{},r{};(i<4?l[i]:r[i-4])=1;
        qblock(1,0,0,l);qblock(1,0,1,r);
        Q[i]=U[1][0];Qd[i]=Ud[1][0];
        for(int a=0;a<4;a++)for(int c=0;c<4;c++){
            U[1][a]=Q[i];Ud[1][a]=Qd[i];
            ts[a][c][i]=tt(1,a,1,c);
            for(auto it=ts[a][c][i].begin();it!=ts[a][c][i].end();)
                if(it->first&~allowed)it=ts[a][c][i].erase(it);else ++it;
        }
    }
    for(int a=0;a<64;a++)for(int b=0;b<8;b++)for(int c=0;c<8;c++)moment[a][b][c]=fourth(a/8,a%8,b,c);
    for(int k=0;k<3;k++)for(int e=0;e<(k==2?1:8);e++){
        int l=k==2?3:2;
        auto p=build(k,l,e,e,allowed);
        for(auto& [m,ps]:p)for(auto [q,v]:ps)if(v){
            auto z=parity(q,k,l);
            support[k].insert(z);
            masked[k][z].insert(m|(e<<16));
        }
    }
    }
    cout<<"unconditioned parity sizes "<<support[0].size()<<" "<<support[1].size()<<" "<<support[2].size()<<endl;
    uint64_t matches=0,matches_mask=0;
    unordered_set<uint32_t> slices;
    for(auto a:support[0])for(auto b:support[1])if(support[2].contains(a^b)){
        matches++;
        for(auto akey:masked[0][a])for(auto bkey:masked[1][b]) {
            uint32_t ma=akey&allowed,mb=bkey&allowed;
            if(ma&mb)continue;
            for(auto mc:masked[2][a^b])if(!((ma|mb)&mc)){
                auto m=ma|mb|mc;
                if((m&0xFF00)==0xFF00&&popcount(m&255)==2&&popcount(m>>24)==2){
                    matches_mask++;
                    slices.insert(((akey>>16)&7) | (((bkey>>16)&7)<<3) | ((m&255)<<6) | ((m>>24)<<14));
                }
            }
        }
    }
    for(auto s:slices)cout<<"slice "<<(s&7)<<" "<<((s>>3)&7)<<" "<<((s>>6)&255)<<" "<<(s>>14)<<endl;
    cout<<"unique supported slices "<<slices.size()<<endl;
    cout<<"global parity joins "<<matches<<"; with disjoint site-saturated masks "<<matches_mask<<endl;
}
