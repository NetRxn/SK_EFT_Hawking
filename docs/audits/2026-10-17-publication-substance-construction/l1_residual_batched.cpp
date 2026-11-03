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

Poly right_factor(int c,int d,uint32_t allowed){
    Poly out;
    auto make_t=[&](int axis,int gamma_index,int q){
        const int y=fwd(1,axis);
        Mat g1=gamma_index>=0?g[gamma_index]:Mat{};
        auto r=bil(mul(Qd[q],g1),1,y);
        merge(r,bil(mul(g1,Q[q]),y,1),-1);
        return r;
    };
    for(int a=0;a<8;a++)for(int b=0;b<8;b++){
        auto left=make_t(0,c,a),right=make_t(1,d,b);
        for(auto [m,z]:wedge(left,right))if(z&&!(m&~allowed))out[m][pack({a,b,0,0})]=z;
    }
    return out;
}
int invm(int a){int t=1;for(int n=P-2;n;n>>=1,a=mod(1LL*a*a))if(n&1)t=mod(1LL*t*a);return t;}
int moment[64][8][8];
int split=0, inv16=0;
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
        if(j<2 && (split&(1<<j))){
            int pair=j==0?qa:qb;
            int single=j==0?qb:qa;
            w=(pair/8==pair%8 && single==qc)?inv16:0;
        }
        if(!w)return 0;
        value=mod(value*w);
    }
    return int(value);
}
using G=array<long long,2>;
using Gaussian=unordered_map<uint32_t,unordered_map<uint32_t,G>>;
struct Left {uint32_t mask,key; G coeff;};
struct Right {uint32_t mask; int c,d; G coeff;};
using Group=array<vector<Left>,64>;
G gm(G a,G b){return {a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]};}
Gaussian exact(Poly p,Poly n){
    Gaussian out;
    for(auto& [m,mp]:n)for(auto [k,z]:mp)if(z&&!p[m].contains(k))p[m][k]=0;
    auto lift=[](int v){return v>P/2?v-P:v;};
    int rscale=invm(2),iscale=invm(512);
    for(auto& [m,mp]:p)for(auto [k,z]:mp){
        auto zz=n[m][k];
        G v={lift(mod(1LL*(z+zz)*rscale)),lift(mod(1LL*(z-zz)*iscale))};
        if(abs(v[0])>1152||abs(v[1])>1152)throw runtime_error("coefficient lift exceeded bound");
        if(v[0]||v[1])out[m][k]=v;
    }
    return out;
}
void init(int iroot,uint32_t allowed){
    I=iroot;setup(1);
    for(int i=0;i<8;i++){
        array<int,4> l{},r{};(i<4?l[i]:r[i-4])=1;
        qblock(1,0,0,l);qblock(1,0,1,r);
        Q[i]=U[1][0];Qd[i]=Ud[1][0];
        for(int a=0;a<4;a++)for(int c=0;c<4;c++){
            U[1][a]=Q[i];Ud[1][a]=Qd[i];ts[a][c][i]=tt(1,a,1,c);
            for(auto it=ts[a][c][i].begin();it!=ts[a][c][i].end();)
                if(it->first&~allowed)it=ts[a][c][i].erase(it);else ++it;
        }
    }
}
int main(int argc,char**argv){
    int family=argc>1?stoi(argv[1]):1;
    int mode=argc>2?stoi(argv[2]):-1;
    uint32_t allowed=0xFF00FFFF;
    int mixed_l=family?3:2;
    array<array<Poly,8>,2> lp,ln;
    array<Poly,16> rp,rn;
    for(int root:{256,65281}){
        init(root,allowed);
        auto& left=root==256?lp:ln;
        auto& right=root==256?rp:rn;
        for(int e=0;e<8;e++){
            left[0][e]=build(0,2,e,e,allowed);
            left[1][e]=build(1,mixed_l,e,e,allowed);
        }
        for(int g=0;g<16;g++)right[g]=right_factor(g/4,g%4,allowed);
    }
    array<array<Group,8>,2> grouped;
    array<uint64_t,3> terms{};
    for(int f=0;f<2;f++)for(int e=0;e<8;e++){
        auto x=exact(move(lp[f][e]),move(ln[f][e]));
        for(auto& [m,ks]:x)for(auto [k,v]:ks){
            int tq=((k>>12)&7)|(((k>>18)&7)<<3);
            grouped[f][e][tq].push_back({m,k,v});
            terms[f]++;
        }
    }
    array<vector<Right>,64*256> right;
    for(int g=0;g<16;g++){
        auto x=exact(move(rp[g]),move(rn[g]));
        for(auto& [m,ks]:x)for(auto [k,v]:ks){
            int center=(m>>8)&255;
            int pair=(k&7)|(((k>>6)&7)<<3);
            right[64*center+pair].push_back({m,g/4,g%4,v});
            terms[2]++;
        }
    }
    cerr<<"exact factor terms: "<<terms[0]<<" "<<terms[1]<<" "<<terms[2]<<"\n";
    vector<int> valid[64][8];
    int weights[64][8][8]{};
    for(int a=0;a<64;a++)for(int b=0;b<8;b++)for(int c=0;c<8;c++){
        int t=fourth(a/8,a%8,b,c);
        if(t){valid[a][b].push_back(c);weights[a][b][c]=mod(48LL*t);}
    }
    array<unordered_map<uint32_t,array<__int128,2>>,4> result;
    uint64_t considered=0,kept=0,matched=0;
    for(int e=0;e<8;e++)for(int f=0;f<8;f++)for(int j=0;j<64;j++){
        for(auto& a:grouped[0][e][j])for(auto& b:grouped[1][f][j]){
            considered++;
            if(a.mask&b.mask)continue;
            uint32_t ab=a.mask|b.mask;
            int center=255^((ab>>8)&255);
            int p0=a.key&63,s0=b.key&7,p1=(b.key>>6)&63,s1=(a.key>>6)&7;
            const auto& v0=valid[p0][s0];const auto& v1=valid[p1][s1];
            if(v0.empty()||v1.empty())continue;
            kept++;
            auto left=gm(a.coeff,b.coeff);
            int left_sign=sign(a.mask,b.mask);
            for(int q0:v0)for(int q1:v1){
                int q=q0|(q1<<3);
                bool split0=p0/8==p0%8&&s0==q0;
                bool split1=p1/8==p1%8&&s1==q1;
                for(auto& c:right[64*center+q])if(!(ab&c.mask)){
                    matched++;
                    uint32_t out=ab|c.mask;
                    uint32_t key=e|(f<<3)|((out&255)<<6)|((out>>24)<<14)|(c.c<<22)|(c.d<<24);
                    auto val=gm(left,c.coeff);
                    int s=left_sign*sign(ab,c.mask);
                    for(int k=0;k<4;k++){
                        if(mode>=0&&mode!=k)continue;
                        if(((k&1)&&!split0)||((k&2)&&!split1))continue;
                        auto& acc=result[k][key];
                        // 48^4 times two transverse second moments and two
                        // extended quartic (or split second×second) moments.
                        int w=144*((k&1)?3:weights[p0][s0][q0])*((k&2)?3:weights[p1][s1][q1]);
                        for(int t=0;t<2;t++)acc[t]+=(__int128)s*w*val[t];
                    }
                }
            }
        }
    }
    cerr<<"batched join "<<considered<<" pairs, "<<kept<<" parity+mask candidates, "<<matched<<" right matches\n";
    for(int k=0;k<4;k++)for(auto [key,v]:result[k])if(v[0]||v[1]){
        for(auto z:v)if(z!=static_cast<long long>(z))throw runtime_error("receipt too wide");
        cout<<"variant "<<k<<" exact slice "<<(key&7)<<" "<<((key>>3)&7)<<" "<<((key>>6)&255)<<" "<<((key>>14)&255)<<" "<<((key>>22)&3)<<" "<<((key>>24)&3)<<" scaled Gaussian ("<<static_cast<long long>(v[0])<<","<<static_cast<long long>(v[1])<<")/5308416\n";
    }
}
