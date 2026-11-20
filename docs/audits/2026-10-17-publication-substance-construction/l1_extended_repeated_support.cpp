#include <array>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
struct Ways { array<int,16> incoming{}; uint64_t count=0; };
void search(const vector<int>& centers,int k,Ways& state){
    if(k==int(centers.size())){
        for(int x:centers)if(state.incoming[x^1]!=2) return;
        ++state.count;
        return;
    }
    int x=centers[k];
    for(int a=0;a<4;++a) for(int b=a+1;b<4;++b){
        auto& u=state.incoming[x^(1<<a)];
        auto& v=state.incoming[x^(1<<b)];
        if(u==2||v==2)continue;
        ++u;++v;
        search(centers,k+1,state);
        --u;--v;
    }
}
int main(){
    vector<int> even,odd;
    for(unsigned x=0;x<16;++x)(__builtin_popcount(x)%2?odd:even).push_back(x);
    Ways a,b;
    search(even,0,a);
    search(odd,0,b);
    cout<<a.count<<" "<<b.count<<" "<<a.count*b.count<<" "<<(a.count*b.count*(1ULL<<32))<<"\n";
}
