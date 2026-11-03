#define main residual_batch_main
#include "l1_residual_batched.cpp"
#undef main
int top(const vector<array<int,5>>& labels) {
    Ext left{{0,1}}, right{{0,1}};
    for (int j=0;j<4;j++) left=wedge(left,action(labels[j]));
    for (int j=4;j<8;j++) right=wedge(right,action(labels[j]));
    int result=0;
    for(auto [mask,value]:left){
        auto it=right.find(~mask);
        if(it!=right.end()) result=mod(result+1LL*sign(mask,~mask)*value*it->second);
    }
    return result;
}
int main() {
    const vector<array<int,5>> labels = {
        {0,0,1,0,0}, {0,2,3,0,0}, {1,0,2,1,1}, {1,1,2,1,1},
        {2,0,3,2,2}, {2,1,3,2,2}, {3,0,1,3,3}, {3,2,3,3,3}
    };
    setup(1);
    const int before = top(labels);
    Mat rotation = unit(), inverse = unit();
    rotation[0][0] = inverse[1][1] = I;
    rotation[1][1] = inverse[0][0] = mod(-I);
    for (int x=0; x<4; ++x) for (int d=0; d<4; ++d) {
        if (x == 0) {
            U[x][d] = mul(rotation, U[x][d]);
            Ud[x][d] = mul(Ud[x][d], inverse);
        }
        if (fwd(x,d) == 0) {
            U[x][d] = mul(U[x][d], inverse);
            Ud[x][d] = mul(rotation, Ud[x][d]);
        }
    }
    const int after = top(labels);
    cout << before << " " << after << "\n";
    return before == 36770 && after == 10060 ? 0 : 1;
}
