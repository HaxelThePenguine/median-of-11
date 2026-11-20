// Reverse breadth-first search over complete one-output Boolean functions.
// Each truth table fits in a 64-bit word for n <= 6.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>
using Table = std::uint64_t;
struct Substitution { Table left, right; int shift; };

int main() {
    for (int n=2; n<=6; ++n) {
        std::vector<Table> frontier(n), target(n);
        for (unsigned x=0; x<(1u<<n); ++x) {
            Table row = Table{1} << x;
            for (int i=0; i<n; ++i) {
                if ((x>>i)&1u) frontier[i] |= row;
                if (std::popcount(x)>=n-i) target[i] |= row;
            }
        }
        std::vector<Substitution> substitutions;
        for (int a=0; a<n; ++a) for (int b=a+1; b<n; ++b)
            substitutions.push_back({frontier[a] & ~frontier[b], frontier[b] & ~frontier[a],
                                     (1<<b)-(1<<a)});
        std::unordered_set<Table> seen(frontier.begin(),frontier.end());
        std::vector<int> optimum(n,-1);
        for (int depth=0; !frontier.empty(); ++depth) {
            for (int i=0; i<n; ++i)
                if (optimum[i]<0 && seen.contains(target[i])) optimum[i]=depth;
            if (std::find(optimum.begin(),optimum.end(),-1)==optimum.end()) break;
            std::vector<Table> next;
            for (Table f : frontier) for (auto [left,right,shift] : substitutions) {
                // Pull back f under each orientation, copying the value from
                // the ordered configuration to its discordant preimage.
                Table down = (f & ~left) | ((f>>shift) & left);
                Table up = (f & ~right) | ((f<<shift) & right);
                for (Table g : {down,up}) if (seen.insert(g).second) next.push_back(g);
            }
            frontier.swap(next);
        }
        for (int i=0; i<n; ++i) {
            if (optimum[i]<0) return 1;
            std::cout << n << ' ' << i+1 << ' ' << optimum[i] << '\n';
        }
    }
}
