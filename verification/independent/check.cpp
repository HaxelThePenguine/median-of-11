// C++20, zlib. Replay the release profile described in docs/certificate.md.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <zlib.h>

namespace fs = std::filesystem;
using Word = unsigned;
using Rows = std::vector<Word>;
using Gate = std::pair<int,int>; // first output is the minimum
using Claim = std::array<int,3>;
using Bounds = std::map<std::pair<int,int>, int>;

void need(bool ok, const std::string& reason) {
    if (!ok) throw std::runtime_error(reason);
}

std::string read_file(const fs::path& path) {
    need(fs::is_regular_file(fs::symlink_status(path)), "missing or nonregular file: " + path.string());
    const auto size = fs::file_size(path);
    need(size <= 1'000'000, "file exceeds release profile");
    std::ifstream file(path, std::ios::binary);
    std::string bytes(size, '\0');
    need(bool(file.read(bytes.data(), size)) && file.peek() == EOF, "incomplete read");
    return bytes;
}

// Recognize only the JSON grammar used by the release (arrays of integer triples).
class Parser {
    const std::string& s;
    size_t pos = 0;
    void space() { pos = s.find_first_not_of(" \n\r\t", pos); }
    bool take(char ch) {
        space();
        if (pos == s.npos || s[pos] != ch) return false;
        ++pos;
        return true;
    }
    void expect(char ch) { need(take(ch), "invalid manifest delimiter"); }
    int number() {
        space();
        need(pos < s.size() && s[pos] >= '0' && s[pos] <= '9', "expected unsigned integer");
        int v = 0;
        const auto start = s.data() + pos;
        auto [end, err] = std::from_chars(start, s.data() + s.size(), v);
        need(err == std::errc{} && (end == start+1 || *start != '0'), "invalid integer");
        pos = end - s.data();
        return v;
    }
public:
    explicit Parser(const std::string& text) : s(text) {}
    std::vector<Claim> claims() {
        std::vector<Claim> entries;
        expect('[');
        do {
            expect('[');
            int n = number(); expect(',');
            int r = number(); expect(',');
            int budget = number(); expect(']');
            need(n >= 2 && n <= 11 && r >= 1 && r <= (n+1)/2 && budget <= 30,
                 "claim outside release profile");
            entries.push_back({n,r,budget});
        } while (take(','));
        expect(']'); space();
        need(pos == s.npos, "trailing manifest content");
        return entries;
    }
};

std::vector<unsigned char> proof_bytes(const fs::path& path) {
    auto compressed = read_file(path);
    std::vector<unsigned char> bytes(1'000'001);
    z_stream z{};
    need(inflateInit2(&z, 16+MAX_WBITS) == Z_OK, "zlib initialization failed");
    z.next_in = reinterpret_cast<Bytef*>(compressed.data());
    z.avail_in = compressed.size();
    z.next_out = bytes.data();
    z.avail_out = bytes.size();
    const int status = inflate(&z, Z_FINISH);
    const bool complete = status == Z_STREAM_END && z.avail_in == 0 && z.avail_out > 0;
    const auto size = z.total_out;
    inflateEnd(&z);
    need(complete, "invalid, oversized, or trailing gzip data");
    bytes.resize(size);
    return bytes;
}

struct Layer {
    int size = 0;
    Word any = 0, all = ~0u;
    void add(Word x) { ++size; any |= x; all &= x; }
};

class Replay {
    int n, weight, budget;
    std::array<int,2> cap;
    const std::vector<unsigned char>& script;
    size_t pc = 0;
    std::vector<Gate> prefix;
    std::map<Rows,int> closed;

    // Run the current prefix backwards. At a gate both source positions
    // inherit the destiny of its extreme-output port with one extra encounter.
    Word saturated() const {
        Word mask = 0;
        for (int sign : {0,1}) {
            std::array<int,11> terminal{}, length{};
            std::iota(terminal.begin(), terminal.end(), 0);
            for (auto it = prefix.rbegin(); it != prefix.rend(); ++it) {
                auto [a,b] = *it;
                int port = sign ? b : a;
                int end = terminal[port], cost = length[port]+1;
                terminal[a] = terminal[b] = end;
                length[a] = length[b] = cost;
            }
            for (int i=0; i<n; ++i) {
                need(length[i] <= cap[sign], "reached excluded edge");
                if (length[i] == cap[sign]) mask |= 1u << terminal[i];
            }
        }
        return mask;
    }

    Rows key(const Rows& rows) const {
        std::array<std::array<int,2>,11> sums{};
        for (Word x : rows) {
            int layer = std::popcount(x) - weight;
            for (int i=0; i<n; ++i) sums[i][layer] += (x >> i) & 1u;
        }
        std::vector<int> order(n);
        std::iota(order.begin(), order.end(), 0);
        std::stable_sort(order.begin(), order.end(), [&](int i,int j){return sums[i]<sums[j];});
        Rows normalized;
        for (Word x : rows) {
            Word y = 0;
            for (int i=n-1; i>=0; --i) y = (y<<1) | ((x>>order[i]) & 1u);
            normalized.push_back(y);
        }
        std::sort(normalized.begin(), normalized.end());
        return normalized;
    }

    void visit(const Rows& rows, int left) {
        need(pc < script.size(), "missing branch");
        int op = script[pc++];
        std::array<Layer,2> layer{};
        for (Word x : rows) layer[std::popcount(x)-weight].add(x);
        need((~layer[0].any & layer[1].all) == 0, "separating output already exists");
        if (op == 1) {
            need(std::max(layer[0].size, layer[1].size) > (1<<left), "false cardinality leaf");
            return;
        }
        if (op == 2) {
            auto earlier = closed.find(key(rows));
            need(earlier != closed.end() && earlier->second >= left, "false completed reference");
            return;
        }
        Word blocked = saturated();
        if (op == 3) {
            Word varies = (layer[0].any ^ layer[0].all) | (layer[1].any ^ layer[1].all);
            need((blocked & varies) != 0, "false frozen leaf");
            return;
        }
        need(op == 0 && left > 0, "invalid opcode or depth");
        for (int a=0; a<n; ++a) for (int b=a+1; b<n; ++b) {
            Word low = 1u<<a, high = 1u<<b, ports = low | high;
            if (ports & blocked) continue;
            // Compute the image before deciding if this child is required.
            // Both discordant patterns must occur on the union of the layers.
            Rows image;
            bool up = false, down = false;
            for (Word x : rows) {
                Word pair = x & ports;
                if (pair == low) { up = true; x ^= ports; }
                if (pair == high) down = true;
                image.push_back(x);
            }
            if (!(up && down)) continue;
            std::sort(image.begin(), image.end());
            image.erase(std::unique(image.begin(), image.end()), image.end());
            prefix.emplace_back(a,b);
            visit(image, left-1);
            prefix.pop_back();
        }
        auto& limit = closed[key(rows)];
        limit = std::max(limit,left);
    }
public:
    Replay(Claim c, const Bounds& known, const std::vector<unsigned char>& data)
        : n(c[0]), weight(n-c[1]), budget(c[2]), script(data) {
        for (int sign : {0,1}) {
            int rank = c[1]-1+sign;
            auto it = known.find({n-1,std::min(rank,n-rank)});
            cap[sign] = budget - (it == known.end() ? 0 : it->second);
        }
    }
    size_t verify() {
        Rows initial;
        for (Word x=0; x<(1u<<n); ++x)
            if (std::popcount(x)==weight || std::popcount(x)==weight+1) initial.push_back(x);
        visit(initial,budget);
        need(pc==script.size(), "extra proof nodes");
        return pc;
    }
};

int main(int argc, char** argv) try {
    need(argc <= 2, "usage: check [certificate-directory]");
    fs::path dir = argc==2 ? argv[1] : "certificate";
    auto entries = Parser(read_file(dir/"claims.json")).claims();
    std::set<std::string> files{"claims.json"};
    Bounds verified;
    size_t index=0, total=0;
    for (int n=2; n<=11; ++n) {
        int first = n>=10 ? (n+1)/2 : 1;
        for (int r=first; r<=(n+1)/2; ++r) {
            need(index<entries.size() && entries[index][0]==n && entries[index][1]==r,
                 "missing, duplicate or unordered claim");
            Claim claim = entries[index++];
            auto name = std::to_string(n)+"-"+std::to_string(r)+".gz";
            files.insert(name);
            auto proof = proof_bytes(dir/name);
            auto nodes = Replay(claim,verified,proof).verify();
            verified[{n,r}] = claim[2]+1;
            total += nodes;
            std::cout << "checked n=" << n << " rank=" << r << " lower=" << claim[2]+1
                      << " nodes=" << nodes << '\n';
        }
    }
    need(index==entries.size() && verified.at({11,6})>=25, "wrong conclusion or extra claim");
    for (const auto& entry : fs::directory_iterator(dir))
        need(files.contains(entry.path().filename().string()), "unexpected certificate file");
    std::cout << "ACCEPT median(11) >= 25; " << total << " proof nodes\n";
} catch (const std::exception& error) {
    std::cerr << "REJECT " << error.what() << '\n';
    return 1;
}
