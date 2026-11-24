#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <vector>

// Exact synthesis on five primary inputs. The four-input script uses an
// independent, labelled enumeration and supplies a small reference case.
constexpr int n = 5;
constexpr int maxGates = 8;
constexpr int never = 99;
using Truth = std::uint32_t;

struct Gate { int a, b; bool meet; };
struct Result {
    int bound = 0, minimum = never, missing = never, witnessGraph = 0;
    std::vector<Gate> witness;
};

struct Search {
    int limit;
    int bit[n][n]{}, canon[1 << 10]{};
    int depth[n + maxGates]{}, used[n + maxGates]{}, linear[n + maxGates]{};
    Truth value[n + maxGates]{};
    Gate gates[maxGates]{};
    std::unordered_map<Truth, int> target;
    std::array<Result, 1 << 10> results;

    explicit Search(int cap) : limit(cap) {
        int j = 0;
        for (int a = 0; a < n; ++a) {
            linear[a] = 1 << a;
            for (int x = 0; x < (1 << n); ++x)
                if (x & (1 << a)) value[a] |= Truth(1) << x;
            for (int b = a + 1; b < n; ++b)
                bit[a][b] = bit[b][a] = 1 << j++;
        }
        for (int g = 1; g < (1 << 10); ++g) {
            int nb[n]{};
            Truth f = 0;
            for (int a = 0; a < n; ++a)
                for (int b = a + 1; b < n; ++b)
                    if (g & bit[a][b]) {
                        nb[a] |= 1 << b;
                        nb[b] |= 1 << a;
                        f |= value[a] & value[b];
                    }
            bool square = false;
            for (int a = 0; a < n; ++a)
                for (int b = a + 1; b < n; ++b)
                    if (__builtin_popcount(nb[a] & nb[b]) > 1) square = true;
            if (square) continue;
            int best = g;
            std::array<int, n> perm{};
            std::iota(perm.begin(), perm.end(), 0);
            do {
                int h = 0;
                for (int a = 0; a < n; ++a)
                    for (int b = a + 1; b < n; ++b)
                        if (g & bit[a][b]) h |= bit[perm[a]][perm[b]];
                best = std::min(best, h);
            } while (std::next_permutation(perm.begin(), perm.end()));
            canon[g] = best;
            target[f] = g;
            int cover = n;
            for (int s = 0; s < (1 << n); ++s) {
                bool ok = true;
                for (int v = 0; v < n; ++v)
                    if (!(s & (1 << v)) && (nb[v] & ~s)) ok = false;
                if (ok) cover = std::min(cover, __builtin_popcount(unsigned(s)));
            }
            results[best].bound = __builtin_popcount(unsigned(g)) + cover - 1;
        }
    }

    bool hasMissing(int g, int length) const {
        int covered = 0;
        for (int j = 0; j < length; ++j) {
            Gate t = gates[j];
            int left = linear[t.a], right = linear[t.b];
            if (!t.meet || (left & right)) continue;
            int cross = 0;
            for (int a = 0; a < n; ++a)
                if (left & (1 << a))
                    for (int b = 0; b < n; ++b)
                        if (right & (1 << b)) cross |= bit[a][b];
            if (!(cross & ~g)) covered |= cross;
        }
        return covered != g;
    }

    void extend(int length, int fresh, int sinks) {
        int wire = n + length;
        for (int a = 0; a < wire; ++a) {
            if (a < n && a > fresh) continue;
            int afterA = fresh + (a < n && a == fresh);
            for (int b = a + 1; b < wire; ++b) {
                if (b < n && b > afterA) continue;
                int afterB = afterA + (b < n && b == afterA);
                int level = 1 + std::max(depth[a], depth[b]);
                if (length && level < depth[wire - 1]) continue;
                int nextSinks = sinks + 1 - (a >= n && !used[a]) - (b >= n && !used[b]);
                // A later binary gate can remove at most one outstanding sink.
                if (nextSinks > limit - length) continue;
                depth[wire] = level;
                ++used[a];
                ++used[b];
                for (bool meet : {true, false}) {
                    Truth f = meet ? value[a] & value[b] : value[a] | value[b];
                    if (std::find(value, value + wire, f) != value + wire) continue;
                    gates[length] = {a, b, meet};
                    linear[wire] = meet ? 0 : linear[a] | linear[b];
                    value[wire] = f;
                    if (nextSinks == 1) {
                        auto it = target.find(f);
                        if (it != target.end()) {
                            int g = it->second;
                            auto &r = results[canon[g]];
                            r.minimum = std::min(r.minimum, length + 1);
                            if (length + 1 <= r.bound && length + 1 < r.missing && hasMissing(g, length + 1)) {
                                r.missing = length + 1;
                                r.witnessGraph = g;
                                r.witness.assign(gates, gates + length + 1);
                            }
                        }
                    }
                    if (length + 1 < limit) extend(length + 1, afterB, nextSinks);
                }
                --used[a];
                --used[b];
            }
        }
    }

    void report() const {
        int labelled = 0, classes = 0, below = 0, missing = 0;
        for (const auto &[f, g] : target)
            if (results[canon[g]].bound <= limit) ++labelled;
        for (size_t g = 0; g < results.size(); ++g) {
            const auto &r = results[g];
            if (!r.bound) continue;
            if (r.minimum < r.bound) ++below;
            if (r.bound > limit) continue;
            ++classes;
            if (r.minimum > r.bound) std::abort();
            if (r.missing == r.minimum) {
                ++missing;
                std::cout << "Optimal circuit missing an edge, canonical graph " << g
                          << ", edges in witness labelling";
                for (int a = 0; a < n; ++a)
                    for (int b = a + 1; b < n; ++b)
                        if (r.witnessGraph & bit[a][b]) std::cout << " " << a << "-" << b;
                std::cout << ", gates";
                for (auto t : r.witness) std::cout << " " << (t.meet ? "and" : "or") << "(" << t.a << "," << t.b << ")";
                std::cout << "\n";
            }
        }
        std::cout << "Cap " << limit << ", classes with predicted size within cap " << classes
                  << ", labelled graphs in those classes " << labelled
                  << ", graphs below bound (classes over all inspected outputs) " << below
                  << ", classes with an optimal circuit missing an edge " << missing << "\n";
    }
};

int main(int argc, char **argv) {
    int limit = argc > 1 ? std::atoi(argv[1]) : maxGates;
    if (limit < 1 || limit > maxGates) return 2;
    Search search(limit);
    search.extend(0, 0, 0);
    search.report();
}
