#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

using Word = std::uint32_t;
using Pairs = unsigned __int128;
constexpr int capacity = 16;

struct State {
    std::array<Word, capacity> wires{};
    int width = 0;
    int left = 0;

    bool operator==(const State &other) const {
        return width == other.width && left == other.left &&
            std::equal(wires.begin(), wires.begin() + width, other.wires.begin());
    }
};

struct Operation { Word a, b, out; bool meet; };

class Synthesis {
    std::vector<Pairs> separates;
    Pairs required = 0;
    std::vector<State> memo;
    Word target = 0, allBits = 0;
    std::vector<Operation> trace;
    State initial;

    bool seen(const State &s) {
        std::uint64_t hash = unsigned(s.left + 1);
        for (int i = 0; i < s.width; ++i) hash = (hash ^ s.wires[i]) * 0x9e3779b185ebca87ULL;
        hash ^= hash >> 33;
        State &entry = memo[hash & (memo.size() - 1)];
        if (entry == s) return true;
        entry = s;  // A collision only evicts an entry. Pruning compares the entire state.
        return false;
    }

    bool search(const State &s) {
        if (std::binary_search(s.wires.begin(), s.wires.begin() + s.width, target)) return true;
        if (s.left == 0 || s.width - 1 > s.left || seen(s)) return false;
        ++expanded;
        for (int i = 0; i < s.width; ++i) {
            for (int j = i + 1; j < s.width; ++j) {
                Word a = s.wires[i], b = s.wires[j];
                State base;
                base.left = s.left - 1;
                Pairs others = 0;
                for (int t = 0; t < s.width; ++t) {
                    if (t == i || t == j) continue;
                    Word v = s.wires[t];
                    base.wires[base.width++] = v;
                    others |= separates[v];
                }
                for (bool meet : {true, false}) {
                    Word out = meet ? a & b : a | b;
                    if (out == 0 || out == allBits ||
                        std::binary_search(s.wires.begin(), s.wires.begin() + s.width, out)) continue;
                    for (int keep = 0; keep < 4; ++keep) {
                        int width = base.width + 1 + bool(keep & 1) + bool(keep & 2);
                        if (width > base.left + 1) continue;
                        Pairs possible = others | separates[out];
                        if (keep & 1) possible |= separates[a];
                        if (keep & 2) possible |= separates[b];
                        if (possible != required) continue;
                        State next = base;
                        next.wires[next.width++] = out;
                        if (keep & 1) next.wires[next.width++] = a;
                        if (keep & 2) next.wires[next.width++] = b;
                        std::sort(next.wires.begin(), next.wires.begin() + next.width);
                        trace.push_back({a, b, out, meet});
                        if (search(next)) return true;
                        trace.pop_back();
                    }
                }
            }
        }
        return false;
    }

public:
    std::uint64_t expanded = 0;

    Synthesis(int n, const std::vector<int> &edges, int budget) : memo(1 << 16) {
        if (n >= 16 || budget + 1 > capacity) throw std::runtime_error("circuit capacity");
        std::vector<int> negative;
        auto positive = [&](int x) {
            return std::any_of(edges.begin(), edges.end(), [x](int e) { return (x & e) == e; });
        };
        for (int x = 0; x < (1 << n); ++x) {
            if (positive(x)) continue;
            bool maximal = true;
            for (int v = 0; v < n; ++v)
                if (!(x & (1 << v)) && !positive(x | (1 << v))) maximal = false;
            if (maximal) negative.push_back(x);
        }
        std::vector<int> examples = edges;
        examples.insert(examples.end(), negative.begin(), negative.end());
        int m = int(edges.size()), k = int(negative.size());
        if (m * k >= 128 || examples.size() > 20) throw std::runtime_error("truth table capacity");
        required = (Pairs(1) << (m * k)) - 1;
        target = (Word(1) << m) - 1;
        allBits = (Word(1) << examples.size()) - 1;
        separates.resize(allBits + 1);
        for (Word f = 0; f <= allBits; ++f) {
            Word rejected = (~(f >> m)) & ((Word(1) << k) - 1);
            Pairs pairs = 0;
            for (int i = 0; i < m; ++i)
                if (f & (Word(1) << i)) pairs |= Pairs(rejected) << (i * k);
            separates[f] = pairs;
        }
        initial.width = n;
        initial.left = budget;
        for (int v = 0; v < n; ++v)
            for (int i = 0; i < int(examples.size()); ++i)
                if (examples[i] & (1 << v)) initial.wires[v] |= Word(1) << i;
        std::sort(initial.wires.begin(), initial.wires.begin() + n);
    }

    bool run() { return search(initial); }
    void printTrace() const {
        for (const auto &op : trace)
            std::cout << "  " << op.out << " = " << op.a << (op.meet ? " AND " : " OR ") << op.b << "\n";
    }
};

int main(int argc, char **argv) {
    int first = argc > 1 ? std::atoi(argv[1]) : 0;
    int last = argc > 2 ? std::atoi(argv[2]) : 1000;
    int offset = argc > 3 ? std::atoi(argv[3]) : 0;
    int id, n, m, cover, processed = 0;
    while (std::cin >> id >> n >> m >> cover) {
        std::vector<int> edges;
        for (int i = 0; i < m; ++i) {
            int a, b;
            if (!(std::cin >> a >> b) || a < 0 || b < 0 || a >= n || b >= n || a == b) return 2;
            edges.push_back((1 << a) | (1 << b));
        }
        if (id < first || id > last) continue;
        int budget = m + cover - 2 + offset;
        Synthesis solver(n, edges, budget);
        bool found = solver.run();
        std::cout << "kernel " << id << " n " << n << " edges " << m << " budget " << budget
                  << " " << (found ? "FOUND" : "NONE") << " states " << solver.expanded << std::endl;
        if (found) solver.printTrace();
        ++processed;
    }
    return processed ? 0 : 2;
}
