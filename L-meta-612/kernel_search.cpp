#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Pairs = std::bitset<256>;
constexpr int capacity = 24;

struct State {
    std::array<Word, capacity> wires{};
    int width = 0;
    int left = 0;
    Word slack = 0;

    bool operator==(const State &other) const {
        return width == other.width && left == other.left && slack == other.slack &&
            std::equal(wires.begin(), wires.begin() + width, other.wires.begin());
    }
};

struct Operation { Word a, b, out; bool meet; };

class Synthesis {
    std::vector<Pairs> separates;
    std::vector<Word> cacheKeys;
    Pairs required;
    std::vector<State> memo;
    Word target = 0, allBits = 0;
    int positiveCount = 0, negativeCount = 0;
    int boundaryBits = 0;
    Word rejectionMask = 0;
    Word boundaryMask = 0, tracked = 0, guards = 0;
    std::vector<Word> digits;
    std::vector<Operation> trace;
    State initial;

    static Word lowMask(unsigned bits) {
        return (Word(1) << bits) - 1;
    }

    const Pairs &separation(Word f) {
        f &= boundaryMask;
        std::size_t slot = (std::uint64_t(f) * 0x9e3779b185ebca87ULL) >> 47;
        if (cacheKeys[slot] != f) {
            Word rejected = (~(f >> positiveCount)) & rejectionMask;
            Pairs pairs;
            Word accepted = f & target;
            while (accepted) {
                int i = __builtin_ctz(accepted);
                pairs |= Pairs(rejected) << (i * negativeCount);
                accepted &= accepted - 1;
            }
            cacheKeys[slot] = f;
            separates[slot] = pairs;
        }
        return separates[slot];
    }

    bool seen(const State &s) {
        std::uint64_t hash = unsigned(s.left + 1) ^ (s.slack * 0x9e3779b185ebca87ULL);
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
                    others |= separation(v);
                }
                for (bool meet : {true, false}) {
                    Word out = meet ? a & b : a | b;
                    if (out == 0 || out == allBits ||
                        std::binary_search(s.wires.begin(), s.wires.begin() + s.width, out)) continue;
                    Word neededA = (~a >> boundaryBits) & tracked;
                    Word neededB = (~b >> boundaryBits) & tracked;
                    // Slack is the remaining deletion allowance minus the number
                    // of live wires that vanish when the corresponding v is zero.
                    // Combining two such wires spends no slack if both retire.
                    // An AND with exactly one such operand spends one extra unit.
                    Word meetCost = meet ? digits[neededA ^ neededB] : 0;
                    for (int keep = 0; keep < 4; ++keep) {
                        int width = base.width + 1 + bool(keep & 1) + bool(keep & 2);
                        if (width > base.left + 1) continue;
                        Word cost = meetCost + ((keep & 1) ? digits[neededA] : 0) +
                            ((keep & 2) ? digits[neededB] : 0);
                        // Each digit starts with its high bit set. A single step
                        // costs at most two, so subtracting cannot borrow between digits.
                        Word slack = s.slack - cost;
                        if ((slack & guards) != guards) continue;
                        Pairs possible = others | separation(out);
                        if (keep & 1) possible |= separation(a);
                        if (keep & 2) possible |= separation(b);
                        if (possible != required) continue;
                        State next = base;
                        next.slack = slack;
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

    Synthesis(int n, const std::vector<int> &edges, int budget, bool smallerOptimal,
              unsigned memoBits, int firstA = -1, int firstB = -1) : memo(std::size_t(1) << memoBits) {
        if (n >= 16 || budget + 1 > capacity) throw std::runtime_error("circuit capacity");
        bool fixedFirst = firstA >= 0;
        if (fixedFirst && (firstB < 0 || firstA >= n || firstB >= n || firstA == firstB))
            throw std::runtime_error("invalid first OR operands");
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
        if (m * k > 256 || examples.size() > 32 || m >= 32)
            throw std::runtime_error("truth table capacity");
        positiveCount = m;
        negativeCount = k;
        rejectionMask = lowMask(k);
        for (int i = 0; i < m * k; ++i) required.set(i);
        target = lowMask(m);
        boundaryBits = int(examples.size());
        boundaryMask = lowMask(boundaryBits);
        // Optional induction on the number of vertices. Each tracked restriction
        // uses the previously proved lower bound for the graph with v deleted.
        if (smallerOptimal) {
            for (int v = 0; v < n; ++v) {
                int without = (1 << n) - 1 - (1 << v);
                int restEdges = std::count_if(edges.begin(), edges.end(),
                    [without](int e) { return (e & without) == e; });
                examples.push_back(without);
                if (!restEdges) continue;
                target |= Word(1) << (boundaryBits + v);
                int cover = n;
                for (int set = 0; set < (1 << n); ++set) {
                    if (std::all_of(edges.begin(), edges.end(), [set, v](int e) {
                        return (e & (1 << v)) || (e & set);
                    })) cover = std::min(cover, __builtin_popcount(unsigned(set)));
                }
                int allowance = budget - (restEdges + cover - 1);
                // The prescribed first OR simplifies when either operand is zero.
                if (v == firstA || v == firstB) --allowance;
                if (allowance < 1) { impossible = true; continue; }
                if (allowance > 8) continue;
                tracked |= Word(1) << v;
                guards |= Word(8) << (4 * v);
                initial.slack |= Word(8 + allowance - 1) << (4 * v);
            }
        }
        digits.resize(smallerOptimal ? (1 << n) : 1);
        for (unsigned i = 1; i < digits.size(); ++i)
            digits[i] = digits[i & (i - 1)] | (Word(1) << (4 * __builtin_ctz(i)));
        allBits = lowMask(unsigned(examples.size()));
        separates.resize(1 << 17);
        cacheKeys.resize(1 << 17);
        initial.width = n;
        initial.left = budget - int(fixedFirst);
        for (int v = 0; v < n; ++v)
            for (int i = 0; i < int(examples.size()); ++i)
                if (examples[i] & (1 << v)) initial.wires[v] |= Word(1) << i;
        if (fixedFirst) {
            Word a = initial.wires[firstA], b = initial.wires[firstB];
            initial.wires[initial.width++] = a | b;
            trace.push_back({a, b, a | b, false});
        }
        std::sort(initial.wires.begin(), initial.wires.begin() + initial.width);
    }

    bool impossible = false;
    bool run() { return !impossible && search(initial); }
    void printTrace() const {
        for (const auto &op : trace)
            std::cout << "  " << op.out << " = " << op.a << (op.meet ? " AND " : " OR ") << op.b << "\n";
    }
};

int main(int argc, char **argv) {
    int first = argc > 1 ? std::atoi(argv[1]) : 0;
    int last = argc > 2 ? std::atoi(argv[2]) : 1000;
    int offset = argc > 3 ? std::atoi(argv[3]) : 0;
    bool smallerOptimal = argc > 4 && std::string(argv[4]) == "--smaller-optimal";
    if (argc > 4 && !smallerOptimal && std::string(argv[4]) != "--direct") return 2;
    int memoBits = argc > 5 ? std::atoi(argv[5]) : 16;
    if (memoBits < 10 || memoBits > 21) return 2;
    if (argc > 6 && (argc != 9 || std::string(argv[6]) != "--all-live-first-or")) return 2;
    int firstA = argc == 9 ? std::atoi(argv[7]) : -1;
    int firstB = argc == 9 ? std::atoi(argv[8]) : -1;
    if (argc == 9 && (firstA < 0 || firstB < 0)) return 2;
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
        Synthesis solver(n, edges, budget, smallerOptimal, unsigned(memoBits), firstA, firstB);
        bool found = solver.run();
        std::cout << "kernel " << id << " n " << n << " edges " << m << " budget " << budget
                  << " " << (found ? "FOUND" : "NONE") << " states " << solver.expanded << std::endl;
        if (found) solver.printTrace();
        ++processed;
    }
    return processed ? 0 : 2;
}
