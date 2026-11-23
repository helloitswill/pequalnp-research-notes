// Exhaustive monotone circuit lower bound for the three-cube. Standard C++17.
// A state stores projected example rows. Every transition appends a gate value
// and can drop either operand, both operands, or neither after the last use.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using Row = std::uint16_t;
constexpr unsigned inputs = 8;
constexpr unsigned positiveCount = 12;
constexpr unsigned negativeCount = 6;
constexpr unsigned maxWidth = 10; // With budget 12, width <= floor((8+12+1)/2).
constexpr Row unused = UINT16_MAX;

bool hasEdge(unsigned x) {
    for (unsigned vertex = 0; vertex < inputs; ++vertex) {
        for (unsigned difference : {1u, 2u, 4u}) {
            unsigned neighbor = vertex ^ difference;
            if ((x & (1u << vertex)) && (x & (1u << neighbor))) return true;
        }
    }
    return false;
}

struct State {
    std::array<Row, positiveCount> positives;
    std::array<Row, negativeCount> negatives;

    bool operator==(const State& other) const {
        return positives == other.positives && negatives == other.negatives;
    }
};

struct StateHash {
    std::size_t operator()(const State& state) const {
        std::size_t hash = 0;
        for (Row r : state.positives) hash = (hash ^ r) * 1000003u;
        for (Row r : state.negatives) hash = (hash ^ r) * 1000003u;
        return hash;
    }
};

struct GateMove {
    unsigned widthAfter;
    std::vector<Row> projection;
};

unsigned deleteBit(unsigned x, unsigned bit) {
    unsigned low = (1u << bit) - 1;
    return (x & low) | ((x >> 1) & ~low);
}

std::vector<GateMove> allMoves(unsigned width) {
    std::vector<GateMove> moves;
    for (unsigned a = 0; a < width; ++a) {
        for (unsigned b = a + 1; b < width; ++b) {
            for (bool isAnd : {true, false}) {
                for (unsigned drop = 0; drop != 4; ++drop) {
                    unsigned after = width + 1 - (drop & 1) - (drop >> 1);
                    if (after > maxWidth) continue;
                    GateMove move{after, {}};
                    move.projection.reserve(1u << width);
                    for (unsigned row = 0; row < (1u << width); ++row) {
                        unsigned first = (row >> a) & 1, second = (row >> b) & 1;
                        unsigned result = isAnd ? first & second : first | second;
                        unsigned retained = row;
                        if (drop & 2) retained = deleteBit(retained, b);
                        if (drop & 1) retained = deleteBit(retained, a);
                        move.projection.push_back(Row(retained | (result << (after-1))));
                    }
                    moves.push_back(std::move(move));
                }
            }
        }
    }
    return moves;
}

template <std::size_t N>
void canonicalize(std::array<Row, N>& rows) {
    std::sort(rows.begin(), rows.end());
    auto end = std::unique(rows.begin(), rows.end());
    std::fill(end, rows.end(), unused);
}

class Search {
    std::array<std::vector<GateMove>, maxWidth + 1> choices;
    // At a given width, trying a state at a larger remaining budget covers
    // all continuations of that state at a smaller budget.
    std::array<std::unordered_map<State, unsigned, StateHash>, maxWidth + 1> memo;
public:
    std::uint64_t expanded = 0, attempted = 0;
    Search() {
        for (unsigned w = 1; w <= maxWidth; ++w) choices[w] = allMoves(w);
    }

    bool exists(const State& state, unsigned width, unsigned left) {
        unsigned good = (1u << width) - 1;
        for (Row p : state.positives) {
            if (p == unused) break;
            good &= p;
        }
        for (Row n : state.negatives) {
            if (n == unused) break;
            good &= ~unsigned(n);
        }
        if (good) return true; // A current coordinate already equals the target.
        if (!left || width > left + 1) return false;
        auto [it, inserted] = memo[width].try_emplace(state, left);
        if (!inserted && it->second >= left) return false;
        it->second = left;
        ++expanded;

        for (const GateMove& move : choices[width]) {
            if (move.widthAfter > left) continue;
            ++attempted;
            State next;
            next.positives.fill(unused);
            next.negatives.fill(unused);
            unsigned nCount = 0;
            for (Row n : state.negatives) {
                if (n == unused) break;
                next.negatives[nCount++] = move.projection[n];
            }
            unsigned pCount = 0;
            bool impossible = false;
            for (Row p : state.positives) {
                if (p == unused) break;
                Row projected = move.projection[p];
                // If projected <= n coordinatewise, no monotone suffix can
                // send projected to true and n to false.
                for (unsigned i = 0; i < nCount; ++i)
                    if ((projected & next.negatives[i]) == projected) {
                        impossible = true;
                        break;
                    }
                if (impossible) break;
                next.positives[pCount++] = projected;
            }
            if (impossible) continue;
            canonicalize(next.positives);
            canonicalize(next.negatives);
            if (exists(next, move.widthAfter, left - 1)) return true;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    int budget = argc == 2 ? std::atoi(argv[1]) : 12;
    if (budget < 1 || budget > 12) {
        std::cerr << "Specify a gate budget from 1 through 12.\n";
        return 2;
    }
    State start;
    unsigned np = 0, nn = 0;
    for (unsigned x = 0; x < (1u << inputs); ++x) {
        bool positive = hasEdge(x);
        bool boundary = true;
        for (unsigned j = 0; j < inputs; ++j) {
            if (bool(x & (1u << j)) == positive && hasEdge(x ^ (1u << j)) == positive)
                boundary = false;
        }
        if (boundary) {
            if (positive) start.positives.at(np++) = Row(x);
            else start.negatives.at(nn++) = Row(x);
        }
    }
    assert(np == positiveCount && nn == negativeCount);
    Search solve;
    bool found = solve.exists(start, inputs, unsigned(budget));
    std::cout << "rows " << np << "+" << nn << ", budget " << budget << ": "
              << (found ? "FOUND" : "NONE") << ", states " << solve.expanded
              << ", transitions " << solve.attempted << '\n';
}
