// Monotone heat-bath coupling from the past for uniform boxed profiles.
// C++17, standard library only. This executable emits raw sufficient
// statistics; confidence bounds are computed by cluster_sampling_probe.py.
// Exactness is algorithmic under independent uniform random bits, not a
// Lean certificate or a claim that a finite PRNG is truly random.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

struct Grid {
    int d, m, size, modulus;
    std::vector<std::vector<int>> predecessors, successors;
    Grid(int dimension, int side, bool ordered = false) : d(dimension), m(side), size(1), modulus(1) {
        for (int i = 0; i < d; ++i) size *= m;
        if (ordered) size *= 2;
        for (int i = 1; i <= m; ++i) modulus = std::lcm(modulus, i);
        predecessors.resize(size);
        successors.resize(size);
        int stride = 1;
        for (int axis = 0; axis < d + int(ordered); ++axis) {
            int length = axis < d ? m : 2;
            for (int x = 0; x < size; ++x) {
                int coordinate = (x / stride) % length;
                if (coordinate) predecessors[x].push_back(x - stride);
                if (coordinate + 1 < length) successors[x].push_back(x + stride);
            }
            stride *= length;
        }
    }
    void update(std::vector<int>& state, int site, int quantile) const {
        int lo = 0, hi = m - 1;
        for (int x : successors[site]) lo = std::max(lo, state[x]);
        for (int x : predecessors[site]) hi = std::min(hi, state[x]);
        if (lo > hi) throw std::runtime_error("Invalid heat-bath interval");
        // Every possible interval length divides modulus, so this is
        // exactly uniform on [lo,hi], with no floating-point rounding.
        state[site] = lo + quantile * (hi - lo + 1) / modulus;
    }
    bool valid(const std::vector<int>& state) const {
        for (int x = 0; x < size; ++x) {
            if (state[x] < 0 || state[x] >= m) return false;
            for (int y : successors[x]) if (state[y] > state[x]) return false;
        }
        return true;
    }
    int clusters(const std::vector<int>& a, const std::vector<int>& b) const {
        std::vector<int> lower(size), upper(size), parent(size);
        int count = 0;
        for (int i = 0; i < size; ++i) {
            lower[i] = std::min(a[i], b[i]);
            upper[i] = std::max(a[i], b[i]);
            parent[i] = i;
            count += lower[i] < upper[i];
        }
        auto root = [&](int x) {
            while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
            return x;
        };
        for (int x = 0; x < size; ++x) {
            if (lower[x] == upper[x]) continue;
            for (int y : successors[x]) {
                if (lower[y] == upper[y] || lower[x] >= upper[y]) continue;
                int rx = root(x), ry = root(y);
                if (rx != ry) { parent[rx] = ry; --count; }
            }
        }
        return count;
    }
};

struct Draw {
    std::vector<int> state;
    std::uint64_t updates;
    std::size_t horizon;
};

Draw sample(const Grid& grid, std::mt19937_64& rng, std::size_t max_horizon) {
    const std::uint64_t choices = std::uint64_t(grid.size) * grid.modulus;
    if (choices > std::numeric_limits<std::uint32_t>::max())
        throw std::runtime_error("Event encoding would overflow");
    std::uniform_int_distribution<std::uint32_t> event(0, std::uint32_t(choices - 1));
    // history[0] is time -1, history[1] is time -2, etc. Extending the
    // history retains EVERY previously used map at its original time.
    std::vector<std::uint32_t> history;
    std::size_t horizon = 1;
    while (horizon < std::size_t(grid.size)) horizon *= 2;
    std::uint64_t updates = 0;
    while (horizon <= max_horizon) {
        while (history.size() < horizon) history.push_back(event(rng));
        std::vector<int> lower(grid.size, 0), upper(grid.size, grid.m - 1);
        for (auto it = history.rbegin(); it != history.rend(); ++it) {
            int site = *it / grid.modulus, quantile = *it % grid.modulus;
            grid.update(lower, site, quantile);
            grid.update(upper, site, quantile);
        }
        updates += 2 * horizon;
        if (lower == upper) {
            if (!grid.valid(lower)) throw std::runtime_error("Coalesced profile is not antitone");
            return {std::move(lower), updates, horizon};
        }
        horizon *= 2;
    }
    // Never discard a difficult draw and replace it with an easy one.
    // Abort the whole fixed-size batch rather than report a biased sample.
    throw std::runtime_error("CFTP horizon cap reached; no completed batch is reported");
}

void self_test() {
    // Exhaustive interval-level uniformity and monotonicity checks for
    // every height range permitted by the command-line limits.
    for (int m = 1; m <= 12; ++m) {
        int modulus = 1;
        for (int i = 1; i <= m; ++i) modulus = std::lcm(modulus, i);
        for (int lo = 0; lo < m; ++lo) for (int hi = lo; hi < m; ++hi) {
            std::vector<int> counts(m);
            for (int u = 0; u < modulus; ++u) ++counts[lo + u * (hi - lo + 1) / modulus];
            for (int k = 0; k < m; ++k)
                if (counts[k] != (lo <= k && k <= hi ? modulus / (hi - lo + 1) : 0))
                    throw std::runtime_error("Heat-bath update is not uniform");
            for (int lo2 = lo; lo2 < m; ++lo2) for (int hi2 = std::max(hi, lo2); hi2 < m; ++hi2)
                for (int u = 0; u < modulus; ++u)
                    if (lo + u * (hi - lo + 1) / modulus > lo2 + u * (hi2 - lo2 + 1) / modulus)
                        throw std::runtime_error("Heat-bath coupling is not monotone");
        }
    }
    std::cout << "heat-bath uniformity and monotonicity checks passed\n";
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") { self_test(); return 0; }
        if (argc != 5 && argc != 6)
            throw std::runtime_error("usage: cluster_cftp BASE_DIM SIDE PAIRS SEED [--ordered]");
        bool ordered = argc == 6;
        if (ordered && std::string(argv[5]) != "--ordered") throw std::runtime_error("Unknown ensemble flag");
        int dimension = std::stoi(argv[1]), side = std::stoi(argv[2]), pairs = std::stoi(argv[3]);
        std::uint64_t seed = std::stoull(argv[4]);
        if (dimension < 1 || dimension > 3 || side < 1 || side > 12 || pairs < 2 || pairs > 1000000)
            throw std::runtime_error("Allowed: base dimension 1..3, side 1..12, pairs 2..1000000");
        Grid grid(dimension, side);
        Grid sampling_grid(dimension, side, ordered);
        std::mt19937_64 rng(seed);
        std::vector<std::uint64_t> histogram(grid.size + 1), volumes(grid.size * (side - 1) + 1);
        std::uint64_t updates = 0;
        std::size_t largest_horizon = 0;
        const auto started = std::chrono::steady_clock::now();
        for (int i = 0; i < pairs; ++i) {
            std::vector<int> first, second;
            if (ordered) {
                auto draw = sample(sampling_grid, rng, 1u << 24);
                updates += draw.updates;
                largest_horizon = std::max(largest_horizon, draw.horizon);
                first.assign(draw.state.begin(), draw.state.begin() + grid.size);
                second.assign(draw.state.begin() + grid.size, draw.state.end());
                for (int x = 0; x < grid.size; ++x)
                    if (first[x] < second[x]) throw std::runtime_error("Ordered layers crossed");
            } else {
                auto a = sample(grid, rng, 1u << 24), b = sample(grid, rng, 1u << 24);
                updates += a.updates + b.updates;
                largest_horizon = std::max({largest_horizon, a.horizon, b.horizon});
                first = std::move(a.state); second = std::move(b.state);
            }
            ++histogram[grid.clusters(first, second)];
            ++volumes[std::accumulate(first.begin(), first.end(), 0)];
            ++volumes[std::accumulate(second.begin(), second.end(), 0)];
            if ((i + 1) % std::max(1, pairs / 10) == 0)
                std::cerr << "side=" << side << " completed " << i + 1 << "/" << pairs << " pairs\n";
        }
        auto seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
        std::cout << "{\"ensemble\":\"" << (ordered ? "ordered" : "independent") << "\",\"base_dimension\":" << dimension << ",\"side\":" << side
                  << ",\"pairs\":" << pairs << ",\"seed\":" << seed
                  << ",\"heat_bath_modulus\":" << grid.modulus
                  << ",\"total_coupled_updates\":" << updates
                  << ",\"largest_horizon\":" << largest_horizon
                  << ",\"seconds\":" << seconds << ",\"cluster_histogram\":[";
        for (int i = 0; i <= grid.size; ++i) std::cout << (i ? "," : "") << histogram[i];
        std::cout << "],\"volume_histogram\":[";
        for (std::size_t i = 0; i < volumes.size(); ++i) std::cout << (i ? "," : "") << volumes[i];
        std::cout << "]}\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
    return 0;
}
