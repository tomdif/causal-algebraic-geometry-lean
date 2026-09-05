// Exhaustive small-state checks of the actual sampler implementation.
#define main cag_sampler_main
#include "cluster_cftp.cpp"
#undef main
#include <map>

// Independent representation: flood-fill individual unit cells of the
// disagreement band, not the sampler's union-find on base columns.
int cell_components(const Grid& grid, const std::vector<int>& a, const std::vector<int>& b) {
    const int height = grid.m - 1;
    std::vector<bool> active(grid.size * height), seen(active.size());
    for (int x = 0; x < grid.size; ++x)
        for (int h = std::min(a[x], b[x]); h < std::max(a[x], b[x]); ++h)
            active[x * height + h] = true;
    int count = 0;
    for (int cell = 0; cell < int(active.size()); ++cell) {
        if (!active[cell] || seen[cell]) continue;
        ++count;
        std::vector<int> queue{cell}; seen[cell] = true;
        auto visit = [&](int next) {
            if (active[next] && !seen[next]) { seen[next] = true; queue.push_back(next); }
        };
        for (std::size_t i = 0; i < queue.size(); ++i) {
            int x = queue[i] / height, h = queue[i] % height;
            if (h > 0) visit(x * height + h - 1);
            if (h + 1 < height) visit(x * height + h + 1);
            for (int y : grid.predecessors[x]) visit(y * height + h);
            for (int y : grid.successors[x]) visit(y * height + h);
        }
    }
    return count;
}

int main() {
    try {
        self_test();
        int cases_checked = 0;
        for (bool ordered : {false, true}) for (int d = 1; d <= 3; ++d) for (int m = 2; m <= 3; ++m) {
            Grid grid(d, m, ordered);
            std::uint64_t functions = 1;
            for (int i = 0; i < grid.size && functions <= 65536; ++i) functions *= m;
            if (functions > 65536) continue;
            std::vector<std::vector<int>> states;
            std::map<std::vector<int>, int> index;
            for (std::uint64_t code = 0; code < functions; ++code) {
                auto remainder = code;
                std::vector<int> state(grid.size);
                for (auto& value : state) { value = remainder % m; remainder /= m; }
                if (grid.valid(state)) { index[state] = int(states.size()); states.push_back(state); }
            }
            std::vector<std::vector<int>> transitions(states.size(), std::vector<int>(states.size()));
            for (std::size_t i = 0; i < states.size(); ++i)
                for (int site = 0; site < grid.size; ++site) for (int u = 0; u < grid.modulus; ++u) {
                    auto target = states[i];
                    grid.update(target, site, u);
                    if (!index.count(target)) throw std::runtime_error("Update left the state space");
                    ++transitions[i][index.at(target)];
                }
            for (std::size_t i = 0; i < states.size(); ++i) {
                if (!transitions[i][i]) throw std::runtime_error("Missing self loop");
                for (std::size_t j = 0; j < states.size(); ++j) {
                    if (transitions[i][j] != transitions[j][i]) throw std::runtime_error("Detailed balance failed");
                    bool comparable = true;
                    for (int x = 0; x < grid.size; ++x) comparable &= states[i][x] <= states[j][x];
                    if (!comparable) continue;
                    for (int site = 0; site < grid.size; ++site) for (int u = 0; u < grid.modulus; ++u) {
                        auto lower = states[i], upper = states[j];
                        grid.update(lower, site, u); grid.update(upper, site, u);
                        for (int x = 0; x < grid.size; ++x)
                            if (lower[x] > upper[x]) throw std::runtime_error("Coupling lost monotonicity");
                    }
                }
            }
            // Connectivity of the entire transition graph, not just local validity.
            std::vector<bool> seen(states.size());
            std::vector<int> queue{0}; seen[0] = true;
            for (std::size_t k = 0; k < queue.size(); ++k)
                for (std::size_t j = 0; j < states.size(); ++j)
                    if (transitions[queue[k]][j] && !seen[j]) { seen[j] = true; queue.push_back(int(j)); }
            if (queue.size() != states.size()) throw std::runtime_error("Transition graph is not irreducible");
            for (std::size_t i = 0; i < states.size(); ++i)
                for (std::size_t j = i; j < states.size(); ++j)
                    if (grid.clusters(states[i], states[j]) != cell_components(grid, states[i], states[j]))
                        throw std::runtime_error("Column clusters disagree with unit-cell flood fill");
            ++cases_checked;
        }
        std::cout << "exhaustive full-state checks passed for " << cases_checked << " grid ensembles\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n'; return 1;
    }
}
