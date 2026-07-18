#include <algorithm>
#include <cstdlib>
#include <iostream>

// For D(n,q) = {t(1,q,q^2,q^3,q^4): t in Z_n}, test whether its
// minimum cyclic l_infinity distance is at least ceil(2n/7). Such a code
// would map injectively to an independent n-set in C_7^5.
bool meets_direct_c7_threshold(int n, int q, int threshold) {
    long long power[5] = {1, q, 0, 0, 0};
    for (int coordinate = 2; coordinate < 5; ++coordinate) {
        power[coordinate] = power[coordinate - 1] * q % n;
    }

    // The distances for t and n-t are identical.
    for (int t = 1; t <= n / 2; ++t) {
        int maximum_coordinate_distance = 0;
        for (int coordinate = 0; coordinate < 5; ++coordinate) {
            const int residue = int(t * power[coordinate] % n);
            maximum_coordinate_distance = std::max(
                maximum_coordinate_distance, std::min(residue, n - residue));
        }
        if (maximum_coordinate_distance < threshold) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    const int maximum_n = argc == 2 ? std::atoi(argv[1]) : 100000;
    if (maximum_n < 368) {
        std::cerr << "maximum_n must be at least 368\n";
        return 2;
    }

    long long parameter_pairs = 0;
    for (int n = 368; n <= maximum_n; ++n) {
        const int threshold = (2 * n + 6) / 7;  // ceil(2n/7)
        for (int q = 0; q < n; ++q) {
            ++parameter_pairs;
            if (meets_direct_c7_threshold(n, q, threshold)) {
                std::cout << "construction found: n=" << n << " q=" << q
                          << " minimum distance >= " << threshold << '\n';
                return 1;
            }
        }
    }

    std::cout << "no direct cyclic construction for 368 <= n <= "
              << maximum_n << '\n';
    std::cout << "parameter pairs tested: " << parameter_pairs << '\n';
}
