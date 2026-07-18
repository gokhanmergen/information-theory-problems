#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <iterator>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Word = std::array<int, 5>;
constexpr int kAlphabet = 7;
constexpr int kDimension = 5;
constexpr int kVertexCount = 16807;  // 7^5
constexpr int kRecordSize = 367;
constexpr int kRadius = 5;

std::array<Word, kVertexCount> words;

int word_id(const Word& word) {
    int value = 0;
    for (int letter : word) value = kAlphabet * value + letter;
    return value;
}

std::vector<int> closed_neighborhood(int vertex) {
    std::vector<int> result;
    result.reserve(243);  // 3^5
    const Word& word = words[vertex];
    for (int code = 0; code < 243; ++code) {
        int remaining = code;
        Word neighbor{};
        for (int coordinate = 0; coordinate < kDimension; ++coordinate) {
            const int trit = remaining % 3;
            remaining /= 3;
            const int delta = trit == 1 ? 1 : (trit == 2 ? -1 : 0);
            neighbor[coordinate] =
                (word[coordinate] + delta + kAlphabet) % kAlphabet;
        }
        result.push_back(word_id(neighbor));
    }
    return result;
}

// A subset of at most five indices from {0,...,366}, packed into 9-bit fields.
// Stored values are index+1, so zero terminates the encoding.
std::uint64_t encode_indices(std::vector<int> indices) {
    std::sort(indices.begin(), indices.end());
    indices.erase(std::unique(indices.begin(), indices.end()), indices.end());
    std::uint64_t encoded = 0;
    int shift = 0;
    for (int index : indices) {
        encoded |= std::uint64_t(index + 1) << shift;
        shift += 9;
    }
    return encoded;
}

std::vector<int> decode_indices(std::uint64_t encoded) {
    std::vector<int> result;
    while (encoded != 0) {
        result.push_back(int(encoded & 511) - 1);
        encoded >>= 9;
    }
    return result;
}

// UINT64_MAX denotes a union larger than the exchange radius.
std::uint64_t bounded_union(std::uint64_t left, std::uint64_t right) {
    const std::vector<int> a = decode_indices(left);
    const std::vector<int> b = decode_indices(right);
    std::vector<int> result;
    result.reserve(2 * kRadius);
    std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                   std::back_inserter(result));
    if (result.size() > kRadius) return UINT64_MAX;
    return encode_indices(result);
}

std::vector<int> reconstruct_record_set(
    const std::vector<std::vector<int>>& neighborhoods) {
    // Polak--Schrijver steps (i)--(iii).
    const int shift[kDimension] = {40, 123, 40, 123, 40};
    const int powers[kDimension] = {1, 7, 49, 343, 109};
    std::unordered_set<int> mapped;
    for (int t = 0; t < 382; ++t) {
        Word word{};
        for (int coordinate = 0; coordinate < kDimension; ++coordinate) {
            const int residue =
                (t * powers[coordinate] + shift[coordinate]) % 382;
            word[coordinate] = (2 * residue) / 109;
        }
        mapped.insert(word_id(word));
    }

    // Step (iv): the 327 mapped words having no mapped conflict.
    std::vector<int> record;
    for (int vertex : mapped) {
        bool isolated = true;
        for (int neighbor : neighborhoods[vertex]) {
            if (neighbor != vertex && mapped.contains(neighbor)) {
                isolated = false;
                break;
            }
        }
        if (isolated) record.push_back(vertex);
    }
    assert(record.size() == 327);

    // The 40-word extension from the paper's appendix.
    const std::string extension =
        "00521 01005 02533 03565 04052 04365 04624 04660 05046 05225 "
        "10534 14246 15435 22524 24615 24651 32046 34035 34043 36525 "
        "40040 41246 42530 43514 45641 50531 51456 52400 52563 53050 "
        "53142 53320 53412 56340 61505 62425 64154 64340 65105 66025";
    for (std::size_t position = 0; position < extension.size();) {
        while (position < extension.size() && extension[position] == ' ') ++position;
        if (position == extension.size()) break;
        Word word{};
        for (int coordinate = 0; coordinate < kDimension; ++coordinate) {
            word[coordinate] = extension[position++] - '0';
        }
        record.push_back(word_id(word));
    }

    std::sort(record.begin(), record.end());
    record.erase(std::unique(record.begin(), record.end()), record.end());
    assert(record.size() == kRecordSize);
    return record;
}

bool confusable(int left, int right) {
    for (int coordinate = 0; coordinate < kDimension; ++coordinate) {
        const int difference =
            (words[left][coordinate] - words[right][coordinate] + kAlphabet) %
            kAlphabet;
        if (difference != 0 && difference != 1 && difference != 6) return false;
    }
    return true;
}

bool has_independent_six(const std::vector<int>& candidates) {
    std::vector<int> chosen;
    const auto search = [&](const auto& self, int position) -> bool {
        if (chosen.size() == 6) return true;
        if (chosen.size() + candidates.size() - position < 6) return false;
        for (int i = position; i < int(candidates.size()); ++i) {
            bool compatible = true;
            for (int previous : chosen) {
                if (confusable(previous, candidates[i])) {
                    compatible = false;
                    break;
                }
            }
            if (compatible) {
                chosen.push_back(candidates[i]);
                if (self(self, i + 1)) return true;
                chosen.pop_back();
            }
        }
        return false;
    };
    return search(search, 0);
}

int main() {
    for (int vertex = 0; vertex < kVertexCount; ++vertex) {
        int remaining = vertex;
        for (int coordinate = kDimension - 1; coordinate >= 0; --coordinate) {
            words[vertex][coordinate] = remaining % kAlphabet;
            remaining /= kAlphabet;
        }
    }

    std::vector<std::vector<int>> neighborhoods(kVertexCount);
    for (int vertex = 0; vertex < kVertexCount; ++vertex) {
        neighborhoods[vertex] = closed_neighborhood(vertex);
        std::sort(neighborhoods[vertex].begin(), neighborhoods[vertex].end());
    }

    const std::vector<int> record = reconstruct_record_set(neighborhoods);
    std::vector<char> in_record(kVertexCount, false);
    for (int i = 0; i < kRecordSize; ++i) {
        in_record[record[i]] = true;
        for (int j = i + 1; j < kRecordSize; ++j) {
            assert(!std::binary_search(neighborhoods[record[i]].begin(),
                                       neighborhoods[record[i]].end(), record[j]));
        }
    }

    // The record-neighborhood N_R(x) of each word outside R.
    std::vector<std::vector<int>> record_neighbors(kVertexCount);
    for (int index = 0; index < kRecordSize; ++index) {
        for (int neighbor : neighborhoods[record[index]]) {
            if (neighbor != record[index]) record_neighbors[neighbor].push_back(index);
        }
    }

    // Group outside words by their N_R(x), retaining masks of size at most five.
    std::unordered_map<std::uint64_t, std::vector<int>> groups;
    std::array<std::size_t, 20> conflict_histogram{};
    for (int vertex = 0; vertex < kVertexCount; ++vertex) {
        if (in_record[vertex]) continue;
        const std::size_t degree = record_neighbors[vertex].size();
        ++conflict_histogram[degree];
        if (degree >= 1 && degree <= kRadius) {
            groups[encode_indices(record_neighbors[vertex])].push_back(vertex);
        }
    }
    assert(conflict_histogram[0] == 0);

    std::vector<std::uint64_t> group_keys;
    std::size_t candidate_word_count = 0;
    for (const auto& [key, vertices] : groups) {
        group_keys.push_back(key);
        candidate_word_count += vertices.size();
    }

    // Generate the closure of the occurring masks under unions of size <= 5.
    std::unordered_set<std::uint64_t> unions;
    unions.reserve(1'500'000);
    std::vector<std::uint64_t> queue;
    queue.reserve(1'500'000);
    const auto add_union = [&](std::uint64_t key) {
        if (unions.insert(key).second) queue.push_back(key);
    };
    add_union(0);
    for (std::uint64_t key : group_keys) add_union(key);

    for (std::size_t position = 0; position < queue.size(); ++position) {
        const std::uint64_t current = queue[position];
        const std::vector<int> members = decode_indices(current);
        const int size = members.size();

        if (size <= 3) {
            // A new mask can add at most 5-size members; scan all occurring masks.
            for (std::uint64_t other : group_keys) {
                const std::uint64_t combined = bounded_union(current, other);
                if (combined != UINT64_MAX) add_union(combined);
            }
        } else if (size == 4) {
            // A strict bounded extension is current plus one index j. It occurs iff
            // some candidate mask contained in current U {j} contains j.
            std::array<bool, kRecordSize> present{};
            for (int member : members) present[member] = true;
            for (int added = 0; added < kRecordSize; ++added) {
                if (present[added]) continue;
                std::vector<int> five_set = members;
                five_set.push_back(added);
                std::sort(five_set.begin(), five_set.end());

                bool extends = false;
                for (int bits = 1; bits < 32 && !extends; ++bits) {
                    std::vector<int> subset;
                    bool contains_added = false;
                    for (int bit = 0; bit < 5; ++bit) {
                        if ((bits >> bit) & 1) {
                            subset.push_back(five_set[bit]);
                            if (five_set[bit] == added) contains_added = true;
                        }
                    }
                    if (contains_added && groups.contains(encode_indices(subset))) {
                        extends = true;
                    }
                }
                if (extends) add_union(encode_indices(five_set));
            }
        }
    }

    std::array<std::size_t, 6> union_count_by_size{};
    for (std::uint64_t key : unions) {
        ++union_count_by_size[decode_indices(key).size()];
    }

    // For every occurring five-word removal mask S, collect all x with N_R(x)
    // contained in S, then exhaustively test all six-subsets for independence.
    std::size_t relevant_five_sets = 0;
    std::size_t maximum_pool_size = 0;
    std::array<std::size_t, 20> pool_histogram{};
    for (std::uint64_t removal_key : unions) {
        const std::vector<int> removal = decode_indices(removal_key);
        if (removal.size() != 5) continue;

        std::vector<int> candidates;
        for (int bits = 1; bits < 32; ++bits) {
            std::vector<int> subset;
            for (int bit = 0; bit < 5; ++bit) {
                if ((bits >> bit) & 1) subset.push_back(removal[bit]);
            }
            const auto found = groups.find(encode_indices(subset));
            if (found != groups.end()) {
                candidates.insert(candidates.end(), found->second.begin(),
                                  found->second.end());
            }
        }

        maximum_pool_size = std::max(maximum_pool_size, candidates.size());
        if (candidates.size() < 6) continue;
        ++relevant_five_sets;
        ++pool_histogram[candidates.size()];
        if (has_independent_six(candidates)) {
            std::cerr << "Found a 5-to-6 improving exchange; certificate failed.\n";
            return 1;
        }
    }

    std::cout << "record size: " << record.size() << '\n';
    std::cout << "candidate mask keys of size <= 5: " << groups.size() << '\n';
    std::cout << "candidate words of mask size <= 5: " << candidate_word_count << '\n';
    std::cout << "union masks by size:";
    for (int size = 0; size <= 5; ++size) {
        std::cout << ' ' << size << ':' << union_count_by_size[size];
    }
    std::cout << '\n';
    std::cout << "five-masks with at least six candidates: "
              << relevant_five_sets << '\n';
    std::cout << "candidate-pool histogram:";
    for (std::size_t size = 6; size < pool_histogram.size(); ++size) {
        if (pool_histogram[size] != 0) {
            std::cout << ' ' << size << ':' << pool_histogram[size];
        }
    }
    std::cout << '\n';
    std::cout << "maximum candidate-pool size: " << maximum_pool_size << '\n';
    std::cout << "no improving exchange deleting at most five words\n";
}
