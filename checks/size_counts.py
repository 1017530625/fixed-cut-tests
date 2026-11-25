"""Count actual four-cut families by the number of 2-, 3- and 4-corner smaller sides."""

from collections import Counter
from itertools import combinations
import json
from math import comb

from burnside_cycles import objects


def predicted_coefficients():
    """Expand 9(a+2b)^4 + 42(a+2b)^2 c^2 + 9c^4 by the binomial theorem."""
    counts = {}
    for crossing, pairings in [(4, 9), (2, 42), (0, 9)]:
        for triples in range(crossing + 1):
            profile = (crossing - triples, triples, 4 - crossing)
            counts[profile] = pairings * comb(crossing, triples) * 2**triples
    return counts


def main():
    cuts, witnesses, detects = objects()
    witness_bit = {witness: 1 << i for i, witness in enumerate(witnesses)}
    all_hits = (1 << len(witnesses)) - 1
    pair_profiles = {frozenset(pair): Counter() for pair in combinations(witnesses, 2)}
    rows = []
    for cut in cuts:
        small_side = min(map(len, cut))
        hits = detects[cut]
        assert len(hits) in (0, 2)
        if hits:
            assert small_side in (2, 3, 4)
            pair_profiles[hits][small_side] += 1
        rows.append((sum(witness_bit[w] for w in hits), small_side))

    pair_types = Counter(tuple(sizes[s] for s in (2, 3, 4)) for sizes in pair_profiles.values())
    assert pair_types == {(1, 2, 0): 12, (0, 0, 1): 12, (0, 0, 0): 4}

    # Each row denotes a distinct unordered cut. Equal signatures keep their multiplicity.
    counts = Counter()
    for (first, u), (second, v), (third, w), (fourth, x) in combinations(rows, 4):
        if (first | second | third | fourth) == all_hits:
            sizes = (u, v, w, x)
            counts[sizes.count(2), sizes.count(3), sizes.count(4)] += 1
    assert counts == predicted_coefficients()

    restricted = {
        "balanced_only": counts[0, 0, 4],
        "two_corner_only": counts[4, 0, 0],
        "three_corner_only": counts[0, 4, 0],
        "at_most_three_corners": sum(n for (a, b, c), n in counts.items() if c == 0),
        "no_two_corner_side": sum(n for (a, b, c), n in counts.items() if a == 0),
    }
    result = {
        "source_geometry": "burnside_cycles.objects; raw vertex triples and unordered bipartitions",
        "unoriented_proper_cuts": len(rows),
        "distinct_witness_pairs": len(pair_profiles),
        "candidate_four_cut_families": comb(len(rows), 4),
        "sufficient_four_cut_families": sum(counts.values()),
        "coefficients": [
            {"two": a, "three": b, "four": c, "families": counts[a, b, c]}
            for a, b, c in sorted(counts)
        ],
        "restricted_families": restricted,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
