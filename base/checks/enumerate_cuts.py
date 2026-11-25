"""Recompute the optimal labelled families from all proper unordered cube cuts.

Each bipartition is represented by its unique side not containing vertex 000.
The only inputs are the binary definition of cube adjacency and the definition
of a face crossing a cut. Counts can be replayed using Python's standard library.
"""

from collections import Counter
from itertools import combinations
from math import comb
import json


def split(side, edge):
    return (side & edge).bit_count() == 1


def main():
    vertices = range(8)
    edges = [(1 << u) | (1 << v) for u, v in combinations(vertices, 2)
             if (u ^ v).bit_count() == 1]
    cuts = list(range(2, 256, 2))
    rings = [255 ^ ((1 << v) | (1 << (v ^ 7))) for v in range(4)]
    matchings = []
    for ring in rings:
        choices = [m for m in combinations(edges, 3) if m[0] | m[1] | m[2] == ring]
        assert len(choices) == 2
        matchings.extend(choices)

    def witness_mask(side):
        mask = 0
        for j, matching in enumerate(matchings):
            ring = rings[j // 2]
            if side & ring and ~side & ring and sum(split(side, e) for e in matching) < 1:
                mask |= 1 << j
        return mask

    rows = {side: witness_mask(side) for side in cuts}
    assert all(mask == witness_mask(side ^ 255) for side, mask in rows.items())
    covered_by_one = Counter(mask.bit_count() for mask in rows.values())
    all_witnesses = (1 << 8) - 1
    assert max(covered_by_one) == 2  # Three tests cover at most six witnesses.
    counts = Counter(rows.values())
    four_count = sum((a | b | c | d) == all_witnesses
                     for a, b, c, d in combinations(rows.values(), 4))
    pair_sides = [e if e & 1 == 0 else 255 ^ e for e in edges]
    pair_count = sum((rows[a] | rows[b] | rows[c] | rows[d]) == all_witnesses
                     for a, b, c, d in combinations(pair_sides, 4))
    per_ring = []
    for q, ring in enumerate(rings):
        m, n = matchings[2*q:2*q+2]
        coefficient_pairs = Counter()
        for side in cuts:
            if not (side & ring and ~side & ring):
                continue
            a, b = sum(split(side, e) for e in m), sum(split(side, e) for e in n)
            # With alternating weights u,v, the inequality is (a-1)u+(b-1)v >= 0.
            assert (a, b) in {(0, 2), (2, 0)} or min(a, b) >= 1
            coefficient_pairs[a, b] += 1
        both = 3 << (2*q)
        number = sum(((rows[a] | rows[b]) & both) == both for a, b in combinations(cuts, 2))
        assert all((mask & both) != both for mask in rows.values())
        per_ring.append({'vertices': [v for v in vertices if ring & (1 << v)],
                         'coefficient_histogram': {f'{a},{b}': value
                                                   for (a, b), value in sorted(coefficient_pairs.items())},
                         'two_cut_families': number})
    example = next(s for s in combinations([a for a in cuts if a.bit_count() == 4], 4)
                   if rows[s[0]] | rows[s[1]] | rows[s[2]] | rows[s[3]] == all_witnesses)
    print(json.dumps({'canonical_proper_cuts': len(cuts), 'by_witnesses_rejected': covered_by_one,
                      'active_pair_signatures': {str(k): n for k, n in
                                                   sorted(Counter(c for m, c in counts.items() if m).items())},
                      'four_cut_families_examined': comb(len(cuts), 4),
                      'sufficient_four_cut_families': four_count,
                      'sufficient_adjacent_four_cut_families': pair_count,
                      'optimal_example_with_all_sides_balanced':
                          [[v for v in vertices if a & (1 << v)] for a in example],
                      'rings': per_ring}, indent=2))


if __name__ == '__main__':
    main()
