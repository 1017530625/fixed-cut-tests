"""Orbit enumeration by signed axis permutations on actual four-element cut families."""
import argparse
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import json

V = range(8)
ALL = 255
SIDES = tuple(range(2, 256, 2))


def canonical(mask):
    return mask ^ ALL if mask & 1 else mask


def transform_mask(mask, g):
    return sum(1 << g[v] for v in V if mask & 1 << v)


def compose(g, h):
    return tuple(g[u] for u in h)


def signed_axis_group():
    group = {}
    for p in permutations(range(3)):
        inversions = sum(p[i] > p[j] for i, j in combinations(range(3), 2))
        for flip in V:
            g = tuple(flip ^ sum(((u >> p[i]) & 1) << i for i in range(3)) for u in V)
            group[g] = (-1) ** (inversions + flip.bit_count())
    assert len(group) == 48 and sum(d == 1 for d in group.values()) == 24
    assert all(group[compose(g,h)] == group[g] * group[h] for g in group for h in group)
    return group


def witnesses():
    edges = tuple((1 << a) | (1 << b) for a,b in combinations(V, 2) if (a ^ b).bit_count() == 1)
    result = []
    for u in range(4):
        ring = ALL ^ ((1 << u) | (1 << (u ^ 7)))
        for a, b, c in combinations(edges, 3):
            if (a | b | c) == ring:
                result.append(tuple(sorted((a,b,c))))
    assert len(set(result)) == len(result) == 8
    return result


def detection(mask, matching):
    sides = [mask & edge for edge in matching]
    return all(part in (0,edge) for part,edge in zip(sides,matching)) and 0 < sum(bool(p) for p in sides) < 3


def get_orbits(universe, maps):
    remaining = set(universe)
    orbits = []
    while remaining:
        representative = min(remaining)
        orbit = {tuple(sorted(table[a] for a in representative)) for table in maps}
        assert representative in orbit and orbit <= remaining
        remaining -= orbit
        orbits.append({"size": len(orbit), "representative": list(representative), "members": sorted(orbit)})
    return orbits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("output", type=Path)
    output = ap.parse_args().output
    group, W = signed_axis_group(), witnesses()
    hits = {A: sum(1 << j for j,M in enumerate(W) if detection(A,M)) for A in range(256)}
    assert all(hits[A ^ ALL] == hits[A] for A in range(256))
    # Inspect every choice, including all cuts with empty detection signature.
    families = {(a,b,c,d) for a,b,c,d in combinations(SIDES,4)
                if (hits[a] | hits[b] | hits[c] | hits[d]) == 255}
    assert len(families) == 1116
    actions = {}
    fixed = {}
    for g in group:
        table = {A: canonical(transform_mask(A,g)) for A in SIDES}
        assert set(table.values()) == set(SIDES)
        witness_image = tuple(W.index(tuple(sorted(transform_mask(edge,g) for edge in M))) for M in W)
        for A in SIDES:
            assert transform_mask(hits[A],witness_image) == hits[table[A]]
        actions[g] = table
        images = {family: tuple(sorted(table[a] for a in family)) for family in families}
        assert set(images.values()) == families
        fixed[g] = sum(a == b for a,b in images.items())
    # Compose on canonical (unordered) cuts, including a possible reversal of either side.
    for g in group:
        for h in group:
            gh = actions[compose(g,h)]
            assert all(gh[A] == actions[g][actions[h][A]] for A in SIDES)
    partitions = {}
    for name, members in [("full", list(group)), ("rotations",[g for g in group if group[g] == 1])]:
        orbits = get_orbits(families,[actions[g] for g in members])
        assert sum(a["size"] for a in orbits) == len(families)
        partitions[name] = {"group_size":len(members), "orbit_count":len(orbits),
                            "size_distribution":dict(sorted(Counter(o["size"] for o in orbits).items())),
                            "fixed_distribution":dict(sorted(Counter(fixed[g] for g in members).items())),
                            "orbits":orbits}
    result = {"script":"explicit_orbits.py","labelled_families":len(families),
              "canonical_side":"8-bit vertex membership mask with bit zero clear",
              "partitions":partitions,"elements":[{"permutation":list(g),"det":group[g],
              "fixed":fixed[g]} for g in sorted(group)]}
    output.write_text(json.dumps(result, separators=(",",":"), sort_keys=True)+"\n", encoding="utf8")
    for k,v in partitions.items():
        print(k,"orbits",v["orbit_count"],"orbit sizes",v["size_distribution"],"fixed counts",v["fixed_distribution"])


if __name__ == "__main__":
    main()
