"""Burnside count without constructing the 1,116 families or using a side representative."""
import argparse
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import json

# The numerical labels are only for reporting vertex permutations. Geometry uses triples.
POINTS = tuple(tuple((u >> i) & 1 for i in range(3)) for u in range(8))
Q = frozenset(POINTS)


def adjacent(a,b):
    return sum(x != y for x,y in zip(a,b)) == 1


def matchings(R):
    if not R:
        yield frozenset()
        return
    a = min(R)
    for b in R - {a}:
        if adjacent(a,b):
            e = frozenset((a,b))
            for rest in matchings(R-e):
                yield rest | {e}


def objects():
    W = set()
    for a in Q:
        opposite = tuple(1-x for x in a)
        W.update(matchings(Q-{a,opposite}))
    cuts = set()
    for size in range(1,8):
        for subset in combinations(POINTS,size):
            left = frozenset(subset)
            cuts.add(frozenset((left,Q-left)))
    assert len(W) == 8 and len(cuts) == 127
    detects = {}
    for cut in cuts:
        found = set()
        for M in W:
            # A side contains exactly one entire matched edge, its opposite contains two.
            distribution = sorted(sum(e <= side for e in M) for side in cut)
            if distribution == [1,2]:
                found.add(M)
        detects[cut] = frozenset(found)
    return cuts, frozenset(W), detects


def determinant(cols):
    (a,d,g),(b,e,h),(c,f,i) = cols
    return a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)


def automorphisms():
    E = [(u,v) for u,v in combinations(range(8),2) if adjacent(POINTS[u],POINTS[v])]
    # Every vertex bijection that maps all 12 edges into the graph is an automorphism.
    for p in permutations(range(8)):
        if all(adjacent(POINTS[p[u]],POINTS[p[v]]) for u,v in E):
            base = POINTS[p[0]]
            cols = [tuple(x-y for x,y in zip(POINTS[p[1 << i]],base)) for i in range(3)]
            sign = determinant(cols)
            assert sign in (-1,1)
            yield p,dict(zip(POINTS,(POINTS[j] for j in p))),sign


def cycle_data(cuts, g, detect):
    unseen = set(cuts)
    blocks = []
    while unseen:
        first = next(iter(unseen))
        cut = first
        orbit = []
        while cut in unseen:
            unseen.remove(cut)
            orbit.append(cut)
            cut = frozenset(frozenset(g[x] for x in side) for side in cut)
        assert cut == first
        blocks.append((len(orbit),frozenset.union(*(detect[c] for c in orbit))))
    assert sum(n for n,_ in blocks) == len(cuts)
    return blocks


def fixed_by_cycles(blocks, all_witnesses):
    counts = Counter({(0,frozenset()):1})
    for length,hits in blocks:
        if length > 4:
            continue
        nxt = counts.copy()
        for (size,covered),number in counts.items():
            if size+length <= 4:
                nxt[(size+length,covered|hits)] += number
        counts = nxt
    return counts[4,all_witnesses]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("output", type=Path)
    output = ap.parse_args().output
    cuts,W,detected = objects()
    rows = []
    for p,g,sign in automorphisms():
        blocks = cycle_data(cuts,g,detected)
        rows.append({"permutation":list(p),"det":sign, "fixed":fixed_by_cycles(blocks,W),
                     "cut_cycle_lengths":dict(sorted(Counter(n for n,_ in blocks).items()))})
    assert len(rows) == 48
    result = {"script":"burnside_cycles.py","elements":rows,"groups":{}}
    for name,which in (("full",rows),("rotations",[r for r in rows if r["det"]==1])):
        counts = Counter(r["fixed"] for r in which)
        total = sum(r["fixed"] for r in which)
        q, r = divmod(total,len(which))
        assert r == 0
        result["groups"][name] = {"group_size":len(which), "fixed_sum":total,
                                  "fixed_distribution":dict(sorted(counts.items())), "orbits":q}
        print(name,"sum fixed",total,"group order",len(which),"orbits",q,"fixed histogram",dict(sorted(counts.items())))
    output.write_text(json.dumps(result,sort_keys=True,separators=(",",":"))+"\n",encoding="utf8")


if __name__ == "__main__":
    main()
