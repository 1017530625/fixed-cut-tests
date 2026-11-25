"""Finite checks of the corner identities and witness incidence in Sections 2–3."""
from collections import Counter
from itertools import combinations, product
import json


def check_regions(d):
    bits = list(product(range(2), repeat=d))
    cases = 0
    for membership in product(({0}, {1}, {0, 1}), repeat=d):
        inclusive = {p for p in bits if all(b in m for b, m in zip(p, membership))}
        for p in bits:
            private = all(m == {b} for b, m in zip(p, membership))
            unique_region = p in inclusive and len(inclusive) == 1
            assert unique_region == private
            if d == 2:
                # Membership in the second side of (X∩U,Y∪W).
                opposite_union = any(1-b in m for b, m in zip(p, membership))
                close = p in inclusive
                assert close or opposite_union
                assert private == (close and not opposite_union)
                assert (close and opposite_union) == (close and not private)
            cases += 1
    return cases


def cube_evidence():
    vertices = frozenset(range(8))
    cube_edges = [frozenset((x,y)) for x,y in combinations(vertices,2) if (x^y).bit_count() == 1]
    sides = [frozenset(v for v in vertices if mask & (1<<v)) for mask in range(2,256,2)]
    halves = [frozenset(v for v in vertices if v & (1<<bit) == 0) for bit in range(3)]
    parity = [frozenset(v for v in vertices if v.bit_count()%2 == i) for i in range(2)]
    rings = [vertices - {v,7^v} for v in range(4)]
    covers = {frozenset(v for v in vertices if mask & (1<<v)) for mask in range(256)}
    covers = {s for s in covers if all(s & edge for edge in cube_edges)}
    assert {s for s in covers if not any(cls<=s for cls in parity)} == set(rings)
    assert len(covers) == 35

    def split(e,side):
        return bool(e & side and e-side)

    # Verify the paper's additive identities on each indivisible face weight.
    face_count = 0
    for coords in product((None,0,1),repeat=3):
        f = {v for v in vertices if all(b is None or b==(v>>i)&1 for i,b in enumerate(coords))}
        edges = [e for e in cube_edges if e<=f]
        dim = coords.count(None)
        cut = lambda a: int(any(split(e,a) for e in edges))
        h,s1,s2 = [int(dim==k) for k in (3,1,2)]
        coord_sum = sum(cut(a) for a in halves)
        assert coord_sum == 3*h+s1+2*s2
        for cls in parity:
            assert sum(cut({v}) for v in cls) == 4*h+s1+2*s2
        for ring in rings:
            outside = int(dim==1 and not f<=ring)
            assert sum(cut({v}) for v in ring)+outside+s2 == 2*coord_sum
        face_count += 1

    witnesses = []
    active_records = 0
    for ring in rings:
        r_edges = [e for e in cube_edges if e<=ring]
        pair = [m for m in combinations(r_edges,3) if frozenset.union(*m)==ring]
        assert len(pair)==2 and set(pair[0]).isdisjoint(pair[1])
        witnesses.extend((ring,m) for m in pair)
        for side in sides:
            if not split(ring,side):
                continue
            a,b = [sum(split(e,side) for e in m) for m in pair]
            assert (a>=1 and b>=1) or (a,b) in ((0,2),(2,0))
            active_records += 1

    def detects(side,witness):
        ring,edges=witness
        return split(ring,side) and all(not split(e,side) for e in edges)

    hit_count = Counter()
    size_hits = Counter()
    for side in sides:
        hits = sum(detects(side,w) for w in witnesses)
        hit_count[hits] += 1
        if hits:
            size_hits[min(len(side),8-len(side))] += 1
        for ring,edges in witnesses:
            passes = not split(ring,side) or sum(split(e,side) for e in edges) >= 1
            assert passes != detects(side,(ring,edges))
            assert detects(side,(ring,edges)) == detects(vertices-side,(ring,edges))
    assert hit_count == {0:79,2:48} and size_hits == {2:12,3:24,4:12}
    for bit in range(3):
        parallel = [e for e in cube_edges if split(e,halves[bit])]
        assert len(parallel)==4
        for ring,edges in witnesses:
            assert sum(split(e,halves[bit]) for e in edges)==1
            assert all(sum(split(e,{v}) for e in edges)==1 for v in ring)
            assert sum(detects(side,(ring,edges)) for side in parallel)==1
    return {
        'cube_faces':face_count, 'vertex_covers':len(covers),'parity_class_covers':len(covers)-4,
        'six_cycle_covers':len(rings),'witnesses':len(witnesses),'proper_unordered_cuts':len(sides),
        'threshold_one_witness_cut_checks':len(witnesses)*len(sides),
        'active_ring_cut_patterns_checked':active_records,'witnesses_per_cut':dict(hit_count),
        'detecting_cuts_by_smaller_side':dict(size_hits),'parallel_edge_families':3}


if __name__=='__main__':
    evidence=cube_evidence()
    evidence['pair_vertex_membership_checks']=check_regions(2)
    evidence['triple_vertex_membership_checks']=check_regions(3)
    assert evidence['pair_vertex_membership_checks']==36 and evidence['triple_vertex_membership_checks']==216
    print(json.dumps(evidence,ensure_ascii=True,sort_keys=True))
