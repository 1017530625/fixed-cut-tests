"""Finite, graph-first checks of the cubical diagram statements using only the Python standard library."""

from collections import Counter, deque
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
from time import perf_counter
import json
import platform


HERE = Path(__file__).resolve().parent
STATS = Counter()


def geometry(d):
    corners = range(1 << d)
    all_corners = (1 << len(corners)) - 1
    edges = [(p, q) for p, q in combinations(corners, 2) if (p ^ q).bit_count() == 1]
    faces = list(product((0, 1, 2), repeat=d))  # 2 denotes a free bit.
    members = [sum(1 << p for p in corners
                   if all(t == 2 or t == ((p >> i) & 1) for i, t in enumerate(f))) for f in faces]
    neighbors = {p: [q for q in corners if (p ^ q).bit_count() == 1] for p in corners}
    for inside in members:
        for p in corners:
            if not inside & (1 << p):
                continue
            dist = {p: 0}
            queue = deque([p])
            while queue:
                current = queue.popleft()
                for q in neighbors[current]:
                    if q not in dist and inside & (1 << q):
                        dist[q] = dist[current] + 1
                        queue.append(q)
            for q in corners:
                if inside & (1 << q):
                    assert dist[q] == (p ^ q).bit_count()
                    STATS["ordered_pairs_inside_faces_distance_checked"] += 1
    active = []
    for subset in range(all_corners + 1):
        marked = 0
        boundary_edges = [(p, q) for p, q in edges if ((subset >> p) ^ (subset >> q)) & 1]
        for i, inside in enumerate(members):
            contains_edge = any(inside & (1 << p) and inside & (1 << q) for p, q in boundary_edges)
            straddles = bool(inside & subset and inside & (all_corners ^ subset))
            assert contains_edge == straddles
            marked |= int(contains_edge) << i
            STATS["face_cut_incidence_checks"] += 1
        active.append(marked)
    for subset in range(all_corners + 1):
        assert active[subset] == active[all_corners ^ subset]
    halves = [[sum(1 << p for p in corners if ((p >> i) & 1) == b) for b in (0, 1)] for i in range(d)]
    return corners, faces, {f: i for i, f in enumerate(faces)}, members, active, halves


def valid_separations(n, edge_list):
    universe = (1 << n) - 1
    choices = []
    for left in range(universe + 1):
        for right in range(universe + 1):
            if left | right != universe:
                continue
            exclusive_l, exclusive_r = left & ~right, right & ~left
            if any((edge & exclusive_l) and (edge & exclusive_r) for edge in edge_list):
                continue
            choices.append((left, right))
    return choices


def components(n, D, geom):
    corners, faces, face_number, members, active, halves = geom
    universe = (1 << n) - 1
    region = []
    for p in corners:
        vertices = universe
        for i, sides in enumerate(D):
            vertices &= sides[(p >> i) & 1]
        region.append(vertices)
    labels = []
    for x in range(n):
        vx = 1 << x
        label = tuple(2 if left & right & vx else 0 if left & vx else 1 for left, right in D)
        face_id = face_number[label]
        labels.append(face_id)
        assert members[face_id] == sum(1 << p for p in corners if region[p] & vx)
    aggregates = [0]
    largest_region = [-1]
    for subset in range(1, len(active)):
        bit = subset & -subset
        p = bit.bit_length() - 1
        aggregates.append(aggregates[subset ^ bit] | region[p])
        largest_region.append(max(largest_region[subset ^ bit], region[p].bit_count()))
    weights = Counter(labels)
    masses = list(weights.items())
    values = [sum(weight for face, weight in masses if marked & (1 << face)) for marked in active]
    return labels, region, aggregates, largest_region, weights, values


def unbreakability_thresholds(n, choices):
    eligible = []
    for q in range(n + 2):
        for k in range(n + 2):
            if k == 0 or all((left & right).bit_count() >= k
                             or min((left & ~right).bit_count(), (right & ~left).bit_count()) <= q
                             for left, right in choices):
                eligible.append((q, k))
    return eligible


def verify_diagram(n, d, edge_list, D, geom, valid, thresholds):
    corners, faces, face_number, members, active, halves = geom
    labels, region, aggregates, maxima, weights, values = components(n, D, geom)
    all_corners = len(active) - 1
    for edge in edge_list:
        assert any((vertices & edge) == edge for vertices in region)
        STATS["graph_edge_shared_corner_checks"] += 1
    for i, (left, right) in enumerate(D):
        a, b = halves[i]
        assert (aggregates[a], aggregates[b]) == (left, right)
        assert (aggregates[b], aggregates[a]) == (right, left)
        assert values[a] == values[b] == (left & right).bit_count()
        STATS["input_oriented_coordinate_recoveries"] += 1
    for p in corners:
        opposite_side_union = 0
        for i, sides in enumerate(D):
            opposite_side_union |= sides[1 - ((p >> i) & 1)]
        assert aggregates[all_corners ^ (1 << p)] == opposite_side_union
    for side, left in enumerate(aggregates):
        other = all_corners ^ side
        right = aggregates[other]
        assert (left, right) in valid
        assert (left & right).bit_count() == values[side] == values[other]
        STATS["graph_lifted_cut_checks"] += 1
        max_both = min(maxima[side], maxima[other])
        for q, k in thresholds:
            if max_both >= q + k:
                assert values[side] >= k
                STATS["applicable_large_corner_bounds_at_positive_k" if k else
                      "applicable_large_corner_bounds_at_k_zero"] += 1
    if d == 2:
        base = sum((left & right).bit_count() for left, right in D)
        for p in (0, 1):  # Both pairs of opposite corners.
            q = 3 ^ p
            a0, b0 = D[0][p & 1], D[0][1 - (p & 1)]
            a1, b1 = D[1][(p >> 1) & 1], D[1][1 - ((p >> 1) & 1)]
            assert (a0 & a1 & (b0 | b1)).bit_count() + (b0 & b1 & (a0 | a1)).bit_count() == base
            assert values[1 << p] + values[1 << q] == base
            STATS["opposite_pair_order_identities"] += 1
    if not D:
        assert len(faces) == len(corners) == 1 and region == [(1 << n) - 1]
        assert aggregates == [0, (1 << n) - 1] and values == [0, 0] and weights[0] == n
        STATS["empty_coordinate_diagrams"] += 1
    if n == 0:
        assert all(value == 0 for value in values)
        STATS["empty_graph_diagrams"] += 1


def weight_vectors(d, length):
    if d == 0:
        yield from ((mass,) for mass in (0, 1, 2, 7))
    elif d == 1:
        yield from product(range(3), repeat=length)
    elif d == 2:
        yield from product((0, 1), repeat=length)
        yield tuple(i % 4 for i in range(length))
    else:
        yield (0,) * length
        for j in range(length):
            yield tuple(2 if i == j else 0 for i in range(length))
        yield (1,) * length
        yield tuple((i * i + 2) % 4 for i in range(length))


def verify_realization(d, geom):
    corners, faces, _, _, active, _ = geom
    for wanted in weight_vectors(d, len(faces)):
        # The carrier stores a different vertex for each unit of prescribed face mass.
        carrier = [(face, k) for face, mass in zip(faces, wanted) for k in range(mass)]
        D = []
        for i in range(d):
            left = sum(1 << x for x, (f, _) in enumerate(carrier) if f[i] != 1)
            right = sum(1 << x for x, (f, _) in enumerate(carrier) if f[i] != 0)
            D.append((left, right))
        labels, _, aggregates, _, measured, values = components(len(carrier), D, geom)
        assert [faces[j] for j in labels] == [f for f, _ in carrier]
        assert tuple(measured[i] for i in range(len(faces))) == wanted
        for a, left in enumerate(aggregates):
            right = aggregates[len(active) - 1 - a]
            assert (left & right).bit_count() == values[a]
            STATS["realization_cut_orders"] += 1
        STATS["prescribed_weight_vectors"] += 1


def main():
    start = perf_counter()
    geometry_by_dimension = [geometry(d) for d in range(4)]
    per_model = []
    for n in range(4):
        complete_edges = [(1 << x) + (1 << y) for x, y in combinations(range(n), 2)]
        for graph_mask in range(1 << len(complete_edges)):
            edge_list = [e for j, e in enumerate(complete_edges) if graph_mask & (1 << j)]
            choices = valid_separations(n, edge_list)
            valid = set(choices)
            thresholds = unbreakability_thresholds(n, choices)
            for d in (range(4) if n <= 2 else range(3)):
                tested = 0
                for D in product(choices, repeat=d):
                    verify_diagram(n, d, edge_list, D, geometry_by_dimension[d], valid, thresholds)
                    tested += 1
                per_model.append({"n": n, "graph_mask": graph_mask, "dimension": d, "diagrams": tested})
    for d, geom in enumerate(geometry_by_dimension):
        verify_realization(d, geom)

    # Two exclusive unit vertex-face masses force a disconnection on a two-vertex host.
    one = geometry_by_dimension[1]
    target = (1, 1, 0)
    for graph, expected in (([], True), ([3], False)):
        found = any(tuple(result.get(f, 0) for f in range(3)) == target
                    for sides in valid_separations(2, graph)
                    for result in [components(2, [sides], one)[4]])
        assert found == expected

    elapsed = perf_counter() - start
    summary = {"python": platform.python_version(), "runtime_seconds": round(elapsed, 4),
               "definitions": "Actual ordered vertex separations L union R=V, no graph edge between L\\R and R\\L. Oriented subsets of cube corners include the empty and full sets.",
               "model_range": "All labelled simple graphs on 0,1,2,3 vertices; all indexed separation families in dimensions 0..3 for up to two vertices and 0..2 for three vertices.",
               "realization_range": "Dimension 0 masses 0,1,2,7. Dimension 1 all ternary vectors; dimension 2 all binary vectors plus one mixed higher vector. Dimension 3 zero, 27 single-face double masses, all ones, one mixed vector.",
               "hypothesis_range": "For each graph q,k run from zero through n+1. At k>0 global unbreakability checks every graph separation of order <k. At k=0 no unbreakability is required. Two opposite-side large inclusive corners must exist.",
               "n_labelled_graphs": sum(1 << (n*(n-1)//2) for n in range(4)),
               "input_diagrams": sum(x["diagrams"] for x in per_model),
               "checks": dict(sorted(STATS.items())), "per_model": per_model,
               "unrealizable_on_K2_but_edgeless_realizable": {"dimension": 1, "w(0),w(1),w(*)": target},
               "program_sha256": sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE / "model-results.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("Python", summary["python"], "graphs", summary["n_labelled_graphs"], "diagrams", summary["input_diagrams"])
    print(json.dumps(summary["checks"], indent=2))
    print("Runtime seconds", summary["runtime_seconds"])


if __name__ == "__main__":
    main()

