"""Recover both C24 examples from the graph adjacencies and oriented coordinate sides."""
from __future__ import annotations

import hashlib
import itertools
import json
import platform
import sys
from datetime import datetime, timezone
from pathlib import Path

VERTICES = frozenset(range(24))
GRAPH_EDGES = tuple((i, (i + 1) % 24) for i in sorted(VERTICES))
COORDINATES = "rst"
CUBE = tuple(f"{p:03b}" for p in range(8))
CUBE_EDGES = tuple((p, q) for p, q in itertools.combinations(CUBE, 2)
                   if sum(a != b for a, b in zip(p, q)) == 1)
FACES = tuple("".join(t) for t in itertools.product("01*", repeat=3))
FACE_CORNERS = {f: frozenset(p for p in CUBE if all(a == "*" or a == b for a, b in zip(f, p)))
                for f in FACES}
RING = ("001", "011", "010", "110", "100", "101")


def closed_arc(start, end):
    length = (end - start) % 24
    return frozenset((start + i) % 24 for i in range(length + 1))


def arc_pair(start, end):
    return closed_arc(start, end), closed_arc(end, start)


def coordinates_for_ring():
    # At 4j the vertex gets both corners of ring edge j, at the next three
    # vertices it gets only the latter corner, as in the formal definition.
    labels = {v: (RING[v // 4], RING[(v // 4 + 1) % 6]) if v % 4 == 0 else
              (RING[(v // 4 + 1) % 6],) for v in VERTICES}
    sides = tuple(tuple(frozenset(v for v, ps in labels.items() if any(p[i] == b for p in ps))
                        for b in "01") for i in range(3))
    assert sides == tuple(arc_pair(start, end) for start, end in [(20, 8), (12, 0), (4, 16)])
    return sides


def coordinates_for_nested():
    # Here the upper endpoint exceeds the lower in each zero-side interval.
    endpoints = ((0, 12), (8, 16), (4, 20))
    arc_sides = tuple(arc_pair(start, end) for start, end in endpoints)
    linear = tuple((frozenset(v for v in VERTICES if start <= v <= end),
                    frozenset(v for v in VERTICES if v <= start or end <= v))
                   for start, end in endpoints)
    assert linear == arc_sides
    assert arc_sides[1][0] < arc_sides[2][0] and arc_sides[2][1] < arc_sides[1][1]
    return arc_sides


def check_graph_separation(left, right):
    assert left | right == VERTICES
    a, b = left - right, right - left
    assert not any((x in a and y in b) or (y in a and x in b) for x, y in GRAPH_EDGES)
    return left & right


def adjacency_reachability(excluded):
    survivors = VERTICES - excluded
    start = min(survivors)
    seen = {start}
    queue = [start]
    while queue:
        v = queue.pop()
        for x, y in GRAPH_EDGES:
            if x == v or y == v:
                neighbour = y if x == v else x
                if neighbour in survivors and neighbour not in seen:
                    seen.add(neighbour)
                    queue.append(neighbour)
    assert seen == survivors
    return len(seen)


def proper(s, b):
    return s[b] - s[1 - b]


def pair_geometry(first, second):
    orientations = [(a, b) for a, b in itertools.product(range(2), repeat=2)
                    if first[a] <= second[b] and second[1 - b] <= first[1 - a]]
    corners = {}
    for a, b in itertools.product(range(2), repeat=2):
        left = first[a] & second[b]
        right = first[1 - a] | second[1 - b]
        z = check_graph_separation(left, right)
        exclusive = proper(first, a) & proper(second, b)
        assert exclusive == left - right
        corners[f"{a}{b}"] = {"proper": sorted(exclusive), "proper_size": len(exclusive),
                              "corner_separator": sorted(z), "corner_order": len(z)}
    return {"crossing": not orientations, "nested_orientations": orientations, "corners": corners}


def function_on_faces(diagram):
    fibre = {f: [] for f in FACES}
    for v in sorted(VERTICES):
        face = "".join("*" if v in zero & one else ("0" if v in zero else "1")
                       for zero, one in diagram)
        fibre[face].append(v)
    regions = {p: frozenset.intersection(*(diagram[i][int(b)] for i, b in enumerate(p)))
               for p in CUBE}
    for p, region in regions.items():
        labelled = {v for face, vs in fibre.items() if p in FACE_CORNERS[face] for v in vs}
        assert labelled == region
    return fibre, regions


def check_flower(fibre, k):
    # Test the frozen definition on every possible antipodal pole pair and ell.
    squares_zero = all(not fibre[f] for f in FACES if f.count("*") == 2)
    solutions = []
    for i in range(4):
        poles = {CUBE[i], CUBE[7 ^ i]}
        for ell in range(k // 2 + 1):
            if not squares_zero or len(fibre["***"]) != k - 2 * ell:
                continue
            if all(len(fibre[f]) == (0 if FACE_CORNERS[f] & poles else ell)
                   for f in FACES if f.count("*") == 1):
                solutions.append({"poles": sorted(poles), "ell": ell})
    return solutions


def confirm_lifts(fibre, regions, large):
    result = []
    for mask in range(256):
        side = {p for i, p in enumerate(CUBE) if mask & (1 << i)}
        other = set(CUBE) - side
        left = frozenset().union(*(regions[p] for p in side))
        right = frozenset().union(*(regions[p] for p in other))
        separator = check_graph_separation(left, right)
        crossing_edges = [(p, q) for p, q in CUBE_EDGES if (p in side) != (q in side)]
        weight = sum(len(fibre[face]) for face in FACES if any(
            p in FACE_CORNERS[face] and q in FACE_CORNERS[face] for p, q in crossing_edges))
        assert len(separator) == weight
        active = bool(large & side and large & other)
        assert not active or len(separator) >= 2
        result.append({"mask": mask, "order": len(separator), "large_regions_both_sides": active})
    return result


def audit_example(name, diagram):
    coordinates = {}
    for letter, (left, right) in zip(COORDINATES, diagram):
        s = check_graph_separation(left, right)
        assert len(s) == 2
        coordinates[letter] = {"side_0": sorted(left), "side_1": sorted(right), "separator": sorted(s)}
    pairs = {}
    for i, j in itertools.combinations(range(3), 2):
        record = pair_geometry(diagram[i], diagram[j])
        if record["crossing"]:
            assert all(c["proper_size"] > 2 and c["corner_order"] == 2
                       for c in record["corners"].values())
        pairs[COORDINATES[i] + COORDINATES[j]] = record
    links = {}
    uniform_partitions = {}
    for i, (a, b) in enumerate(diagram):
        z = a & b
        partitions = set()
        for j, (c, d) in enumerate(diagram):
            if i == j:
                continue
            centre = z & c & d
            z0, z1 = z & (c - d), z & (d - c)
            assert centre | z0 | z1 == z
            assert not ((centre & z0) | (centre & z1) | (z0 & z1))
            unordered = tuple(sorted([tuple(sorted(z0)), tuple(sorted(z1))]))
            letters = COORDINATES[i] + COORDINATES[j]
            cross = pairs["".join(sorted(letters))]["crossing"]
            links[letters] = {"target_separator": COORDINATES[i], "induced_by": COORDINATES[j],
                              "crossing": cross, "centre": sorted(centre),
                              "link_0": sorted(z0), "link_1": sorted(z1), "unordered_links": unordered}
            if cross:
                partitions.add((tuple(sorted(centre)), unordered))
        assert len(partitions) == 1
        centre, unordered = partitions.pop()
        uniform_partitions[COORDINATES[i]] = {"centre": centre, "unordered_links": unordered}
    fibre, regions = function_on_faces(diagram)
    large = {p for p in CUBE if len(regions[p]) >= 2}
    uncovered = [(p, q) for p, q in CUBE_EDGES if p not in large and q not in large]
    flower = check_flower(fibre, 2)
    if name == "all_crossing":
        assert all(v["crossing"] for v in pairs.values())
        assert all([c["proper_size"] for c in v["corners"].values()] == [3, 7, 7, 3]
                   for v in pairs.values())
        assert flower == [{"poles": ["000", "111"], "ell": 1}] and not uncovered
    else:
        assert [v["crossing"] for v in pairs.values()] == [True, True, False]
        assert flower == [] and uncovered == [("001", "101")]
    return {"coordinate_separations": coordinates, "pair_geometry": pairs, "ordered_inductions": links,
            "uniform_partitions": uniform_partitions, "uniformly_crossing": True,
            "face_fibres": fibre, "inclusive_regions": {p: sorted(r) for p, r in regions.items()},
            "large_labels_q0_k2": sorted(large), "cube_edges_missed_by_large_labels": uncovered,
            "all_flower_solutions_up_to_pole_order": flower,
            "cube_cut_checks": confirm_lifts(fibre, regions, large)}


def main(out):
    assert adjacency_reachability(set()) == 24
    deletions = [adjacency_reachability({i}) for i in range(24)]
    assert deletions == [23] * 24
    results = {"all_crossing": audit_example("all_crossing", coordinates_for_ring()),
               "nested_pair": audit_example("nested_pair", coordinates_for_nested())}
    data = {"utc": datetime.now(timezone.utc).isoformat(), "python": sys.version,
            "platform": platform.platform(), "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "replay": "python audit_cycles.py", "coordinate_order": list(COORDINATES),
            "corner_bit_order": ["00", "01", "10", "11"], "zero_side_selects": "first graph side",
            "vertices": sorted(VERTICES), "graph_edges": GRAPH_EDGES, "q": 0, "k": 2,
            "reachable_size_before_deletion": 24, "reachable_sizes_after_vertex_deletions_0_through_23": deletions,
            "diagrams": results}
    with (out / "cycles-data.json").open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, indent=2)
        stream.write("\n")
    for name, record in results.items():
        print(name)
        for p, r in record["pair_geometry"].items():
            print(f"  {p}: crossing={r['crossing']}; strict-corner sizes "
                  f"{[v['proper_size'] for v in r['corners'].values()]}; "
                  f"orders {[v['corner_order'] for v in r['corners'].values()]}")
        print("  uniform partitions:", record["uniform_partitions"])
        print("  admissible pole pairs and ell:", record["all_flower_solutions_up_to_pole_order"])
        print("  uncovered cube edges:", record["cube_edges_missed_by_large_labels"])
    print("Both named triples are equitable and (2q+k)-criss-compatible at q=0, k=2.")
    print("Checked 25 connected graphs (no deletion or one deletion) and all 2 x 256 oriented cube cuts.")


if __name__ == "__main__":
    main(Path(__file__).resolve().parent)
