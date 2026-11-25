"""Reconstruct every corner cut from three vertex separations of a four-vertex star."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

HOST = frozenset("habc")
HOST_EDGES = (("h", "a"), ("h", "b"), ("h", "c"))
CUBE = frozenset(range(8))
CUBE_EDGES = tuple((u, v) for u, v in itertools.combinations(sorted(CUBE), 2)
                   if (u ^ v).bit_count() == 1)


def bits(vertex):
    return format(vertex, "03b")


def mask_side(mask):
    return frozenset(v for v in CUBE if mask & (1 << v))


def matchings():
    # Independently derive the two perfect matchings on each anti-diagonal ring.
    for u in range(4):
        ring = CUBE - {u, 7 ^ u}
        edges = [e for e in CUBE_EDGES if set(e) <= ring]
        pairs = [triple for triple in itertools.combinations(edges, 3)
                 if frozenset(v for e in triple for v in e) == ring]
        assert len(pairs) == 2
        for triple in pairs:
            yield ring, triple


def check_separation(left, right):
    """Check union and the actual three host adjacencies, then return the order."""
    assert left | right == HOST
    lproper, rproper = left - right, right - left
    assert all(not ((u in lproper and v in rproper) or
                    (v in lproper and u in rproper)) for u, v in HOST_EDGES)
    return len(left & right)


def coordinate_sides(matching):
    diagram = []
    for i in range(3):
        sides = []
        for side_bit in "01":
            leaves = {leaf for leaf, edge in zip("abc", matching)
                      if any(bits(v)[i] == side_bit for v in edge)}
            sides.append(frozenset({"h"} | leaves))
        assert check_separation(*sides) == 2
        diagram.append(tuple(sides))
    return diagram


def possible_reversals(separation):
    return (separation, separation[::-1])


def crossing(s, t):
    return not any(a <= c and d <= b
                   for a, b in possible_reversals(s)
                   for c, d in possible_reversals(t))


def sizes_for_pairs_and_links(diagram):
    pair_details = []
    for (i, s), (j, t) in itertools.combinations(enumerate(diagram), 2):
        assert crossing(s, t)
        corners = []
        for (i_bit, (a, b)), (j_bit, (c, d)) in itertools.product(
                enumerate(possible_reversals(s)), enumerate(possible_reversals(t))):
            strict = (a - b) & (c - d)
            left, right = a & c, b | d
            order = check_separation(left, right)
            corners.append({"bits": f"{i_bit}{j_bit}", "proper": sorted(strict),
                            "separation_order": order})
        assert sorted(len(record["proper"]) for record in corners) == [0, 0, 0, 1]
        assert sorted(record["separation_order"] for record in corners) == [1, 2, 2, 3]
        pair_details.append({"coordinates": [i + 1, j + 1], "crossing": True,
                             "corner_separations": corners})
    tripartitions = []
    for i, (a, b) in enumerate(diagram):
        separator = a & b
        records = []
        for j, (c, d) in enumerate(diagram):
            if i == j:
                continue
            centre = separator & c & d
            links = sorted([sorted(separator & (c - d)), sorted(separator & (d - c))])
            records.append({"crossing_coordinate": j + 1, "centre": sorted(centre), "links": links})
        assert records[0]["centre"] == records[1]["centre"] == ["h"]
        assert records[0]["links"] == records[1]["links"]
        assert records[0]["links"][0] == [] and len(records[0]["links"][1]) == 1
        tripartitions.append({"coordinate": i + 1, "records": records})
    return pair_details, tripartitions


def low_order_profile():
    low_order = []
    # Every vertex is on the left only, the right only, or both sides.
    for states in itertools.product("LBR", repeat=4):
        left = frozenset(v for v, s in zip("habc", states) if s != "R")
        right = frozenset(v for v, s in zip("habc", states) if s != "L")
        if len(left & right) >= 2:
            continue
        lproper, rproper = left - right, right - left
        if any((u in lproper and v in rproper) or (v in lproper and u in rproper)
               for u, v in HOST_EDGES):
            continue
        check_separation(left, right)
        low_order.append(min(len(lproper), len(rproper)))
    assert max(low_order) == 1
    return {"order_strictly_below": 2, "number_of_oriented_separations": len(low_order),
            "max_smaller_exclusive_side": max(low_order)}


def audit_diagram(j, ring, matching):
    diagram = coordinate_sides(matching)
    # Derive the eight regions FROM THE GRAPH SIDES (intersections), before
    # computing any cut order. The matched-edge count is checked afterwards.
    regions = {p: frozenset.intersection(*(diagram[i][int(b)] for i, b in enumerate(bits(p))))
               for p in CUBE}
    labels = {x: frozenset(p for p in CUBE if x in regions[p]) for x in HOST}
    assert labels["h"] == CUBE
    assert all(labels[x] == set(e) for x, e in zip("abc", matching))
    assert all(len(regions[p]) == (2 if p in ring else 1) for p in CUBE)
    assert not any(len(labels[x]) == 1 for x in HOST)
    assert all(u in ring or v in ring for u, v in CUBE_EDGES)
    pair_details, tripartitions = sizes_for_pairs_and_links(diagram)
    rows = []
    canonical_histogram = Counter()
    for mask in range(256):
        side = mask_side(mask)
        complement = CUBE - side
        left = frozenset().union(*(regions[p] for p in side))
        right = frozenset().union(*(regions[p] for p in complement))
        order = check_separation(left, right)
        separator = left & right
        split = sum((u in side) != (v in side) for u, v in matching)
        is_proper = bool(side and complement)
        active = bool(ring & side and ring & complement)
        detected = active and split == 0
        required_failure = active and order < 2
        assert required_failure == detected
        assert order == int(is_proper) + split
        if len(side) == 1:
            assert order == (2 if side <= ring else 1)
        canonical = is_proper and 0 not in side
        if canonical:
            canonical_histogram["order_" + str(order)] += 1
            canonical_histogram["inactive" if not active else
                                ("active_failed" if required_failure else "active_passed")] += 1
        rows.append({"j": j, "mask": mask, "A": [bits(p) for p in sorted(side)],
                     "canonical": canonical, "active": active, "graph_left": sorted(left),
                     "graph_right": sorted(right), "separator": sorted(separator), "order": order,
                     "split_matched_edges": split, "detected_by_definition": detected,
                     "fails_required_order": required_failure})
    for mask, row in enumerate(rows):
        reverse = rows[255 ^ mask]
        assert row["graph_left"] == reverse["graph_right"]
        assert row["graph_right"] == reverse["graph_left"]
        assert row["detected_by_definition"] == reverse["detected_by_definition"]
    assert canonical_histogram == Counter({"order_1": 15, "order_2": 48, "order_3": 48,
                                          "order_4": 16, "inactive": 3,
                                          "active_failed": 12, "active_passed": 112})
    whole_cube_weight = sum(labels[x] == CUBE for x in HOST)
    permitted = [2 - 2 * ell for ell in range(2)]
    assert whole_cube_weight == 1 and whole_cube_weight not in permitted
    details = {"witness_id": j, "omitted": [bits(v) for v in sorted(CUBE - ring)],
               "cover": [bits(v) for v in sorted(ring)],
               "matched_edges_by_leaf": {x: list(map(bits, e)) for x, e in zip("abc", matching)},
               "input_separations": [[sorted(s) for s in sep] for sep in diagram],
               "inclusive_regions": {bits(p): sorted(regions[p]) for p in sorted(CUBE)},
               "proper_triple_corners_empty": True, "pair_geometry": pair_details,
               "uniform_tripartitions": tripartitions, "whole_cube_weight": whole_cube_weight,
               "possible_whole_cube_weights_for_a_2_flower": permitted,
               "unordered_proper_cut_counts": dict(canonical_histogram)}
    return rows, details


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(out):
    out.mkdir(parents=True, exist_ok=True)
    details, all_rows = [], []
    for j, (ring, matching) in enumerate(matchings()):
        rows, witness = audit_diagram(j, ring, matching)
        details.append(witness)
        all_rows.extend(rows)
    proper = [r for r in all_rows if r["canonical"]]
    assert len(details) == 8 and len(all_rows) == 2048 and len(proper) == 1016
    detections = Counter(r["mask"] for r in proper if r["detected_by_definition"])
    by_number = Counter(detections.get(mask, 0) for mask in range(2, 255, 2))
    by_size = Counter(min(mask.bit_count(), 8 - mask.bit_count()) for mask in detections)
    assert by_number == Counter({0: 79, 2: 48}) and by_size == {2: 12, 3: 24, 4: 12}
    path = out / "star-cut-rows.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        for row in all_rows:
            print(json.dumps(row, separators=(",", ":")), file=stream)
    example_masks = [sum(1 << v for v in a) for a in [(4, 5), (0, 4), (0,), (), range(8)]]
    summary = {"utc": datetime.now(timezone.utc).isoformat(), "python": sys.version,
               "platform": platform.platform(), "program_sha256": sha(Path(__file__)),
               "entry_point": "python audit_star.py --out .", "row_file": path.name,
               "row_file_sha256": sha(path), "id_convention":
               "Omit (u,7 xor u) for u=0,1,2,3, lexicographically order the two edge matchings.",
               "mask_convention": "Bit p represents binary cube vertex p. The 127 canonical proper sides omit 000.",
               "host_vertices": sorted(HOST), "host_edges": HOST_EDGES,
               "low_order": low_order_profile(), "oriented_rows_including_boundaries": len(all_rows),
               "proper_unordered_cut_rows": len(proper), "oriented_boundary_rows": 16,
               "canonical_required_failures": sum(r["fails_required_order"] for r in proper),
               "canonical_inactive": sum(not r["active"] for r in proper),
               "canonical_active_passes": sum(r["active"] and r["order"] >= 2 for r in proper),
               "canonical_cut_count_by_number_of_detected_witnesses": dict(by_number),
               "detecting_cuts_by_smaller_side_size": dict(by_size),
               "examples_for_witness_zero": [all_rows[m] for m in example_masks],
               "witness_diagrams": details}
    (out / "star-audit.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Checked {len(all_rows)} oriented rows, including 16 empty/full rows, and {len(proper)} proper unordered rows.")
    print("Proper unordered cases: 96 active failures, 896 active passes, 24 inactive.")
    print(f"Row log SHA-256 {sha(path)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    audit(parser.parse_args().out)
