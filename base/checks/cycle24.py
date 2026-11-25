"""Independent finite-set audit of the twenty-four-cycle and its three separations."""
from collections import Counter
import json


def main():
    # At vertex 4r the neighbouring corner labels are both present. The
    # next three vertices all carry the common endpoint of the next edge.
    ring = ("001", "011", "010", "110", "100", "101")
    vertices = set(range(24))
    labels = []
    for v in range(24):
        edge, step = divmod(v, 4)
        end = ring[(edge + 1) % len(ring)]
        labels.append({ring[edge], end} if step == 0 else {end})
    edges = [(v, (v + 1) % 24) for v in range(24)]
    sides = [
        [{v for v in vertices if any(p[i] == bit for p in labels[v])} for bit in "01"]
        for i in range(3)
    ]
    proper = [[a - b, b - a] for a, b in sides]
    separators = [a & b for a, b in sides]
    for i, (a, b) in enumerate(sides):
        assert a | b == vertices
        for v, w in edges:
            assert not (v in proper[i][0] and w in proper[i][1])
            assert not (w in proper[i][0] and v in proper[i][1])

    # Connectivity is tested without using the ring labels.
    reached = {}
    for removed in [None, *range(24)]:
        live = vertices - {removed}
        seen = {min(live)}
        agenda = list(seen)
        while agenda:
            v = agenda.pop()
            for w in ((v - 1) % 24, (v + 1) % 24):
                if w in live and w not in seen:
                    seen.add(w)
                    agenda.append(w)
        assert seen == live
        reached["none" if removed is None else str(removed)] = len(seen)

    metrics = {}
    for i in range(3):
        for j in range(i + 1, 3):
            pair = f"{i},{j}"
            data = {}
            for a in range(2):
                for b in range(2):
                    assert not (sides[i][a] <= sides[j][b]
                                and sides[j][1 - b] <= sides[i][1 - a])
                    strict = proper[i][a] & proper[j][b]
                    corner_separator = sides[i][a] & sides[j][b] & (
                        sides[i][1 - a] | sides[j][1 - b])
                    assert len(strict) == (3 if a == b else 7)
                    assert len(corner_separator) == 2
                    data[f"{a}{b}"] = {
                        "proper_card": len(strict),
                        "corner_separator": sorted(corner_separator),
                    }
            data["centre"] = sorted(separators[i] & separators[j])
            data["links_on_first"] = [sorted(separators[i] & p) for p in proper[j]]
            metrics[pair] = data

    partitions = []
    for i in range(3):
        incoming = [
            (frozenset(separators[i] & separators[j]),
             frozenset(frozenset(separators[i] & side) for side in proper[j]))
            for j in range(3) if j != i
        ]
        assert incoming[0] == incoming[1]
        centre, links = incoming[0]
        assert not centre and sorted(map(len, links)) == [1, 1]
        partitions.append([sorted(centre), sorted(map(sorted, links))])

    faces = Counter()
    for corners in labels:
        agreed = [set(column) for column in zip(*corners)]
        face = ''.join(next(iter(bits)) if len(bits) == 1 else '*' for bits in agreed)
        faces[face] += 1
    assert sum(faces.values()) == 24
    assert sorted(v for f, v in faces.items() if '*' in f) == [1] * 6
    print(json.dumps({"order": list(map(len, separators)), "pairs": metrics,
                      "partitions": partitions, "single_vertex_deletions": reached,
                      "face_weights_nonzero": dict(sorted(faces.items()))},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
