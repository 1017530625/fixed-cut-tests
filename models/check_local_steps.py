"""Independent finite checks for the three local arguments in Key Lemma 4.14."""
from collections import Counter
from hashlib import sha256
from itertools import permutations, product
from pathlib import Path
from time import perf_counter
import json
import platform

HERE = Path(__file__).resolve().parent
ZERO, ONE, FREE = 0, 1, 2


def side_masks(vertices, coord):
    return tuple(sum(1 << i for i, value in enumerate(vertices) if value[coord] in (b, FREE))
                 for b in (ZERO, ONE))


def pair_data(r, s):
    zr, zs = r[0] & r[1], s[0] & s[1]
    links = tuple(zr & s[b] & ~s[1-b] for b in (ZERO, ONE))
    corners, violations = [], []
    for a, b in product((ZERO, ONE), repeat=2):
        chosen = r[a] & s[b]
        corner = chosen & (r[1-a] | s[1-b])
        open_corner = (r[a] & ~r[1-a]) & (s[b] & ~s[1-b])
        common_term = zs & r[a]
        assert chosen == corner | open_corner and corner & open_corner == 0
        assert corner == (links[b] | common_term) and links[b] & common_term == 0
        corners.append(corner)
        # A chosen host gives the specified nesting orientation iff no listed vertex occurs.
        violations.append((r[a] & ~s[b]) | (s[1-b] & ~r[1-a]))
    return zr & zs, links, corners, violations


def test_atom_identities():
    atoms = list(product((ZERO, ONE, FREE), repeat=2))
    full = (1 << len(atoms)) - 1
    r, s = side_masks(atoms, 0), side_masks(atoms, 1)
    for x in range(len(atoms)):
        point = 1 << x
        pair_data(tuple(v & point for v in r), tuple(v & point for v in s))
    k_polynomial_tests = 0
    for mask in range(full+1):
        _, links, corners, _ = pair_data(tuple(v & mask for v in r), tuple(v & mask for v in s))
        if len({f.bit_count() for f in corners}) == 1:
            assert links[0].bit_count() == links[1].bit_count()
            k_polynomial_tests += 1
    return {"pointwise_with_bit_choices": len(atoms)*4,
            "full_pair_subsets": full+1, "equal_corner_order_pairs": k_polynomial_tests}


def test_adjacent_regions():
    # Inside one inclusive 2D corner, mark a vertex as proper or boundary.
    # Split each part by third-coordinate left-only/right-only/both membership.
    configurations = applicable = positive_overlap = 0
    for proper_l, proper_r, proper_both, boundary_l, boundary_r, boundary_both in product(range(4), repeat=6):
        proper = proper_l + proper_r + proper_both
        k = boundary_l + boundary_r + boundary_both
        first = proper_l + proper_both + boundary_l + boundary_both
        second = proper_r + proper_both + boundary_r + boundary_both
        overlap = proper_both + boundary_both
        assert first + second - overlap == proper + k
        configurations += 1
        for q in range(4):
            if proper > 2*q + k:
                assert first >= q+k or second >= q+k
                applicable += 1
                positive_overlap += overlap > 0
    return {"six_cell_vectors_0_through_3": configurations, "q_values_each": 4,
            "strict_threshold_applicable": applicable, "applicable_with_overlap": positive_overlap}


def test_flower():
    all_faces = list(product((ZERO, ONE, FREE), repeat=3))
    all_poles = list(product((ZERO, ONE), repeat=3))
    tested = accepted = edge_cases = all_free_cases = 0
    equality_poles = opposite_poles = 0
    for pole in all_poles:
        opposite = tuple(1-b for b in pole)
        for i, j, t in permutations(range(3)):
            labels_on_separator = []
            for f in all_faces:
                tested += 1
                if f[i] != FREE or f.count(FREE) == 2:
                    continue
                if f.count(FREE) == 1 and any(all(b==FREE or b == p[c] for c,b in enumerate(f)) for p in (pole,opposite)):
                    continue
                accepted += 1
                if f[j] == FREE:
                    assert f[t] == FREE
                    all_free_cases += 1
                else:
                    assert f[t] != FREE
                    assert int(f[j]==pole[j]) + int(f[t]==pole[t]) == 1
                    permutation = int(pole[j] == pole[t])
                    assert f[j] == f[t] ^ permutation
                    edge_cases += 1
                labels_on_separator.append(f)
            # Directly recover three actual preimages for all surviving types at once.
            for b in (ZERO, ONE, FREE):
                paired_bit = FREE if b == FREE else b ^ int(pole[j]==pole[t])
                ej = {f for f in labels_on_separator if f[j]==b}
                et = {f for f in labels_on_separator if f[t]==paired_bit}
                assert ej == et
            if pole[j] == pole[t]:
                equality_poles += 1
            else:
                opposite_poles += 1
    return {"all_poles_faces_ordered_indices":tested, "positive_support_candidates":accepted,
            "one_free_edge_cases":edge_cases, "full_cube_cases":all_free_cases,
            "whole_separator_permutations_flip":equality_poles, "whole_separator_permutations_identity":opposite_poles}


def test_balanced_nested_margins():
    # s <= t means left_s subset left_t and right_t subset right_s.
    # These six cells exhaust s,t label pairs for a vertex on the common separator.
    allowed = [(s,t) for s,t in product((ZERO, ONE, FREE), repeat=2)
               if (s not in (ZERO,FREE) or t in (ZERO,FREE))
               and (t not in (ONE,FREE) or s in (ONE,FREE))]
    configurations = balanced = with_nonempty_links = 0
    for multiplicities in product(range(6), repeat=len(allowed)):
        left_s = sum(n for (s,t),n in zip(allowed,multiplicities) if s==ZERO)
        right_s = sum(n for (s,t),n in zip(allowed,multiplicities) if s==ONE)
        left_t = sum(n for (s,t),n in zip(allowed,multiplicities) if t==ZERO)
        right_t = sum(n for (s,t),n in zip(allowed,multiplicities) if t==ONE)
        assert left_s <= left_t and right_t <= right_s
        configurations += 1
        if left_s != right_s or left_t != right_t:
            continue
        assert left_s == left_t
        assert all(s==t or n==0 for (s,t),n in zip(allowed,multiplicities))
        balanced += 1
        with_nonempty_links += left_s > 0
    return {"nested_vertex_cells":len(allowed), "multiplicities_0_through_5":configurations,
            "balanced":balanced,"balanced_with_nonempty_links":with_nonempty_links}


def test_genuine_nested_diagrams():
    # Every allowed role triple occurs either once or not at all on a labelled edgeless host.
    # This enforces the vertex-separation axioms and includes two distinct genuine crossing pairs.
    points = [(r,s,t) for r,s,t in product((ZERO, ONE, FREE), repeat=3)
              if (s not in (ZERO,FREE) or t in (ZERO,FREE))
              and (t not in (ONE,FREE) or s in (ONE,FREE))]
    r,s,t = (side_masks(points,i) for i in range(3))
    rs,rt = pair_data(r,s), pair_data(r,t)
    sep_r,sep_s,sep_t = (z[0]&z[1] for z in (r,s,t))
    same_st = (s[0]^t[0]) | (s[1]^t[1])
    swapped_st = (s[1]^t[0]) | (s[0]^t[1])
    cross_two = equitable = genuine = with_centre = positive = 0
    for mask in range(1 << len(points)):
        if any(not (mask & violation) for violation in rs[3]+rt[3]):
            continue
        cross_two += 1
        k = (mask&sep_r).bit_count()
        if (mask&sep_s).bit_count()!=k or (mask&sep_t).bit_count()!=k:
            continue
        if any((mask&corner).bit_count()!=k for corner in rs[2]+rt[2]):
            continue
        equitable += 1
        assert mask & rs[1][0] & ~rt[1][0] == 0 and mask & rt[1][1] & ~rs[1][1] == 0
        assert mask & rs[1][0] == mask & rt[1][0] and mask & rs[1][1] == mask & rt[1][1]
        assert mask & rs[0] == mask & rt[0]
        if mask & same_st and mask & swapped_st:
            genuine += 1
            with_centre += bool(mask & rs[0])
            positive += bool(mask & rs[1][0]) and bool(mask & rs[1][1])
    assert positive > 0
    return {"allowed_r_s_t_roles":len(points), "all_subsets_of_roles":1<<len(points),
            "r_crosses_both":cross_two, "same_input_orders_four_equal_pair_corner_orders":equitable,
            "among_equitable_distinct_unoriented_s_and_t":genuine, "genuine_with_centre":with_centre,
            "genuine_with_nonempty_links":positive}


def main():
    start = perf_counter()
    report = {"atom_identities":test_atom_identities(), "cover":test_adjacent_regions(),
              "pole_permutations":test_flower(),"nested_margins":test_balanced_nested_margins(),
              "nested_actual_separations":test_genuine_nested_diagrams()}
    report["scope"] = "Finite independent checks of local paper-proof steps; the full theorem uses the weighted 3D Corner Lemma and graph unbreakability. Nested test hosts are edgeless; the 4.18 intermediate only needs equitable nested data."
    report["python"] = platform.python_version()
    report["seconds"] = round(perf_counter()-start,3)
    report["program_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/"checks.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))

if __name__ == "__main__":
    main()

