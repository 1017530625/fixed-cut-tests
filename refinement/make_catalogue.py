"""Generate packed cut-index tuples from the already certified incidence rows.

Usage: python make_catalogue.py path/to/ArbitraryCutTable.lean [--check]
The output is a certificate. Its validity, injectivity, coverage and size labels
are independently justified in Lean against actual canonical cuts.
"""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
import re


PROFILES = [(4,0,0), (3,1,0), (2,2,0), (1,3,0), (0,4,0),
            (2,0,2), (1,1,2), (0,2,2), (0,0,4)]


def catalogue(path):
    source = path.read_text(encoding='utf8')
    table = source.split('def signatureMask',1)[1].split(' : Array Nat)',1)[0]
    masks = [int(s,16) for s in re.findall(r'0x[0-9A-Fa-f]+',table)]
    if len(masks)!=127:
        raise ValueError('expected the certified table of 127 masks')
    active = [i for i,m in enumerate(masks) if m]
    sizes = [min(n,8-n) for i in range(127) for n in [(2*(i+1)).bit_count()]]
    selected = []
    hist = Counter()
    for four in combinations(active,4):
        u,v,w,r = four
        if masks[u] | masks[v] | masks[w] | masks[r] != 255:
            continue
        shape = tuple(sum(sizes[i]==d for i in four) for d in (2,3,4))
        tag = PROFILES.index(shape)
        word = sum(i*127**j for j,i in enumerate(four)) + tag*127**4
        sort_key = sum(2**i for i in four)
        selected.append((sort_key,word))
        hist[shape] += 1
    selected.sort()
    if len(selected)!=1116:
        raise ValueError('selected family count changed')
    words = [word for _,word in selected]
    group_size = 31
    groups = [words[i:i+group_size] for i in range(0,len(words),group_size)]
    block_names = [f"block{i}" for i in range(len(groups))]
    definitions = []
    for name,group in zip(block_names,groups):
        rows = [", ".join(str(n) for n in group[i:i+7]) for i in range(0,len(group),7)]
        definitions.append(f"private def {name} : Array Nat := #[\n  " + ",\n  ".join(rows) + "]")
    output = ("import Mathlib.Data.Fin.Basic\n\n"
              "/-! Generated candidate families. Small tables keep kernel reductions bounded. -/\n"
              "namespace CornerArbitraryCuts.SizeRefinement.Catalogue\n\n"
              + "\n\n".join(definitions)
              + "\n\n/-- Four base-127 digits give cut indices; the leading digit records the profile. -/\n"
              "def packed (n : Fin 1116) : ℕ :=\n"
              "  let blocks : Array (Array Nat) := #[" + ", ".join(block_names) + "]\n"
              "  (blocks[n.val / 31]!)[n.val % 31]!\n\n"
              "end CornerArbitraryCuts.SizeRefinement.Catalogue\n")
    return output, hist


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('table',type=Path)
    p.add_argument('--check',action='store_true')
    args=p.parse_args()
    contents,hist=catalogue(args.table)
    output=Path(__file__).with_name('SizeCatalogue.lean')
    if args.check:
        if output.read_bytes()!=contents.encode('utf8'):
            raise ValueError('committed certificate differs from regeneration')
    else:
        output.write_bytes(contents.encode('utf8'))
    print('ordered groups', [hist[s] for s in PROFILES], 'total', sum(hist.values()))


if __name__=='__main__':
    main()