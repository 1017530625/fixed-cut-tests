"""Directly count labelled unordered families by canonical cut masks; independent of Lean."""
from collections import Counter
from itertools import combinations, product
from math import comb
from pathlib import Path
import json
import time

face=[(1,2,3),(0,3,2),(0,1,3),(0,2,1)]
wedges={}
for i,front in enumerate(face):
    for sign,cycle in [("+",front),("-",front[::-1])]:
        wedges[f"{i}{sign}"]=tuple((a,4+b) for a,b in zip(cycle,cycle[1:]+cycle[:1]))
names=list(wedges)
def detected(mask):
    bit=lambda j:(mask>>j)&1
    return tuple(n for n,edges in wedges.items()
                 if all(bit(a)==bit(b) for a,b in edges) and len({bit(a) for a,b in edges})==2)
def cut_size(mask):return min(mask.bit_count(),8-mask.bit_count())
table=[]
for s,t in product(range(2),repeat=2):
    mask=(1<<1)|(1<<6)|s|(t<<4)
    other,=set(detected(mask))-{"0+"}
    table.append([s,t,other,cut_size(mask)])
assert table==[[0,0,"3-",2],[0,1,"2-",3],[1,0,"1-",3],[1,1,"3+",4]]
rows=[]; incidence=Counter()
for mask in range(2,256,2):
    hit=detected(mask)
    if hit:incidence[tuple(sorted(hit))+(cut_size(mask),)]+=1
    rows.append((sum(1<<names.index(n) for n in hit),cut_size(mask)))
hist=Counter(x.bit_count() for x,k in rows)
assert hist=={0:79,2:48}
for a,b in combinations(names,2):
    expected=(0,0,0) if a[0]==b[0] else (1,2,0) if a[1]!=b[1] else (0,0,1)
    assert tuple(incidence[tuple(sorted((a,b)))+(k,)] for k in [2,3,4])==expected
start=time.monotonic()
c=Counter()
for (x,i),(y,j),(z,k),(w,l) in combinations(rows,4):
    if x|y|z|w==255: c[tuple((i,j,k,l).count(t) for t in (2,3,4))]+=1
expected=Counter()
for u in range(5):expected[4-u,u,0]+=9*comb(4,u)*2**u
for u in range(3):expected[2-u,u,2]+=42*comb(2,u)*2**u
expected[0,0,4]+=9
assert c==expected and sum(c.values())==1116
result={"convention":"E_i=i; O_i=4+i. Canonical cuts omit vertex E_0; complementary sides identified.","representative_rows_s_t_second_minimum_size":table,"cut_mark_histogram":hist,"tested_four_cut_families":comb(127,4),"monomials":[{"size_2":k[0],"size_3":k[1],"size_4":k[2],"coefficient":n} for k,n in sorted(c.items())],"total":sum(c.values()),"balanced":c[0,0,4],"only_size_3":c[0,4,0],"at_most_size_3":sum(n for k,n in c.items() if k[2]==0),"no_size_2":sum(n for k,n in c.items() if k[0]==0),"runtime_seconds":round(time.monotonic()-start,3)}
assert [result[k] for k in ("balanced","only_size_3","at_most_size_3","no_size_2")]==[9,144,729,321]
Path(__file__).with_name("direct-enumeration.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
print("checked",result["tested_four_cut_families"],"families;",dict(c),"total",result["total"],"seconds",result["runtime_seconds"])
