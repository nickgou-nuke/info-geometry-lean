"""CAS diagnosis of the exact Lean matrix carrier and the second reflection."""
import itertools
import sympy as sp

def M(rows):
    return sp.Matrix([[int(j in row) for j in range(8)] for row in rows])

gens = [
 M([[0,3],[1,3],[2,7],[3],[3,4,5],[5],[0,1,3,6,7],[7]]),
 M([[0,7],[1,7],[2],[2,3],[0,1,3,4,7],[2,3,5,6,7],[2,6,7],[7]]),
 M([[0,2,7],[1,2,7],[2],[3,7],[0,1,3,4,6],[0,1,2,3,5,7],[2,6,7],[7]]),
 M([[0],[1],[2],[3],[3,4],[5],[6,7],[7]]),
 M([[0,7],[1,7],[2],[3],[0,1,3,4,7],[3,5],[2,6,7],[7]]),
 M([[0],[1],[2],[3],[2,4],[5,7],[6],[7]]),
]
s = M([[0],[1],[3],[2],[4],[6],[5],[7]])
cycle = M([[0],[1],[3],[4],[2],[6],[7],[5]])
cartan = M([[1],[0],[5],[6],[7],[2],[3],[4]])
c = cycle * cartan
for name, t in (("c*s", c*s), ("s*c", s*c)):
    print(name)
    for i in range(1, 6):
        target = t * gens[i] * t
        hits = []
        for bits in itertools.product((0,1), repeat=6):
            w = sp.eye(8)
            for k, bit in enumerate(bits):
                if bit:
                    w = gens[k] * w
            if w == target:
                hits.append(bits)
        print(i, hits)
