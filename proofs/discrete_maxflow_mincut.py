import itertools

"""Toy discrete max-flow / min-cut witness (3-node network).

Graph:
  0 -> 1 capacity 3
  1 -> 2 capacity 2
  0 -> 2 capacity 1
"""

caps = {(0, 1): 3, (1, 2): 2, (0, 2): 1}
nodes = [0, 1, 2]
source, sink = 0, 2

# enumerate all feasible integer flows under bounds and conservation at node 1
max_flow = 0
best = None
for f01, f12, f02 in itertools.product(
    range(caps[(0, 1)] + 1),
    range(caps[(1, 2)] + 1),
    range(caps[(0, 2)] + 1),
):
    if f01 == f12 and f01 <= caps[(0, 1)] and f12 <= caps[(1, 2)] and f02 <= caps[(0, 2)]:
        val = f12 + f02
        if val > max_flow:
            max_flow = val
            best = (f01, f12, f02)

print(f"max flow = {max_flow} (attained at {best})")


def cut_cost(S):
    c = 0
    if 0 in S and 1 not in S:
        c += caps[(0, 1)]
    if 1 in S and 2 not in S:
        c += caps[(1, 2)]
    if 0 in S and 2 not in S:
        c += caps[(0, 2)]
    return c

# source-sink cuts on 3 nodes only: {0} and {0,1}
cuts = [{0}, {0, 1}]
for S in cuts:
    print(f"cut {sorted(S)} cost = {cut_cost(S)}")

min_cut = min(cut_cost(S) for S in cuts)
print(f"min cut = {min_cut}")
print("max flow = min cut ?", max_flow == min_cut)
