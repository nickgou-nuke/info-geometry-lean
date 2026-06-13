#!/usr/bin/env python3
"""GAP incidence ledger for the fixed points of an outer C2 witness in G2(2).

This script reconstructs the degree-63 split Cayley hexagon point graph from the
Atlas permutation action of G2(2).  The point graph is the invariant orbital
graph of valency 6; its 63 triangles are the 63 lines of H(2).

For the selected outer C2 representative used in
`g2_2_automorphism_theorem.py`, the seven fixed points are
  [1, 19, 30, 32, 41, 42, 54].
They contain exactly three internal H(2) lines, not seven.  Thus this witness's
fixed set should not be promoted to a Fano-plane claim without additional data.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def verify_gap_fixed_point_incidence() -> dict[str, Any]:
    code = r'''
LoadPackage("atlasrep");;
G := AtlasGroup("G2(2)");;
D := DerivedSubgroup(G);;
h := First(RightTransversal(G,D), r -> not r in D);;
pts := [1..LargestMovedPoint(G)];;
fixed := Filtered(pts, i -> i = i^h);;
st := Stabilizer(G,1);;
subs := Orbits(st, pts, OnPoints);;
# The suborbit of length 6 yields the H(2) point graph: 63 points, 189 edges,
# valency 6.  In this Atlas action representative 19 lies in that suborbit.
pairOrbit := Orbit(G, Set([1,19]), OnSets);;
IsEdge := function(i,j)
  return Set([i,j]) in pairOrbit;
end;;
triangles := [];;
for i in pts do
  for j in [i+1..Length(pts)] do
    if IsEdge(i,j) then
      for k in [j+1..Length(pts)] do
        if IsEdge(i,k) and IsEdge(j,k) then
          Add(triangles, [i,j,k]);
        fi;
      od;
    fi;
  od;
od;
fixedEdges := [];;
for i in [1..Length(fixed)] do
  for j in [i+1..Length(fixed)] do
    if IsEdge(fixed[i], fixed[j]) then
      Add(fixedEdges, [fixed[i], fixed[j]]);
    fi;
  od;
od;
fixedTriangles := Filtered(triangles, t -> ForAll(t, x -> x in fixed));;
incidentFixedLines := Filtered(triangles, t -> ForAny(t, x -> x in fixed));;
perFixed := [];;
for p in fixed do
  Add(perFixed, [p, Length(Filtered(triangles, t -> p in t))]);
od;
Print("{\"degree\":", Length(pts),
  ",\"suborbit_lengths\":", List(subs, Length),
  ",\"edge_count\":", Length(pairOrbit),
  ",\"line_triangle_count\":", Length(triangles),
  ",\"fixed_points\":", fixed,
  ",\"fixed_edge_count\":", Length(fixedEdges),
  ",\"fixed_edges\":", fixedEdges,
  ",\"fixed_internal_line_count\":", Length(fixedTriangles),
  ",\"fixed_internal_lines\":", fixedTriangles,
  ",\"incident_fixed_line_count\":", Length(incidentFixedLines),
  ",\"incident_fixed_lines\":", incidentFixedLines,
  ",\"per_fixed_point_line_counts\":", perFixed,
  "}\n");
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], cwd=ROOT, input=code, text=True)
    start = out.index("{")
    end = out.rindex("}") + 1
    data = json.loads(out[start:end].replace("\n", ""))
    data["is_h2_fixed_point_incidence_ledger"] = (
        data["degree"] == 63
        and sorted(data["suborbit_lengths"]) == [1, 6, 24, 32]
        and data["edge_count"] == 189
        and data["line_triangle_count"] == 63
        and data["fixed_points"] == [1, 19, 30, 32, 41, 42, 54]
        and data["fixed_edge_count"] == 9
        and data["fixed_internal_line_count"] == 3
        and data["incident_fixed_line_count"] == 15
        and all(count == 3 for _, count in data["per_fixed_point_line_counts"])
    )
    data["fixed_set_is_fano_plane_under_this_incidence"] = data["fixed_internal_line_count"] == 7
    return data


def main() -> None:
    data = verify_gap_fixed_point_incidence()
    assert data["is_h2_fixed_point_incidence_ledger"]
    assert data["fixed_set_is_fano_plane_under_this_incidence"] is False
    print(json.dumps(data, sort_keys=True))
    print("G2_2_FIXED_POINT_INCIDENCE_LEDGER_OK")


if __name__ == "__main__":
    main()
