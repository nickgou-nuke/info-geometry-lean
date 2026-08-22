#!/usr/bin/env python3
"""Finite split Cayley hexagon incidence witness for the Atlas `U3(3).2`
action, the order-12096 realization isomorphic to `G2(2)`.

This script derives the unique `G2(2)`-invariant line orbit of size 63 in the
Atlas degree-63 permutation action, validates the generalized hexagon incidence
parameters, and records how the already-committed outer `C2` involution acts on
that line system.

Scope boundary:
  * This is a finite GAP/Atlas runtime certificate.
  * It records the split Cayley hexagon incidence data in the degree-63 action.
  * It does not claim a Fano-plane fixed subgeometry.  The certificate shows the
    fixed point set has only three all-fixed lines under this incidence system.
"""
from __future__ import annotations

import ast
import json
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def parse_gap_value(value: str) -> Any:
    value = value.strip()
    if value == "true":
        return True
    if value == "false":
        return False
    if value.startswith("["):
        return ast.literal_eval(value)
    return int(value)


def run_gap_hexagon_certificate() -> dict[str, Any]:
    code = r'''
LoadPackage("atlasrep");;
 G := AtlasGroup("U3(3).2");;
D := DerivedSubgroup(G);;
h := First(RightTransversal(G,D), r -> not r in D);;
pts := [1..LargestMovedPoint(G)];;
fixedPts := Filtered(pts, i -> i^h = i);;
triples := Combinations(pts, 3);;
seen := [];;
flatSeen := [];;
candidates := [];;
for t in triples do
  st := Set(t);
  if st in flatSeen then
    continue;
  fi;
  orb := Orbit(G, st, OnSets);;
  Add(seen, orb);
  Append(flatSeen, orb);
  if Length(orb) = 63 then
    counts := List(pts, p -> 0);;
    for b in orb do
      for p in b do
        counts[p] := counts[p] + 1;
      od;
    od;
    if Set(counts) = [3] then
      Add(candidates, orb);
    fi;
  fi;
od;
lines := candidates[1];;
pointDegrees := List(pts, p -> Length(Filtered(lines, b -> p in b)));;
pairDegrees := [];;
for pair in Combinations(pts,2) do
  Add(pairDegrees, Length(Filtered(lines, b -> ForAll(pair, p -> p in b))));
od;
fixedLinesAllPts := Filtered(lines, b -> ForAll(b, p -> p in fixedPts));;
fixedLinesSetwise := Filtered(lines, b -> Set(List(b, p -> p^h)) = b);;
fixedLineIntersections := List(fixedLinesSetwise, b -> Intersection(b, fixedPts));;
adj := List([1..126], i -> []);;
for li in [1..Length(lines)] do
  for p in lines[li] do
    Add(adj[p], 63 + li);
    Add(adj[63 + li], p);
  od;
od;
diam := 0;;
girth := 999;;
connected := true;;
for s in [1..126] do
  dist := List([1..126], i -> -1);;
  parent := List([1..126], i -> 0);;
  q := [s];;
  dist[s] := 0;;
  head := 1;;
  while head <= Length(q) do
    v := q[head];; head := head + 1;;
    for w in adj[v] do
      if dist[w] = -1 then
        dist[w] := dist[v] + 1;;
        parent[w] := v;;
        Add(q, w);
      elif parent[v] <> w and parent[w] <> v then
        cyc := dist[v] + dist[w] + 1;;
        if cyc < girth then girth := cyc; fi;
      fi;
    od;
  od;
  if ForAny(dist, d -> d = -1) then connected := false; fi;
  diam := Maximum(diam, Maximum(dist));;
od;
Print("POINT_COUNT=", Length(pts), "\n");
Print("LINE_COUNT=", Length(lines), "\n");
Print("LINE_SIZE_SET=", Set(List(lines, Length)), "\n");
Print("POINT_DEGREE_SET=", Set(pointDegrees), "\n");
Print("PAIR_LINE_COUNT_SET=", Set(pairDegrees), "\n");
Print("CONNECTED=", connected, "\n");
Print("INCIDENCE_GRAPH_DIAMETER=", diam, "\n");
Print("INCIDENCE_GRAPH_GIRTH=", girth, "\n");
Print("CANDIDATE_LINE_ORBIT_COUNT=", Length(candidates), "\n");
Print("REPRESENTATIVE_LINE=", lines[1], "\n");
Print("FIXED_POINTS=", fixedPts, "\n");
Print("ALL_FIXED_POINT_LINES_COUNT=", Length(fixedLinesAllPts), "\n");
for b in fixedLinesAllPts do
  Print("ALL_FIXED_POINT_LINE=", b, "\n");
od;
Print("SETWISE_FIXED_LINES_COUNT=", Length(fixedLinesSetwise), "\n");
for b in fixedLinesSetwise do
  Print("SETWISE_FIXED_LINE=", b, "\n");
od;
for b in fixedLineIntersections do
  Print("SETWISE_FIXED_LINE_INTERSECTION=", b, "\n");
od;
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], cwd=ROOT, input=code, text=True)
    data: dict[str, Any] = {
        "all_fixed_point_lines": [],
        "setwise_fixed_lines": [],
        "setwise_fixed_line_intersections": [],
    }
    repeated_keys = {
        "all_fixed_point_line": "all_fixed_point_lines",
        "setwise_fixed_line": "setwise_fixed_lines",
        "setwise_fixed_line_intersection": "setwise_fixed_line_intersections",
    }
    for line in out.splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        normalized_key = key.lower()
        parsed = parse_gap_value(value)
        if normalized_key in repeated_keys:
            data[repeated_keys[normalized_key]].append(parsed)
        else:
            data[normalized_key] = parsed
    return data


def main() -> None:
    data = run_gap_hexagon_certificate()
    expected = {
        "point_count": 63,
        "line_count": 63,
        "line_size_set": [3],
        "point_degree_set": [3],
        "pair_line_count_set": [0, 1],
        "connected": True,
        "incidence_graph_diameter": 6,
        "incidence_graph_girth": 12,
        "candidate_line_orbit_count": 1,
        "fixed_points": [1, 19, 30, 32, 41, 42, 54],
        "all_fixed_point_lines_count": 3,
        "setwise_fixed_lines_count": 9,
    }
    for key, value in expected.items():
        assert data[key] == value, (key, data[key], value)
    assert len(data["all_fixed_point_lines"]) == data["all_fixed_point_lines_count"]
    assert len(data["setwise_fixed_lines"]) == data["setwise_fixed_lines_count"]
    assert data["all_fixed_point_lines_count"] != 7
    data["is_split_cayley_hexagon_incidence_certificate"] = True
    data["fixed_points_form_fano_plane_under_this_line_system"] = False
    print(json.dumps(data, sort_keys=True))
    print("G2_2_HEXAGON_INCIDENCE_WITNESS_OK")


if __name__ == "__main__":
    main()
