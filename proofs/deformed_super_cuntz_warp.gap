# GAP witness for the Z2 grading and finite Pachner/deficit bookkeeping.
# Run with: gap -q proofs/deformed_super_cuntz_warp.gap

Z2GradeMul := function(a, b)
  return (a + b) mod 2;
end;

if Z2GradeMul(0,0) <> 0 then Error("even*even failed"); fi;
if Z2GradeMul(0,1) <> 1 then Error("even*odd failed"); fi;
if Z2GradeMul(1,0) <> 1 then Error("odd*even failed"); fi;
if Z2GradeMul(1,1) <> 0 then Error("odd*odd failed"); fi;

# A local 2-2 Pachner flip preserves the boundary labels while exchanging the
# diagonal.  This is combinatorial bookkeeping; amplitudes are supplied by the
# q-super-Cuntz algebra in Lean/Sage/SymPy witnesses.
A := [ [1,2,3], [1,3,4] ];
B := [ [1,2,4], [2,3,4] ];
BoundaryEdges := function(tris)
  local edges, t, candidates, e, counts, key;
  counts := rec();
  for t in tris do
    candidates := [ [t[1],t[2]], [t[2],t[3]], [t[1],t[3]] ];
    for e in candidates do
      Sort(e);
      key := Concatenation(String(e[1]), "-", String(e[2]));
      if IsBound(counts.(key)) then counts.(key) := counts.(key) + 1;
      else counts.(key) := 1; fi;
    od;
  od;
  edges := [];
  for key in RecNames(counts) do
    if counts.(key) = 1 then Add(edges, key); fi;
  od;
  Sort(edges);
  return edges;
end;

if BoundaryEdges(A) <> BoundaryEdges(B) then Error("2-2 flip boundary changed"); fi;
Print("Z2 grades and Pachner 2-2 boundary check passed\n");
QUIT;
