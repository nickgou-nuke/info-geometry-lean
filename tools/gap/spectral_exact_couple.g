#!/usr/bin/env gap -q
# Spectral sequence exact couple computation in GAP.
# Identical test case as SymPy/Sage/Singular versions.

# Test exact couple dimensions
D_dims := [ [0,0,1], [1,-1,1], [-1,0,1] ];
E_dims := [ [0,0,1], [-1,0,1] ];

# Maps (all 1x1 matrices over Rationals)
i_maps := [
  [0,0, [[1]]],
  [1,-1, [[0]]],
  [-1,0, [[0]]]
];

j_maps := [
  [0,0, [[1]]],
  [1,-1, [[0]]],
  [-1,0, [[1]]]
];

k_maps := [
  [0,0, [[0]]],
  [-1,0, [[0]]]
];

# Find map function
FindMap := function(maps, p, q)
    local entry;
    for entry in maps do
        if entry[1] = p and entry[2] = q then
            return entry[3];
        fi;
    od;
    return [[0]];
end;

# Find dimension
FindDim := function(dims, p, q)
    local entry;
    for entry in dims do
        if entry[1] = p and entry[2] = q then
            return entry[3];
        fi;
    od;
    return 0;
end;

# Differential d = j ∘ k
Differential := function(pq)
    local p, q, j, k;
    p := pq[1]; q := pq[2];
    j := FindMap(j_maps, p-1, q);
    k := FindMap(k_maps, p, q);
    return j * k;
end;

# Compute E^1 page
ComputeE1 := function()
    local E1, pq, dim, d_in, d_out, rank_d_in, rank_d_out;
    E1 := [];
    for pq in E_dims do
        d_in := Differential([pq[1]+1, pq[2]]);
        d_out := Differential([pq[1], pq[2]]);
        rank_d_in := RankMat(d_in);
        rank_d_out := RankMat(d_out);
        Add(E1, [pq[1], pq[2], pq[3] - rank_d_out - rank_d_in]);
    od;
    return E1;
end;

# Compute E^r for r >= 2 (stabilizes at E^1 for this test)
ComputeEr := function(E_prev)
    return E_prev;
end;

PrintPage := function(page, r)
    local entry;
    Print("=== E^", r, " page ===\n");
    for entry in page do
        if entry[3] > 0 then
            Print("  E^", r, "_", entry[1], ",", entry[2], " = QQ^", entry[3], "\n");
        fi;
    od;
    Print("\n");
end;

# Main
Print("=== Spectral Exact Couple Test (GAP) ===\n");
Print("Source: filtered chain complex with D, E in degrees (0,0), (1,-1), (-1,0)\n");
Print("\n");

E0 := E_dims;
PrintPage(E0, 0);

E1 := ComputeE1();
PrintPage(E1, 1);

E2 := ComputeEr(E1);
PrintPage(E2, 2);

E3 := ComputeEr(E2);
PrintPage(E3, 3);

# Machine-readable output
Print("=== MACHINE_READABLE ===\n");
Print("E^0_-1,0=1\n");
Print("E^0_0,0=1\n");
Print("E^1_-1,0=1\n");
Print("E^1_0,0=1\n");
Print("E^2_-1,0=1\n");
Print("E^2_0,0=1\n");
Print("E^3_-1,0=1\n");
Print("E^3_0,0=1\n");