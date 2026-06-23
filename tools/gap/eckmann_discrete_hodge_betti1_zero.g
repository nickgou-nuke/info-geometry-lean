RequireTrue := function(label, cond)
  if not cond then
    Error(label);
  fi;
  Print(label, ": ok\n");
end;

RequireEnergyIdentity := function(label, d0, L1)
  RequireTrue(Concatenation(label, " energy identity"), L1 = d0 * TransposedMat(d0));
end;

path_d0 := [[-1, 1, 0], [0, -1, 1]];
path_rank_d0 := RankMat(path_d0);
path_b1 := 2 - path_rank_d0;
path_L1 := path_d0 * TransposedMat(path_d0);
path_harmonic_dim := 2 - RankMat(path_L1);
RequireTrue("path-tree b1=0", path_b1 = 0);
RequireTrue("path-tree harmonic=0", path_harmonic_dim = 0);
RequireEnergyIdentity("path-tree", path_d0, path_L1);

cycle_d0 := [[-1, 1, 0], [0, -1, 1], [1, 0, -1]];
cycle_rank_d0 := RankMat(cycle_d0);
cycle_b1 := 3 - cycle_rank_d0;
cycle_L1 := cycle_d0 * TransposedMat(cycle_d0);
cycle_harmonic_dim := 3 - RankMat(cycle_L1);
RequireTrue("triangle-cycle b1=1", cycle_b1 = 1);
RequireTrue("triangle-cycle harmonic=1", cycle_harmonic_dim = 1);
RequireEnergyIdentity("triangle-cycle", cycle_d0, cycle_L1);

QUIT;
