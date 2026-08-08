EMPiOrder := function(group_order, k, n)
  if k = n then
    return group_order;
  fi;
  return 1;
end;

if EMPiOrder(7, 3, 3) <> 7 then Error("diagonal pi"); fi;
if EMPiOrder(7, 2, 3) <> 1 then Error("lower off-diagonal pi"); fi;
if EMPiOrder(7, 4, 3) <> 1 then Error("upper off-diagonal pi"); fi;

ProductEMPiOrder := function(g_order, h_order, k)
  return EMPiOrder(g_order, k, 1) * EMPiOrder(h_order, k, 2);
end;

if ProductEMPiOrder(5, 11, 1) <> 5 then Error("product pi1"); fi;
if ProductEMPiOrder(5, 11, 2) <> 11 then Error("product pi2"); fi;
if ProductEMPiOrder(5, 11, 3) <> 1 then Error("product pi3"); fi;

ReducedSphereCohomologyRank := function(k, n)
  if k = n then
    return 1;
  fi;
  return 0;
end;

if ReducedSphereCohomologyRank(4, 4) <> 1 then Error("sphere diagonal"); fi;
if ReducedSphereCohomologyRank(3, 4) <> 0 then Error("sphere lower"); fi;
if ReducedSphereCohomologyRank(5, 4) <> 0 then Error("sphere upper"); fi;

SuspensionShiftIndex := function(k)
  return k + 1;
end;

if SuspensionShiftIndex(1) <> 2 then Error("shift 1"); fi;
if SuspensionShiftIndex(2) <> 3 then Error("shift 2"); fi;

FreudenthalStable := function(n, k)
  return k <= 2*n - 2;
end;

if not FreudenthalStable(2, 2) then Error("freudenthal 2 2"); fi;
if not FreudenthalStable(3, 4) then Error("freudenthal 3 4"); fi;
if FreudenthalStable(2, 3) then Error("freudenthal boundary"); fi;

G := CyclicGroup(IsPermGroup, 7);
H := AbelianGroup(IsPermGroup, [5, 5]);
if not IsAbelian(G) then Error("G abelian"); fi;
if not IsAbelian(H) then Error("H abelian"); fi;
if Size(G) <> 7 then Error("G size"); fi;
if Size(H) <> 25 then Error("H size"); fi;

Print(rec(
  pi_K_Z7_3_at_3 := EMPiOrder(Size(G), 3, 3),
  pi_K_Z7_3_at_2 := EMPiOrder(Size(G), 2, 3),
  product_pi1 := ProductEMPiOrder(5, 11, 1),
  product_pi2 := ProductEMPiOrder(5, 11, 2),
  Htilde_S4_degree4_rank := ReducedSphereCohomologyRank(4, 4)
), "\n");

QUIT;
