# GAP polynomial-shadow witnesses for the concrete J₂(O_s) scaling packet.

NegZ := z -> List(z, c -> -c);;
DetZ := function(z)
  return z[1]*z[2] - (z[3]*z[6] + z[4]*z[7] + z[5]*z[8]);
end;;
ScaleZ := function(r, z)
  return List(z, c -> r*c);
end;;
TraceReversal := function(H)
  return [ H[2], H[1], NegZ(H[3]) ];
end;;
ScaleHerm := function(r, H)
  return [ r*H[1], r*H[2], ScaleZ(r, H[3]) ];
end;;
DetHerm := function(H)
  return H[1]*H[2] - DetZ(H[3]);
end;;

F := GF(5);;
z0 := Zero(F);;
z1 := One(F);;
z2 := z1 + z1;;
z3 := z2 + z1;;
z4 := z3 + z1;;
samples := [
  [ z0, z0, [ z1, z0, z0, z0, z0, z0, z0, z0 ] ],
  [ z1, z2, [ z3, z4, z1, z2, z3, z4, z1, z2 ] ],
  [ z2, z3, [ z4, z1, z2, z3, z4, z1, z2, z3 ] ]
];;
for H in samples do
  for r in F do
    if TraceReversal(TraceReversal(H)) <> H then Error("trace reversal involution failed"); fi;
    if DetHerm(TraceReversal(H)) <> DetHerm(H) then Error("det trace reversal failed"); fi;
    if TraceReversal(ScaleHerm(r, H)) <> ScaleHerm(r, TraceReversal(H)) then Error("trace reversal scale failed"); fi;
    if DetHerm(ScaleHerm(r, H)) <> r^2 * DetHerm(H) then Error("det scale failed"); fi;
  od;
od;

Print("GAP_JORDAN_CAYLEY_OS_TRACE_REVERSAL_INVOLUTIVE_OK\n");
Print("GAP_JORDAN_CAYLEY_OS_DET_TRACE_REVERSAL_OK\n");
Print("GAP_JORDAN_CAYLEY_OS_TRACE_REVERSAL_SCALE_OK\n");
Print("GAP_JORDAN_CAYLEY_OS_DET_SCALE_OK\n");
QUIT;
