F := GF(5);;
x := [ Z(5)^0, Z(5)^1, Z(5)^2, Z(5)^3, Z(5)^0+Z(5)^1,
       -Z(5)^0, -Z(5)^1, -Z(5)^2, -Z(5)^3, -(Z(5)^0+Z(5)^1) ];;
NegAll := v -> List(v, a -> -a);;
ReflPair0 := function(v)
  local out;
  out := ShallowCopy(v);
  out[1] := -out[1]; out[6] := -out[6];
  return out;
end;;
ReflPair1 := function(v)
  local out;
  out := ShallowCopy(v);
  out[2] := -out[2]; out[7] := -out[7];
  return out;
end;;
ReflPair01 := v -> ReflPair0(ReflPair1(v));;
ProjectiveSignEq := function(a,b)
  return b = a or b = NegAll(a);
end;;
InV4Orbit := function(a,b)
  return b = a or b = ReflPair0(a) or b = ReflPair1(a) or b = ReflPair01(a);
end;;
orbit := [x, ReflPair0(x), ReflPair1(x), ReflPair01(x)];;
for y in orbit do
  if not InV4Orbit(x,y) then Error("orbit membership failed"); fi;
  if not InV4Orbit(x, ReflPair0(y)) then Error("reflPair0 closure failed"); fi;
  if not InV4Orbit(x, ReflPair1(y)) then Error("reflPair1 closure failed"); fi;
  if not InV4Orbit(NegAll(x), NegAll(y)) then Error("negAll orbit closure failed"); fi;
od;
for y in orbit do
  for z in orbit do
    if ProjectiveSignEq(y,z) then
      if not ProjectiveSignEq(ReflPair0(y), ReflPair0(z)) then Error("reflPair0 proj failed"); fi;
      if not ProjectiveSignEq(ReflPair1(y), ReflPair1(z)) then Error("reflPair1 proj failed"); fi;
      if not ProjectiveSignEq(ReflPair01(y), ReflPair01(z)) then Error("reflPair01 proj failed"); fi;
      if not ProjectiveSignEq(NegAll(y), NegAll(z)) then Error("negAll proj failed"); fi;
    fi;
  od;
od;
Print("GAP_O55_PROJECTIVE_DESCENT_OK\n");
Print("GAP_O55_V4_ORBIT_CLOSED_OK\n");
Print("GAP_O55_NEGALL_ORBIT_CLOSED_OK\n");
QUIT;
