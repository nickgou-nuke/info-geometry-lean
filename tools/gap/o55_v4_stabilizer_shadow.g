x := [0,0,3,4,0,0,0,2,1,4];;
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
InV4Orbit := function(a,b)
  return b = a or b = ReflPair0(a) or b = ReflPair1(a) or b = ReflPair01(a);
end;;
if not ReflPair0(x) = x then Error("pair0 stabilizer failed"); fi;
if not ReflPair1(x) = x then Error("pair1 stabilizer failed"); fi;
if not ReflPair01(x) = x then Error("pair01 stabilizer failed"); fi;
for y in [x, ReflPair0(x), ReflPair1(x), ReflPair01(x)] do
  if not InV4Orbit(x,y) then Error("orbit membership failed"); fi;
  if not y = x then Error("orbit singleton failed"); fi;
od;
Print("GAP_O55_STABILIZER_PAIR0_OK\n");
Print("GAP_O55_STABILIZER_PAIR1_OK\n");
Print("GAP_O55_STABILIZER_ORBIT_SINGLETON_OK\n");
QUIT;
