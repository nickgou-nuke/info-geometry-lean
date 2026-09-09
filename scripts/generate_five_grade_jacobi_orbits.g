# Finite orbit-routing artifact for a six-lane five-graded carrier.
# The output is discovery data only: Lean must replay every certificate.

Print("FIVE_GRADE_JACOBI_ORBITS\n");

grades := [-2,-1,0,1,2];;
lanes := ["m2","m1","zS","zH","p1","p2"];;

rank := function(a)
  return Position(lanes,a);
end;;

rotate := function(t,k)
  local r;
  r := ShallowCopy(t);
  if k=1 then
    return [t[2],t[3],t[1]];
  fi;
  if k=2 then
    return [t[3],t[1],t[2]];
  fi;
  return r;
end;;

key := function(t)
  return Concatenation(t[1],"/",t[2],"/",t[3]);
end;;

canonical := function(t)
  local orbit;
  orbit := List([0..2], k -> rotate(t,k));
  SortBy(orbit,key);
  return orbit[1];
end;;

orbitIndex := [];;
representatives := [];;
for a in lanes do for b in lanes do for c in lanes do
  t := [a,b,c];;
  rep := canonical(t);;
  k := Position(representatives,rep);
  if k=fail then
    Add(representatives,rep);
    k := Length(representatives);
  fi;
  Add(orbitIndex,[t,k]);
od; od; od;

Print("lane_count=6\n");
Print("triple_count=",Length(orbitIndex),"\n");
Print("orbit_count=",Length(representatives),"\n");
Print("representatives=\n");
for i in [1..Length(representatives)] do
  Print(i,":",JoinStringsWithSeparator(representatives[i],","),"\n");
od;

Print("routing=\n");
for row in orbitIndex do
  t := row[1];;
  rep := representatives[row[2]];;
  p := First([0..2],k -> rotate(t,k)=rep);;
  Print(JoinStringsWithSeparator(t,",")," -> ",row[2],
    " cyclic_shift=",p,"\n");
od;

Print("finite_routing_artifact=PASS\n");
