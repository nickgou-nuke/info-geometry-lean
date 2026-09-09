# Deterministic routing artifact for the native six-lane Lean carrier.
# This file exports only finite cyclic dispatch data.  It does not assert
# bracket coefficients or Jacobi identities; those remain Lean-owner facts.

Print("FREUDENTHAL_JACOBI_LANE_DISPATCH\n");

lanes := ["minus2","minus1","zeroSymp","zeroScale","plus1","plus2"];;

rotate := function(t,k)
  if k=0 then return t; fi;
  if k=1 then return [t[2],t[3],t[1]]; fi;
  return [t[3],t[1],t[2]];
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

cyclicShift := function(t,rep)
  local k;
  for k in [0..2] do
    if rotate(t,k)=rep then return k; fi;
  od;
  return fail;
end;;

representatives := [];;
routing := [];;
for a in lanes do for b in lanes do for c in lanes do
  t := [a,b,c];;
  rep := canonical(t);;
  i := Position(representatives,rep);
  if i=fail then
    Add(representatives,rep);
    i := Length(representatives);
  fi;
  shift := cyclicShift(t,rep);;
  Add(routing,[t,i,shift]);
od; od; od;

Print("lane_count=",Length(lanes),"\n");
Print("ordered_triple_count=",Length(routing),"\n");
Print("cyclic_orbit_count=",Length(representatives),"\n");
Print("representatives=\n");
for i in [1..Length(representatives)] do
  Print(i,":",JoinStringsWithSeparator(representatives[i],","),"\n");
od;
Print("routing=\n");
for row in routing do
  Print(JoinStringsWithSeparator(row[1],",")," -> ",row[2],
    " cyclic_shift=",row[3],"\n");
od;
Print("routing_only=PASS\n");
QUIT;
