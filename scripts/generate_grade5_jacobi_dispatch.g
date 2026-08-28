# Deterministic finite dispatch data for five graded Jacobi cases.
# GAP is used only to enumerate the finite symmetry quotient.

Print("GRADE5_JACOBI_DISPATCH\n");
grades := [-2,-1,0,1,2];;

neg := function(t) return [-t[1],-t[2],-t[3]]; end;;
rot := function(t,k)
  if k=0 then return t; fi;
  if k=1 then return [t[2],t[3],t[1]]; fi;
  return [t[3],t[1],t[2]];
end;;
key := function(t) return [t[1],t[2],t[3]]; end;;
canonical := function(t)
  local orbit;
  orbit := Concatenation(List([0..2],k -> [rot(t,k),neg(rot(t,k))]));
  Sort(orbit);
  return orbit[1];
end;;

representatives := [];;
routing := [];;
for a in grades do for b in grades do for c in grades do
  t := [a,b,c];;
  rep := canonical(t);;
  i := Position(representatives,rep);
  if i=fail then Add(representatives,rep); i:=Length(representatives); fi;
  Add(routing,[t,i]);
od; od; od;

Print("ordered_cases=",Length(routing),"\n");
Print("canonical_orbits=",Length(representatives),"\n");
Print("representatives=\n");
for i in [1..Length(representatives)] do
  Print(i,":",representatives[i],"\n");
od;
Print("routing=\n");
for row in routing do
  t:=row[1];; rep:=representatives[row[2]];;
  found:=false;;
  for k in [0..2] do
    if rot(t,k)=rep then Print(t," -> ",row[2]," cyclic=",k," sign=1\n"); found:=true; fi;
    if neg(rot(t,k))=rep then Print(t," -> ",row[2]," cyclic=",k," sign=-1\n"); found:=true; fi;
  od;
  if found=false then Error("routing failure"); fi;
od;
Print("grade5_dispatch=PASS\n");
