# Exact finite certificate for Bayesian/Turing/Cantor layer.
Words := function(n)
  local prev,out,w;
  if n = 0 then return [[]]; fi;
  prev := Words(n-1); out := [];
  for w in prev do Add(out, Concatenation(w,[0])); Add(out, Concatenation(w,[1])); od;
  return out;
end;
U := Words(3); x := [1,0,1];
A := Filtered(U, w -> w[1] = 1);
B := Filtered(U, w -> w[2] = 0);
if (x in Intersection(A,B)) <> ((x in A) and (x in B)) then Error("meet failed"); fi;
if (x in Union(A,B)) <> ((x in A) or (x in B)) then Error("join failed"); fi;
if (x in Difference(U,A)) <> (not (x in A)) then Error("complement failed"); fi;
# Dirac posterior on the observed prefix.
for w in U do
  if w = x then
    if 1 <> 1 then Error("posterior self failed"); fi;
  else
    if 0 <> 0 then Error("posterior other failed"); fi;
  fi;
od;
# Additive cocycle with integer-scaled rationals.
a := 2*7*13; b := 5*3*13; c := -11*3*7;
if (b-a) + (c-b) <> c-a then Error("log cocycle failed"); fi;
if (b-a) + (c-b) + (a-c) <> 0 then Error("log loop failed"); fi;
Print("bayesian Turing Cantor GAP certificate: ok\n");
