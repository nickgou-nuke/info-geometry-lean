# GAP transport certificate: native flag stabilizer <-> six-bit PC words.
# This script is intentionally finite and explicit.  Its output is evidence
# for a later Lean certificate, not a Lean theorem.

F := GF(2);
entry := function(j,r) if j in r then return One(F); else return Zero(F); fi; end;
M := function(rows) return List(rows, r -> List([1..8], j -> entry(j,r))); end;
pcgens := [
 M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
 M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
 M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
 M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
 M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
 M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]]) ];
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
c := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
h := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
G := Group(Concatenation(pcgens,[s,c^2*s*h]));
U := Group(pcgens);
p := [Zero(F),Zero(F),Zero(F),Zero(F),One(F),Zero(F),Zero(F),Zero(F)];
y := [Zero(F),Zero(F),Zero(F),Zero(F),Zero(F),One(F),Zero(F),Zero(F)];
line := Set([p,y,p+y]);
OnLeft := function(v,g) return g^-1*v; end;
OnFlag := function(F,g) return [OnLeft(F[1],g),Set(List(AsSet(F[2]),v->OnLeft(v,g)))]; end;
S := Stabilizer(G,[p,line],OnFlag);

if Size(S) <> 64 then Error("TRANSPORT_STABILIZER_SIZE_FAILED"); fi;
if S <> U then Error("TRANSPORT_STABILIZER_NOT_EQUAL_PC_GROUP"); fi;
Print("TRANSPORT_STABILIZER_EQUALS_PC=PASS\n");
Print("TRANSPORT_STABILIZER_SIZE=",Size(S),"\n");

allBits := [];
for mask in [0..63] do Add(allBits,List([0..5],i->Int(mask/2^i) mod 2)); od;
pcWord := function(bits)
 local r,i; r:=One(U);
 for i in [6,5,4,3,2,1] do if bits[i]=1 then r:=pcgens[i]*r; fi; od;
 return r;
end;

seen := [];
bits := fail; hit := fail;
for g in Elements(S) do
  hit:=First(allBits,function(b) return pcWord(b)=g; end);
 if hit=fail then Error("TRANSPORT_WORD_WITNESS_FAILED"); fi;
 Add(seen,hit);
 Print("TRANSPORT_WITNESS ",hit,"\n");
od;
if Length(Set(seen)) <> 64 then Error("TRANSPORT_WITNESS_NOT_BIJECTIVE"); fi;
Print("TRANSPORT_ALL_64_WITNESSES=PASS\n");
QUIT;
