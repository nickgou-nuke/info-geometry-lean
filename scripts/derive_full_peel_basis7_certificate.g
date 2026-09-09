# CAS exporter for the final basis-7 residual formula.
# Convention: matrices act on column vectors; words are p0*p1*...*p5.
# This file emits ANF data only after checking the convention and residual.

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
inv := [pcgens[1],pcgens[6]*pcgens[2],pcgens[6]*pcgens[3],pcgens[4],pcgens[5],pcgens[6]];

vec := function(i) local v; v:=List([1..8],j->Zero(F)); v[i]:=One(F); return v; end;
mulVec := function(m,v) return List([1..8],i -> Sum([1..8],j -> v[j]*m[j][i])); end;
word := function(bits) local r,i; r:=IdentityMat(8,F); for i in [1..6] do if bits[i]=1 then r:=r*pcgens[i]; fi; od; return r; end;
bitsOf := function(mask) return List([0..5],i->Int(mask/2^i) mod 2); end;

peel := function(bits)
 local m,states,recovered,i,b;
 m:=word(bits); states:=[]; recovered:=[];
 for i in [1..6] do
  if i=1 then b:=m[3][8]; elif i=2 then b:=m[4][3];
  elif i=3 then b:=m[4][8]; elif i=4 then b:=m[7][3];
  elif i=5 then b:=m[5][4]+m[7][3]; else b:=m[5][3]; fi;
  b:=Int(b); Add(recovered,b); Add(states,m);
  if b=1 then m:=inv[i]*m; fi;
 od;
 Add(states,m); return rec(bits:=bits,recovered:=recovered,states:=states); end;

anf := function(values)
 local a,bit,mask; a:=ShallowCopy(values);
 for bit in [0..5] do for mask in [0..63] do
  if QuoInt(mask,2^bit) mod 2=1 then
   a[mask+1]:=Int(a[mask+1]+a[mask-2^bit+1]) mod 2;
  fi; od; od; return a; end;
monomial := function(mask)
 local n,out,i; n:=["e0","e1","e2","e3","e4","e5"]; out:=[];
 for i in [0..5] do if QuoInt(mask,2^i) mod 2=1 then Add(out,n[i+1]); fi; od;
 if Length(out)=0 then return "1"; fi; return JoinStringsWithSeparator(out,"*"); end;
printANF := function(label,values)
 local a,terms,mask; a:=anf(values); terms:=[];
 for mask in [0..63] do if a[mask+1]=1 then Add(terms,monomial(mask)); fi; od;
 if Length(terms)=0 then Add(terms,"0"); fi;
 Print("ANF ",label," = ",JoinStringsWithSeparator(terms," + "),"\n"); end;

b7:=vec(8); active:=vec(6)+vec(8); labels:=["a","b","x0","x1","x2","y0","y1","y2"];
Print("FULL_PEEL_BASIS7_CAS_CERTIFICATE v2\n");
Print("CONVENTION=column,m*v; WORD=p0*p1*p2*p3*p4*p5\n");

vals:=[]; for c in [1..8] do vals[c]:=[]; od;
activeVals:=[]; for c in [1..8] do activeVals[c]:=[]; od;
ok:=true;
for mask in [0..63] do
 bits:=bitsOf(mask); pd:=peel(bits); residual:=pd.states[7]; image:=mulVec(residual,b7);
 for c in [1..8] do Add(vals[c],Int(image[c])); od;
 if bits[6]=1 then
  pre:=mulVec(pd.states[6],active);
  for c in [1..8] do Add(activeVals[c],Int(pre[c])); od;
 else
  for c in [1..8] do Add(activeVals[c],0); od;
 fi;
 if image<>b7 then ok:=false; fi;
od;
for c in [1..8] do printANF(Concatenation("fullPeel_basis7.",labels[c]),vals[c]); od;
Print("ACTIVE_BRANCH e5=1\n");
for c in [1..8] do printANF(Concatenation("active_pre_peel5.",labels[c]),activeVals[c]); od;
Print("CERTIFICATE_CHECK residual_basis7_is_basis7=",ok,"\n");
if not ok then Error("residual certificate failed"); fi;
QUIT;
