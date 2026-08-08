MatMul := function(A,B)
  return [[A[1][1]*B[1][1]+A[1][2]*B[2][1], A[1][1]*B[1][2]+A[1][2]*B[2][2]],
          [A[2][1]*B[1][1]+A[2][2]*B[2][1], A[2][1]*B[1][2]+A[2][2]*B[2][2]]];
end;
MatAdd := function(A,B) return [[A[1][1]+B[1][1],A[1][2]+B[1][2]],[A[2][1]+B[2][1],A[2][2]+B[2][2]]]; end;
MatNeg := A -> [[-A[1][1],-A[1][2]],[-A[2][1],-A[2][2]]];
MatSub := function(A,B) return MatAdd(A,MatNeg(B)); end;
SMul := function(k,A) return [[k*A[1][1],k*A[1][2]],[k*A[2][1],k*A[2][2]]]; end;
Bracket := function(A,B) return MatSub(MatMul(A,B),MatMul(B,A)); end;
Anti := function(A,B) return MatAdd(MatMul(A,B),MatMul(B,A)); end;
I2 := [[1,0],[0,1]]; Z2 := [[0,0],[0,0]];
e := [[1,0],[0,-1]]; ebar := [[0,1],[-1,0]];
S := MatMul(e,ebar); n := MatAdd(e,ebar); nbar := MatSub(e,ebar);
H := MatNeg(S); Egen := SMul(1/2,n); Fgen := SMul(1/2,nbar);
Casimir := MatAdd(MatMul(H,H), SMul(2, MatAdd(MatMul(Egen,Fgen), MatMul(Fgen,Egen))));
checks := [
  MatMul(e,e)=I2, MatMul(ebar,ebar)=MatNeg(I2), Anti(e,ebar)=Z2,
  MatMul(S,S)=I2, MatMul(S,n)=MatNeg(n), MatMul(n,S)=n,
  MatMul(S,nbar)=nbar, MatMul(nbar,S)=MatNeg(nbar),
  Anti(S,n)=Z2, Anti(S,nbar)=Z2, Anti(n,nbar)=SMul(4,I2),
  Bracket(S,n)=SMul(-2,n), Bracket(S,nbar)=SMul(2,nbar), Bracket(n,nbar)=SMul(-4,S),
  Bracket(H,Egen)=SMul(2,Egen), Bracket(H,Fgen)=SMul(-2,Fgen), Bracket(Egen,Fgen)=H,
  Casimir=SMul(3,I2), Bracket(Casimir,H)=Z2, Bracket(Casimir,Egen)=Z2, Bracket(Casimir,Fgen)=Z2
];
if false in checks then Error("Wareham dilator SL2 check"); fi;
edges := ["generated_by","anticommutes_with","closes_to","has_casimir","isomorphic_to"];
Print(rec(Ssquare:=1, anticommutator_n_nbar:=4, commutator_n_nbar:="-4S", sl2:=true, casimir:=3, casimirCentral:=true, edges:=Length(edges)),"\n");
QUIT;
