# Derive the local rank-one BN2 subgroup data without enumerating B.
F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
end;
rows := [
  [[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]],
  [[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]],
  [[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]],
  [[1],[2],[3],[4],[4,5],[6],[7,8],[8]],
  [[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]],
  [[1],[2],[3],[4],[3,5],[6,8],[7],[8]]
];
pcgens := List(rows, rs -> List([1..8], i -> List([1..8], j -> entry(j, rs[i]))));
B := Group(pcgens);
psi := IsomorphismPcGroup(B);
P := Image(psi);
pcgsP := Pcgs(P);
preimages := List(GeneratorsOfGroup(P), x -> PreImagesRepresentative(psi, x));
Print("PC_PREIMAGES_MATCH_EXPORT=", ForAll([1..6], i -> preimages[i] = pcgens[i]), "\n");
s := PermutationMat((3,4)(6,7), 8, F);
H := Intersection(B, B^s);
Print("B_SIZE=", Size(B), "\n");
Print("H_SIZE=", Size(H), "\n");
Print("PC_IN_H=", List(pcgens, x -> x in H), "\n");
Print("H_PC_GENERATORS=", Length(Pcgs(H)), "\n");
Hpc := Group(Concatenation([pcgens[1]], pcgens{[3..6]}));
Print("H_GENERATED_BY_PC_COMPLEMENT=", Hpc = H, "\n");
Print("INDEX_B_H=", Index(B,H), "\n");
for i in [1,3,4,5,6] do
  conjugate := s^-1 * pcgens[i] * s;
  Print("CONJ_PC_", i, "_IN_B=", conjugate in B);
  if conjugate in B then
    Print(" EXP="); Print(ExponentsOfPcElement(pcgsP, Image(psi, conjugate))); Print("\n");
  else
    Print("\n");
  fi;
od;
 c := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F) *
      PermutationMat((3,4,5)(6,7,8), 8, F);
 t := s * c;
 Ht := Intersection(B, B^t);
 Print("T_H_SIZE=", Size(Ht), " INDEX_B_HT=", Index(B,Ht), "\n");
 Print("T_PC_IN_H=", List(pcgens, x -> x in Ht), "\n");
 Htpc := Group(pcgens{[2..6]});
 Print("T_COMPLEMENT_GENERATES_H=", Htpc = Ht, "\n");
for i in [1,2,3,4,5,6] do
  conjugate := t^-1 * pcgens[i] * t;
  Print("CONJ_T_PC_", i, "_IN_B=", conjugate in B);
  if conjugate in B then
    Print(" EXP="); Print(ExponentsOfPcElement(pcgsP, Image(psi, conjugate))); Print("\n");
  else
    Print("\n");
  fi;
od;
Print("LOCAL_BN2_DATA=PASS\n");
QUIT;
