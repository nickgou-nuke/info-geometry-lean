# CAS-only concrete BN/Bruhat certificate for the carrier.
# GAP computes subgroup intersections and double cosets directly; no Lean
# theorem or imported order formula is used here.
Read("scripts/verify_carrier_u64_exact.g");

F := GF(2);
matrixFromColumns := function(codes)
  return List([1..8], function(i)
    return List([1..8], function(j)
      return ((Int(codes[j] / 2^(i-1)) mod 2) * One(F));
    end);
  end);
end;

weylGens := List([
  [1,2,8,4,16,64,32,128],
  [1,2,8,16,4,64,128,32],
  [2,1,32,64,128,4,8,16]
], matrixFromColumns);

B := SylowSubgroup(G, 2);
N := Group(weylGens);
H := Intersection(B, N);
Print("BN group sizes: G=", Size(G), " B=", Size(B), " N=", Size(N),
  " B_intersect_N=", Size(H), "\n");
if Size(G) <> 12096 or Size(B) <> 64 or Size(N) <> 12 or Size(H) <> 1 then
  Error("concrete BN size contract failed");
fi;
BNgenerated := Group(Concatenation(GeneratorsOfGroup(B), weylGens));
if Size(BNgenerated) <> Size(G) then
  Error("B and N do not generate the carrier");
fi;

cells := List(AsList(N), w -> DoubleCoset(B, w, B));
cellSizes := List(cells, Size);
unionSize := Size(Union(cells));
Print("Bruhat cell sizes: ", cellSizes, "\n");
Print("Bruhat union size: ", unionSize, "\n");
if Set(cellSizes) <> Set([64,128,256,512,1024,2048,4096]) then
  Error("unexpected Bruhat cell size spectrum");
fi;
if Length(Set(cellSizes)) = 0 then Error("empty cell list"); fi;

# GAP's double-coset representatives are disjoint by construction.  Verify
# the stronger concrete partition by comparing the sum of cell cardinalities
# with the carrier order and by checking every B-double-coset has a unique
# representative in the computed list.
if Sum(cellSizes) <> Size(G) then
  Error("Bruhat cell coverage failed");
fi;
if unionSize <> Size(G) then Error("Bruhat union is not the carrier"); fi;
if Sum(cellSizes) <> unionSize then Error("Bruhat cells overlap"); fi;
if Length(cells) <> 12 then Error("wrong number of Bruhat cells"); fi;
Print("Concrete BN/Bruhat certificate: PASS (12 double cosets, total 12096)\n");
QUIT;
