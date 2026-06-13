# GAP exact group backbone for the dual split-octonion / G2(2) lane.
#
# This script intentionally does not prove Aut(D O_s) = G2 ⋉ R^7.  It records
# finite group facts used as exact computational evidence: the Atlas degree-63
# action of G2(2), its derived subgroup index, and one outer-C2 representative
# with seven fixed points in that finite action.

LoadPackage("atlasrep");;
atlasData := AtlasGenerators("G2(2)", 1);;
if atlasData = fail then
  Error("AtlasGenerators(G2(2),1) unavailable");
fi;

G := Group(atlasData.generators);;
D := DerivedSubgroup(G);;
if Size(G) <> 12096 then Error("unexpected G2(2) order"); fi;
if Size(D) <> 6048 then Error("unexpected derived subgroup order"); fi;
if Index(G, D) <> 2 then Error("unexpected derived index"); fi;

h := fail;;
for g in Elements(G) do
  if Order(g) = 2 and not g in D then
    fixed := Filtered([1..63], i -> i^g = i);;
    if Length(fixed) = 7 then
      h := g;
      break;
    fi;
  fi;
od;
if h = fail then Error("no outer involution with seven fixed points found"); fi;

fixed := Filtered([1..63], i -> i^h = i);;
if Length(fixed) <> 7 then Error("fixed point count changed"); fi;

Print("DUAL_SPLIT_OCTONION_GAP_GROUP_BACKBONE_OK\n");
Print("G2_2_order=", Size(G), "\n");
Print("G2_2_derived_order=", Size(D), "\n");
Print("outer_involution_fixed_count=", Length(fixed), "\n");
Print("fixed_points=", fixed, "\n");
QUIT;
