# Carrier-level GAP check for the exact six-generator chart.
# CAS test artifact only; it is not a Lean proof of group order.
F := GF(2);
codes := [
  [2,1,128,64,32,16,8,4],
  [2,1,128,192,224,24,12,4],
  [134,133,128,68,175,211,136,4],
  [1,2,4,8,24,32,192,128],
  [129,130,4,8,147,40,68,128],
  [2,1,64,32,128,8,4,16]
];

gens := List(codes, c -> List([1..8], i -> List([1..8], j -> ((Int(c[j] / 2^(i-1)) mod 2) * One(F)))));

for g in gens do
  if Order(g) <> 2 then Error("generator is not an involution"); fi;
od;
G := Group(gens);
Print("generator_orders=", List(gens, Order), "\n");
Print("generated_group_size=", Size(G), "\n");
S := SylowSubgroup(G, 2);
Print("sylow_two_size=", Size(S), "\n");
psi := IsomorphismPcGroup(S);
P := Image(psi);
pcgs := Pcgs(P);
Print("sylow_pc_relative_orders=", RelativeOrders(pcgs), "\n");
Print("sylow_pc_coordinate_product=", Product(RelativeOrders(pcgs)), "\n");

Print("PC coordinate normal form is certified by the relative-order product,\n");
Print("not by enumerating words.\n");
if Size(S) <> 64 or Product(RelativeOrders(pcgs)) <> 64 then
  Error("PC Sylow coordinate cardinality failed");
fi;
