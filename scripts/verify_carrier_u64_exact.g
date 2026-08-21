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
words := [];
for e1 in [0,1] do for e2 in [0,1] do for e3 in [0,1] do
for e4 in [0,1] do for e5 in [0,1] do for e6 in [0,1] do
  Add(words, gens[1]^e1 * gens[2]^e2 * gens[3]^e3 *
    gens[4]^e4 * gens[5]^e5 * gens[6]^e6);
od; od; od; od; od; od;
Print("ordered_word_count=", Length(Set(words)), "\n");
Print("ordered words are a diagnostic only; they are not a B normal form.\n");

S := SylowSubgroup(G, 2);
Print("sylow_two_size=", Size(S), "\n");
psi := IsomorphismPcGroup(S);
P := Image(psi);
pcgs := Pcgs(P);
Print("sylow_pc_relative_orders=", RelativeOrders(pcgs), "\n");
Print("sylow_pc_coordinate_product=", Product(RelativeOrders(pcgs)), "\n");

pcgens := List(GeneratorsOfGroup(P), x -> PreImagesRepresentative(psi, x));
pcwords := [];
for e1 in [0,1] do for e2 in [0,1] do for e3 in [0,1] do
for e4 in [0,1] do for e5 in [0,1] do for e6 in [0,1] do
  Add(pcwords, pcgens[1]^e1 * pcgens[2]^e2 * pcgens[3]^e3 *
    pcgens[4]^e4 * pcgens[5]^e5 * pcgens[6]^e6);
od; od; od; od; od; od;
Print("sylow_pc_word_count=", Length(Set(pcwords)), "\n");
if Size(S) <> 64 or Length(Set(pcwords)) <> 64 then
  Error("PC Sylow normal form failed");
fi;
