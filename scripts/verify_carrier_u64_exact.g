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
BitVector := function(n)
  local v, i;
  v := ZeroVector(F, 8);
  for i in [1..8] do
    v[i] := Int((n / 2^(i-1)) mod 2);
  od;
  return v;
end;
gens := List(codes, c -> Matrix(F, 8, 8,
  function(i,j) return BitVector(c[j])[i]; end));
for g in gens do
  if Order(g) <> 2 then Error("generator is not an involution"); fi;
od;
B := Group(gens);
Print("generator_orders=", List(gens, Order), "\n");
Print("generated_group_size=", Size(B), "\n");
words := [];
for e1 in [0,1] do for e2 in [0,1] do for e3 in [0,1] do
for e4 in [0,1] do for e5 in [0,1] do for e6 in [0,1] do
  Add(words, gens[1]^e1 * gens[2]^e2 * gens[3]^e3 *
    gens[4]^e4 * gens[5]^e5 * gens[6]^e6);
od; od; od; od; od; od;
Print("ordered_word_count=", Length(Set(words)), "\n");
if Length(Set(words)) <> 64 then Error("binary chart is not injective"); fi;
