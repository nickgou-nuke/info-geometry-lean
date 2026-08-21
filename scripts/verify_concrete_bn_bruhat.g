# Machine-verified GAP BN/Bruhat double coset decomposition for G2(2)
Read("scripts/verify_carrier_u64_exact.g");

# G is the 12,096-element matrix group over GF(2)
Print("Full group |G| = ", Size(G), "\n");

# Borel subgroup B (Sylow 2-subgroup of order 64):
B := SylowSubgroup(G, 2);
Print("Borel |B| = ", Size(B), "\n");

# The 12 Bruhat double cosets B \ G / B:
dc := DoubleCosets(G, B, B);
Print("Number of double cosets |B \\ G / B| = ", Length(dc), " (must be 12)\n");

dc_sizes := List(dc, Size);
Print("Double coset sizes: ", SortedList(dc_sizes), "\n");
Print("Sum of double coset sizes = ", Sum(dc_sizes), " (must be 12096)\n");

if Length(dc) <> 12 then Error("Bruhat cell count is not 12"); fi;
if Sum(dc_sizes) <> 12096 then Error("Bruhat union is not 12096"); fi;

Print("GAP BN/Bruhat decomposition: PASS ✅\n");
QUIT;
