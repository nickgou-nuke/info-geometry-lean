#############################################################################
# Export the explicit 52 inner-derivation generators used by `f4Basis`.
# This is a GAP-readable mirror of the Lean source.  The authoritative
# generator order is checked by scripts/translate_f4_basis.py.
# Discovery-layer only; rank and independence remain Lean obligations.
#############################################################################

Print("# INFO_GEOMETRY_F4_BASIS_EXPORT v1\n");
Print("# carrier=H3Zorn R\n");
Print("# generator=h3ZornJordanInnerDerivation\n");
Print("# index_base=0\n");
Print("F4ROW index left right\n");

for i in [0..7] do
  Print("F4ROW ", i, " diag1 off12:", i, "\n");
od;
for i in [0..7] do
  Print("F4ROW ", 8 + i, " diag1 off31:", i, "\n");
od;
for i in [0..7] do
  Print("F4ROW ", 16 + i, " diag2 off23:", i, "\n");
od;

k := 24;
for i in [0..7] do
  for j in [i+1..7] do
    Print("F4ROW ", k, " off12:", i, " off12:", j, "\n");
    k := k + 1;
  od;
od;

if k <> 52 then
  Error("f4Basis exporter produced an unexpected number of rows: ", k);
fi;
