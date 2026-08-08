# GAP witness for the finite modular/Krein commuting square.
#
# This is the finite discrete shadow of the Lean tower theorem:
#   J^2 = 1,
#   I^2 = -1,
#   J I J = -I,
# and block-doubling preserves the same relations.

Print("Hestenes-Krein commuting-square witness\n");

I2 := IdentityMat(2, Rationals);
imat := [[0, -1], [1, 0]];
jmat := DiagonalMat([1, -1]);

if not jmat * jmat = I2 then
  Error("J^2 failed");
fi;

if not imat * imat = -I2 then
  Error("I^2 failed");
fi;

if not jmat * imat * jmat = -imat then
  Error("J I J = -I failed");
fi;

Embed := function(M)
  return DirectSumMat(M, M);
end;

ej := Embed(jmat);
ei := Embed(imat);
I4 := IdentityMat(4, Rationals);

if not ej * ej = I4 then
  Error("embedded J^2 failed");
fi;

if not ei * ei = -I4 then
  Error("embedded I^2 failed");
fi;

if not ej * ei * ej = -ei then
  Error("embedded J I J = -I failed");
fi;

Print("hestenes_krein_colimit.gap: J_compat and I_compat verified\n");
