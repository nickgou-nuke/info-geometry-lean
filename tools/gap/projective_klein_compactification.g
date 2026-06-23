# Exact-rational GAP audit for the projective Klein formula packet.

A := [[1, 0], [0, -1]];
B := [[1, 1], [0, 1]];
Ainv := A;
Binv := [[1, -1], [0, 1]];
I2 := IdentityMat(2);
MinusI2 := -I2;
S := [[0, -1], [1, 0]];

ProjectivelyEqual := function(X, Y)
  return X = Y or X = -Y;
end;

if not ProjectivelyEqual(I2, MinusI2) then
  Error("projective central sign relation failed");
fi;
if MinusI2 * MinusI2 <> I2 then
  Error("central sign square failed");
fi;
if A * Ainv <> I2 then
  Error("twist inverse failed");
fi;
if B * Binv <> I2 then
  Error("parabolic right inverse failed");
fi;
if Binv * B <> I2 then
  Error("parabolic left inverse failed");
fi;
if A * B * Ainv <> Binv then
  Error("Klein conjugacy failed");
fi;
if A * B * Ainv * B <> I2 then
  Error("Klein word failed");
fi;
if not ProjectivelyEqual(S * S, I2) then
  Error("Mobius square projective identity failed");
fi;

Print("projective Klein compactification GAP audit: ok\n");
