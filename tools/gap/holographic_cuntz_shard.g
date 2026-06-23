# Exact-rational GAP audit for the finite holographic Cuntz shard.

Print("=== Holographic Cuntz shard GAP audit ===\n");

S := [[0, 1], [0, 0]];
T := [[0, 0], [1, 0]];
Psource := [[0, 0], [0, 1]];
Paperture := [[1, 0], [0, 0]];
I2 := IdentityMat(2);

if TransposedMat(S) * S <> Psource then
  Error("source projection failed");
fi;
if S * TransposedMat(S) <> Paperture then
  Error("aperture projection failed");
fi;
if TransposedMat(T) * T <> Paperture then
  Error("complement source projection failed");
fi;
if Psource * Psource <> Psource then
  Error("source idempotence failed");
fi;
if Paperture * Paperture <> Paperture then
  Error("aperture idempotence failed");
fi;
if Psource + Paperture <> I2 then
  Error("source partition failed");
fi;
if Paperture = I2 then
  Error("aperture must be proper");
fi;
if S * TransposedMat(S) * S <> S then
  Error("partial isometry failed");
fi;

Print("HOLOGRAPHIC_CUNTZ_SHARD_GAP_AUDIT_OK\n");
