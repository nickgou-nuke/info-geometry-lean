# Exact-rational GAP certificate for finite holographic Cuntz shard algebra.

S := [[0,1],[0,0]];;
Psource := [[0,0],[0,1]];;
Paperture := [[1,0],[0,0]];;
if TransposedMat(S) * S <> Psource then Error("source projection failed"); fi;
if S * TransposedMat(S) <> Paperture then Error("aperture projection failed"); fi;
if Psource * Psource <> Psource then Error("source idempotent failed"); fi;
if Paperture * Paperture <> Paperture then Error("aperture idempotent failed"); fi;
if S * TransposedMat(S) * S <> S then Error("partial isometry failed"); fi;
T := [[0,0],[1,0]];;
if TransposedMat(S)*S + TransposedMat(T)*T <> IdentityMat(2, Rationals) then Error("two shard partition failed"); fi;
Print("holographic Cuntz shard GAP certificate: ok\n");
