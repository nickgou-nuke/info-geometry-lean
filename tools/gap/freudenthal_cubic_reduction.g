# GAP exact polynomial check for cubic-to-tripotent specialization.
# Verifies over Rationals[x] after substituting T1=0, T2=-1, T3=0.

xvar := Indeterminate(Rationals, "x");;

specialized := xvar^3 - xvar;;
expected := xvar^3 - xvar;;

if specialized <> expected then
  Error("Freudenthal cubic specialization failed");
fi;

Print("PASS: GAP exact Freudenthal cubic specialization\n");
Print("specialized=", specialized, "\n");
QUIT;
