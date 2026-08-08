Tz := function(N, Z)
  return (N - Z) / 2;
end;

IMME := function(a, b, c, tz)
  return a + b * tz + c * tz^2;
end;

ScatteringCIB := function(app, ann, anp)
  return (app + ann) / 2 - anp;
end;

ScatteringCSB := function(app, ann)
  return app - ann;
end;

MED := function(EminusTz, EplusTz)
  return EminusTz - EplusTz;
end;

if 2 * Tz(12, 11) <> 1 then Error("Tz"); fi;
if (467/100) - (219/100) <> 62/25 then Error("qcd split"); fi;
if ((219/100) + (467/100)) / 2 <> 343/100 then Error("isoscalar"); fi;
if ((219/100) - (467/100)) / 2 <> -31/25 then Error("isovector"); fi;
if IMME(1, 2, 3, 4) <> 57 then Error("IMME"); fi;
if 782/1000 <> 391/500 then Error("deltaNH"); fi;
if ScatteringCIB(0, 0, -57/10) <> 57/10 then Error("CIB"); fi;
if ScatteringCSB(3/4, -3/4) <> 3/2 then Error("CSB"); fi;
if (93957/100) - (93828/100) <> 129/100 then Error("mass np"); fi;
if MED(477, 0) <> 477 then Error("MED 477"); fi;
if MED(-1298, 0) <> -1298 then Error("MED -1298"); fi;

Print(rec(
  qcdSplit := (467/100) - (219/100),
  qcdIsoscalar := ((219/100) + (467/100)) / 2,
  qcdIsovector := ((219/100) - (467/100)) / 2,
  CIB := ScatteringCIB(0, 0, -57/10),
  MED26Si4plus := MED(477, 0)
), "\n");

QUIT;
