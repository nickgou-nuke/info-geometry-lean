T3 := function(Z, N)
  return (Z - N) / 2;
end;

MassNumber := function(N, Z)
  return N + Z;
end;

if MassNumber(32, 32) <> 64 then Error("mass"); fi;
if T3(32, 32) <> 0 then Error("T3"); fi;
if 40 + 32 - 4 * 2 <> 64 then Error("reaction"); fi;

large_delta := -39 / 10;
chi2_large := 54 / 100;
chi2_small := 80 / 100;

QuadrupoleContent := function(delta)
  return delta^2 / (1 + delta^2);
end;

if not (chi2_large < chi2_small) then Error("chi2"); fi;
if QuadrupoleContent(large_delta) <> 1521/1621 then Error("quadrupole"); fi;
if not (93/100 < QuadrupoleContent(large_delta)) then Error("quadrupole window"); fi;

tau9_upper := 4;
tau7 := 431 / 10;
tau5 := 242 / 10;
lambda7 := 232 / 10000;
if not (tau9_upper < tau5 and tau5 < tau7) then Error("tau order"); fi;
if not (43 < 1 / lambda7 and 1 / lambda7 < 432 / 10) then Error("lambda7"); fi;

I1665 := 567;
I1048 := 130;
I747 := 89;
if I1665 + I1048 + I747 <> 786 then Error("branch sum"); fi;
if not (I1048 + I747 < I1665) then Error("branch dominance"); fi;

BE1_64 := 247 / 1000000000;
BM2_64 := 606 / 100;
BE1_66 := 37 / 10000000;
BM2_66 := 39 / 10000;
BM2_68 := 71 / 100;

if BE1_64 / BE1_66 <> 247/3700 then Error("BE1 ratio"); fi;
if not (BE1_64 < BE1_66) then Error("BE1 order"); fi;
if BM2_64 / BM2_66 <> 20200/13 then Error("BM2 ratio"); fi;
if not (BM2_68 < BM2_64) then Error("BM2 order"); fi;

BE2_64_747 := 1;
BE2_66_886 := 4 / 10;
if BE2_64_747 / BE2_66_886 <> 5/2 then Error("BE2 ratio"); fi;

AlphaDifference := function(alpha_i, alpha_f)
  return alpha_i - alpha_f;
end;

Eq6AmplitudeScale := function(alpha_i, alpha_f)
  return (2 / 3) * AlphaDifference(alpha_i, alpha_f)^2;
end;

Alpha2FromBE1 := function(be1_64, be1_66)
  return (3 / 8) * be1_64 / be1_66;
end;

Eq7BE164 := function(alpha2, be1_66)
  return (8 / 3) * alpha2 * be1_66;
end;

if Eq6AmplitudeScale(1, -1) <> 8/3 then Error("Eq6"); fi;
alpha2 := Alpha2FromBE1(BE1_64, BE1_66);
if alpha2 <> 741/29600 then Error("alpha2"); fi;
if 100 * alpha2 <> 741/296 then Error("alpha2 percent"); fi;
if not (24/1000 < alpha2 and alpha2 < 26/1000) then Error("alpha2 window"); fi;
if Eq7BE164(alpha2, BE1_66) <> BE1_64 then Error("Eq7"); fi;

Print(rec(
  T3_Ge64 := T3(32, 32),
  quadrupole_content_delta_minus_3_9 := QuadrupoleContent(large_delta),
  BE1_64_over_66 := BE1_64 / BE1_66,
  alpha2 := alpha2,
  alpha2_percent := 100 * alpha2
), "\n");

QUIT;
