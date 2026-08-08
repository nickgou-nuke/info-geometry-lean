T3 := function(Z, N)
  return (Z - N) / 2;
end;

if T3(33, 34) <> -1/2 then Error("T3 As67"); fi;
if T3(34, 33) <> 1/2 then Error("T3 Se67"); fi;

As725_BE1 := 14 / 10000000;
Se717_BE1 := 4 / 10000000;
As725_ME1 := 37 / 10000;
Se717_ME1 := 20 / 10000;
As319_BE1 := 83 / 10000000;
Se303_BE1_upper := 14 / 10000000;
As319_ME1 := 91 / 10000;
Se303_ME1_upper := 37 / 10000;

if As725_BE1 / Se717_BE1 <> 7/2 then Error("Table I first BE1"); fi;
if As725_ME1 / Se717_ME1 <> 37/20 then Error("Table I first ME1"); fi;
if As319_BE1 / Se303_BE1_upper <> 83/14 then Error("Table I second BE1"); fi;
if As319_ME1 / Se303_ME1_upper <> 91/37 then Error("Table I second ME1"); fi;

MIV := 29 / 10000;
MIS := 9 / 10000;
if MIS / MIV <> 9/29 then Error("MIS/MIV"); fi;

radial_cubic_siegert_ratio := 834 / 1000;
charge_correction_1MeV := 190 / 10000000;
magnetic_correction_1MeV := 53 / 100000;
if radial_cubic_siegert_ratio <> 417/500 then Error("Siegert radial"); fi;
if not (charge_correction_1MeV < 1/1000) then Error("charge correction"); fi;
if not (magnetic_correction_1MeV < 1/1000) then Error("magnetic correction"); fi;

C := 116 / 1000;
one_body := 752 / 1000;
two_body := 410 / 1000;
eta := (one_body - two_body) / one_body;
pf_average_r2 := 615 / 1000;
if eta <> 171/376 then Error("eta"); fi;
if not (45/100 < eta and eta < 46/100) then Error("eta window"); fi;
if (2/3) * pf_average_r2 <> two_body then Error("two-body"); fi;

MirrorRatio := function(eps)
  return ((1 + eps) / (1 - eps))^2;
end;

eps_A1_negligible := -872 / 10000;
eps_A0_negligible := 120 / 1000;
eps_WS_A1_negligible := -852 / 10000;
eps_WS_A0_negligible := 116 / 1000;

if MirrorRatio(eps_A1_negligible) <> 1301881/1846881 then Error("R A1"); fi;
if MirrorRatio(eps_A0_negligible) <> 196/121 then Error("R A0"); fi;
if not (70/100 < MirrorRatio(eps_WS_A1_negligible) and MirrorRatio(eps_WS_A1_negligible) < 72/100) then Error("R WS A1"); fi;
if not (158/100 < MirrorRatio(eps_WS_A0_negligible) and MirrorRatio(eps_WS_A0_negligible) < 160/100) then Error("R WS A0"); fi;

Eq60EpsilonKernel := function(C0, radial_ratio, eta0, A1, A0)
  return 3 * C0 * radial_ratio * ((eta0 * A1 - A0) / (A1 + 3 * A0));
end;

if Eq60EpsilonKernel(C, one_body, eta, 1, 0) <> 14877/125000 then Error("Eq60"); fi;
if ((67 - 1) / (4 * 20)) * (1 + 1) <> 33/20 then Error("A67 kernel"); fi;

Print(rec(
  T3_As := T3(33, 34),
  T3_Se := T3(34, 33),
  tableI_first_BE1_ratio := As725_BE1 / Se717_BE1,
  eta := eta,
  R_A1_negligible := MirrorRatio(eps_A1_negligible),
  R_A0_negligible := MirrorRatio(eps_A0_negligible)
), "\n");

QUIT;
