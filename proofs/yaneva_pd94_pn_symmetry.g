ZPd94 := 46;;
NPd94 := 48;;
APd94 := 94;;
protonHoles := 50 - ZPd94;;
neutronHoles := 50 - NPd94;;
totalHoles := protonHoles + neutronHoles;;
Tz := function(N, Z) return (N - Z) / 2; end;;
InIsospinMultiplet := function(T, twoTz) return AbsInt(twoTz) <= 2*T; end;;
g92Degeneracy := 10;;
singleJConfigCount := Binomial(g92Degeneracy, protonHoles) * Binomial(g92Degeneracy, neutronHoles);;
isoscalarDim := 2*0 + 1;;
isovectorDim := 2*1 + 1;;
yrast8B := 205;;
yrast8BLower := yrast8B - 25;;
yrast8BUpper := yrast8B + 34;;
gdsNeutronCharge := 84/100;;
gds8to6 := 192;;
g9full14 := 112;; g9t0_14 := 82;; g9t1_14 := 9;;
g9full8 := 144;; g9t0_8 := 191;; g9t1_8 := 11;;
g9full6 := 398;; g9t0_6 := 398;; g9t1_6 := 5;;

if ZPd94 + NPd94 <> APd94 then Error("A"); fi;
if NPd94 <> ZPd94 + 2 then Error("N=Z+2"); fi;
if Tz(NPd94, ZPd94) <> 1 then Error("Tz"); fi;
if [protonHoles, neutronHoles, totalHoles] <> [4,2,6] then Error("holes"); fi;
if not InIsospinMultiplet(1, NPd94 - ZPd94) then Error("T=1 Pd"); fi;
if not InIsospinMultiplet(1, 47 - 47) then Error("T=1 Ag"); fi;
if g92Degeneracy <> 10 or singleJConfigCount <> 9450 then Error("g9/2"); fi;
if isoscalarDim <> 1 or isovectorDim <> 3 then Error("pair dims"); fi;
if not (8 = 6 + 2 and 6 = 4 + 2 and 14 = 12 + 2) then Error("E2"); fi;
if yrast8BLower <> 180 or yrast8BUpper <> 239 or not (yrast8B < 250) then Error("B(E2)"); fi;
if gdsNeutronCharge <> 21/25 then Error("GDS charge"); fi;
if not (yrast8BLower <= gds8to6 and gds8to6 <= yrast8BUpper) then Error("GDS interval"); fi;
if not (AbsInt(g9full14-g9t0_14) < AbsInt(g9full14-g9t1_14)) then Error("T0 14"); fi;
if not (AbsInt(g9full8-g9t0_8) < AbsInt(g9full8-g9t1_8)) then Error("T0 8"); fi;
if not (AbsInt(g9full6-g9t0_6) < AbsInt(g9full6-g9t1_6)) then Error("T0 6"); fi;

Print(rec(
  A := APd94,
  Z := ZPd94,
  N := NPd94,
  Tz := Tz(NPd94, ZPd94),
  protonHoles := protonHoles,
  neutronHoles := neutronHoles,
  g92Degeneracy := g92Degeneracy,
  singleJConfigCount := singleJConfigCount,
  isoscalarDim := isoscalarDim,
  isovectorDim := isovectorDim,
  B_E2_8_to_6 := yrast8B,
  B_E2_interval := [yrast8BLower, yrast8BUpper],
  table1GDS8to6 := gds8to6,
  table1T0CloserThanT1 := true,
  gdsNeutronCharge := gdsNeutronCharge,
  edges := 7
), "\n");
QUIT;
