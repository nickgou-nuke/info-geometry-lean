EqualMixingAmplitude := function(Mexp, M01, M10)
  return Mexp / (M01 + M10);
end;;

MixingProbability := function(Mexp, M01, M10)
  local b;
  b := EqualMixingAmplitude(Mexp, M01, M10);
  return b^2;
end;;

if MixingProbability(138/10000, -228/10000, 801/10000) <> 2116/36481 then Error("P30"); fi;
if MixingProbability(162/10000, 1086/10000, -127/10000) <> 26244/919681 then Error("S32"); fi;
if MixingProbability(160/100000, 819/100000, 2533/100000) <> 400/175561 then Error("Cl34"); fi;
if MixingProbability(38/10000, -144/10000, -233/10000) <> 1444/142129 then Error("Ar36"); fi;

if not (57/10 < 100 * MixingProbability(138/10000, -228/10000, 801/10000)
  and 100 * MixingProbability(138/10000, -228/10000, 801/10000) < 59/10) then Error("P30 percent"); fi;

Print([
  MixingProbability(138/10000, -228/10000, 801/10000),
  MixingProbability(162/10000, 1086/10000, -127/10000),
  MixingProbability(160/100000, 819/100000, 2533/100000),
  MixingProbability(38/10000, -144/10000, -233/10000)
], "\n");
