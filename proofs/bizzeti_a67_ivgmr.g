MirrorAsymmetryRatio := function(eps)
  return ((1 + eps) / (1 - eps))^2;
end;;

uniformOneBody := 752 / 1000;;
uniformTwoBody := 410 / 1000;;
uniformEta := (uniformOneBody - uniformTwoBody) / uniformOneBody;;
if uniformEta <> 171 / 376 then Error("uniformEta"); fi;

epsUniformA1Negligible := -872 / 10000;;
epsUniformA0Negligible := 120 / 1000;;
epsWsA1Negligible := -852 / 10000;;
epsWsA0Negligible := 116 / 1000;;

RUniformA1Negligible := MirrorAsymmetryRatio(epsUniformA1Negligible);;
RUniformA0Negligible := MirrorAsymmetryRatio(epsUniformA0Negligible);;
RWsA1Negligible := MirrorAsymmetryRatio(epsWsA1Negligible);;
RWsA0Negligible := MirrorAsymmetryRatio(epsWsA0Negligible);;

if RUniformA1Negligible <> 1301881 / 1846881 then Error("RUniformA1"); fi;
if RUniformA0Negligible <> 196 / 121 then Error("RUniformA0"); fi;
if not (70/100 < RWsA1Negligible and RWsA1Negligible < 72/100) then Error("RWsA1"); fi;
if not (158/100 < RWsA0Negligible and RWsA0Negligible < 160/100) then Error("RWsA0"); fi;

if (2/3) * (615/1000) <> 41/100 then Error("twoBodyCoefficient"); fi;

Print([uniformEta, RUniformA1Negligible, RUniformA0Negligible,
  RWsA1Negligible, RWsA0Negligible, 41/100], "\n");
