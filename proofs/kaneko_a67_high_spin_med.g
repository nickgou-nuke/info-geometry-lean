TotalMED := function(VCM, VCr, ell, ls)
  return VCM + VCr + ell + ls;
end;;

if (-95) - (-58) <> -37 then Error("epsilonLL gap"); fi;
if (-66) - 66 <> -132 then Error("epsilonLS gap"); fi;

RadialMED := function(m9, mJ)
  return 280 * (m9 / 2 - mJ / 2);
end;;

if RadialMED(4, 4) <> 0 then Error("radial zero"); fi;
if RadialMED(4, 3) <> 140 then Error("radial positive"); fi;
if 2 + 1 <> 3 then Error("g9 jump"); fi;
if 140 + (-132) <> 8 then Error("interference"); fi;

highMED := TotalMED(-40, 140, 0, -132);;
if highMED <> -32 then Error("high MED"); fi;

Print([-37, -132, 140, 3, highMED], "\n");
