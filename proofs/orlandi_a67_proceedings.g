CentroidShiftTime := function(cForward, cReverse)
  return ((cReverse - cForward) * (56/100)) / 2;
end;;

rawTau := CentroidShiftTime(409497/100, 409805/100);;
if rawTau <> 1078/1250 then Error("rawTau"); fi;

if 10/100 + 84/100 + 6/100 <> 1 then Error("branching"); fi;

ratioFirst := (13/10) / 1;;
ratioSecond := (81/10) / (17/10);;
if ratioFirst <> 13/10 then Error("ratioFirst"); fi;
if ratioSecond <> 81/17 then Error("ratioSecond"); fi;
if not (AbsoluteValue(ratioFirst - 1) <= 3/10) then Error("near symmetric"); fi;
if not (ratioSecond > 4) then Error("second asymmetric"); fi;
if not (7/10 < 13/10) then Error("lifetime order"); fi;
if not (7/10 < 12/4) then Error("12ns rejection"); fi;

Print([rawTau, 7/10, 13/10, ratioFirst, ratioSecond], "\n");
