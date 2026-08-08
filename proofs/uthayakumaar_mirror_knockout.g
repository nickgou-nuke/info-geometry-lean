TwoTz := function(Z, N)
  return N - Z;
end;;

if TwoTz(25, 22) <> -3 then Error("Mn47 twoTz"); fi;
if TwoTz(22, 25) <> 3 then Error("Ti47 twoTz"); fi;
if TwoTz(24, 21) <> -3 then Error("Cr45 twoTz"); fi;
if TwoTz(21, 24) <> 3 then Error("Sc45 twoTz"); fi;

MED := function(eProtonRich, eNeutronRich)
  return eProtonRich - eNeutronRich;
end;;

SuppressionLine := function(deltaS)
  return 61/100 - (2/125) * deltaS;
end;;

RsTi47 := SuppressionLine(1916/1000);;
RsMn47 := SuppressionLine(1442/100);;
if RsTi47 <> 72418/125000 then Error("RsTi47"); fi;
if RsMn47 <> 4741/12500 then Error("RsMn47"); fi;
if not (RsMn47 < RsTi47) then Error("suppression order"); fi;

if MED(1226/10, 1594/10) <> -184/5 then Error("A47 MED"); fi;
if AbsoluteValue(97/100 - 1) > 1/10 then Error("BM1 precision"); fi;

Print([RsMn47, RsTi47, MED(1226/10, 1594/10), 97/100], "\n");
