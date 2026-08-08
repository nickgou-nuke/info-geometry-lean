ObservedGap := function(E1, E2)
  return E2 - E1;
end;

H11 := function(E1, E2, b2)
  return E1 + b2 * ObservedGap(E1, E2);
end;

H22 := function(E1, E2, b2)
  return E2 - b2 * ObservedGap(E1, E2);
end;

UnperturbedGap := function(E1, E2, b2)
  return H22(E1, E2, b2) - H11(E1, E2, b2);
end;

B2FromGap := function(gap, obsGap)
  return (1 - gap / obsGap) / 2;
end;

Mg24E1 := 982811 / 100;
Mg24E2 := 996719 / 100;
Mg24ShellGap := 3;
Mg24ObsGap := ObservedGap(Mg24E1, Mg24E2);
Mg24B2 := B2FromGap(Mg24ShellGap, Mg24ObsGap);

if Mg24ObsGap <> 3477 / 25 then Error("Mg24 observed gap"); fi;
if Mg24B2 <> 567 / 1159 then Error("Mg24 b2"); fi;
if UnperturbedGap(Mg24E1, Mg24E2, Mg24B2) <> Mg24ShellGap then
  Error("Mg24 unperturbed gap");
fi;
if not (48 / 100 < Mg24B2 and Mg24B2 < 49 / 100) then
  Error("Mg24 percent window");
fi;
if (285084 / 100) - (265244 / 100) <> 992 / 5 then
  Error("Co54 gap");
fi;
if 2688 / 1000 <> 336 / 125 then Error("S32 percent"); fi;
if 2460 / 1000 <> 123 / 50 then Error("Ar36 percent"); fi;

Print(rec(
  Mg24ObsGap := Mg24ObsGap,
  Mg24B2 := Mg24B2,
  Mg24UnperturbedGap := UnperturbedGap(Mg24E1, Mg24E2, Mg24B2),
  Co54Gap := (285084 / 100) - (265244 / 100)
), "\n");

QUIT;
