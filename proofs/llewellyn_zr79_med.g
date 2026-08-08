Tz := function(N, Z)
  return (N - Z) / 2;
end;

MED := function(excitationTzNegHalf, excitationTzPosHalf)
  return excitationTzNegHalf - excitationTzPosHalf;
end;

LevelFromTransition := function(lower, gamma)
  return lower + gamma;
end;

if Tz(39, 40) <> -1 / 2 then Error("Zr79 Tz"); fi;
if Tz(40, 39) <> 1 / 2 then Error("Y79 Tz"); fi;
if MED(184, 183) <> 1 then Error("7/2 MED"); fi;
if MED(416, 411) <> 5 then Error("9/2 MED"); fi;
if MED(715, 726) <> -11 then Error("11/2 MED"); fi;
if MED(1042, 1042) <> 0 then Error("13/2 MED"); fi;
if LevelFromTransition(183, 227) - 411 <> -1 then Error("Y cascade"); fi;
if LevelFromTransition(184, 230) - 416 <> -2 then Error("Zr cascade"); fi;
if not (294 / 1000 < 296 / 1000 and 296 / 1000 < 304 / 1000) then Error("Y beta"); fi;
if not (298 / 1000 < 304 / 1000) then Error("Zr beta"); fi;
if 10 * 4 <> 40 then Error("config count"); fi;

Print(rec(
  TzZr79 := Tz(39, 40),
  TzY79 := Tz(40, 39),
  MED7_2 := MED(184, 183),
  MED9_2 := MED(416, 411),
  MED11_2 := MED(715, 726),
  ZrCascadeDiscrepancy := LevelFromTransition(184, 230) - 416
), "\n");

QUIT;
