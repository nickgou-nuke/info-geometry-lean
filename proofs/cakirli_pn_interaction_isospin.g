Tz := function(N, Z)
  return (N - Z) / 2;
end;

if Tz(12, 11) <> 1 / 2 then Error("Tz 23Na"); fi;
if Tz(11, 12) <> -1 / 2 then Error("Tz 23Mg"); fi;

MirrorDelta := function(deltaTzNegHalf, deltaTzPosHalf)
  return deltaTzNegHalf - deltaTzPosHalf;
end;

WithinError := function(central, reported, err)
  return AbsInt(NumeratorRat(central - reported)) / DenominatorRat(central - reported) <= err;
end;

if MirrorDelta(5785, 5970) <> -185 then Error("A7"); fi;
if MirrorDelta(914, 1037) <> -123 then Error("A9"); fi;
if not WithinError(MirrorDelta(1661, 2222), -562, 3) then Error("A13"); fi;
if MirrorDelta(41384 / 10, 41320 / 10) <> 64 / 10 then Error("A15"); fi;
if not WithinError(MirrorDelta(935, 14625 / 10), -527, 7) then Error("A17"); fi;
if not WithinError(MirrorDelta(37467 / 10, 36966 / 10), 500 / 10, 3 / 10) then Error("A19"); fi;
if MirrorDelta(31920 / 10, 318140 / 100) <> 106 / 10 then Error("A23"); fi;
if AbsInt(NumeratorRat(MirrorDelta(10650 / 10, 10650 / 10))) / DenominatorRat(MirrorDelta(10650 / 10, 10650 / 10)) > 50 then
  Error("A25 band");
fi;
if AbsInt(NumeratorRat(MirrorDelta(1661, 2222))) / DenominatorRat(MirrorDelta(1661, 2222)) <= 50 then
  Error("A13 band");
fi;

if 7 mod 4 <> 3 or 11 mod 4 <> 3 or 15 mod 4 <> 3 or 19 mod 4 <> 3 then
  Error("large mod4");
fi;
if 9 mod 4 <> 1 or 13 mod 4 <> 1 or 17 mod 4 <> 1 or 21 mod 4 <> 1 then
  Error("small mod4");
fi;

Print(rec(
  Tz23Na := Tz(12, 11),
  deltaA7 := MirrorDelta(5785, 5970),
  deltaA13 := MirrorDelta(1661, 2222),
  deltaA25 := MirrorDelta(10650 / 10, 10650 / 10)
), "\n");

QUIT;
