twoTz := function(N, Z)
  return N - Z;
end;

TzValue := function(N, Z)
  return (N - Z) / 2;
end;

mu := 219 / 100;
md := 467 / 100;
ms := 94;

isoscalar := (mu + md) / 2;
isovector := (mu - md) / 2;

if md - mu <> 62 / 25 then Error("quark mass difference"); fi;
if isoscalar <> 343 / 100 then Error("isoscalar mass"); fi;
if isovector <> -31 / 25 then Error("isovector mass"); fi;
if isoscalar + isovector <> mu then Error("u reconstruction"); fi;
if isoscalar - isovector <> md then Error("d reconstruction"); fi;
if ms <> 94 then Error("strange mass"); fi;

tzNeutron := 1 / 2;
tzProton := -1 / 2;

HenleyClassIII := function(d, tau3i, tau3j)
  return d * (tau3i + tau3j);
end;

if HenleyClassIII(7, tzNeutron, tzProton) <> 0 then
  Error("class III np");
fi;

if HenleyClassIII(7, tzNeutron, tzNeutron) +
    HenleyClassIII(7, tzProton, tzProton) <> 0 then
  Error("class III opposite");
fi;

Split := function(left, right)
  return left - right;
end;

if Split(93957 / 100, 93828 / 100) <> 129 / 100 then Error("n-p"); fi;
if Split(280894 / 100, 280842 / 100) <> 13 / 25 then Error("3H-3He"); fi;
if Split(466787 / 100, 466766 / 100) <> 21 / 100 then Error("5He-5Li"); fi;
if Split(653389 / 100, 653424 / 100) <> -7 / 20 then Error("7Li-7Be"); fi;

Print(rec(
  twoTz1616 := twoTz(16, 16),
  qcdIsoscalar := isoscalar,
  qcdIsovector := isovector,
  classIIINP := HenleyClassIII(7, tzNeutron, tzProton),
  neutronProtonSplit := Split(93957 / 100, 93828 / 100)
), "\n");

QUIT;
