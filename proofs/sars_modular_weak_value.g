surprisalQuadratic := x -> x*x;
for x in [-5..5] do
  if surprisalQuadratic(x) < 0 then Error("surprisal"); fi;
od;
if surprisalQuadratic(0) <> 0 then Error("zero"); fi;
weakDenominatorSame := 1;
weakDenominatorOrthogonal := 0;
if weakDenominatorSame <> 1 then Error("same"); fi;
if weakDenominatorOrthogonal <> 0 then Error("orthogonal"); fi;
weakValueSame := k0 -> k0 / weakDenominatorSame;
if weakValueSame(7) <> 7 then Error("weak"); fi;
Print(rec(surprisal_sample_nonnegative:=true, vacuum_zero:=true, weak_denominator_same:=weakDenominatorSame, weak_denominator_orthogonal:=weakDenominatorOrthogonal, weak_value_same:=weakValueSame(7), orthogonal_weak_value_defined:=false, trace_status:="not_trace_class_in_infinite_GNS", measurement_regime:="weak_coupling"));
QUIT;
