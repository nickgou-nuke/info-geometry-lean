# GAP rational witness for q55 zero/null/generic strata.

RequireTrue := function(label, cond)
  if not cond then Error(Concatenation(label, " failed")); fi;
  Print(label, " OK\n");
end;

Q55 := function(v)
  local s, i;
  s := 0;
  for i in [1..5] do s := s + v[i]^2; od;
  for i in [6..10] do s := s - v[i]^2; od;
  return s;
end;

zero := List([1..10], i -> 0);
e0 := ShallowCopy(zero);; e0[1] := 1;;
e5 := ShallowCopy(zero);; e5[6] := 1;;
null := e0 + e5;

RequireTrue("GAP_SPINOR_ORBIT_Q55_ZERO", Q55(zero) = 0);
RequireTrue("GAP_SPINOR_ORBIT_Q55_NULL", null <> zero and Q55(null) = 0);
RequireTrue("GAP_SPINOR_ORBIT_Q55_GENERIC_POS", Q55(e0) = 1);
RequireTrue("GAP_SPINOR_ORBIT_Q55_GENERIC_NEG", Q55(e5) = -1);
for v in [zero, null, e0, e5] do
  RequireTrue("GAP_SPINOR_ORBIT_Q55_NEGALL_PRESERVES", Q55(-v) = Q55(v));
od;
Print("GAP_SPINOR_ORBIT_Q55_PACKET_OK\n");
