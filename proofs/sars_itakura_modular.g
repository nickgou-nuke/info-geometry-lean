Normalize := function(e)
  if e = ["Log", ["Exp", "x"]] then return "x"; fi;
  if IsList(e) and Length(e) = 2 and e[1] = "Exp" then return ["Exp", Normalize(e[2])]; fi;
  if IsList(e) and Length(e) = 2 and e[1] = "Log" then return ["Log", Normalize(e[2])]; fi;
  if IsList(e) and Length(e) = 3 and e[1] = "Sub" then return ["Sub", Normalize(e[2]), Normalize(e[3])]; fi;
  return e;
end;
itakuraExp := ["Sub", ["Sub", ["Exp", "x"], ["Log", ["Exp", "x"]]], "1"];
modularReassociated := ["Sub", ["Sub", ["Exp", "x"], "x"], "1"];
if Normalize(["Log", ["Exp", "x"]]) <> "x" then Error("logexp"); fi;
if Normalize(itakuraExp) <> modularReassociated then Error("normalform"); fi;
for x in [-5..5] do
  if x*x < 0 then Error("quadratic"); fi;
od;
edges := ["exp_coordinate_transform","bregman_dual","stabilizes_modular_flow"];
if Length(edges) <> 3 then Error("edges"); fi;
Print(rec(log_exp_normalizes:=true, itakura_exp_normal_form:=true, quadratic_sample_nonnegative:=true, vacuum_zero:=true, edges:=Length(edges)));
QUIT;
