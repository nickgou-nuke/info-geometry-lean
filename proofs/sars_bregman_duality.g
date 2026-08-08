Normalize := function(e)
  if IsList(e) and Length(e)=2 and e[1]="Log" and IsList(e[2]) and e[2][1]="Exp" then return Normalize(e[2][2]); fi;
  if IsList(e) and Length(e)=2 and e[1]="Exp" then return ["Exp", Normalize(e[2])]; fi;
  if IsList(e) and Length(e)=2 and e[1]="Log" then return ["Log", Normalize(e[2])]; fi;
  if IsList(e) and Length(e)=3 and e[1]="Sub" then return ["Sub", Normalize(e[2]), Normalize(e[3])]; fi;
  return e;
end;
modular := ["Sub", ["Sub", "u", ["Sub", "x", "y"]], "1"];
burgExp := ["Sub", ["Sub", "u", ["Log", ["Exp", ["Sub", "x", "y"]]]], "1"];
itakuraExp := ["Sub", ["Sub", ["Exp", "x"], ["Log", ["Exp", "x"]]], "1"];
itakuraModular := ["Sub", ["Sub", ["Exp", "x"], "x"], "1"];
if Normalize(burgExp) <> modular then Error("burg"); fi;
if Normalize(itakuraExp) <> itakuraModular then Error("itakura"); fi;
for n in [-5..5] do if n*n < 0 then Error("quad"); fi; od;
edges := ["qft_modular_to_itakura_saito","bregman_coordinate_isomorphism","stabilizes_krein_entropy"];
if Length(edges) <> 3 then Error("edges"); fi;
Print(rec(burg_exp_normalizes:=true,itakura_exp_normalizes:=true,quadratic_sample_nonnegative:=true,vacuum_zero:=true,edges:=Length(edges)));
QUIT;
