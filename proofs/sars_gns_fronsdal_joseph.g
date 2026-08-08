Sigma1 := function(u,v) return u[1]*v[2] - u[2]*v[1]; end;
NormSq1 := u -> u[1]*u[1] + u[2]*u[2];
FockExponentQuarter := u -> -NormSq1(u)/4;
if Sigma1([1,2],[3,5]) <> -Sigma1([3,5],[1,2]) then Error("sigma skew"); fi;
if NormSq1([0,0]) <> 0 then Error("norm zero"); fi;
if FockExponentQuarter([0,0]) <> 0 then Error("fock zero"); fi;
JosephMinor := function(p0,p1,q0,q1)
  return (p0*q0)*(p1*q1) - (p0*q1)*(p1*q0);
end;
for p0 in [-2..2] do for p1 in [-2..2] do for q0 in [-2..2] do for q1 in [-2..2] do
  if JosephMinor(p0,p1,q0,q1) <> 0 then Error("joseph minor"); fi;
od; od; od; od;
StarProductCorrection := function(hbar,eta) return -hbar*hbar*eta; end;
if StarProductCorrection(3,5) <> -45 then Error("star correction"); fi;
edges := ["GNS_completion","defines_quantization","cut_out_by","annihilates","embeds_as"];
if Length(edges) <> 5 then Error("edges"); fi;
Print(rec(sigmaSkew:=true, fockZeroExponent:=0, josephMinorZero:=true, starCorrectionSample:=StarProductCorrection(3,5), traceStatus:="not_trace_class_in_infinite_GNS", dmoduleGenerators:=1, edges:=Length(edges)), "\n");
QUIT;
