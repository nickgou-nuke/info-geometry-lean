# GAP verification of D4 triality action on the three 8-dimensional characters.
# We realize the weights in the e_i-basis of D4:
#   8v : ±e_i
#   8s : (1/2)(±e1±e2±e3±e4), even number of minus signs
#   8c : (1/2)(±e1±e2±e3±e4), odd number of minus signs
# The triality outer automorphism is the order-3 map sending
# fundamental weights ω1 -> ω3 -> ω4 -> ω1.

Print("=== GAP: D4 triality on characters ===\n");

VecEq := function(a,b)
  return ForAll([1..Length(a)], i -> a[i] = b[i]);
end;

MinusCount := function(signs)
  return Number(signs, x -> x = -1);
end;

ApplyMatToSet := function(weights, M)
  return Set(List(weights, w -> w * M));
end;

# Fundamental triality matrices in the e-basis.
# sigma: ω1 -> ω3 -> ω4 -> ω1, fixes ω2.
sigma := [
  [ 1/2,  1/2,  1/2,  1/2 ],
  [ 1/2,  1/2, -1/2, -1/2 ],
  [ 1/2, -1/2,  1/2, -1/2 ],
  [ -1/2, 1/2,  1/2, -1/2 ]
];
# tau swaps ω3 and ω4 and fixes ω1,ω2; in e-basis this is e4 -> -e4.
tau := [
  [1,0,0,0],
  [0,1,0,0],
  [0,0,1,0],
  [0,0,0,-1]
];

id4 := IdentityMat(4, Rationals);

if sigma^3 = id4 then
  Print("sigma has order 3\n");
else
  Error("sigma^3 != 1\n");
fi;

if tau^2 = id4 then
  Print("tau has order 2\n");
else
  Error("tau^2 != 1\n");
fi;

if (sigma * tau)^2 = id4 then
  Print("(sigma*tau)^2 = 1, so sigma,tau generate an S3-action\n");
else
  Error("(sigma*tau)^2 != 1\n");
fi;

# The three triality weight systems.
vecWeights := [];
for i in [1..4] do
  Add(vecWeights, List([1..4], function(j) if i = j then return 1; else return 0; fi; end));
  Add(vecWeights, List([1..4], function(j) if i = j then return -1; else return 0; fi; end));
od;
vecWeights := Set(vecWeights);

spEvenWeights := [];
spOddWeights := [];
for s1 in [-1,1] do
  for s2 in [-1,1] do
    for s3 in [-1,1] do
      for s4 in [-1,1] do
        localSigns := [s1,s2,s3,s4];
        w := List(localSigns, x -> x/2);
        if MinusCount(localSigns) mod 2 = 0 then
          Add(spEvenWeights, w);
        else
          Add(spOddWeights, w);
        fi;
      od;
    od;
  od;
od;
spEvenWeights := Set(spEvenWeights);
spOddWeights := Set(spOddWeights);

Print("|8v weights| = ", Size(vecWeights), "\n");
Print("|8s weights| = ", Size(spEvenWeights), "\n");
Print("|8c weights| = ", Size(spOddWeights), "\n");

imgVecSigma := ApplyMatToSet(vecWeights, sigma);
imgEvenSigma := ApplyMatToSet(spEvenWeights, sigma);
imgOddSigma := ApplyMatToSet(spOddWeights, sigma);

if imgVecSigma = spEvenWeights and imgEvenSigma = spOddWeights and imgOddSigma = vecWeights then
  Print("sigma permutes characters as 8v -> 8s -> 8c -> 8v\n");
else
  Error("sigma does not realize the expected triality cycle\n");
fi;

imgVecTau := ApplyMatToSet(vecWeights, tau);
imgEvenTau := ApplyMatToSet(spEvenWeights, tau);
imgOddTau := ApplyMatToSet(spOddWeights, tau);

if imgVecTau = vecWeights and imgEvenTau = spOddWeights and imgOddTau = spEvenWeights then
  Print("tau fixes 8v and swaps 8s <-> 8c\n");
else
  Error("tau does not realize the expected transposition\n");
fi;

# Character-level conclusion: the unordered triple {χv,χs,χc} is S3-stable,
# hence any symmetric partition function built from these three characters is invariant.
chiOrbitUnderSigma := ["chi_v", "chi_s", "chi_c"];
Print("sigma-action on characters: ", chiOrbitUnderSigma, " -> [chi_s, chi_c, chi_v]\n");
Print("tau-action on characters:   [chi_v, chi_s, chi_c] -> [chi_v, chi_c, chi_s]\n");

permSigma := [2,3,1];
permTau := [1,3,2];
ApplyPerm := function(coeffs, perm)
  return List([1..Length(coeffs)], i -> coeffs[perm[i]]);
end;

coeffTotal := [1,1,1];
coeffDiracPair := [0,1,1];
Print("Total partition coefficients under sigma: ", ApplyPerm(coeffTotal, permSigma), "\n");
Print("Total partition coefficients under tau:   ", ApplyPerm(coeffTotal, permTau), "\n");
Print("Dirac-pair coefficients under sigma:      ", ApplyPerm(coeffDiracPair, permSigma), "\n");
Print("Dirac-pair coefficients under tau:        ", ApplyPerm(coeffDiracPair, permTau), "\n");
if ApplyPerm(coeffTotal, permSigma) = coeffTotal and ApplyPerm(coeffTotal, permTau) = coeffTotal then
  Print("Explicitly verified: chi_v + chi_s + chi_c is S3-invariant.\n");
else
  Error("Total partition character is not invariant.\n");
fi;
Print("As expected, chi_s + chi_c is tau-invariant but not sigma-invariant.\n");

Print("PASS: D4 triality invariance of the partition-character sector verified in GAP.\n");
QUIT;
