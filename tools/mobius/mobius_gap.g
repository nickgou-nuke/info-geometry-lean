ClassifySigma := function(sigma)
  if sigma = 4 then
    return "parabolic";
  fi;
  if IsRat(sigma) then
    if sigma < 4 then
      return "elliptic";
    fi;
    return "hyperbolic";
  fi;
  return "loxodromic";
end;;

Contragredient := function(M)
  return [[M[2][2], -M[1][2]], [-M[2][1], M[1][1]]];
end;;

Pairing := function(eta, theta)
  return eta[1] * theta[1] + eta[2] * theta[2];
end;;

ApplySL2 := function(M, theta)
  return [M[1][1] * theta[1] + M[1][2] * theta[2], M[2][1] * theta[1] + M[2][2] * theta[2]];
end;;

ApplyDual := function(M, eta)
  local C;
  C := Contragredient(M);
  return [eta[1] * C[1][1] + eta[2] * C[2][1], eta[1] * C[1][2] + eta[2] * C[2][2]];
end;;

MobiusAction := function(M, z)
  if z = "infinity" then
    if M[2][1] = 0 then
      return "infinity";
    fi;
    return M[1][1] / M[2][1];
  fi;
  if M[2][1] * z + M[2][2] = 0 then
    return "infinity";
  fi;
  return (M[1][1] * z + M[1][2]) / (M[2][1] * z + M[2][2]);
end;;

Packet := function(name)
  if name = "hyperbolic" then
    return [[2, 0], [0, 1/2]];
  elif name = "parabolic" then
    return [[1, 1], [0, 1]];
  elif name = "elliptic" then
    return [[0, -1], [1, 0]];
  elif name = "loxodromic" then
    return [[1 + E(4), 1], [E(4), 1]];
  fi;
  Error("unknown packet");
end;;

if not IsBound(PacketName) then
  Error("Set PacketName before reading this file");
fi;

name := PacketName;;
M := Packet(name);;
det := M[1][1] * M[2][2] - M[1][2] * M[2][1];;
trace := M[1][1] + M[2][2];;
sigma := trace^2 / det;;
classification := ClassifySigma(sigma);;
if classification <> name then
  Error(Concatenation("classification mismatch: expected ", name, ", got ", classification));
fi;

Print("classification = ", classification, "\n");
Print("matrix = ", M, "\n");
Print("trace = ", trace, "\n");
Print("determinant = ", det, "\n");
Print("sigma = ", sigma, "\n");

if name = "hyperbolic" then
  eta := [3, 5];;
  theta := [7, 11];;
  lhs := Pairing(ApplyDual(M, eta), ApplySL2(M, theta));;
  rhs := Pairing(eta, theta);;
  if lhs <> rhs then
    Error("pairing invariance failed");
  fi;

  orbit := [1];;
  value := 1;;
  for i in [1..4] do
    value := MobiusAction(M, value);
    Add(orbit, value);
  od;
  if orbit <> [1, 4, 16, 64, 256] then
    Error("orbit computation failed");
  fi;
  if MobiusAction(M, 0) <> 0 then
    Error("0 should be fixed");
  fi;
  if MobiusAction(M, "infinity") <> "infinity" then
    Error("infinity should be fixed");
  fi;
  Print("multipliers = [4, 1/4]\n");
  Print("forward orbit from 1 = ", orbit, "\n");
fi;

Print("MOBIUS_GAP_OK\n");
QUIT;
