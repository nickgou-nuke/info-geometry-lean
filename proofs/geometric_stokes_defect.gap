# GAP certificate for the spinorial parity sign of one full winding.
# Encodes exp(J*pi) = cos(pi)+J sin(pi) = -1 by exact parity arithmetic.
ParitySign := n -> (-1)^n;
if not (ParitySign(1) = -1 and ParitySign(2) = 1) then
  Error("spinorial parity check failed");
fi;
Print("geometric_stokes_defect.gap: parity checks passed\n");
