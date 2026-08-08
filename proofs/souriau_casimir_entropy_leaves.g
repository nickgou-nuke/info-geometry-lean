IsospinCasimir := function(I)
  return I * (I + 1);
end;

PoincareMassCasimir := function(massSq)
  return -massSq;
end;

DilationSpringStiffness := function(C1)
  return -C1;
end;

IVGMRCoefficient := function(A, e, R, deltaE0)
  return ((A - 1) * e^2) / (4 * R * deltaE0);
end;

IVGMROneBodyRadial := function(ri, R)
  return ri^3 / R^2;
end;

IVGMRTwoBodyRadial := function(ri, rj, R)
  return ri * rj^2 / R^3;
end;

InducedIsoscalarE1Kernel := function(A, e, R, deltaE0, ri, rj)
  return IVGMRCoefficient(A, e, R, deltaE0) *
    (IVGMROneBodyRadial(ri, R) + IVGMRTwoBodyRadial(ri, rj, R));
end;

if IsospinCasimir(1 / 2) <> 3 / 4 then Error("isospin casimir"); fi;
if -1 / 2 + 1 / 2 <> 0 then Error("Tz flip"); fi;
if DilationSpringStiffness(PoincareMassCasimir(67)) <> 67 then Error("spring"); fi;
if InducedIsoscalarE1Kernel(67, 1, 1, 20, 1, 1) <> 33 / 20 then Error("IVGMR"); fi;

Print(rec(
  isospinCasimirHalf := IsospinCasimir(1 / 2),
  tzFlipSum := -1 / 2 + 1 / 2,
  dilationStiffness67 := DilationSpringStiffness(PoincareMassCasimir(67)),
  ivgmrKernelA67 := InducedIsoscalarE1Kernel(67, 1, 1, 20, 1, 1)
), "\n");

QUIT;
