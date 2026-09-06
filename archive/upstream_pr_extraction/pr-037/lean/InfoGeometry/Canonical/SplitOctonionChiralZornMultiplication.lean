import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations

namespace InfoGeometry.Canonical

/-!
Chiral presentation of the native split-octonion carrier.

This is not an associative matrix algebra and does not install a `Mul`
instance on the carrier.  The multiplication below is the existing native
split-octonion multiplication, exposed with the chiral/Witt generators as a
named basis interface.
-/

abbrev ChiralZornCarrier := StandardRationalSplitOctonion

def chiralZornMul
    (x y : ChiralZornCarrier) : ChiralZornCarrier :=
  splitOctonionMulQ x y

def chiralZornOne : ChiralZornCarrier := rationalBasis .one

def chiralZornBasis
    (c : SplitOctonionColour) : Fin 4 → ChiralZornCarrier
  | 0 => modularNPlus
  | 1 => modularNMinus
  | 2 => modularSigmaPlus c
  | 3 => modularSigmaMinus c

@[simp] theorem chiralZornMul_eq_native
    (x y : ChiralZornCarrier) :
    chiralZornMul x y = splitOctonionMulQ x y :=
  rfl

@[simp] theorem chiralZornBasis_nPlus
    (c : SplitOctonionColour) :
    chiralZornBasis c 0 = modularNPlus :=
  rfl

@[simp] theorem chiralZornBasis_nMinus
    (c : SplitOctonionColour) :
    chiralZornBasis c 1 = modularNMinus :=
  rfl

@[simp] theorem chiralZornBasis_sigmaPlus
    (c : SplitOctonionColour) :
    chiralZornBasis c 2 = modularSigmaPlus c :=
  rfl

@[simp] theorem chiralZornBasis_sigmaMinus
    (c : SplitOctonionColour) :
    chiralZornBasis c 3 = modularSigmaMinus c :=
  rfl

@[simp] theorem chiralZorn_nPlus_mul_nPlus :
    chiralZornMul modularNPlus modularNPlus = modularNPlus :=
  modularNPlus_sq

@[simp] theorem chiralZorn_nMinus_mul_nMinus :
    chiralZornMul modularNMinus modularNMinus = modularNMinus :=
  modularNMinus_sq

@[simp] theorem chiralZorn_nPlus_mul_nMinus :
    chiralZornMul modularNPlus modularNMinus = 0 :=
  modularNPlus_mul_modularNMinus

@[simp] theorem chiralZorn_nMinus_mul_nPlus :
    chiralZornMul modularNMinus modularNPlus = 0 :=
  modularNMinus_mul_modularNPlus

@[simp] theorem chiralZorn_sigmaPlus_sq
    (c : SplitOctonionColour) :
    chiralZornMul (modularSigmaPlus c) (modularSigmaPlus c) = 0 :=
  modularSigmaPlus_sq_zero c

@[simp] theorem chiralZorn_sigmaMinus_sq
    (c : SplitOctonionColour) :
    chiralZornMul (modularSigmaMinus c) (modularSigmaMinus c) = 0 :=
  modularSigmaMinus_sq_zero c

@[simp] theorem chiralZorn_sigmaPlus_mul_sigmaMinus
    (c : SplitOctonionColour) :
    chiralZornMul (modularSigmaPlus c) (modularSigmaMinus c) = modularNPlus :=
  modularSigmaPlus_mul_modularSigmaMinus c

@[simp] theorem chiralZorn_sigmaMinus_mul_sigmaPlus
    (c : SplitOctonionColour) :
    chiralZornMul (modularSigmaMinus c) (modularSigmaPlus c) = modularNMinus :=
  modularSigmaMinus_mul_modularSigmaPlus c

theorem chiralZorn_basis_resolution :
    modularNPlus + modularNMinus = chiralZornOne :=
  modularPolarized_one

end InfoGeometry.Canonical
