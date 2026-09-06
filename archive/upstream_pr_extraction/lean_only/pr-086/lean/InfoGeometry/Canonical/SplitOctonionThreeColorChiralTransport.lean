import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations

namespace InfoGeometry.Canonical

noncomputable section

/-!
# Three-colour chiral transport identities

This owner is a thin transport layer for the already-proved polarized basis on
three coloured split-octonion slices.  It does not introduce new algebraic
structure; it only re-exports the standard-to-polarized dictionary under a
transport-themed surface so umbrella imports in `Canonical/All` remain honest.
-/

open SplitOctonionColour

abbrev chiralTransportNPlus := modularNPlus
abbrev chiralTransportNMinus := modularNMinus
abbrev chiralTransportSigmaPlus := modularSigmaPlus
abbrev chiralTransportSigmaMinus := modularSigmaMinus

@[simp] theorem chiralTransport_one :
    chiralTransportNPlus + chiralTransportNMinus = rationalBasis .one :=
  modularPolarized_one

@[simp] theorem chiralTransport_epsilon :
    chiralTransportNPlus - chiralTransportNMinus = fundamentalSymmetry :=
  modularPolarized_epsilon

@[simp] theorem chiralTransport_phaseAxis (c : SplitOctonionColour) :
    chiralTransportSigmaMinus c - chiralTransportSigmaPlus c = phaseAxis c :=
  modularPolarized_phaseAxis c

@[simp] theorem chiralTransport_modularJ (c : SplitOctonionColour) :
    chiralTransportSigmaPlus c + chiralTransportSigmaMinus c = modularJ c :=
  modularPolarized_modularJ c

end

end InfoGeometry.Canonical
