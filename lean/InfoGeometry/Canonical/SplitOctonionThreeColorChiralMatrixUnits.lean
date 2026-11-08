import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Three-colour chiral matrix-unit interface

The native multiplication and matrix-unit relations are owned by
`SplitOctonionThreeColorChiralRelations`.  This file keeps the chiral naming
interface separate from the modular owner and does not install an associative
algebra structure on the ambient split-octonion carrier.
-/

abbrev ChiralOctonionCarrier := StandardRationalSplitOctonion

def threeColorChiralOne : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.one
def threeColorChiralL : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.l
def threeColorChiralI : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.i
def threeColorChiralIL : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.il
def threeColorChiralJ : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.j
def threeColorChiralJL : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.jl
def threeColorChiralK : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.k
def threeColorChiralKL : ChiralOctonionCarrier := rationalBasis IntegralSplitBasis.kl

inductive ChiralColour where
  | red | green | blue
deriving DecidableEq

def chiralUnit : ChiralColour → ChiralOctonionCarrier
  | .red => threeColorChiralI | .green => threeColorChiralJ | .blue => threeColorChiralK

def chiralLUnit : ChiralColour → ChiralOctonionCarrier
  | .red => threeColorChiralIL | .green => threeColorChiralJL | .blue => threeColorChiralKL

def chiralNPlus : ChiralOctonionCarrier :=
  (1 / 2 : ℚ) • (threeColorChiralOne + threeColorChiralL)

def chiralNMinus : ChiralOctonionCarrier :=
  (1 / 2 : ℚ) • (threeColorChiralOne - threeColorChiralL)

def chiralSigmaPlus (c : ChiralColour) : ChiralOctonionCarrier :=
  (1 / 2 : ℚ) • (-(chiralUnit c + chiralLUnit c))

def chiralSigmaMinus (c : ChiralColour) : ChiralOctonionCarrier :=
  (1 / 2 : ℚ) • (chiralUnit c - chiralLUnit c)
end InfoGeometry.Canonical
