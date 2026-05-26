import InfoGeometry.Arithmetic.SplitMajoranaPrimeGas
import InfoGeometry.Arithmetic.PrimeMajoranaOPE

/-!
# InfoGeometry.Quantum.PrimeMajoranaOPE

OPE Socket for Prime Majorana fields.
This module defines the structural predicates for the Operator Product Expansion
(OPE) limits of the split-Majorana prime gas. 
It intentionally defers the actual analytic mode expansions to a later, full CFT
construction. The purpose is to formally state the expected OPE behaviors
that correspond to the algebraic CAR layer without enforcing analytic limits here.
-/

noncomputable section

namespace InfoGeometry.Quantum.PrimeMajoranaOPE

/-- 
Carrier for the Operator Product Expansion. 
`Field` represents the analytic fields c(z), d(z).
`Kernel` represents the singular structure (e.g. 1/(z-w)).
-/
structure SplitMajoranaOPE
    (PrimeLabel Field Kernel : Type*) where
  c : PrimeLabel → Field
  d : PrimeLabel → Field
  singularPart : Field → Field → Kernel
  deltaPole : PrimeLabel → PrimeLabel → Kernel
  negDeltaPole : PrimeLabel → PrimeLabel → Kernel
  regularPart : Kernel

/-- OPE Predicate: c_p(z) c_q(w) ~ δ_pq / (z - w) -/
def IsCCOPE {PrimeLabel Field Kernel : Type*} 
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel) : Prop :=
  ∀ p q, OPE.singularPart (OPE.c p) (OPE.c q) = OPE.deltaPole p q

/-- OPE Predicate: d_p(z) d_q(w) ~ -δ_pq / (z - w) -/
def IsDDOPE {PrimeLabel Field Kernel : Type*} 
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel) : Prop :=
  ∀ p q, OPE.singularPart (OPE.d p) (OPE.d q) = OPE.negDeltaPole p q

/-- OPE Predicate: c_p(z) d_q(w) ~ regular -/
def IsCDRegular {PrimeLabel Field Kernel : Type*} 
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel) : Prop :=
  ∀ p q, OPE.singularPart (OPE.c p) (OPE.d q) = OPE.regularPart

/--
Equation-level quantum OPE data induces the arithmetic witness packet.

This is a genuine transport theorem from explicit singular-part equalities into
the witness-gated `Arithmetic.PrimeMajoranaOPE` surface; it does not claim any
analytic VOA/Laurent construction beyond the supplied equations.
-/
def toArithmeticSplitMajoranaOPE
    {PrimeLabel Field Kernel : Type*} [Zero Kernel] [Neg Kernel]
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel)
    (hcc : IsCCOPE OPE)
    (hdd : IsDDOPE OPE)
    (hcd : IsCDRegular OPE) :
    InfoGeometry.Arithmetic.PrimeMajoranaOPE.SplitMajoranaOPE PrimeLabel Field Kernel where
  cField := OPE.c
  dField := OPE.d
  delta := OPE.deltaPole
  zeroCoeff := 0
  neg := Neg.neg
  cc_singular := fun p q =>
    OPE.singularPart (OPE.c p) (OPE.c q) = OPE.deltaPole p q
  dd_singular := fun p q =>
    OPE.singularPart (OPE.d p) (OPE.d q) = OPE.negDeltaPole p q
  cd_regular := fun p q =>
    OPE.singularPart (OPE.c p) (OPE.d q) = OPE.regularPart
  cc_certificate := hcc
  dd_certificate := hdd
  cd_certificate := hcd

theorem toArithmeticSplitMajoranaOPE_cc_valid
    {PrimeLabel Field Kernel : Type*} [Zero Kernel] [Neg Kernel]
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel)
    (hcc : IsCCOPE OPE)
    (hdd : IsDDOPE OPE)
    (hcd : IsCDRegular OPE)
    (p q : PrimeLabel) :
    (toArithmeticSplitMajoranaOPE OPE hcc hdd hcd).cc_singular p q := by
  exact hcc p q

theorem toArithmeticSplitMajoranaOPE_dd_valid
    {PrimeLabel Field Kernel : Type*} [Zero Kernel] [Neg Kernel]
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel)
    (hcc : IsCCOPE OPE)
    (hdd : IsDDOPE OPE)
    (hcd : IsCDRegular OPE)
    (p q : PrimeLabel) :
    (toArithmeticSplitMajoranaOPE OPE hcc hdd hcd).dd_singular p q := by
  exact hdd p q

theorem toArithmeticSplitMajoranaOPE_cd_regular_valid
    {PrimeLabel Field Kernel : Type*} [Zero Kernel] [Neg Kernel]
    (OPE : SplitMajoranaOPE PrimeLabel Field Kernel)
    (hcc : IsCCOPE OPE)
    (hdd : IsDDOPE OPE)
    (hcd : IsCDRegular OPE)
    (p q : PrimeLabel) :
    (toArithmeticSplitMajoranaOPE OPE hcc hdd hcd).cd_regular p q := by
  exact hcd p q

end InfoGeometry.Quantum.PrimeMajoranaOPE
