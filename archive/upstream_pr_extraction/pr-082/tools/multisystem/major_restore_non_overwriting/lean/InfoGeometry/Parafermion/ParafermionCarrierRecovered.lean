import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient

noncomputable section

namespace InfoGeometry.Parafermion.Recovered

/--
A minimal archive recovery for the parafermion carrier sketch.

This is intentionally non-canonical and non-overwriting: it records the algebra,
carrier quotient, and highest-weight predicate interface from the recovered
fragment without claiming a built quotient action that has not yet been wired
into a live owner file.
-/
structure ParafermionAlgebra (R : Type*) [CommRing R] where
  A : Type*
  instRing : Ring A
  instAlgebra : Algebra R A

attribute [instance] ParafermionAlgebra.instRing ParafermionAlgebra.instAlgebra

variable {R : Type*} [CommRing R]

/--
Recovered quotient carrier used by the archive fragment.

We keep the carrier small and explicit: a quotient of the ambient algebra by a
chosen ideal.
-/
abbrev SpinorCarrierSpace (Alg : ParafermionAlgebra R) (I_null : Ideal Alg.A) : Type* :=
  Alg.A ⧸ I_null

/--
Abstract action datum for a parafermion algebra on its recovered spinor carrier.

This avoids overclaiming that the quotient action has already been constructed in
this fragment; later owner integration can replace this with a concrete module or
representation structure.
-/
structure CarrierAction (Alg : ParafermionAlgebra R) (I_null : Ideal Alg.A) where
  act : Alg.A → SpinorCarrierSpace Alg I_null → SpinorCarrierSpace Alg I_null

/--
Recovered highest-weight predicate from the archive sketch.

A vector is highest weight when the chosen algebra element annihilates it under
the supplied carrier action.
-/
def IsHighestWeightVector
    (Alg : ParafermionAlgebra R)
    (I_null : Ideal Alg.A)
    (ρ : CarrierAction Alg I_null)
    (v : SpinorCarrierSpace Alg I_null)
    (psi : Alg.A) : Prop :=
  ρ.act psi v = 0

/--
Zero is always highest weight for any annihilating algebra element under the
recovered action interface.
-/
theorem isHighestWeightVector_zero
    (Alg : ParafermionAlgebra R)
    (I_null : Ideal Alg.A)
    (ρ : CarrierAction Alg I_null)
    (psi : Alg.A)
    (hpsi : ρ.act psi 0 = 0) :
    IsHighestWeightVector Alg I_null ρ 0 psi :=
  hpsi

end InfoGeometry.Parafermion.Recovered
