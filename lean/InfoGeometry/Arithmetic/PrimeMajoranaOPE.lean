import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaOPE

Split-Majorana OPE surface for prime-indexed fields.

This file records the OPE grammar

* `c_p(z)c_q(w) ~ δ_pq / (z - w)`;
* `d_p(z)d_q(w) ~ -δ_pq / (z - w)`;
* `c_p(z)d_q(w)` is regular.

It does not construct a vertex operator algebra, prove CFT locality, assert a
Pfaffian identity, or assert an infinite Euler product.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaOPE

/-- A symbolic singular OPE carrier. -/
structure SingularOPE
    (Field Label Coeff : Type*) where
  singularPart : Field → Field → Label → Coeff

/--
Split-Majorana OPE grammar.

`PrimeLabel` indexes finite prime modes.  The laws are deliberately `Prop`
fields so a later VOA/Laurent-series backend can supply the concrete
singular-part semantics.
-/
structure SplitMajoranaOPE
    (PrimeLabel Field Coeff : Type*) where
  cField : PrimeLabel → Field
  dField : PrimeLabel → Field
  delta : PrimeLabel → PrimeLabel → Coeff
  zeroCoeff : Coeff
  neg : Coeff → Coeff
  cc_singular : PrimeLabel → PrimeLabel → Prop
  dd_singular : PrimeLabel → PrimeLabel → Prop
  cd_regular : PrimeLabel → PrimeLabel → Prop
  cc_proof : ∀ p q, cc_singular p q
  dd_proof : ∀ p q, dd_singular p q
  cd_proof : ∀ p q, cd_regular p q

namespace SplitMajoranaOPE

variable {PrimeLabel Field Coeff : Type*}
variable (O : SplitMajoranaOPE PrimeLabel Field Coeff)

/-- The supplied `c c` OPE law is available. -/
theorem cc_holds
    (p q : PrimeLabel) :
    O.cc_singular p q :=
  O.cc_proof p q

/-- The supplied `d d` OPE law is available. -/
theorem dd_holds
    (p q : PrimeLabel) :
    O.dd_singular p q :=
  O.dd_proof p q

/-- The supplied `c d` regularity law is available. -/
theorem cd_regular_holds
    (p q : PrimeLabel) :
    O.cd_regular p q :=
  O.cd_proof p q

end SplitMajoranaOPE

/--
Möbius current OPE data.

The current is intended to be `j_p = :c_p d_p:`. Its action on the
split-Majorana fields is visible as propositions on concrete owner data; this
file does not prove abstract current-action laws without such data.
-/
structure MobiusCurrentOPE
    (PrimeLabel Field : Type*) where
  cField : PrimeLabel → Field
  dField : PrimeLabel → Field
  current : PrimeLabel → Field
  CurrentActsOnC : PrimeLabel → Field → Field → Field → Prop
  CurrentActsOnD : PrimeLabel → Field → Field → Field → Prop
  current_c :
    ∀ p : PrimeLabel, CurrentActsOnC p (current p) (cField p) (dField p)
  current_d :
    ∀ p : PrimeLabel, CurrentActsOnD p (current p) (cField p) (dField p)

namespace MobiusCurrentOPE

variable {PrimeLabel Field : Type*}
variable (O : MobiusCurrentOPE PrimeLabel Field)

/-- The supplied current-on-`c` law is available from the packet. -/
theorem current_c_holds
    (p : PrimeLabel) :
    O.CurrentActsOnC p (O.current p) (O.cField p) (O.dField p) :=
  O.current_c p

/-- The supplied current-on-`d` law is available from the packet. -/
theorem current_d_holds
    (p : PrimeLabel) :
    O.CurrentActsOnD p (O.current p) (O.cField p) (O.dField p) :=
  O.current_d p

end MobiusCurrentOPE

end InfoGeometry.Arithmetic.PrimeMajoranaOPE
