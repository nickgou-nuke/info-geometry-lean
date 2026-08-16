import Mathlib.Tactic

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

end InfoGeometry.Arithmetic.PrimeMajoranaOPE
