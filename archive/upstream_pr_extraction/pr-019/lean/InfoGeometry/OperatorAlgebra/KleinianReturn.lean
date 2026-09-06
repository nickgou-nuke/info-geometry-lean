/-
InfoGeometry/OperatorAlgebra/KleinianReturn.lean

Non-orientable/projective return witness.

This module does not prove that every `Cl(1,1)` model is a Klein bottle.  It
records the boundary-gluing datum saying that the projective boundary returns
through the Tomita mirror.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KleinianReturn

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## 1. Projective Tomita return -/

/--
A projective boundary return datum.

`boundaryLimit` is the algebraic replacement for “flow to infinity/null
boundary.”  The gluing law says that boundary return applies the Tomita mirror.
-/
structure ProjectiveTomitaReturn
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Boundary limit/return map. -/
  boundaryLimit : Op → Op

  /-- Boundary return is Tomita mirroring on observable algebra elements. -/
  boundary_eq_mirror :
    ∀ x : Op, x ∈ T.M →
      boundaryLimit x = T.tomitaMirror x

namespace ProjectiveTomitaReturn

variable
    {Op : Type*} [Ring Op]
    {T : TomitaCommutantDatum Op}

variable (R : ProjectiveTomitaReturn Op T)

/--
Observable algebra elements return through the boundary into the commutant.
-/
theorem observable_returns_to_commutant
    {x : Op}
    (hx : x ∈ T.M) :
    R.boundaryLimit x ∈ T.Mcomm := by
  rw [R.boundary_eq_mirror x hx]
  exact T.mirror_M_to_comm x hx

end ProjectiveTomitaReturn

/-! ## 2. Interpretation certificate -/

/--
A non-orientable return interpretation certificate.

This is where a model may say “the projective Tomita return is represented
topologically as a Moebius/Klein-type gluing.”
-/
structure NonOrientableReturnInterpretation
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (R : ProjectiveTomitaReturn Op T) where
  /-- Certificate for non-orientable gluing. -/
  nonorientable_gluing_certificate : Prop

  /-- Certificate for the chosen boundary model. -/
  v4_boundary_certificate : Prop

  /-- CPT/PT interpretation certificate. -/
  cpt_or_pt_interpretation_certificate : Prop

end InfoGeometry.OperatorAlgebra.KleinianReturn
