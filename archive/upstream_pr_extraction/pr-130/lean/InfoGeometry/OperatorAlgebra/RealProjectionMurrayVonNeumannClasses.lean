import InfoGeometry.OperatorAlgebra.RealProjectionMurrayVonNeumann

/-!
# Projection classes modulo Murray--von Neumann equivalence

This file constructs the native quotient carrier only.  A monoid operation
requires a chosen stabilized block-sum construction and is intentionally left
to the matrix-specific downstream owner.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A] [StarRing A]

abbrev RealProjection : Type _ :=
  {p : A // IsIdempotentElem p ∧ star p = p}

def ProjectionMurrayVonNeumannRel
    (p q : RealProjection (A := A)) : Prop :=
  MurrayVonNeumannEquivalent p.1 q.1

theorem projectionMurrayVonNeumannRel_refl (p : RealProjection (A := A)) :
    ProjectionMurrayVonNeumannRel p p :=
  mvn_refl p.2

theorem projectionMurrayVonNeumannRel_symm
    {p q : RealProjection (A := A)}
    (h : ProjectionMurrayVonNeumannRel p q) :
    ProjectionMurrayVonNeumannRel q p :=
  mvn_symm h

theorem projectionMurrayVonNeumannRel_trans
    {p q r : RealProjection (A := A)}
    (hpq : ProjectionMurrayVonNeumannRel p q)
    (hqr : ProjectionMurrayVonNeumannRel q r) :
    ProjectionMurrayVonNeumannRel p r :=
  mvn_trans p.2 r.2 hpq hqr

instance : Setoid (RealProjection (A := A)) where
  r := ProjectionMurrayVonNeumannRel
  iseqv := {
    refl := projectionMurrayVonNeumannRel_refl
    symm := projectionMurrayVonNeumannRel_symm
    trans := projectionMurrayVonNeumannRel_trans
  }

abbrev RealProjectionClasses : Type _ :=
  Quotient (inferInstance : Setoid (RealProjection (A := A)))

def projectionClass (p : RealProjection (A := A)) :
    RealProjectionClasses (A := A) :=
  Quotient.mk _ p

theorem projectionClass_eq_of_equivalent
    {p q : RealProjection (A := A)}
    (h : ProjectionMurrayVonNeumannRel p q) :
    projectionClass p = projectionClass q :=
  Quotient.sound h

end InfoGeometry.OperatorAlgebra
