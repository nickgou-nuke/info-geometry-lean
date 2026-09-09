import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

/-!
# Units and coordinate action for the local split-Cl(1,1) packet

This owner packages the involutive switch and the two signature generators as
units.  It records the induced central inversion on the two-dimensional
quadratic generator space, without claiming a Pin-cover theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorLocalCl11Units

open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

noncomputable def localCl11PositiveUnit
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) : Units Op :=
  Units.mkOfMulEqOne (localCl11Positive P) (localCl11Positive P)
    (localCl11Positive_sq P)

noncomputable def localCl11NegativeUnit
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) : Units Op :=
  Units.mkOfMulEqOne (localCl11Negative P) (-localCl11Negative P) (by
    rw [mul_neg, localCl11Negative_sq]
    simp)

noncomputable def localCl11SwitchUnit
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) : Units Op :=
  Units.mkOfMulEqOne (P.bitOperator true) (P.bitOperator true)
    P.bitOperator_true_sq

@[simp] theorem localCl11PositiveUnit_coe
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) :
    (localCl11PositiveUnit P : Op) = localCl11Positive P := rfl

@[simp] theorem localCl11NegativeUnit_coe
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) :
    (localCl11NegativeUnit P : Op) = localCl11Negative P := rfl

@[simp] theorem localCl11SwitchUnit_coe
    {Op : Type*} [Ring Op] [IsDedekindFiniteMonoid Op]
    (P : BinaryWordTiltReadout Op) :
    (localCl11SwitchUnit P : Op) = P.bitOperator true := rfl

end InfoGeometry.Canonical.CantorLocalCl11Units
