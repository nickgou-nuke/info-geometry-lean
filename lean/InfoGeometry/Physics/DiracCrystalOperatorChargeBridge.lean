import Mathlib.Tactic
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Physics.SuperPoincareOperatorCharges

/-!
# Finite operator-charge and odd phase bridge

This file records only the finite matrix-algebra content needed by a later
Dirac-crystal or split-charge realization. An odd--odd anticommutator is an
operator-valued matrix; it is called central only after a commutation
hypothesis is supplied. The sign reversal below is derived from multiplying
both odd operators by `Complex.I`, not from ordinary conjugation.

No Narain lattice decomposition, Pin lift, glide action, or TKK grading is
asserted here. Those are separate bridge theorems.
-/

noncomputable section

namespace InfoGeometry.Physics.DiracCrystalOperatorChargeBridge

abbrev M2C := CuntzDeformedSuperPoincare.M2C

def hoppingAnticommutator (Q₁ Q₂ : M2C) : M2C :=
  SuperPoincareOperatorCharges.anti Q₁ Q₂

@[simp] theorem hoppingAnticommutator_comm (Q₁ Q₂ : M2C) :
    hoppingAnticommutator Q₁ Q₂ = hoppingAnticommutator Q₂ Q₁ := by
  exact SuperPoincareOperatorCharges.anti_comm _ _

def IsCentralOperator (Z : M2C) : Prop :=
  ∀ X : M2C, Z * X = X * Z

structure CentralHoppingPair where
  Q₁ : M2C
  Q₂ : M2C
  central : IsCentralOperator (hoppingAnticommutator Q₁ Q₂)

theorem centralHoppingPair_commutes (P : CentralHoppingPair) (X : M2C) :
    SuperPoincareOperatorCharges.comm
        (hoppingAnticommutator P.Q₁ P.Q₂) X = 0 := by
  exact SuperPoincareOperatorCharges.comm_eq_zero_of_commutes (P.central X)

def oddQuarterTurn (Q : M2C) : M2C := Complex.I • Q

theorem oddQuarterTurn_anticommutator (X Y : M2C) :
    SuperPoincareOperatorCharges.anti
        (oddQuarterTurn X) (oddQuarterTurn Y) =
      -SuperPoincareOperatorCharges.anti X Y := by
  ext i j
  simp [oddQuarterTurn, SuperPoincareOperatorCharges.anti,
    Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc]
  ring

theorem oddQuarterTurn_reverses_hoppingAnticommutator
    (Q₁ Q₂ : M2C) :
    SuperPoincareOperatorCharges.anti
      (oddQuarterTurn Q₁)
        (oddQuarterTurn Q₂) =
      -hoppingAnticommutator Q₁ Q₂ := by
  exact oddQuarterTurn_anticommutator Q₁ Q₂

theorem oddQuarterTurn_preserves_centrality (Z : M2C)
    (hZ : IsCentralOperator Z) :
    IsCentralOperator (-Z) := by
  intro X
  simpa only [neg_mul, mul_neg] using congrArg Neg.neg (hZ X)

end InfoGeometry.Physics.DiracCrystalOperatorChargeBridge

end
