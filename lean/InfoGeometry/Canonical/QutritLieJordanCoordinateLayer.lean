import InfoGeometry.Algebraic.JordanCliffordLieSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QutritGellMannOperatorBasis

/-!
# Qutrit Lie--Jordan coordinate layer

The qutrit carrier is already an associative matrix algebra and its continuous
coordinates are owned by `QutritGellMannOperatorBasis`.  This file only records
the native Lie--Jordan consequences on that carrier; it does not introduce a
second product or a positivity/dissipation claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritLieJordanCoordinateLayer

open Matrix
open InfoGeometry.Canonical.QutritGellMannOperatorBasis

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

theorem qutrit_mul_jordan_lie_split (A B : QutritMatrix) :
    A * B =
      InfoGeometry.Algebraic.jordanProduct A B +
        InfoGeometry.Algebraic.lieBracket A B := by
  exact InfoGeometry.Algebraic.jordan_lie_split A B

theorem qutrit_jordan_comm (A B : QutritMatrix) :
    InfoGeometry.Algebraic.jordanProduct A B =
      InfoGeometry.Algebraic.jordanProduct B A := by
  unfold InfoGeometry.Algebraic.jordanProduct
  module

theorem qutrit_lie_antisymm (A B : QutritMatrix) :
    InfoGeometry.Algebraic.lieBracket B A =
      -InfoGeometry.Algebraic.lieBracket A B := by
  unfold InfoGeometry.Algebraic.lieBracket
  module

theorem qutrit_commutator_trace_zero (A B : QutritMatrix) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  simp

theorem qutrit_lie_jordan_coordinate_split (A B : QutritMatrix) (r : Fin 9) :
    gellMannCoefficient (A * B) r =
      gellMannCoefficient
          (InfoGeometry.Algebraic.jordanProduct A B) r +
        gellMannCoefficient
          (InfoGeometry.Algebraic.lieBracket A B) r := by
  rw [qutrit_mul_jordan_lie_split]
  simp [gellMannCoefficient]

end InfoGeometry.Canonical.QutritLieJordanCoordinateLayer

end noncomputable section
