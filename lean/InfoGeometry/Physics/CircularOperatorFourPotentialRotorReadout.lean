import InfoGeometry.Physics.CircularOperatorPotentialNativeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Real split readout of the full circular `1+3+3+1` operator packet.
The bivector rotor is kept as the real replacement for the complex phase
symbol; no external `Complex.I` is introduced here. -/
namespace InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout

open InfoGeometry.Physics
open InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
open InfoGeometry.Physics.CircularChiralFockScalarPoleBridge

noncomputable section
abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5
abbrev RealOperatorFourPotential := Fin 4 → FockOp

def circularCompressedFourPotential (i : Fin 3) : RealOperatorFourPotential :=
  ![(1 / 2 : ℝ) • (circularFockScalarPlus + circularFockScalarMinus),
    (1 / 2 : ℝ) • (positiveFockRail i + negativeFockRail i),
    (1 / 2 : ℝ) • (negativeFockRail i - positiveFockRail i),
    (1 / 2 : ℝ) • (circularFockScalarPlus - circularFockScalarMinus)]

def realSplitFourSoldering (v : RealOperatorFourPotential) :
    Matrix (Fin 2) (Fin 2) FockOp :=
  !![v 0 + v 3, v 1 - v 2; v 1 + v 2, v 0 - v 3]

theorem circularCompressedFourPotential_reconstruct (i : Fin 3) :
    (circularCompressedFourPotential i 0 + circularCompressedFourPotential i 3 =
        circularFockScalarPlus) ∧
    (circularCompressedFourPotential i 0 - circularCompressedFourPotential i 3 =
        circularFockScalarMinus) ∧
    (circularCompressedFourPotential i 1 - circularCompressedFourPotential i 2 =
        positiveFockRail i) ∧
    (circularCompressedFourPotential i 1 + circularCompressedFourPotential i 2 =
        negativeFockRail i) := by
  simp [circularCompressedFourPotential]
  constructor
  · module
  constructor
  · module
  constructor <;> module

theorem realSplitFourSoldering_eq_circularOperatorZorn (i : Fin 3) :
    realSplitFourSoldering (circularCompressedFourPotential i) =
      OperatorZornMatrix.toMatrix (circularColourOperatorZorn i) := by
  rw [circularColourOperatorZorn_toMatrix]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [realSplitFourSoldering, circularCompressedFourPotential] <;>
    norm_num [smul_eq_mul] <;> ring

theorem circular_1331_compressed_four_potential_packet (i : Fin 3) :
    realSplitFourSoldering (circularCompressedFourPotential i) =
      !![circularFockScalarPlus, positiveFockRail i;
         negativeFockRail i, circularFockScalarMinus] := by
  exact realSplitFourSoldering_eq_circularOperatorZorn i

end
end InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout
