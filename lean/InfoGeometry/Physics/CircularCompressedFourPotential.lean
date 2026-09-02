import InfoGeometry.Physics.CircularChiralFockOperatorZornBridge

namespace InfoGeometry.Physics.CircularCompressedFourPotential

open InfoGeometry.Physics
open InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
open InfoGeometry.Physics.Cl55SpinorCartanFock

noncomputable section

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

abbrev RealOperatorFourPotential := Fin 4 →
  InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

local notation "P+" =>
  InfoGeometry.Physics.CircularChiralFockScalarPoleBridge.circularFockScalarPlus
local notation "P-" =>
  InfoGeometry.Physics.CircularChiralFockScalarPoleBridge.circularFockScalarMinus
local notation "ann" =>
  InfoGeometry.Physics.CircularChiralFockScalarPoleBridge.positiveFockRail
local notation "cre" =>
  InfoGeometry.Physics.CircularChiralFockScalarPoleBridge.negativeFockRail

def compressed (i : Fin 3) : RealOperatorFourPotential :=
  ![(1 / 2 : ℝ) • (P+ + P-),
    (1 / 2 : ℝ) • (ann i + cre i),
    (1 / 2 : ℝ) • (cre i - ann i),
    (1 / 2 : ℝ) • (P+ - P-)]

def realSplitSoldering (v : RealOperatorFourPotential) :
    Matrix (Fin 2) (Fin 2) FockOp :=
  !![v 0 + v 3, v 1 - v 2; v 1 + v 2, v 0 - v 3]

theorem compressed_reconstruction (i : Fin 3) :
    (compressed i) 0 + (compressed i) 3 = P+ ∧
    (compressed i) 0 - (compressed i) 3 = P- ∧
    (compressed i) 1 - (compressed i) 2 = ann i ∧
    (compressed i) 1 + (compressed i) 2 = cre i := by
  dsimp [compressed]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

theorem realSplitSoldering_eq_operatorZorn (i : Fin 3) :
    realSplitSoldering (compressed i) =
      OperatorZornMatrix.toMatrix
        (circularColourOperatorZorn i) := by
  apply Matrix.ext
  intro r c
  rw [circularColourOperatorZorn_toMatrix]
  fin_cases r <;> fin_cases c
  · simpa [realSplitSoldering] using (compressed_reconstruction i).1
  · simpa [realSplitSoldering] using (compressed_reconstruction i).2.2.1
  · simpa [realSplitSoldering] using (compressed_reconstruction i).2.2.2
  · simpa [realSplitSoldering] using (compressed_reconstruction i).2.1

end
end InfoGeometry.Physics.CircularCompressedFourPotential
