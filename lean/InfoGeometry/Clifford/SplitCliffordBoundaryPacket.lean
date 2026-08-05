import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Clifford.SplitCl44Complexification
import InfoGeometry.Clifford.Cl44GenerationRotation

/-!
# Split Clifford boundary packet

This file packages the theorem surfaces in the repo that are actually
justifiable from the split Clifford / Bott tower and the split doubling lane:

* the Albert-Cayley-Dickson split doubling layer;
* the recursive `Cl(1,1)` tensor step;
* the recursive split `Cl(n,n)` Bott step;
* the split `Cl(4,4)` null-carrier facts;
* the split `Cl(4,4)` complexification equivalence;
* the quadratic conformal-count diagnostics;
* the label-level `S₃` generation packet.

The split Hopf / bi-twistor / `G_2^*` claims from the external literature are
deliberately not encoded here. The repo owns the split doubling and split
Clifford tower surfaces, not a twistor-identification theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCliffordBoundary

open scoped TensorProduct

open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Clifford.SplitCl44Complexification
open InfoGeometry.Clifford.Cl44GenerationRotation
open InfoGeometry.Canonical.Cl44ConformalNormalization
theorem split_albert_zero_divisors :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0 :=
  AlbertStep.gamma_one_has_canonical_zero_divisors (F := ℝ)
    (A := SplitQuaternion ℝ)

theorem cl44_stage : SplitCl44Algebra = SplitBottClifford 4 := rfl

theorem quadratic_conformal_count :
    quadraticLightSpaceDim
      + (quadraticLeviRotationDim + dilationCharacterDim)
      + quadraticLightSpaceDim
        = quadraticConformalClosureDim :=
  splitCl44_quadratic_conformal_count

theorem spin_factor_not_so55 :
    ¬ spinFactorDim
        + (spinFactorStructureRotationDim + dilationCharacterDim)
        + spinFactorDim
          = quadraticConformalClosureDim :=
  splitCl44_spin_factor_route_not_so55_count

theorem head_null_pairing :
    SplitCl44Bilinear
      (InfoGeometry.Clifford.ClNN.headNullMinus 3)
      (InfoGeometry.Clifford.ClNN.headNullPlus 3) = 1 / 2 :=
  splitCl44_headNull_pairing

theorem head_null_clifford_car :
    InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3
        * InfoGeometry.Clifford.ClNN.gammaHeadNullPlus 3
      + InfoGeometry.Clifford.ClNN.gammaHeadNullPlus 3
        * InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3 = 1 :=
  splitCl44_headNull_clifford_car

end InfoGeometry.Clifford.SplitCliffordBoundary
