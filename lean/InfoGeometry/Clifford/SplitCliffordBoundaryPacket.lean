import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/--
Repo-facing split Clifford boundary packet.

This is a theorem bundle, not a new classification theorem.
-/
structure SplitCliffordBoundaryPacket where
  /-- The split Albert-Cayley-Dickson doubling layer has canonical null factors. -/
  split_albert_zero_divisors :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0

  /-- The recursive split `Cl(1,1)` tensor step used by the tower. -/
  cl11_tensor_step :
    SplitClNNAlg 4 ≃ₐ[ℝ] SplitClNNTensorStep 3

  /-- The repo-owned `Cl(4,4)` stage of the split Bott tower. -/
  cl44_stage : SplitCl44Algebra = SplitBottClifford 4

  /-- The next split Bott stage, i.e. the repo-owned `Cl(5,5)` tower step. -/
  cl55_stage :
    SplitBottClifford 5
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad 4))

  /-- The split `Cl(4,4)` complexification equivalence. -/
  cl44_complexification : Cl44Complex ≃ₐ[ℂ] ℂ ⊗[ℝ] Cl44

  /-- The quadratic split `Cl(4,4)` conformal-count diagnostic. -/
  quadratic_conformal_count :
    quadraticLightSpaceDim
      + (quadraticLeviRotationDim + dilationCharacterDim)
      + quadraticLightSpaceDim
        = quadraticConformalClosureDim

  /-- The split `Cl(4,4)` spin-factor route is not the quadratic `so(5,5)` count. -/
  spin_factor_not_so55 :
    ¬ spinFactorDim
        + (spinFactorStructureRotationDim + dilationCharacterDim)
        + spinFactorDim
          = quadraticConformalClosureDim

  /-- The split `Cl(4,4)` triality placement packet in the Levi layer. -/
  triality_levi_placement : TrialityLeviPlacement

  /-- The label-level `S₃` generation packet. -/
  generation_rotation : SplitCl44GenerationRotationPacket

  /-- The first normalized head null pairing in the split `Cl(4,4)` carrier. -/
  head_null_pairing :
    SplitCl44Bilinear
      (InfoGeometry.Clifford.ClNN.headNullMinus 3)
      (InfoGeometry.Clifford.ClNN.headNullPlus 3) = 1 / 2

  /-- The normalized split-null Clifford CAR in the `Cl(4,4)` carrier. -/
  head_null_clifford_car :
    InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3
        * InfoGeometry.Clifford.ClNN.gammaHeadNullPlus 3
      + InfoGeometry.Clifford.ClNN.gammaHeadNullPlus 3
        * InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3 = 1

/-- Canonical repository packet for the split Clifford boundary. -/
def canonicalSplitCliffordBoundaryPacket : SplitCliffordBoundaryPacket where
  split_albert_zero_divisors :=
    AlbertStep.gamma_one_has_canonical_zero_divisors (F := ℝ)
      (A := SplitQuaternion ℝ)
  cl11_tensor_step := splitCliffordTensorStepEquiv 3
  cl44_stage := rfl
  cl55_stage := cl55_as_splitBottStep
  cl44_complexification := cl44ComplexificationEquiv
  quadratic_conformal_count := splitCl44_quadratic_conformal_count
  spin_factor_not_so55 := splitCl44_spin_factor_route_not_so55_count
  triality_levi_placement := splitCl44_triality_levi_placement
  generation_rotation := canonicalGenerationRotationPacket
  head_null_pairing := splitCl44_headNull_pairing
  head_null_clifford_car := splitCl44_headNull_clifford_car

end InfoGeometry.Clifford.SplitCliffordBoundary
