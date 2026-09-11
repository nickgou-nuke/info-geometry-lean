import InfoGeometry.Clifford.ClNN
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

/-!
# InfoGeometry.Canonical.ClNNBottBridge

Adjacent translator from the split `Cl(n,n)` owner surface to the existing Bott
periodicity corridor.

This file keeps the burden local:
- head generators go to the `Cl(1,1)` tensor factor,
- tail generators go to the recursive `Cl(n,n)` tensor factor,
- normalized null head modes inherit that factorization exactly.

Authority note:

- this bridge is downstream of the split-tower owner `ClNN`,
- it does not upgrade the split tower into the corrected phase-space owner,
- the corrected phase-space lane is governed separately by
  `NeutralPhaseSpaceCore` and its adjacent bridge files.
-/

namespace InfoGeometry.Canonical.ClNNBottBridge

open InfoGeometry.Clifford.ClNN
open BottPeriodicity
open InfoGeometry.CliffordTower

@[rep_depth krein] theorem bottStep_headPair
    (n : ℕ) (x : ℝ × ℝ) :
    bottStepEquiv n (CliffordAlgebra.ι (Quad (n + 1)) (headPair n x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x) ᵍ⊗ₜ
          (1 : CliffordAlgebra (Qsplit n)) := by
  change bottGeneratorInjection n (x, (0 : SplitSpace n))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x) ᵍ⊗ₜ
          (1 : CliffordAlgebra (Qsplit n))
  rw [bottGeneratorInjection_apply]
  have hzero : CliffordAlgebra.ι (Qsplit n) (0 : SplitSpace n) = 0 := by
    exact LinearMap.map_zero (CliffordAlgebra.ι (Qsplit n))
  rw [hzero]
  simp

@[rep_depth krein] theorem bottStep_tailLift
    (n : ℕ) (xs : Carrier n) :
    bottStepEquiv n (CliffordAlgebra.ι (Quad (n + 1)) (tailLift n xs))
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11) ᵍ⊗ₜ
          (CliffordAlgebra.ι (Qsplit n) xs) := by
  change bottGeneratorInjection n ((0 : ℝ × ℝ), xs)
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11) ᵍ⊗ₜ
          (CliffordAlgebra.ι (Qsplit n) xs)
  rw [bottGeneratorInjection_apply]
  have hzero : CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0 : ℝ × ℝ) = 0 := by
    exact LinearMap.map_zero (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11)
  rw [hzero]
  simp

@[rep_depth krein] theorem bottStep_headNullMinus
    (n : ℕ) :
    bottStepEquiv n (gammaHeadNullMinus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  simpa [gammaHeadNullMinus, headNullMinus, headPair] using
    bottStep_headPair n ((1 / 2 : ℝ), (1 / 2 : ℝ))

@[rep_depth krein] theorem bottStep_headNullPlus
    (n : ℕ) :
    bottStepEquiv n (gammaHeadNullPlus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ))))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  simpa [gammaHeadNullPlus, headNullPlus, headPair] using
    bottStep_headPair n ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))

end InfoGeometry.Canonical.ClNNBottBridge
