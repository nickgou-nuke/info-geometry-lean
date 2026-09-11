import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionAlternativeLaws

noncomputable section

namespace SplitOctonion

def parabolicOperatorFlow (N : Module.End ℝ SplitOctonion) (t : ℝ) :
    Module.End ℝ SplitOctonion :=
  LinearMap.id + t • N

theorem tripotent_of_involutive_operator
    (O : Module.End ℝ SplitOctonion)
    (hO : O.comp O = LinearMap.id) :
    O.comp (O.comp O) = O := by
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun hO z
  simpa [LinearMap.comp_apply] using congrArg O hz

theorem parabolicOperatorFlow_apply
    (N : Module.End ℝ SplitOctonion) (t : ℝ) (z : SplitOctonion) :
    parabolicOperatorFlow N t z = z + t • N z := by
  rfl

theorem parabolicOperatorFlow_zero (N : Module.End ℝ SplitOctonion) :
    parabolicOperatorFlow N 0 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp only [parabolicOperatorFlow, zero_smul,
    add_zero, LinearMap.id_apply]

theorem parabolicOperatorFlow_add
    (N : Module.End ℝ SplitOctonion)
    (hN : N.comp N = 0) (s t : ℝ) :
    (parabolicOperatorFlow N s).comp (parabolicOperatorFlow N t) =
      parabolicOperatorFlow N (s + t) := by
  apply LinearMap.ext
  intro z
  have hNz := LinearMap.congr_fun hN z
  have hNzz : N (N z) = 0 := by
    simpa [LinearMap.comp_apply] using hNz
  simp only [parabolicOperatorFlow, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  change (z + t • N z) + s • N (z + t • N z) =
    z + (s + t) • N z
  rw [map_add, map_smul, hNzz, smul_zero]
  module

theorem parabolicOperatorFlow_inverse
    (N : Module.End ℝ SplitOctonion)
    (hN : N.comp N = 0) (t : ℝ) :
    (parabolicOperatorFlow N (-t)).comp (parabolicOperatorFlow N t) =
      LinearMap.id ∧
    (parabolicOperatorFlow N t).comp (parabolicOperatorFlow N (-t)) =
      LinearMap.id := by
  constructor
  · rw [parabolicOperatorFlow_add N hN, neg_add_cancel,
      parabolicOperatorFlow_zero]
  · rw [parabolicOperatorFlow_add N hN, add_neg_cancel,
      parabolicOperatorFlow_zero]

theorem leftRegular_square_zero_of_square_zero
    (n : SplitOctonion) (hn : n * n = 0) :
    (leftRegular n).comp (leftRegular n) = 0 := by
  apply LinearMap.ext
  intro z
  change n * (n * z) = 0
  rw [← left_alternative n z, hn, zero_mul]

def splitOctonionParabolicFlow (n : SplitOctonion) (t : ℝ) :
    Module.End ℝ SplitOctonion :=
  parabolicOperatorFlow (leftRegular n) t

theorem splitOctonionParabolicFlow_inverse
    (n : SplitOctonion) (hn : n * n = 0) (t : ℝ) :
    (splitOctonionParabolicFlow n (-t)).comp
        (splitOctonionParabolicFlow n t) = LinearMap.id ∧
    (splitOctonionParabolicFlow n t).comp
        (splitOctonionParabolicFlow n (-t)) = LinearMap.id := by
  exact parabolicOperatorFlow_inverse (leftRegular n)
    (leftRegular_square_zero_of_square_zero n hn) t

end SplitOctonion
