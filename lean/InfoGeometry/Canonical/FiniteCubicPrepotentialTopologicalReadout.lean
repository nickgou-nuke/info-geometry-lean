import InfoGeometry.Canonical.FiniteWDVVTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.GaugeQuotient

/-!
# Finite cubic prepotentials and their projective gauge readout

This file formalizes a finite cubic polynomial on a coordinate space.  The
coefficient ray is projective and therefore invariant under nonzero scalar
gauge rescaling.  It does not identify the polynomial with a geometric
Frobenius prepotential or define an enumerative Gromov--Witten invariant.
-/

namespace InfoGeometry.Canonical

open scoped BigOperators
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev CubicCoefficient (dim : ℕ) :=
  Fin dim → Fin dim → Fin dim → ℝ

def cubicPrepotential {dim : ℕ}
    (c : CubicCoefficient dim) (x : Fin dim → ℝ) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ i : Fin dim, ∑ j : Fin dim, ∑ k : Fin dim,
      c i j k * x i * x j * x k

theorem cubicPrepotential_zero {dim : ℕ}
    (c : CubicCoefficient dim) :
    cubicPrepotential c 0 = 0 := by
  simp [cubicPrepotential]

theorem continuous_cubicPrepotential {dim : ℕ}
    (c : CubicCoefficient dim) :
    Continuous (cubicPrepotential c) := by
  unfold cubicPrepotential
  fun_prop

theorem cubicPrepotential_eq_finite_cubic_sum {dim : ℕ}
    (c : CubicCoefficient dim) (x : Fin dim → ℝ) :
    cubicPrepotential c x =
      (1 / 6 : ℝ) *
        ∑ i : Fin dim, ∑ j : Fin dim, ∑ k : Fin dim,
          c i j k * x i * x j * x k :=
  rfl

def cubicCoefficientRay {dim : ℕ}
    (c : InfoGeometry.Projective.Unnormalized
      (V := CubicCoefficient dim)) :
    ℙ ℝ (CubicCoefficient dim) :=
  InfoGeometry.Projective.ray c

theorem cubicCoefficientRay_smul {dim : ℕ}
    (a : ℝˣ)
    (c : InfoGeometry.Projective.Unnormalized
      (V := CubicCoefficient dim)) :
    cubicCoefficientRay
        ⟨a • c.1, smul_ne_zero (Units.ne_zero a) c.2⟩ =
      cubicCoefficientRay c := by
  exact InfoGeometry.Projective.ray_smul a c

end
end InfoGeometry.Canonical
