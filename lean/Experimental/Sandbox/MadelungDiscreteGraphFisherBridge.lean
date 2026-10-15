import Mathlib.Tactic
import InfoGeometry.Topology.EckmannDiscreteHodge
import InfoGeometry.Physics.MadelungZornFisherReadout

/-!
# Finite incidence-matrix variation of amplitude energy

For a finite matrix `B` (in particular, an incidence matrix), this file
computes the exact variation of its amplitude Dirichlet energy and identifies
the linear coefficient with the quadratic-form pairing for `BᵀB`. This is a
finite algebraic statement. It does not assert a continuum functional
derivative or identify the resulting Laplacian with a physical Bohm potential.
-/

open scoped BigOperators

namespace InfoGeometry.Experimental.Sandbox.MadelungDiscreteGraphFisher

open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Physics.MadelungZornFisherReadout

noncomputable section

variable {nV nE : ℕ}

/-- Matrix gradient of a finite vertex vector. For incidence matrices, its
coordinates are the edge differences. -/
def graphGradient (B : Matrix (Fin nE) (Fin nV) ℝ) (f : Fin nV → ℝ) :
    Fin nE → ℝ := B.mulVec f

/-- Four times the Dirichlet energy of the matrix gradient. -/
def graphAmplitudeEnergy (B : Matrix (Fin nE) (Fin nV) ℝ)
    (f : Fin nV → ℝ) : ℝ :=
  4 * eckmannDot (graphGradient B f) (graphGradient B f)

/-- The exact quadratic path obtained by varying the edge gradient affinely.
The vertex-space path is represented by the incidence-linear gradient
`Bf + t Bg`. -/
def graphAmplitudeEnergyAlong (B : Matrix (Fin nE) (Fin nV) ℝ)
    (f g : Fin nV → ℝ) (t : ℝ) : ℝ :=
  fisherEnergyAlong (graphGradient B f) (graphGradient B g) t

/-- The linear coefficient of the exact finite graph-energy variation. -/
def graphAmplitudeVariationCoefficient (B : Matrix (Fin nE) (Fin nV) ℝ)
    (f g : Fin nV → ℝ) : ℝ :=
  fisherVariationCoefficient (graphGradient B f) (graphGradient B g)

/-- Exact quadratic variation of graph amplitude energy along a direction. -/
theorem graphAmplitudeEnergyAlong_variation
    (B : Matrix (Fin nE) (Fin nV) ℝ) (f g : Fin nV → ℝ) (t : ℝ) :
    graphAmplitudeEnergyAlong B f g t -
        graphAmplitudeEnergyAlong B f g 0 =
      t * graphAmplitudeVariationCoefficient B f g +
        t ^ 2 * (4 * eckmannDot (graphGradient B g) (graphGradient B g)) := by
  change fisherEnergyAlong (B.mulVec f) (B.mulVec g) t -
      fisherEnergyAlong (B.mulVec f) (B.mulVec g) 0 =
    t * fisherVariationCoefficient (B.mulVec f) (B.mulVec g) +
      t ^ 2 * (4 * eckmannDot (B.mulVec g) (B.mulVec g))
  simpa [fisherEnergyAlong, fisherVariationCoefficient, eckmannDot, pow_two] using
    (InfoGeometry.Physics.MadelungZornFisherReadout.fisherEnergyAlong_variation
      (B.mulVec f) (B.mulVec g) t)

/-- The graph-gradient path is induced by the affine vertex path, by
linearity of matrix-vector multiplication. -/
theorem graphGradient_affine
    (B : Matrix (Fin nE) (Fin nV) ℝ) (f g : Fin nV → ℝ) (t : ℝ) :
    graphGradient B (f + fun v => t * g v) =
      graphGradient B f + fun e => t * graphGradient B g e := by
  funext e
  change (∑ v, B e v * (f v + t * g v)) =
    (∑ v, B e v * f v) + t * (∑ v, B e v * g v)
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ v, B e v * (t * g v)) =
        ∑ v, t * (B e v * g v) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = t * ∑ v, B e v * g v := by rw [Finset.mul_sum]

/-- Finite summation by parts is derived from the matrix transpose: the first
variation pairs the vertex vector with the normal operator `BᵀB`, with no
summation-by-parts premise. -/
theorem graphAmplitudeVariation_eq_nodeLaplacian_pairing
    (B : Matrix (Fin nE) (Fin nV) ℝ) (f g : Fin nV → ℝ) :
    graphAmplitudeVariationCoefficient B f g =
      8 * eckmannDot f ((B.transpose * B).mulVec g) := by
  change 8 * eckmannDot (B.mulVec f) (B.mulVec g) =
    8 * eckmannDot f ((B.transpose * B).mulVec g)
  congr 1
  calc
    eckmannDot (B.mulVec f) (B.mulVec g) =
        eckmannDot f (B.transpose.mulVec (B.mulVec g)) := by
          symm
          exact eckmannDot_mulVec_transpose B (B.mulVec g) f
    _ = eckmannDot f ((B.transpose * B).mulVec g) := by
          rw [← Matrix.mulVec_mulVec]

/-- The graph amplitude energy is nonnegative, and it vanishes exactly when
the matrix gradient is zero. For an arbitrary rectangular matrix this is the
kernel of `B`; graph connectivity is not assumed. -/
theorem graphAmplitudeEnergy_zero_iff
    (B : Matrix (Fin nE) (Fin nV) ℝ) (f : Fin nV → ℝ) :
    graphAmplitudeEnergy B f = 0 ↔ graphGradient B f = 0 := by
  unfold graphAmplitudeEnergy
  constructor
  · intro h
    have hdot : eckmannDot (graphGradient B f) (graphGradient B f) = 0 := by
      nlinarith
    exact eckmannDot_self_eq_zero hdot
  · intro h
    rw [h]
    simp [eckmannDot]

theorem graphAmplitudeEnergy_nonneg
    (B : Matrix (Fin nE) (Fin nV) ℝ) (f : Fin nV → ℝ) :
    0 ≤ graphAmplitudeEnergy B f := by
  unfold graphAmplitudeEnergy
  exact mul_nonneg (by norm_num) (eckmannDot_self_nonneg _)

end

end InfoGeometry.Experimental.Sandbox.MadelungDiscreteGraphFisher
