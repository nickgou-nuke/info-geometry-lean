/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveMatrixCorner
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear

/-! Compatibility with the metric-conjugated adjoint. The hypotheses
`d# = -B`, `B# = -d` are explicit; no ordinary-adjoint identification is made.
The source metric is `diag(1,-1)` and the target adjoint is the existing
Kasparov/Krein owner operation. -/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- The split metric on the represented two-dimensional matrix algebra. -/
def pairDiracMetric : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

theorem pairMatrixLinear_dirac (K : InfoGeometry.Physics.KasparovKreinData A)
    {d B : A} (hd : K.diracAdjoint d = -B) (hB : K.diracAdjoint B = -d)
    (M : Matrix (Fin 2) (Fin 2) R) :
    K.diracAdjoint (pairMatrixLinear d B M) =
      pairMatrixLinear d B (pairDiracMetric * M.conjTranspose * pairDiracMetric) := by
  have hadd (x y : A) : K.diracAdjoint (x + y) =
      K.diracAdjoint x + K.diracAdjoint y := by
    simp [InfoGeometry.Physics.KasparovKreinData.diracAdjoint, mul_add, add_mul]
  have hsmul (r : R) (x : A) : K.diracAdjoint (r • x) =
      star r • K.diracAdjoint x := by
    simp [InfoGeometry.Physics.KasparovKreinData.diracAdjoint, star_smul]
  have hp : K.diracAdjoint (d * B) = d * B := by
    rw [K.diracAdjoint_mul, hd, hB, neg_mul_neg]
  have hm : K.diracAdjoint (B * d) = B * d := by
    rw [K.diracAdjoint_mul, hd, hB, neg_mul_neg]
  simp [pairMatrixLinear_apply, pairMatrixUnit, hadd, hsmul, hp, hm, hd, hB,
    pairDiracMetric, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]
  abel

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
