import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Quantum.ComplexKramersAntiunitary

/-! Two-boundary matrix coefficients on the existing associative Zorn shell. -/
noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn

open scoped BigOperators Matrix
open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

def matVec (M : Mat2C) (v : H2) : H2 :=
  fun i => ∑ j : Fin 2, M i j * v j

@[simp] theorem matVec_add (M N : Mat2C) (v : H2) :
    matVec (M + N) v = matVec M v + matVec N v := by
  funext i
  simp [matVec]
  ring

structure BoundaryPair where
  pre : H2
  post : H2
  overlap_ne_zero : standardInner post pre ≠ 0

namespace BoundaryPair

variable (B : BoundaryPair)

def overlap : ℂ := standardInner B.post B.pre

def matrixCoefficient (M : Mat2C) : ℂ :=
  standardInner B.post (matVec M B.pre)

def weakValue (M : Mat2C) : ℂ := B.matrixCoefficient M / B.overlap

@[simp] theorem overlap_ne : B.overlap ≠ 0 := B.overlap_ne_zero

@[simp] theorem matrixCoefficient_add (M N : Mat2C) :
    B.matrixCoefficient (M + N) =
      B.matrixCoefficient M + B.matrixCoefficient N := by
  simp [matrixCoefficient, matVec, standardInner, Finset.sum_add_distrib]
  ring

@[simp] theorem weakValue_add (M N : Mat2C) :
    B.weakValue (M + N) = B.weakValue M + B.weakValue N := by
  simp [weakValue, add_div, matrixCoefficient_add]

@[ext] structure ZornReadout where
  forwardWave : ℂ
  backwardWave : ℂ
  leftToRight : ℂ
  rightToLeft : ℂ

def readout (Z : ZornBlock Mat2C) : ZornReadout :=
  ⟨B.weakValue Z.n_plus_op, B.weakValue Z.n_minus_op,
    B.weakValue Z.sigma_plus_op, B.weakValue Z.sigma_minus_op⟩

end BoundaryPair
end InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn
