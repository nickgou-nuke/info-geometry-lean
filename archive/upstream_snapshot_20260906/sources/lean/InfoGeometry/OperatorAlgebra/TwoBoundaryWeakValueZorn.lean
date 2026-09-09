import InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn
import InfoGeometry.Quantum.ComplexKramersAntiunitary

/-!
# Two-boundary matrix coefficients of an operator-Zorn block

The mathematical content of a two-state-vector readout is a pre-selected
vector, a post-selected vector, a nonzero overlap, and the normalized matrix
coefficient

`<post, A pre> / <post, pre>`.

This file applies that construction independently to the four entries of a
`2 x 2` operator-Zorn block over complex `2 x 2` matrices.  It does not infer
nonlocal transport, a Klein quotient, or a physical scattering protocol.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn

open scoped BigOperators Matrix
open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Ordinary matrix action on the canonical two-component complex carrier. -/
def matVec (M : Mat2C) (v : H2) : H2 :=
  fun i => ∑ j : Fin 2, M i j * v j

@[simp] theorem matVec_zero (v : H2) :
    matVec 0 v = 0 := by
  funext i
  simp [matVec]

@[simp] theorem matVec_add (M N : Mat2C) (v : H2) :
    matVec (M + N) v = matVec M v + matVec N v := by
  funext i
  simp [matVec, add_mul, Finset.sum_add_distrib]

@[simp] theorem matVec_neg (M : Mat2C) (v : H2) :
    matVec (-M) v = -matVec M v := by
  funext i
  simp [matVec]

/-- Pre/post boundary pair with nonzero transition amplitude. -/
structure BoundaryPair where
  pre : H2
  post : H2
  overlap_ne_zero : standardInner post pre ≠ 0

namespace BoundaryPair

variable (B : BoundaryPair)

/-- Transition amplitude. -/
def overlap : ℂ :=
  standardInner B.post B.pre

/-- Unnormalized matrix coefficient. -/
def matrixCoefficient (M : Mat2C) : ℂ :=
  standardInner B.post (matVec M B.pre)

/-- Normalized two-boundary matrix coefficient. -/
def weakValue (M : Mat2C) : ℂ :=
  B.matrixCoefficient M / B.overlap

@[simp] theorem overlap_ne : B.overlap ≠ 0 := by
  exact B.overlap_ne_zero

@[simp] theorem matrixCoefficient_zero :
    B.matrixCoefficient 0 = 0 := by
  simp [matrixCoefficient]

@[simp] theorem matrixCoefficient_add (M N : Mat2C) :
    B.matrixCoefficient (M + N) =
      B.matrixCoefficient M + B.matrixCoefficient N := by
  simp [matrixCoefficient, standardInner]
  ring

@[simp] theorem matrixCoefficient_neg (M : Mat2C) :
    B.matrixCoefficient (-M) = -B.matrixCoefficient M := by
  simp [matrixCoefficient, standardInner]
  ring

@[simp] theorem weakValue_zero : B.weakValue 0 = 0 := by
  simp [weakValue]

@[simp] theorem weakValue_add (M N : Mat2C) :
    B.weakValue (M + N) = B.weakValue M + B.weakValue N := by
  simp [weakValue, add_div]

@[simp] theorem weakValue_neg (M : Mat2C) :
    B.weakValue (-M) = -B.weakValue M := by
  simp [weakValue]

/-- Four normalized matrix coefficients associated with one outer Zorn block. -/
@[ext]
structure ZornReadout where
  forwardWave : ℂ
  backwardWave : ℂ
  leftToRight : ℂ
  rightToLeft : ℂ

/-- Read all four blocks against the same boundary pair. -/
def readout (Z : ZornBlock Mat2C) : ZornReadout :=
  ⟨B.weakValue Z.n_plus_op,
    B.weakValue Z.n_minus_op,
    B.weakValue Z.sigma_plus_op,
    B.weakValue Z.sigma_minus_op⟩

/-- Cartan polarization fixes the two diagonal wave readouts and negates the
chiral channel readouts. -/
theorem readout_cartanInvolution (Z : ZornBlock Mat2C) :
    B.readout (cartanInvolution Z) =
      { forwardWave := (B.readout Z).forwardWave
        backwardWave := (B.readout Z).backwardWave
        leftToRight := -(B.readout Z).leftToRight
        rightToLeft := -(B.readout Z).rightToLeft } := by
  rw [cartanInvolution_coordinates]
  apply ZornReadout.ext <;> simp [readout]

/-- Sheet exchange swaps the two boundary waves and the two directed channel
readouts. -/
theorem readout_sheetExchange (Z : ZornBlock Mat2C) :
    B.readout (sheetExchange * Z * sheetExchange) =
      { forwardWave := (B.readout Z).backwardWave
        backwardWave := (B.readout Z).forwardWave
        leftToRight := (B.readout Z).rightToLeft
        rightToLeft := (B.readout Z).leftToRight } := by
  rw [sheetExchange_conjugates]
  rfl

end BoundaryPair

end InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn
