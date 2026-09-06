import Mathlib.Tactic
import InfoGeometry.Canonical.ZornBdGDerivationBridge
import InfoGeometry.Canonical.PhysicalBdGPairingBridge
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-!
# Zorn-native BdG compatibility

This owner closes the finite-dimensional typed bridge between the existing
complex Zorn readout and the repository's native bounded BdG operator.

It deliberately does not assert that the Zorn readout is an algebra
homomorphism.  The source remains the nonassociative Zorn carrier; only its
four selected 2x2 blocks are transported into bounded operators.

The three source predicates are kept separate:

* `IsBdGCompatible`: the lower blocks are the adjoint/negative-adjoint blocks
  required by the BdG pattern;
* `IsHermitianNormalChannel`: the scalar normal block is Hermitian;
* `IsFermionicPairing`: the Pauli pairing matrix is transpose-skew.

The native antiunitary PHS theorem is transported from
`PhysicalBdGPairingBridge` under its four explicit intertwining hypotheses.
A future coordinate-conjugation owner may discharge those hypotheses from the
fermionic skew condition; this file does not identify the algebraic Zorn
`zornStar` with Hilbert-space charge conjugation.
-/

noncomputable section

open Matrix
open ContinuousLinearMap

namespace InfoGeometry.Canonical.ZornNativeBdGCompatibility

open ZornBdGDerivationBridge.PauliSolderedCrossProductBridge
open ZornBdGDerivationBridge.ZornVectorMatrixAlgebra
open ZornBdGDerivationBridge.ZornBdGSolderingReadout
open ZornBdGDerivationBridge.G2BdGOrbit

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

abbrev ZornC := Zorn ℂ
abbrev SpinH := FinKetSpace (Fin 2)
abbrev EndSpin := SpinH →L[ℂ] SpinH
abbrev NambuSpin := WithLp 2 (SpinH × SpinH)
abbrev EndNambuSpin := NambuSpin →L[ℂ] NambuSpin

/-! ## 1. Pauli adjoint and transpose calculus -/

/-- Conjugate transpose of the Pauli soldering is coefficientwise complex
conjugation because all three Pauli matrices are Hermitian. -/
theorem sigmaVec_conjTranspose (u : Fin 3 → ℂ) :
    (sigmaVec u)ᴴ = sigmaVec (fun i => star (u i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaVec, Matrix.conjTranspose_apply] <;> ring

/-- Transpose flips exactly the sigma_2 coordinate. -/
theorem sigmaVec_transpose_formula (u : Fin 3 → ℂ) :
    Matrix.transpose (sigmaVec u) = sigmaVec ![u 0, -u 1, u 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaVec] <;> ring

/-- The Pauli soldering is transpose-skew exactly on the sigma_2 channel. -/
theorem sigmaVec_transpose_eq_neg_iff (u : Fin 3 → ℂ) :
    Matrix.transpose (sigmaVec u) = -sigmaVec u ↔
      u 0 = 0 ∧ u 2 = 0 := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [sigmaVec] at h01 h00
    constructor
    · linear_combination (1 / 2 : ℂ) * h01
    · linear_combination (1 / 2 : ℂ) * h00
  · rintro ⟨h0, h2⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigmaVec, h0, h2] <;> ring

/-! ## 2. Source-side physical compatibility predicates -/

/-- The generic Zorn readout has the BdG block pattern precisely when the
lower scalar/vector coordinates are the required conjugates of the upper
coordinates.  This does not assert self-adjointness of the resulting operator. -/
def IsBdGCompatible (Z : ZornC) : Prop :=
  Z.b = -star Z.a ∧ ∀ i, Z.v i = star (Z.u i)

/-- Hermiticity of the scalar normal block. -/
def IsHermitianNormalChannel (Z : ZornC) : Prop :=
  star Z.a = Z.a

/-- Fermionic skew condition stated structurally at matrix level. -/
def IsFermionicPairing (Z : ZornC) : Prop :=
  Matrix.transpose (sigmaVec Z.u) = -sigmaVec Z.u

/-- Coordinate characterization of the structural fermionic condition. -/
theorem isFermionicPairing_iff (Z : ZornC) :
    IsFermionicPairing Z ↔ Z.u 0 = 0 ∧ Z.u 2 = 0 := by
  exact sigmaVec_transpose_eq_neg_iff Z.u

/-- The constrained source subtype used for a self-adjoint BdG Hamiltonian
with a canonical transpose-skew pairing channel. -/
def IsPhysicalBdGZorn (Z : ZornC) : Prop :=
  IsBdGCompatible Z ∧
  IsHermitianNormalChannel Z ∧
  IsFermionicPairing Z

/-! ## 3. Matrix-to-bounded-operator transport -/

noncomputable def rhoNormal (Z : ZornC) : EndSpin :=
  CblinfunMatrix.matrixOp (block11 (bdgReadout Z))

noncomputable def rhoPairing (Z : ZornC) : EndSpin :=
  CblinfunMatrix.matrixOp (block12 (bdgReadout Z))

noncomputable def rhoLowerPairing (Z : ZornC) : EndSpin :=
  CblinfunMatrix.matrixOp (block21 (bdgReadout Z))

noncomputable def rhoHole (Z : ZornC) : EndSpin :=
  CblinfunMatrix.matrixOp (block22 (bdgReadout Z))

/-- Native bounded Nambu readout using the actual four Zorn-derived blocks. -/
noncomputable def rhoBdG (Z : ZornC) : EndNambuSpin :=
  PhysicalBdGPairingBridge.blockOperator
    (rhoNormal Z) (rhoPairing Z) (rhoLowerPairing Z) (rhoHole Z)

@[simp]
theorem matrixOfOp_neg (T : EndSpin) :
    CblinfunMatrix.matrixOfOp (-T) =
      -CblinfunMatrix.matrixOfOp T := by
  simp [CblinfunMatrix.matrixOfOp]

/-- BdG compatibility turns the lower Zorn pairing block into the native
operator adjoint of the upper pairing block. -/
theorem zorn_pairing_adjoint
    (Z : ZornC) (hZ : IsBdGCompatible Z) :
    rhoLowerPairing Z = ContinuousLinearMap.adjoint (rhoPairing Z) := by
  apply CblinfunMatrix.matrixOfOp_injective
  simp only [rhoLowerPairing, rhoPairing]
  rw [CblinfunMatrix.matrixOfOp_matrixOp]
  rw [CblinfunMatrix.matrixOfOp_adjoint]
  rw [CblinfunMatrix.matrixOfOp_matrixOp]
  rw [bdgReadout_block21_eq_sigmaVec, bdgReadout_block12_eq_sigmaVec]
  rw [sigmaVec_conjTranspose]
  exact congrArg sigmaVec (funext hZ.2)

/-- BdG compatibility turns the lower diagonal Zorn block into minus the
adjoint of the upper diagonal block. -/
theorem zorn_hole_eq_negative_adjoint
    (Z : ZornC) (hZ : IsBdGCompatible Z) :
    rhoHole Z = -ContinuousLinearMap.adjoint (rhoNormal Z) := by
  apply CblinfunMatrix.matrixOfOp_injective
  simp only [rhoHole, rhoNormal]
  rw [CblinfunMatrix.matrixOfOp_matrixOp]
  rw [matrixOfOp_neg, CblinfunMatrix.matrixOfOp_adjoint]
  rw [CblinfunMatrix.matrixOfOp_matrixOp]
  have hd := bdgReadout_diagonal_blocks Z
  rw [hd.2, hd.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hZ.1, Matrix.conjTranspose_apply]

/-- Hermiticity of the scalar Zorn normal channel becomes native operator
self-adjointness. -/
theorem rhoNormal_selfAdjoint
    (Z : ZornC) (hZ : IsHermitianNormalChannel Z) :
    ContinuousLinearMap.adjoint (rhoNormal Z) = rhoNormal Z := by
  apply CblinfunMatrix.matrixOfOp_injective
  simp only [rhoNormal]
  rw [CblinfunMatrix.matrixOfOp_adjoint]
  have hd := bdgReadout_diagonal_blocks Z
  rw [hd.1]
  have hZa : (starRingEnd ℂ) Z.a = Z.a := by
    simpa only [starRingEnd_apply] using hZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.conjTranspose_apply]; simp [hZa])

/-- The actual closure theorem from the Zorn block readout to the repository's
native bounded BdG Hamiltonian. -/
theorem rhoBdG_eq_native_H_BdG
    (Z : ZornC) (hZ : IsBdGCompatible Z) :
    rhoBdG Z =
      PhysicalBdGPairingBridge.H_BdG (rhoNormal Z) (rhoPairing Z) := by
  simp [rhoBdG, PhysicalBdGPairingBridge.H_BdG,
    PhysicalBdGPairingBridge.holeBlock,
    zorn_pairing_adjoint Z hZ,
    zorn_hole_eq_negative_adjoint Z hZ]

/-- Self-adjointness is a separate strengthening: the BdG block pattern alone
is insufficient; the normal channel must also be Hermitian. -/
theorem rhoBdG_selfAdjoint
    (Z : ZornC)
    (hZ : IsBdGCompatible Z)
    (hHerm : IsHermitianNormalChannel Z) :
    IsSelfAdjoint (rhoBdG Z) := by
  rw [rhoBdG_eq_native_H_BdG Z hZ]
  exact PhysicalBdGPairingBridge.H_BdG_isSelfAdjoint
    (rhoNormal Z) (rhoPairing Z) (rhoNormal_selfAdjoint Z hHerm)

/-! ## 4. Transport of the existing genuine antiunitary theorem -/

/-- The repository's genuine antiunitary PHS theorem transported to the
Zorn-derived bounded BdG operator.  The four target-space intertwining laws
remain explicit hypotheses; this theorem does not identify `zornStar` with
Hilbert-space conjugation. -/
theorem zorn_bdg_antiunitary_phs_of_intertwining
    (Z : ZornC)
    (hZ : IsBdGCompatible Z)
    (R : PhysicalBdGPairingBridge.AntiunitaryRealStructure SpinH)
    (h_comm1 : ∀ v : SpinH,
      R.conjugation (ContinuousLinearMap.adjoint (rhoNormal Z) v) =
        rhoNormal Z (R.conjugation v))
    (h_anti1 : ∀ u : SpinH,
      R.conjugation (ContinuousLinearMap.adjoint (rhoPairing Z) u) =
        -rhoPairing Z (R.conjugation u))
    (h_comm2 : ∀ u : SpinH,
      R.conjugation (rhoNormal Z u) =
        ContinuousLinearMap.adjoint (rhoNormal Z) (R.conjugation u))
    (h_anti2 : ∀ v : SpinH,
      R.conjugation (rhoPairing Z v) =
        -ContinuousLinearMap.adjoint (rhoPairing Z) (R.conjugation v))
    (x : NambuSpin) :
    PhysicalBdGPairingBridge.antiunitarySheetSwap R (rhoBdG Z x) =
      -(rhoBdG Z
        (PhysicalBdGPairingBridge.antiunitarySheetSwap R x)) := by
  rw [rhoBdG_eq_native_H_BdG Z hZ]
  exact PhysicalBdGPairingBridge.bdg_antiunitary_particle_hole_symmetry
    (rhoNormal Z) (rhoPairing Z) R
    h_comm1 h_anti1 h_comm2 h_anti2 x

/-! ## 5. Real first-order tangent preservation -/

/-- BdG compatibility is a real-linear condition on the complex Zorn carrier.
It is preserved by a first-order flow only along a real parameter when both
base point and tangent lie in the compatible slice. -/
theorem bdgCompatible_firstOrderFlow
    (D : ZornC → ZornC)
    (Z : ZornC)
    (hZ : IsBdGCompatible Z)
    (hDZ : IsBdGCompatible (D Z))
    (t : ℝ) :
    IsBdGCompatible (firstOrderFlow D Z (t : ℂ)) := by
  constructor
  · change Z.b + (t : ℂ) * (D Z).b =
      -star (Z.a + (t : ℂ) * (D Z).a)
    rw [hZ.1, hDZ.1]
    simp
    ring
  · intro i
    change Z.v i + (t : ℂ) * (D Z).v i =
      star (Z.u i + (t : ℂ) * (D Z).u i)
    rw [hZ.2 i, hDZ.2 i]
    simp

/-- The transpose-skew tangent sector is preserved when both the base pairing
and its first-order variation are transpose-skew. -/
theorem fermionicPairing_firstOrderFlow
    (D : ZornC → ZornC)
    (Z : ZornC)
    (hZ : IsFermionicPairing Z)
    (hDZ : IsFermionicPairing (D Z))
    (t : ℝ) :
    IsFermionicPairing (firstOrderFlow D Z (t : ℂ)) := by
  rw [isFermionicPairing_iff] at hZ hDZ ⊢
  constructor
  · change Z.u 0 + (t : ℂ) * (D Z).u 0 = 0
    rw [hZ.1, hDZ.1]
    ring
  · change Z.u 2 + (t : ℂ) * (D Z).u 2 = 0
    rw [hZ.2, hDZ.2]
    ring

/-- Hermiticity of the scalar normal channel is likewise real-linear. -/
theorem hermitianNormal_firstOrderFlow
    (D : ZornC → ZornC)
    (Z : ZornC)
    (hZ : IsHermitianNormalChannel Z)
    (hDZ : IsHermitianNormalChannel (D Z))
    (t : ℝ) :
    IsHermitianNormalChannel (firstOrderFlow D Z (t : ℂ)) := by
  change star (Z.a + (t : ℂ) * (D Z).a) =
    Z.a + (t : ℂ) * (D Z).a
  rw [star_add, StarMul.star_mul, hZ, hDZ]
  simp [Complex.star_def, Complex.conj_ofReal, mul_comm]

/-- The full constrained physical slice is preserved by real first-order
motion whose tangent remains in the same slice. -/
theorem physicalBdG_firstOrderFlow
    (D : ZornC → ZornC)
    (Z : ZornC)
    (hZ : IsPhysicalBdGZorn Z)
    (hDZ : IsPhysicalBdGZorn (D Z))
    (t : ℝ) :
    IsPhysicalBdGZorn (firstOrderFlow D Z (t : ℂ)) := by
  exact ⟨
    bdgCompatible_firstOrderFlow D Z hZ.1 hDZ.1 t,
    hermitianNormal_firstOrderFlow D Z hZ.2.1 hDZ.2.1 t,
    fermionicPairing_firstOrderFlow D Z hZ.2.2 hDZ.2.2 t
  ⟩

end InfoGeometry.Canonical.ZornNativeBdGCompatibility

end noncomputable section
