import InfoGeometry.Optics.Cl11SplitQuaternionConjugationSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

/-!
# Operator-valued `Cl(1,1)` conjugation and norm

This module closes the finite representation chain on the doubled internal
carrier `Fin 2 → W`.  The real split-quaternion matrix representation is
extended entrywise to `Endℂ(W)`, then realized faithfully as an endomorphism of
the doubled carrier.  Multiplication by the Clifford-conjugate operator is
proved to be the original `(2,2)` norm acting diagonally on `W`.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev Doubled (W : Type*) := Fin 2 → W
abbrev DoubledEnd (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Module.End ℂ (Doubled W)

/-- Entrywise scalar extension preserves real matrix multiplication. -/
theorem complexifyMatrix_mul
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    complexifyMatrix (W := W) (A * B) =
      complexifyMatrix (W := W) A * complexifyMatrix (W := W) B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      map_add, map_mul]

/-- Entrywise scalar extension preserves the identity matrix. -/
@[simp] theorem complexifyMatrix_one :
    complexifyMatrix (W := W) (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyMatrix]

/-- The operator realization of a coordinate `Cl(1,1)` element. -/
def operatorCl11 (q : Cl11) : DoubledEnd W :=
  matrixAction (complexifyMatrix (W := W) (cl11SplitQuaternionMatrix q))

/-- The coordinate product is represented by composition of doubled-carrier
operators. -/
@[simp] theorem operatorCl11_mul (q r : Cl11) :
    operatorCl11 (W := W) (q * r) =
      operatorCl11 (W := W) q * operatorCl11 (W := W) r := by
  unfold operatorCl11
  rw [cl11SplitQuaternionMatrix_mul, complexifyMatrix_mul,
    matrixAction_mul_end]

/-- Scalar `Cl(1,1)` coordinates act diagonally on the doubled internal
carrier. -/
@[simp] theorem operatorCl11_scalarEmbed_apply
    (a : ℝ) (ψ : Doubled W) (i : Fin 2) :
    operatorCl11 (W := W) (scalarEmbed a) ψ i = (a : ℂ) • ψ i := by
  fin_cases i <;>
    simp [operatorCl11, scalarEmbed, cl11SplitQuaternionMatrix,
      InfoGeometry.Algebra.SplitQuaternionMatrices.splitQ_eq_matrix,
      matrixAction_apply, complexifyMatrix, Fin.sum_univ_two]

/-- Clifford conjugation in coordinates is the matrix-adjugate operator
channel after scalar extension. -/
theorem operatorCl11_cliffordConjugate (q : Cl11) :
    operatorCl11 (W := W) (cliffordConjugate q) =
      matrixAction
        (complexifyMatrix (W := W)
          (splitQuaternionMatrixConjugate (cl11SplitQuaternionMatrix q))) := by
  unfold operatorCl11
  rw [cl11SplitQuaternionMatrix_cliffordConjugate]

/-- The operator representation multiplied by its Clifford-conjugate channel
is the split norm represented as a scalar doubled-carrier operator. -/
theorem operatorCl11_mul_cliffordConjugate (q : Cl11) :
    operatorCl11 (W := W) q *
        operatorCl11 (W := W) (cliffordConjugate q) =
      operatorCl11 (W := W) (scalarEmbed (splitNorm q)) := by
  rw [← operatorCl11_mul, mul_cliffordConjugate]

/-- Pointwise form of the operator norm identity on an arbitrary internal
carrier `W`. -/
theorem operatorCl11_mul_cliffordConjugate_apply
    (q : Cl11) (ψ : Doubled W) (i : Fin 2) :
    (operatorCl11 (W := W) q *
        operatorCl11 (W := W) (cliffordConjugate q)) ψ i =
      (splitNorm q : ℂ) • ψ i := by
  rw [operatorCl11_mul_cliffordConjugate,
    operatorCl11_scalarEmbed_apply]

/-- The operator-level adjugate and norm packet, expressed both structurally
and on vectors of the doubled internal carrier. -/
theorem operator_conjugation_norm_packet (q : Cl11) :
    operatorCl11 (W := W) (cliffordConjugate q) =
        matrixAction
          (complexifyMatrix (W := W)
            (splitQuaternionMatrixConjugate (cl11SplitQuaternionMatrix q))) ∧
      operatorCl11 (W := W) q *
          operatorCl11 (W := W) (cliffordConjugate q) =
        operatorCl11 (W := W) (scalarEmbed (splitNorm q)) ∧
      ∀ (ψ : Doubled W) (i : Fin 2),
        (operatorCl11 (W := W) q *
            operatorCl11 (W := W) (cliffordConjugate q)) ψ i =
          (splitNorm q : ℂ) • ψ i := by
  exact ⟨operatorCl11_cliffordConjugate q,
    operatorCl11_mul_cliffordConjugate q,
    operatorCl11_mul_cliffordConjugate_apply q⟩

/-- Public QGT-soldering form of the Clifford norm identity. -/
theorem QGTSoldering_cl11_mul_cliffordConjugate (q : Cl11) :
    InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) q) *
        InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) (cliffordConjugate q)) =
      operatorCl11 (W := W) (scalarEmbed (splitNorm q)) := by
  rw [QGTSoldering_cl11QGTFourVector,
    QGTSoldering_cl11QGTFourVector]
  exact operatorCl11_mul_cliffordConjugate q

/-- On every internal state, the QGT soldering/Clifford-conjugation pair is
exactly multiplication by the `(2,2)` causal norm. -/
theorem QGTSoldering_cl11_mul_cliffordConjugate_apply
    (q : Cl11) (ψ : Doubled W) (i : Fin 2) :
    (InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) q) *
        InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) (cliffordConjugate q))) ψ i =
      (splitNorm q : ℂ) • ψ i := by
  rw [QGTSoldering_cl11_mul_cliffordConjugate,
    operatorCl11_scalarEmbed_apply]

/-- On a nontrivial internal carrier, the causal null cone is exactly the
vanishing locus of the QGT soldering operator multiplied by its
Clifford-conjugate channel. -/
theorem QGTSoldering_cl11_conjugateProduct_eq_zero_iff
    [Nontrivial W] (q : Cl11) :
    InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) q) *
        InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) (cliffordConjugate q)) = 0 ↔
      splitNorm q = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    let ψ : Doubled W := Pi.single 0 x
    have heval := congrArg
      (fun T : DoubledEnd W => T ψ 0) h
    change
      (InfoGeometry.Unified.QGTSoldering
            (cl11QGTFourVector (W := W) q) *
          InfoGeometry.Unified.QGTSoldering
            (cl11QGTFourVector (W := W) (cliffordConjugate q))) ψ 0 = 0
      at heval
    rw [QGTSoldering_cl11_mul_cliffordConjugate_apply] at heval
    simp [ψ] at heval
    exact heval.resolve_right hx
  · intro h
    apply LinearMap.ext
    intro ψ
    funext i
    rw [QGTSoldering_cl11_mul_cliffordConjugate_apply]
    simp [h]

/-- Equivalent non-null formulation: nonzero split norm is detected by a
nonzero conjugate-product operator on every nontrivial internal carrier. -/
theorem QGTSoldering_cl11_conjugateProduct_ne_zero_iff
    [Nontrivial W] (q : Cl11) :
    InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) q) *
        InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) (cliffordConjugate q)) ≠ 0 ↔
      splitNorm q ≠ 0 := by
  exact not_congr (QGTSoldering_cl11_conjugateProduct_eq_zero_iff q)

/-! ## Non-null unit packet -/

/-- Clifford conjugation preserves the split norm. -/
@[simp] theorem splitNorm_cliffordConjugate (q : Cl11) :
    splitNorm (cliffordConjugate q) = splitNorm q := by
  simp [splitNorm, cliffordConjugate_apply]

/-- The conjugate product gives the same scalar norm in the reverse order. -/
theorem cliffordConjugate_mul_self (q : Cl11) :
    cliffordConjugate q * q = scalarEmbed (splitNorm q) := by
  have h := mul_cliffordConjugate (cliffordConjugate q)
  rw [cliffordConjugate_involutive, splitNorm_cliffordConjugate] at h
  exact h

/-- Reverse-order operator norm identity. -/
theorem operatorCl11_cliffordConjugate_mul (q : Cl11) :
    operatorCl11 (W := W) (cliffordConjugate q) *
        operatorCl11 (W := W) q =
      operatorCl11 (W := W) (scalarEmbed (splitNorm q)) := by
  rw [← operatorCl11_mul, cliffordConjugate_mul_self]

/-- Explicit inverse candidate in the non-null operator sector. -/
def operatorCl11InverseCandidate (q : Cl11) : DoubledEnd W :=
  ((splitNorm q : ℂ)⁻¹) • operatorCl11 (W := W) (cliffordConjugate q)

theorem operatorCl11_mul_inverseCandidate
    (q : Cl11) (hq : splitNorm q ≠ 0) :
    operatorCl11 (W := W) q * operatorCl11InverseCandidate (W := W) q = 1 := by
  have hc : (splitNorm q : ℂ) ≠ 0 := by
    exact_mod_cast hq
  rw [operatorCl11InverseCandidate, mul_smul_comm,
    operatorCl11_mul_cliffordConjugate]
  apply LinearMap.ext
  intro ψ
  funext i
  change (splitNorm q : ℂ)⁻¹ •
      operatorCl11 (W := W) (scalarEmbed (splitNorm q)) ψ i = ψ i
  rw [operatorCl11_scalarEmbed_apply]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem operatorCl11_inverseCandidate_mul
    (q : Cl11) (hq : splitNorm q ≠ 0) :
    operatorCl11InverseCandidate (W := W) q * operatorCl11 (W := W) q = 1 := by
  have hc : (splitNorm q : ℂ) ≠ 0 := by
    exact_mod_cast hq
  rw [operatorCl11InverseCandidate, smul_mul_assoc,
    operatorCl11_cliffordConjugate_mul]
  apply LinearMap.ext
  intro ψ
  funext i
  change (splitNorm q : ℂ)⁻¹ •
      operatorCl11 (W := W) (scalarEmbed (splitNorm q)) ψ i = ψ i
  rw [operatorCl11_scalarEmbed_apply]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Every non-null `Cl(1,1)` coordinate gives an actual unit of the
doubled-carrier endomorphism algebra. -/
def operatorCl11Unit (q : Cl11) (hq : splitNorm q ≠ 0) :
    (DoubledEnd W)ˣ where
  val := operatorCl11 (W := W) q
  inv := operatorCl11InverseCandidate (W := W) q
  val_inv := operatorCl11_mul_inverseCandidate q hq
  inv_val := operatorCl11_inverseCandidate_mul q hq

@[simp] theorem operatorCl11Unit_val
    (q : Cl11) (hq : splitNorm q ≠ 0) :
    (operatorCl11Unit (W := W) q hq : DoubledEnd W) = operatorCl11 (W := W) q :=
  rfl

theorem isUnit_operatorCl11_of_splitNorm_ne_zero
    (q : Cl11) (hq : splitNorm q ≠ 0) :
    IsUnit (operatorCl11 (W := W) q) := by
  exact ⟨operatorCl11Unit (W := W) q hq, rfl⟩

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
