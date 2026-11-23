/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.DeWittMatrixForm
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# DeWitt form with finite operator-matrix coefficients

The coefficient algebra here is the full noncommutative operator ring
`Matrix (Fin r) (Fin r) ℝ`.  A spacetime-symmetric perturbation is therefore
a matrix whose entries are operators, not a scalar diagonal ansatz.  The
real-valued pairing is the Hilbert--Schmidt amplification of the existing
DeWitt pairing: it sums that pairing over every ordered operator-matrix
coefficient `(a,b)`, including off-diagonal operator entries.

This file proves the exact slice formula, Sylvester signature, and positivity
on the coefficientwise anisotropic subspace.  The form is real-valued because
signature and positivity are properties of a real quadratic form; its vectors
remain full operator-valued spacetime matrices.
-/

noncomputable section

namespace InfoGeometry.Geometry.OperatorDeWittAmplification

open Matrix
open InfoGeometry.Geometry.DeWittMatrixForm

/-- Full operator-matrix coefficient ring at operator dimension `r`. -/
abbrev OperatorCoeff (r : ℕ) := Matrix (Fin r) (Fin r) ℝ

/-- Spacetime-symmetric perturbations with full operator-matrix entries. -/
def OperatorPerturbation (D r : ℕ) :
    Submodule ℝ (Matrix (Fin D) (Fin D) (OperatorCoeff r)) where
  carrier := {h | h.IsSymm}
  add_mem' := fun h k => h.add k
  zero_mem' := Matrix.isSymm_zero
  smul_mem' := fun c _h hh => hh.smul c

/-- Left operator multiplication on every spacetime entry. -/
def operatorLeftMul {D r : ℕ} (T : OperatorCoeff r)
    (h : OperatorPerturbation D r) : OperatorPerturbation D r :=
  ⟨fun i j => T * h.1 i j, by
    apply Matrix.IsSymm.ext
    intro i j
    rw [h.2.apply i j]⟩

/-- Right operator multiplication on every spacetime entry. -/
def operatorRightMul {D r : ℕ} (h : OperatorPerturbation D r)
    (T : OperatorCoeff r) : OperatorPerturbation D r :=
  ⟨fun i j => h.1 i j * T, by
    apply Matrix.IsSymm.ext
    intro i j
    rw [h.2.apply i j]⟩

/-- The left and right coefficient actions commute by associativity of the
operator coefficient algebra. -/
theorem operatorLeftRight_commute {D r : ℕ} (T S : OperatorCoeff r)
    (h : OperatorPerturbation D r) :
    operatorLeftMul T (operatorRightMul h S) =
      operatorRightMul (operatorLeftMul T h) S := by
  apply Subtype.ext
  ext i j a b
  simp [operatorLeftMul, operatorRightMul, Matrix.mul_assoc]

/-- Successive left actions multiply in their original noncommutative order. -/
theorem operatorLeftMul_mul {D r : ℕ} (T S : OperatorCoeff r)
    (h : OperatorPerturbation D r) :
    operatorLeftMul T (operatorLeftMul S h) = operatorLeftMul (T * S) h := by
  apply Subtype.ext
  ext i j a b
  simp [operatorLeftMul, Matrix.mul_assoc]

/-- The commutator of induced left operator multiplications is precisely the
left action of the coefficient commutator. Thus the action retains, rather
than abelianizes, the operator algebra bracket. -/
theorem operatorLeftMul_commutator {D r : ℕ} (T S : OperatorCoeff r)
    (h : OperatorPerturbation D r) :
    operatorLeftMul T (operatorLeftMul S h) -
      operatorLeftMul S (operatorLeftMul T h) =
        operatorLeftMul (T * S - S * T) h := by
  apply Subtype.ext
  ext i j a b
  change (T * (S * h.1 i j) - S * (T * h.1 i j)) a b =
    ((T * S - S * T) * h.1 i j) a b
  simp [Matrix.mul_assoc, Matrix.sub_mul]

/-- The inner commutator action of an operator coefficient on a symmetric
spacetime perturbation. It is defined using the actual left and right
operator products. -/
def operatorAdjointMul {D r : ℕ} (T : OperatorCoeff r)
    (h : OperatorPerturbation D r) : OperatorPerturbation D r :=
  operatorLeftMul T h - operatorRightMul h T

/-- Inner commutator actions on the full operator-valued perturbation space
represent the operator-ring Lie bracket. This is the Jacobi representation
law, with coefficient order retained throughout. -/
theorem operatorAdjointMul_commutator {D r : ℕ} (T S : OperatorCoeff r)
    (h : OperatorPerturbation D r) :
    operatorAdjointMul T (operatorAdjointMul S h) -
      operatorAdjointMul S (operatorAdjointMul T h) =
        operatorAdjointMul (T * S - S * T) h := by
  apply Subtype.ext
  funext i j
  change T * (S * h.1 i j - h.1 i j * S) -
      (S * h.1 i j - h.1 i j * S) * T -
      (S * (T * h.1 i j - h.1 i j * T) -
        (T * h.1 i j - h.1 i j * T) * S) =
    (T * S - S * T) * h.1 i j - h.1 i j * (T * S - S * T)
  noncomm_ring

/-- A concrete noncommuting pair in the coefficient operator algebra. -/
private def coefficientE01 : OperatorCoeff 2 := !![0, 1; 0, 0]

private def coefficientE10 : OperatorCoeff 2 := !![0, 0; 1, 0]

/-- A genuinely off-diagonal spacetime-symmetric perturbation with operator
matrix coefficients. Every spacetime entry is the identity operator, so the
spacetime matrix is not a diagonal scalar proxy. -/
private def fullOperatorWitness : OperatorPerturbation 2 2 :=
  ⟨fun _ _ => (1 : OperatorCoeff 2), by
    apply Matrix.IsSymm.ext
    intro i j
    rfl⟩

/-- The induced left action on full operator-valued perturbations retains a
nonzero coefficient commutator. Thus the represented action is genuinely
noncommutative already at operator dimension two. -/
theorem operatorLeftMul_commutator_nonzero_witness :
    operatorLeftMul coefficientE01
        (operatorLeftMul coefficientE10 fullOperatorWitness) -
      operatorLeftMul coefficientE10
        (operatorLeftMul coefficientE01 fullOperatorWitness) ≠ 0 := by
  rw [operatorLeftMul_commutator]
  intro hz
  have hentry := congrArg (fun h : OperatorPerturbation 2 2 => h.1 0 1 0 0) hz
  have hcomm : coefficientE01 * coefficientE10 - coefficientE10 * coefficientE01 =
      !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coefficientE01, coefficientE10]
  simp [operatorLeftMul, fullOperatorWitness, hcomm] at hentry

/-- Real-linear left action of one operator coefficient on the full
operator-valued perturbation space. -/
def operatorLeftLinear {D r : ℕ} (T : OperatorCoeff r) :
    OperatorPerturbation D r →ₗ[ℝ] OperatorPerturbation D r where
  toFun := operatorLeftMul T
  map_add' h k := by
    apply Subtype.ext
    funext i j
    change T * (h.1 i j + k.1 i j) = T * h.1 i j + T * k.1 i j
    exact mul_add T (h.1 i j) (k.1 i j)
  map_smul' c h := by
    apply Subtype.ext
    funext i j
    change T * (c • h.1 i j) = c • (T * h.1 i j)
    exact Matrix.mul_smul T c (h.1 i j)

/-- The noncommutative operator coefficient ring acts on full symmetric
spacetime perturbations by a unital algebra representation. Multiplication in
the represented algebra follows the original coefficient order. -/
def operatorLeftRepresentation {D r : ℕ} :
    OperatorCoeff r →+* Module.End ℝ (OperatorPerturbation D r) where
  toFun := operatorLeftLinear
  map_zero' := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    change (0 : OperatorCoeff r) * h.1 i j = 0
    exact zero_mul _
  map_one' := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    change (1 : OperatorCoeff r) * h.1 i j = h.1 i j
    exact one_mul _
  map_add' T S := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    change (T + S) * h.1 i j = T * h.1 i j + S * h.1 i j
    exact add_mul T S (h.1 i j)
  map_mul' T S := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    exact mul_assoc T S (h.1 i j)

/-- The left representation is faithful as soon as there is at least one
spacetime coordinate. Evaluating it on the constant identity-operator
perturbation recovers the coefficient operator itself. -/
theorem operatorLeftRepresentation_injective {D r : ℕ} (hD : 0 < D) :
    Function.Injective (operatorLeftRepresentation (D := D) (r := r)) := by
  intro T S hTS
  let e : Fin D := ⟨0, hD⟩
  have hact : operatorLeftMul T
      (⟨fun _ _ => (1 : OperatorCoeff r), by
        apply Matrix.IsSymm.ext
        intro i j
        rfl⟩ : OperatorPerturbation D r) =
    operatorLeftMul S
      (⟨fun _ _ => (1 : OperatorCoeff r), by
        apply Matrix.IsSymm.ext
        intro i j
        rfl⟩ : OperatorPerturbation D r) := by
    change operatorLeftLinear T _ = operatorLeftLinear S _
    exact congrArg (fun f : Module.End ℝ (OperatorPerturbation D r) =>
      f ⟨fun _ _ => (1 : OperatorCoeff r), by
        apply Matrix.IsSymm.ext
        intro i j
        rfl⟩) hTS
  have hcoeff : T * (1 : OperatorCoeff r) = S * 1 := by
    have heval := congrArg (fun h : OperatorPerturbation D r => h.1 e e) hact
    simpa [operatorLeftMul] using heval
  simpa using hcoeff

/-- The faithful left operator representation preserves the associative Lie
bracket at the level of endomorphisms.  Thus the commutator action on the
full symmetric perturbation module is the represented operator commutator,
not a coefficientwise commutative shadow. -/
theorem operatorLeftRepresentation_commutator {D r : ℕ}
    (T S : OperatorCoeff r) :
    operatorLeftRepresentation (D := D) (r := r) T *
        operatorLeftRepresentation (D := D) (r := r) S -
      operatorLeftRepresentation (D := D) (r := r) S *
        operatorLeftRepresentation (D := D) (r := r) T =
      operatorLeftRepresentation (D := D) (r := r) (T * S - S * T) := by
  rw [← map_mul, ← map_mul, map_sub]

/-- Real-linear right action by an operator coefficient. -/
def operatorRightLinear {D r : ℕ} (T : OperatorCoeff r) :
    OperatorPerturbation D r →ₗ[ℝ] OperatorPerturbation D r where
  toFun := fun h => operatorRightMul h T
  map_add' h k := by
    apply Subtype.ext
    funext i j
    change (h.1 i j + k.1 i j) * T = h.1 i j * T + k.1 i j * T
    exact add_mul _ _ _
  map_smul' c h := by
    apply Subtype.ext
    funext i j
    change (c • h.1 i j) * T = c • (h.1 i j * T)
    exact Matrix.smul_mul c (h.1 i j) T

/-- Right coefficient multiplication is a unital representation of the
opposite operator ring. Its opposite multiplication records the reversal
caused by composing right actions. -/
def operatorRightRepresentation {D r : ℕ} :
    MulOpposite (OperatorCoeff r) →+*
      Module.End ℝ (OperatorPerturbation D r) where
  toFun := fun T => operatorRightLinear (MulOpposite.unop T)
  map_zero' := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    simp [operatorRightLinear, operatorRightMul]
  map_one' := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    simp [operatorRightLinear, operatorRightMul]
  map_add' T S := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    change h.1 i j * (MulOpposite.unop T + MulOpposite.unop S) =
      h.1 i j * MulOpposite.unop T + h.1 i j * MulOpposite.unop S
    exact mul_add _ _ _
  map_mul' T S := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext i j
    simp only [operatorRightLinear, operatorRightMul, MulOpposite.unop_mul,
      Module.End.mul_apply]
    exact (mul_assoc (h.1 i j) (MulOpposite.unop S) (MulOpposite.unop T)).symm

/-- The right representation is faithful for positive spacetime dimension:
testing on the constant identity-operator perturbation recovers the right
coefficient. -/
theorem operatorRightRepresentation_injective {D r : ℕ} (hD : 0 < D) :
    Function.Injective (operatorRightRepresentation (D := D) (r := r)) := by
  intro T S hTS
  let e : Fin D := ⟨0, hD⟩
  let probe : OperatorPerturbation D r :=
    ⟨fun _ _ => (1 : OperatorCoeff r), by
      apply Matrix.IsSymm.ext
      intro i j
      rfl⟩
  have hact : operatorRightLinear (MulOpposite.unop T) probe =
      operatorRightLinear (MulOpposite.unop S) probe := by
    exact congrArg (fun f : Module.End ℝ (OperatorPerturbation D r) => f probe) hTS
  have hcoeff : (1 : OperatorCoeff r) * MulOpposite.unop T =
      1 * MulOpposite.unop S := by
    have heval := congrArg (fun h : OperatorPerturbation D r => h.1 e e) hact
    simpa [operatorRightLinear, operatorRightMul, probe] using heval
  apply MulOpposite.unop_injective
  simpa using hcoeff

/-- The left and right operator-ring representations commute, giving the
operator-valued DeWitt perturbation space its explicit bimodule structure. -/
theorem operatorLeftRightRepresentations_commute {D r : ℕ}
    (T S : OperatorCoeff r) :
    operatorLeftRepresentation (D := D) (r := r) T *
        operatorRightRepresentation (D := D) (r := r) (MulOpposite.op S) =
      operatorRightRepresentation (D := D) (r := r) (MulOpposite.op S) *
        operatorLeftRepresentation (D := D) (r := r) T := by
  apply LinearMap.ext
  intro h
  apply Subtype.ext
  funext i j
  exact (Matrix.mul_assoc T (h.1 i j) S).symm

/-- Extract one real coefficient matrix from a full operator-valued
spacetime perturbation. The two operator indices are unrestricted. -/
def operatorSlice {D r : ℕ} (h : OperatorPerturbation D r)
    (a b : Fin r) : SymmetricPerturbation D :=
  ⟨(fun i j => h.1 i j a b), by
    apply Matrix.IsSymm.ext
    intro i j
    exact congrArg (fun T : OperatorCoeff r => T a b) (h.2.apply i j)⟩

@[simp]
theorem operatorSlice_add {D r : ℕ} (h k : OperatorPerturbation D r)
    (a b : Fin r) :
    operatorSlice (h + k) a b = operatorSlice h a b + operatorSlice k a b := by
  apply Subtype.ext
  rfl

@[simp]
theorem operatorSlice_smul {D r : ℕ} (c : ℝ)
    (h : OperatorPerturbation D r) (a b : Fin r) :
    operatorSlice (c • h) a b = c • operatorSlice h a b := by
  apply Subtype.ext
  rfl

/-- The full operator perturbation space is linearly equivalent to the family
of all `r × r` coefficient slices. This equivalence retains off-diagonal
operator entries. -/
def operatorSliceEquiv (D r : ℕ) :
    OperatorPerturbation D r ≃ₗ[ℝ]
      (Fin r × Fin r → SymmetricPerturbation D) where
  toFun h p := operatorSlice h p.1 p.2
  invFun f :=
    ⟨(fun i j a b => (f (a, b)).1 i j), by
      apply Matrix.IsSymm.ext
      intro i j
      ext a b
      exact (f (a, b)).2.apply i j⟩
  left_inv h := by
    apply Subtype.ext
    ext i j a b
    rfl
  right_inv f := by
    funext p
    rcases p with ⟨a, b⟩
    apply Subtype.ext
    ext i j
    rfl
  map_add' h k := by
    funext p
    exact operatorSlice_add h k p.1 p.2
  map_smul' c h := by
    funext p
    exact operatorSlice_smul c h p.1 p.2

/-- Hilbert--Schmidt sum of the existing DeWitt pairings over all operator
matrix coefficients. This uses all `r^2` operator entries. -/
def pairing (D r : ℕ) (h k : OperatorPerturbation D r) : ℝ :=
  ∑ a : Fin r, ∑ b : Fin r,
    DeWittMatrixForm.pairing D (operatorSlice h a b) (operatorSlice k a b)

/-- Quadratic form associated with the full operator-coefficient DeWitt
pairing. -/
noncomputable def quadraticForm (D r : ℕ) :
    QuadraticForm ℝ (OperatorPerturbation D r) :=
  (QuadraticMap.pi (fun _ : Fin r × Fin r =>
    DeWittMatrixForm.quadraticForm D)).comp (operatorSliceEquiv D r).toLinearMap

@[simp]
theorem quadraticForm_apply (D r : ℕ) (h : OperatorPerturbation D r) :
    quadraticForm D r h = pairing D r h h := by
  rw [quadraticForm, QuadraticMap.comp_apply, QuadraticMap.pi_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change DeWittMatrixForm.pairing D (operatorSlice h a b) (operatorSlice h a b) = _
  rfl

/-- Reordering the coefficient and spacetime slots turns the amplified
quadratic form into a finite product of the already-constructed DeWitt forms.
This is an isometric equivalence of quadratic spaces, not a replacement of
the operator-matrix carrier by a diagonal or commuting subalgebra. -/
def quadraticForm_isometric_pi (D r : ℕ) :
    (quadraticForm D r).IsometryEquiv
      (QuadraticMap.pi (fun _ : Fin r × Fin r =>
        DeWittMatrixForm.quadraticForm D)) := by
  refine ⟨operatorSliceEquiv D r, ?_⟩
  intro h
  rw [quadraticForm_apply, QuadraticMap.pi_apply, Fintype.sum_prod_type]
  rfl

/-- Flatten a finite family of finite-coordinate operators without discarding
any coordinate. -/
def flattenCoefficients (I : Type*) [Fintype I] (m : ℕ) :
    (I → Fin m → ℝ) ≃ₗ[ℝ] (I × Fin m → ℝ) where
  toFun f p := f p.1 p.2
  invFun f i j := f (i, j)
  left_inv f := by funext i j; rfl
  right_inv f := by funext p; rcases p with ⟨i, j⟩; rfl
  map_add' f g := by funext p; rfl
  map_smul' c f := by funext p; rfl

/-- The product of weighted DeWitt forms becomes one weighted form on the
product index by flattening all operator coefficient coordinates. -/
def weightedPiFlattenIsometry (I : Type*) [Fintype I] (m : ℕ)
    (w : Fin m → ℝ) :
    (QuadraticMap.pi (fun _ : I => QuadraticMap.weightedSumSquares ℝ w)).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (fun p : I × Fin m => w p.2)) where
  toLinearEquiv := flattenCoefficients I m
  map_app' f := by
    simp [QuadraticMap.pi_apply, QuadraticMap.weightedSumSquares_apply,
      Fintype.sum_prod_type, flattenCoefficients]

/-- The amplified operator-coefficient DeWitt form has a weighted-square
normal form on the full operator matrix-entry index. The positive and negative
weights count every matrix coefficient, including off-diagonal entries. -/
theorem quadraticForm_weighted_sign_counts (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    ∃ w : ((Fin r × Fin r) ×
        Fin (Module.finrank ℝ (SymmetricPerturbation (d + 1)))) → ℝ,
      (∀ p, w p = -1 ∨ w p = 1) ∧
      (quadraticForm (d + 1) r).Equivalent
        (QuadraticMap.weightedSumSquares ℝ w) ∧
      {p | 0 < w p}.ncard = r * r * Nat.choose (d + 1) 2 ∧
      {p | w p < 0}.ncard = r * r * (d + 1) := by
  classical
  let I := Fin r × Fin r
  let m := Module.finrank ℝ (SymmetricPerturbation (d + 1))
  obtain ⟨w, hw, hEq, hpos, hneg⟩ :=
    DeWittMatrixForm.quadraticForm_weighted_sign_counts d hd
  let wp : I × Fin m → ℝ := fun p => w p.2
  have scalarToWeighted :
      (DeWittMatrixForm.quadraticForm (d + 1)).Equivalent
        (QuadraticMap.weightedSumSquares ℝ w) := hEq
  let productEquiv := QuadraticMap.IsometryEquiv.pi
    (fun _ : I => Classical.choice scalarToWeighted)
  let flattenEquiv := weightedPiFlattenIsometry I m w
  let fullEquiv :=
    (quadraticForm_isometric_pi (d + 1) r).trans
      (productEquiv.trans flattenEquiv)
  have hPosCard : {p : I × Fin m | 0 < wp p}.ncard =
      Fintype.card I * {j : Fin m | 0 < w j}.ncard := by
    have hset : {p : I × Fin m | 0 < wp p} =
        Set.univ ×ˢ {j : Fin m | 0 < w j} := by
      ext p
      rcases p with ⟨i, j⟩
      simp [wp]
    rw [hset, Set.ncard_prod]
    simp
  have hNegCard : {p : I × Fin m | wp p < 0}.ncard =
      Fintype.card I * {j : Fin m | w j < 0}.ncard := by
    have hset : {p : I × Fin m | wp p < 0} =
        Set.univ ×ˢ {j : Fin m | w j < 0} := by
      ext p
      rcases p with ⟨i, j⟩
      simp [wp]
    rw [hset, Set.ncard_prod]
    simp
  refine ⟨wp, ?_, ⟨fullEquiv⟩, ?_, ?_⟩
  · intro p
    rcases p with ⟨i, j⟩
    exact hw j
  · calc
      {p : I × Fin m | 0 < wp p}.ncard =
          Fintype.card I * {j : Fin m | 0 < w j}.ncard := hPosCard
      _ = Fintype.card I * Nat.choose (d + 1) 2 := by rw [hpos]
      _ = r * r * Nat.choose (d + 1) 2 := by simp [I, Fintype.card_prod]
  · calc
      {p : I × Fin m | wp p < 0}.ncard =
          Fintype.card I * {j : Fin m | w j < 0}.ncard := hNegCard
      _ = Fintype.card I * (d + 1) := by rw [hneg]
      _ = r * r * (d + 1) := by simp [I, Fintype.card_prod]

/-- Exact Sylvester signature of the Hilbert--Schmidt amplified DeWitt form
on the complete operator-matrix coefficient carrier. -/
theorem quadraticForm_signature (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    _root_.sigPos (quadraticForm (d + 1) r) =
        r * r * Nat.choose (d + 1) 2 ∧
      _root_.sigNeg (quadraticForm (d + 1) r) = r * r * (d + 1) := by
  obtain ⟨w, hw, hEq, hpos, hneg⟩ := quadraticForm_weighted_sign_counts d hd r
  constructor
  · rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hEq]
    exact hpos
  · rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hEq]
    exact hneg

/-- Exact operator-entry expansion of the amplified quadratic form. -/
theorem pairing_self_eq_sum_slices (D r : ℕ) (h : OperatorPerturbation D r) :
    pairing D r h h =
      ∑ a : Fin r, ∑ b : Fin r,
        DeWittMatrixForm.quadratic D (operatorSlice h a b) := by
  simp [pairing, DeWittMatrixForm.quadratic]

/-- Operator-valued perturbations whose every matrix coefficient lies in the
spatial anisotropic DeWitt kernel. This is the complete coefficientwise
operator subspace, not its diagonal corner. -/
def operatorAnisotropicSubspace (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    Submodule ℝ (OperatorPerturbation (d + 1) r) :=
  Submodule.comap (operatorSliceEquiv (d + 1) r).toLinearMap
    (Submodule.pi Set.univ
      (fun _ : Fin r × Fin r =>
        DeWittMatrixForm.spacetimeAnisotropicSubspace d hd))

/-- The full operator Witt sector consists of all coefficient slices lying
in the explicit lapse/shift hyperbolic-frame span. -/
def operatorWittFrameSubspace (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    Submodule ℝ (OperatorPerturbation (d + 1) r) :=
  Submodule.comap (operatorSliceEquiv (d + 1) r).toLinearMap
    (Submodule.pi Set.univ
      (fun _ : Fin r × Fin r =>
        DeWittMatrixForm.deWittWittFrameSubspace d hd))

/-- The operator-valued DeWitt space splits as all coefficientwise
anisotropic modes plus all coefficientwise lapse/shift Witt-frame modes.
Both summands retain arbitrary full operator matrices in each coefficient;
the result is an internal direct sum on the actual operator-valued carrier. -/
theorem operatorDeWitt_witt_anisotropic_isCompl (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    IsCompl (operatorAnisotropicSubspace d hd r)
      (operatorWittFrameSubspace d hd r) := by
  classical
  let U := DeWittMatrixForm.spacetimeAnisotropicSubspace d hd
  let V := DeWittMatrixForm.deWittWittFrameSubspace d hd
  let hc := DeWittMatrixForm.deWitt_full_witt_anisotropic_isCompl d hd
  let e := operatorSliceEquiv (d + 1) r
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · apply le_antisymm
    · intro h hh
      rw [Submodule.mem_bot]
      apply e.injective
      funext p
      rcases p with ⟨a, b⟩
      have hU : e h (a, b) ∈ U := by
        have hm := (Submodule.mem_comap.mp hh.1)
        exact (Submodule.mem_pi.mp hm) (a, b) (Set.mem_univ _)
      have hV : e h (a, b) ∈ V := by
        have hm := (Submodule.mem_comap.mp hh.2)
        exact (Submodule.mem_pi.mp hm) (a, b) (Set.mem_univ _)
      have hz : e h (a, b) = 0 := by
        have hbot : U ⊓ V = ⊥ := hc.disjoint.eq_bot
        have hmem : e h (a, b) ∈ (⊥ : Submodule ℝ (SymmetricPerturbation (d + 1))) := by
          rw [← hbot]
          exact ⟨hU, hV⟩
        simpa using hmem
      change operatorSlice h a b = operatorSlice (0 : OperatorPerturbation (d + 1) r) a b
      calc
        operatorSlice h a b = 0 := by
          change e h (a, b) = 0 at hz
          simpa [e, operatorSliceEquiv] using hz
        _ = operatorSlice (0 : OperatorPerturbation (d + 1) r) a b := by
          apply Subtype.ext
          rfl
    · exact bot_le
  · apply Submodule.eq_top_iff'.2
    intro h
    let f := e h
    have hsplit : ∀ p : Fin r × Fin r,
        ∃ u : U, ∃ v : V, (u : SymmetricPerturbation (d + 1)) + v = f p := by
      intro p
      obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl hc (f p)
      exact ⟨u, v, huv⟩
    choose u v huv using hsplit
    let fU : Fin r × Fin r → SymmetricPerturbation (d + 1) := fun p => u p
    let fV : Fin r × Fin r → SymmetricPerturbation (d + 1) := fun p => v p
    have hfU : fU ∈ Submodule.pi Set.univ (fun _ : Fin r × Fin r => U) := by
      apply Submodule.mem_pi.mpr
      intro p hp
      exact (u p).property
    have hfV : fV ∈ Submodule.pi Set.univ (fun _ : Fin r × Fin r => V) := by
      apply Submodule.mem_pi.mpr
      intro p hp
      exact (v p).property
    have hf : f = fU + fV := by
      funext p
      exact (huv p).symm
    let hU : OperatorPerturbation (d + 1) r := e.symm fU
    let hV : OperatorPerturbation (d + 1) r := e.symm fV
    have hhU : hU ∈ operatorAnisotropicSubspace d hd r := by
      rw [operatorAnisotropicSubspace, Submodule.mem_comap]
      change e hU ∈ Submodule.pi Set.univ (fun _ : Fin r × Fin r => U)
      rw [e.apply_symm_apply]
      exact hfU
    have hhV : hV ∈ operatorWittFrameSubspace d hd r := by
      rw [operatorWittFrameSubspace, Submodule.mem_comap]
      change e hV ∈ Submodule.pi Set.univ (fun _ : Fin r × Fin r => V)
      rw [e.apply_symm_apply]
      exact hfV
    have heq : h = hU + hV := by
      apply e.injective
      simpa [f, hU, hV] using hf
    rw [heq]
    exact Submodule.add_mem_sup hhU hhV

/-- The operator-amplified DeWitt form is strictly positive on its full
coefficientwise spatial anisotropic subspace. -/
theorem operatorAnisotropic_positive (d : ℕ) (hd : 2 ≤ d) (r : ℕ)
    (h : operatorAnisotropicSubspace d hd r) (hne : (h : OperatorPerturbation (d + 1) r) ≠ 0) :
    0 < quadraticForm (d + 1) r h := by
  classical
  let H : OperatorPerturbation (d + 1) r := h.1
  have hHne : H ≠ 0 := hne
  have hh : operatorSliceEquiv (d + 1) r H ∈
      Submodule.pi Set.univ
        (fun _ : Fin r × Fin r =>
          DeWittMatrixForm.spacetimeAnisotropicSubspace d hd) :=
    Submodule.mem_comap.mp h.2
  have hcoeff (a b : Fin r) :
      operatorSlice H a b ∈ DeWittMatrixForm.spacetimeAnisotropicSubspace d hd := by
    exact (Submodule.mem_pi.mp hh) (a, b) (Set.mem_univ _)
  have hexists : ∃ p : Fin r × Fin r,
      operatorSlice H p.1 p.2 ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hHne
    apply (operatorSliceEquiv (d + 1) r).injective
    funext p
    rcases p with ⟨a, b⟩
    change operatorSlice H a b = operatorSlice (0 : OperatorPerturbation (d + 1) r) a b
    calc
      operatorSlice H a b = 0 := hnot (a, b)
      _ = operatorSlice (0 : OperatorPerturbation (d + 1) r) a b := by
        apply Subtype.ext
        rfl
  change 0 < quadraticForm (d + 1) r H
  rw [quadraticForm_apply, pairing_self_eq_sum_slices]
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin r × Fin r =>
      DeWittMatrixForm.quadratic (d + 1) (operatorSlice H p.1 p.2))]
  apply Finset.sum_pos'
  · intro p hp
    have hmem := hcoeff p.1 p.2
    rcases (LinearMap.mem_range.mp hmem) with ⟨S, hS⟩
    by_cases hz : S.1 = 0
    · rw [← hS]
      simp [DeWittMatrixForm.quadratic, DeWittMatrixForm.pairing,
        DeWittMatrixForm.spacetimeAnisotropicEmbedding, hz]
    · have hSne : S.1 ≠ 0 := hz
      rw [← hS]
      exact le_of_lt (DeWittMatrixForm.spatialAnisotropic_positive d hd S hSne)
  · obtain ⟨p, hp⟩ := hexists
    refine ⟨p, Finset.mem_univ _, ?_⟩
    have hmem := hcoeff p.1 p.2
    rcases (LinearMap.mem_range.mp hmem) with ⟨S, hS⟩
    have hSne : S.1 ≠ 0 := by
      intro hz
      apply hp
      rw [← hS]
      simp [DeWittMatrixForm.spacetimeAnisotropicEmbedding, hz]
    rw [← hS]
    exact DeWittMatrixForm.spatialAnisotropic_positive d hd S hSne

/-- The amplified operator-coefficient DeWitt pairing is symmetric. -/
theorem pairing_swap (D r : ℕ) (h k : OperatorPerturbation D r) :
    pairing D r h k = pairing D r k h := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact DeWittMatrixForm.pairing_swap D (operatorSlice h a b)
    (operatorSlice k a b)

/-- Additivity in the first operator-valued perturbation. -/
theorem pairing_add_left (D r : ℕ) (h₁ h₂ k : OperatorPerturbation D r) :
    pairing D r (h₁ + h₂) k = pairing D r h₁ k + pairing D r h₂ k := by
  unfold pairing
  simp only [operatorSlice_add, DeWittMatrixForm.pairing_add_left,
    Finset.sum_add_distrib]

/-- Additivity in the second operator-valued perturbation. -/
theorem pairing_add_right (D r : ℕ) (h k₁ k₂ : OperatorPerturbation D r) :
    pairing D r h (k₁ + k₂) = pairing D r h k₁ + pairing D r h k₂ := by
  calc
    pairing D r h (k₁ + k₂) = pairing D r (k₁ + k₂) h :=
      pairing_swap D r h (k₁ + k₂)
    _ = pairing D r k₁ h + pairing D r k₂ h := pairing_add_left D r k₁ k₂ h
    _ = pairing D r h k₁ + pairing D r h k₂ := by
      rw [pairing_swap D r k₁ h, pairing_swap D r k₂ h]

/-- Real homogeneity in the first operator-valued perturbation. -/
theorem pairing_smul_left (D r : ℕ) (c : ℝ)
    (h k : OperatorPerturbation D r) :
    pairing D r (c • h) k = c * pairing D r h k := by
  unfold pairing
  simp only [operatorSlice_smul, DeWittMatrixForm.pairing_smul_left,
    Finset.mul_sum]

/-- Real homogeneity in the second operator-valued perturbation. -/
theorem pairing_smul_right (D r : ℕ) (c : ℝ)
    (h k : OperatorPerturbation D r) :
    pairing D r h (c • k) = c * pairing D r h k := by
  calc
    pairing D r h (c • k) = pairing D r (c • k) h := pairing_swap D r h (c • k)
    _ = c * pairing D r k h := pairing_smul_left D r c k h
    _ = c * pairing D r h k := by rw [pairing_swap D r k h]

end InfoGeometry.Geometry.OperatorDeWittAmplification

end
