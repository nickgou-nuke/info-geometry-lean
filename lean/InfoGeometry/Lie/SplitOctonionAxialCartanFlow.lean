import InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Closed traceless axial Cartan flow on canonical split octonions

This file exponentiates the concrete coordinate weights, not an abstract
derivation witness.  For `k : Fin 3 → ℝ`, the upper and lower Zorn vector
coordinates are scaled by `exp (t * k i)` and `exp (-t * k i)` respectively.
Under the proved traceless condition, the native Zorn multiplication is
preserved.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialCartanFlow

open scoped BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CZ := ZornMatrix ℝ

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ
  Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

/-- The closed coordinate scaling with inverse obtained by reversing `t`. -/
def axialCartanFlow (k : Fin 3 → ℝ) (t : ℝ) : CZ ≃ₗ[ℝ] CZ where
  toFun Z :=
    { a := Z.a
      b := Z.b
      x := fun i => Real.exp (t * k i) * Z.x i
      y := fun i => Real.exp (-(t * k i)) * Z.y i }
  invFun Z :=
    { a := Z.a
      b := Z.b
      x := fun i => Real.exp (-(t * k i)) * Z.x i
      y := fun i => Real.exp (t * k i) * Z.y i }
  map_add' X Y := by
    ext i <;> simp [ZornMatrix.add_def] <;> ring
  map_smul' r X := by
    ext i <;> simp [Equiv.smul_def, coordEquiv] <;> ring
  left_inv Z := by
    ext i <;> simp [Real.exp_neg]
  right_inv Z := by
    ext i <;> simp [Real.exp_neg]

@[simp] theorem axialCartanFlow_apply (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialCartanFlow k t Z =
      { a := Z.a
        b := Z.b
        x := fun i => Real.exp (t * k i) * Z.x i
        y := fun i => Real.exp (-(t * k i)) * Z.y i } :=
  rfl

@[simp] theorem axialCartanFlow_one (k : Fin 3 → ℝ) (t : ℝ) :
    axialCartanFlow k t (1 : CZ) = 1 := by
  change axialCartanFlow k t
      ({ a := 1, b := 1, x := 0, y := 0 } : CZ) =
    ({ a := 1, b := 1, x := 0, y := 0 } : CZ)
  ext i <;> simp [axialCartanFlow]

@[simp] theorem axialCartanFlow_chiralUpperBasis
    (k : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    axialCartanFlow k t (chiralUpperBasis i) =
      Real.exp (t * k i) • chiralUpperBasis i := by
  ext j <;>
    simp [axialCartanFlow, chiralUpperBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  all_goals fin_cases i <;> fin_cases j <;> norm_num

@[simp] theorem axialCartanFlow_chiralLowerBasis
    (k : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    axialCartanFlow k t (chiralLowerBasis i) =
      Real.exp (-(t * k i)) • chiralLowerBasis i := by
  ext j <;>
    simp [axialCartanFlow, chiralLowerBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  all_goals fin_cases i <;> fin_cases j <;> norm_num

/-- The traceless closed flow preserves the native nonassociative Zorn
multiplication. -/
theorem axialCartanFlow_map_mul
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    axialCartanFlow k t (X * Y) =
      axialCartanFlow k t X * axialCartanFlow k t Y := by
  have hsum : k 0 + k 1 + k 2 = 0 := by
    simpa [Fin.sum_univ_three] using hk
  have hk0 : k 0 = -(k 1 + k 2) := by linarith
  have hk1 : k 1 = -(k 0 + k 2) := by linarith
  have hk2 : k 2 = -(k 0 + k 1) := by linarith
  have hp0 : Real.exp (t * k 0) =
      Real.exp (-(t * k 1)) * Real.exp (-(t * k 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk0]
    ring
  have hp1 : Real.exp (t * k 1) =
      Real.exp (-(t * k 0)) * Real.exp (-(t * k 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk1]
    ring
  have hp2 : Real.exp (t * k 2) =
      Real.exp (-(t * k 0)) * Real.exp (-(t * k 1)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk2]
    ring
  have hm0 : Real.exp (-(t * k 0)) =
      Real.exp (t * k 1) * Real.exp (t * k 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk0]
    ring
  have hm1 : Real.exp (-(t * k 1)) =
      Real.exp (t * k 0) * Real.exp (t * k 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk1]
    ring
  have hm2 : Real.exp (-(t * k 2)) =
      Real.exp (t * k 0) * Real.exp (t * k 1) := by
    rw [← Real.exp_add]
    congr 1
    rw [hk2]
    ring
  cases X
  cases Y
  ext i
  · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
      ZornMatrix.cross, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
      ZornMatrix.cross, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  · fin_cases i
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hp0]
      ring
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hp1]
      ring
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hp2]
      ring
  · fin_cases i
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross]
      rw [hm0]
      ring
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross]
      rw [hm1]
      ring
    · simp [axialCartanFlow, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross]
      rw [hm2]
      ring

/-! ## Erlangen packaging

The closed coordinate flow is now placed in the native multiplication
stabilizer.  This is a subgroup-valued statement, not a name-based
identification with `G₂`. -/

noncomputable def axialCartanCompositionAut
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    realZornCompositionAut :=
  ⟨axialCartanFlow k t, by
    intro X Y
    exact axialCartanFlow_map_mul k hk t X Y⟩

@[simp] theorem axialCartanCompositionAut_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (Z : CZ) :
    ((axialCartanCompositionAut k hk t : realZornCompositionAut) :
      CanonicalLinearAut) Z = axialCartanFlow k t Z :=
  rfl

theorem axialCartanCompositionAut_preserves_det
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (Z : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        realCrossProduct3 (axialCartanFlow k t Z) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 Z := by
  simpa only [axialCartanCompositionAut_apply] using
    (realZornCompositionAut_preserves_det
      (axialCartanCompositionAut k hk t) Z)

@[simp] theorem axialCartanFlow_zero (k : Fin 3 → ℝ) (Z : CZ) :
    axialCartanFlow k 0 Z = Z := by
  ext i <;> simp [axialCartanFlow]

/-- The zero parameter is the identity element of the native composition
automorphism subgroup. -/
theorem axialCartanCompositionAut_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    axialCartanCompositionAut k hk 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Z
  change axialCartanFlow k 0 Z = Z
  exact axialCartanFlow_zero k Z

theorem axialCartanFlow_add (k : Fin 3 → ℝ) (s t : ℝ) (Z : CZ) :
    axialCartanFlow k (s + t) Z =
      axialCartanFlow k s (axialCartanFlow k t Z) := by
  ext i <;> simp [axialCartanFlow]
  · rw [show (s + t) * k i = s * k i + t * k i by ring, Real.exp_add]
    ring
  · rw [show -((s + t) * k i) = -(s * k i) + -(t * k i) by ring,
      Real.exp_add]
    ring

/-- Coordinate flows with different weight vectors commute. -/
theorem axialCartanFlow_commute
    (k l : Fin 3 → ℝ) (s t : ℝ) (Z : CZ) :
    axialCartanFlow k s (axialCartanFlow l t Z) =
      axialCartanFlow l t (axialCartanFlow k s Z) := by
  ext i <;> simp [axialCartanFlow] <;> ring

/-- The coordinate flow law is the composition law of the native
multiplication-preserving automorphism subgroup. -/
theorem axialCartanCompositionAut_add_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) (Z : CZ) :
    ((axialCartanCompositionAut k hk (s + t) : realZornCompositionAut) :
      CanonicalLinearAut) Z =
      ((axialCartanCompositionAut k hk s : realZornCompositionAut) :
        CanonicalLinearAut)
        (((axialCartanCompositionAut k hk t : realZornCompositionAut) :
          CanonicalLinearAut) Z) := by
  simp only [axialCartanCompositionAut_apply]
  exact axialCartanFlow_add k s t Z

/-- The closed traceless flow satisfies the one-parameter subgroup law inside
the native multiplication-preserving automorphism subgroup. -/
theorem axialCartanCompositionAut_add
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) :
    axialCartanCompositionAut k hk (s + t) =
      axialCartanCompositionAut k hk s * axialCartanCompositionAut k hk t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Z
  change axialCartanFlow k (s + t) Z =
    axialCartanFlow k s (axialCartanFlow k t Z)
  exact axialCartanFlow_add k s t Z

/-- Different traceless weight directions commute inside the native
multiplication-preserving subgroup.  This is the concrete rank-two Cartan
commutation law, stated at the subgroup level rather than only pointwise. -/
theorem axialCartanCompositionAut_commute
    (k l : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (hl : ∑ i, l i = 0)
    (s t : ℝ) :
    axialCartanCompositionAut k hk s * axialCartanCompositionAut l hl t =
      axialCartanCompositionAut l hl t * axialCartanCompositionAut k hk s := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Z
  change axialCartanFlow k s (axialCartanFlow l t Z) =
    axialCartanFlow l t (axialCartanFlow k s Z)
  exact axialCartanFlow_commute k l s t Z

@[simp] theorem axialCartanFlow_neg_apply (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    (axialCartanFlow k t).symm Z = axialCartanFlow k (-t) Z := by
  ext i <;> simp [axialCartanFlow]

/-- Reversing the parameter gives the inverse automorphism in the subgroup. -/
theorem axialCartanCompositionAut_neg
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    axialCartanCompositionAut k hk (-t) =
      (axialCartanCompositionAut k hk t)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Z
  change axialCartanFlow k (-t) Z = (axialCartanFlow k t).symm Z
  exact (axialCartanFlow_neg_apply k t Z).symm

end InfoGeometry.Lie.SplitOctonionAxialCartanFlow
