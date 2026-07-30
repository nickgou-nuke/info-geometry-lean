import Mathlib.Tactic
import InfoGeometryCore.Basic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost
import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Canonical.TomitaBregmanDuality

/-!
# InfoGeometry.Canonical.AlgebraicDerivations

Coordinate-free inner-derivation lemmas on the finite `M₂(ℝ)` seed.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.AlgebraicDerivations

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost
open InfoGeometry.Canonical.ModularSL2R
open InfoGeometry.Canonical.TomitaBregmanDuality

open InfoGeometryCore

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Inner derivation (Lie bracket): `ad_X(Y) = [X,Y]`. -/
def innerDerivation (X Y : M2R) : M2R :=
  X * Y - Y * X

/-- Bracket with self vanishes: `[X,X]=0`. -/
theorem inner_derivation_self (X : M2R) :
    innerDerivation X X = 0 := by
  unfold innerDerivation
  simp

/-- Antisymmetry of the matrix Lie bracket. -/
theorem inner_derivation_antisymm (X Y : M2R) :
    innerDerivation X Y = - innerDerivation Y X := by
  unfold innerDerivation
  abel

/-- Additivity in the left slot of the Lie bracket. -/
theorem inner_derivation_add_left (X₁ X₂ Y : M2R) :
    innerDerivation (X₁ + X₂) Y =
      innerDerivation X₁ Y + innerDerivation X₂ Y := by
  unfold innerDerivation
  simp [add_mul, mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Additivity in the right slot of the Lie bracket. -/
theorem inner_derivation_add_right (X Y₁ Y₂ : M2R) :
    innerDerivation X (Y₁ + Y₂) =
      innerDerivation X Y₁ + innerDerivation X Y₂ := by
  unfold innerDerivation
  simp [add_mul, mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Homogeneity in the left slot of the Lie bracket. -/
theorem inner_derivation_smul_left (c : ℝ) (X Y : M2R) :
    innerDerivation (c • X) Y = c • innerDerivation X Y := by
  unfold innerDerivation
  simp [sub_eq_add_neg, Matrix.smul_mul, Matrix.mul_smul]

/-- Homogeneity in the right slot of the Lie bracket. -/
theorem inner_derivation_smul_right (c : ℝ) (X Y : M2R) :
    innerDerivation X (c • Y) = c • innerDerivation X Y := by
  unfold innerDerivation
  simp [sub_eq_add_neg, Matrix.smul_mul, Matrix.mul_smul]

/-- For fixed `X`, the inner derivation is an `ℝ`-linear endomorphism. -/
def adLinear (X : M2R) : M2R →ₗ[ℝ] M2R where
  toFun := fun Y => innerDerivation X Y
  map_add' Y₁ Y₂ := inner_derivation_add_right X Y₁ Y₂
  map_smul' c Y := inner_derivation_smul_right c X Y

/-- Operator lift: `ad` sends zero to the zero endomorphism. -/
theorem adLinear_zero :
    adLinear (0 : M2R) = (0 : M2R →ₗ[ℝ] M2R) := by
  ext Y i j
  simp [adLinear, innerDerivation]

/-- Operator lift: `ad` is additive in the Lie-algebra argument. -/
theorem adLinear_add (X Y : M2R) :
    adLinear (X + Y) = adLinear X + adLinear Y := by
  ext Z i j
  simp [adLinear, innerDerivation, add_mul, mul_add, sub_eq_add_neg]
  ring

/-- Operator lift: `ad` is homogeneous in the Lie-algebra argument. -/
theorem adLinear_smul (c : ℝ) (X : M2R) :
    adLinear (c • X) = c • adLinear X := by
  ext Y i j
  simp [adLinear, innerDerivation]
  ring

/-- Inner derivations satisfy Leibniz: `ad_X(AB)=ad_X(A)B + A ad_X(B)`. -/
theorem inner_derivation_leibniz (X A B : M2R) :
    innerDerivation X (A * B) =
      (innerDerivation X A) * B + A * (innerDerivation X B) := by
  unfold innerDerivation
  calc
    X * (A * B) - (A * B) * X
        = (X * A) * B - A * (B * X) := by simp [mul_assoc]
    _ = ((X * A) * B - (A * X) * B) + ((A * X) * B - A * (B * X)) := by abel_nf
    _ = (X * A - A * X) * B + A * (X * B - B * X) := by
          simp [mul_assoc, sub_mul, mul_sub, add_assoc, add_left_comm, add_comm]

/-- Jacobi identity for the matrix Lie bracket encoded by `innerDerivation`. -/
theorem inner_derivation_jacobi (X Y Z : M2R) :
    innerDerivation X (innerDerivation Y Z) +
      innerDerivation Y (innerDerivation Z X) +
      innerDerivation Z (innerDerivation X Y) = 0 := by
  unfold innerDerivation
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Adjoint-representation closure: `[ad_X, ad_Y] = ad_[X,Y]`. -/
theorem inner_derivation_commutator (X Y Z : M2R) :
    innerDerivation X (innerDerivation Y Z) -
      innerDerivation Y (innerDerivation X Z) =
      innerDerivation (innerDerivation X Y) Z := by
  unfold innerDerivation
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Function-level form of the adjoint commutator identity. -/
theorem inner_derivation_commutator_funext (X Y : M2R) :
    (fun Z => innerDerivation X (innerDerivation Y Z) - innerDerivation Y (innerDerivation X Z))
      = (fun Z => innerDerivation (innerDerivation X Y) Z) := by
  funext Z
  exact inner_derivation_commutator X Y Z

/-- Linear-map commutator form of the adjoint identity: `[ad X, ad Y] = ad [X,Y]`. -/
theorem adLinear_commutator (X Y : M2R) :
    (adLinear X).comp (adLinear Y) - (adLinear Y).comp (adLinear X) =
      adLinear (innerDerivation X Y) := by
  ext Z i j
  exact congrArg (fun M => M i j) (inner_derivation_commutator X Y Z)

/--
Adjoint map as Lie-morphism on the commutator bracket:
`ad_[X,Y] = [ad_X, ad_Y]`.

This is the coordinate-free cocycle/representation closure identity.
-/
theorem adLinear_lie_morphism (X Y : M2R) :
    adLinear (innerDerivation X Y) =
      (adLinear X).comp (adLinear Y) - (adLinear Y).comp (adLinear X) := by
  simpa using (adLinear_commutator X Y).symm

/-- Scalar 2-cochain from trace of the commutator. -/
def omega2 (X Y : M2R) : ℝ :=
  tr (innerDerivation X Y)

/-- Every inner derivation lies in the trace kernel. -/
theorem tr_innerDerivation_zero (X Y : M2R) :
    tr (innerDerivation X Y) = 0 := by
  unfold innerDerivation tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- This trace-commutator 2-cochain vanishes identically on `M₂(ℝ)`. -/
theorem omega2_zero (X Y : M2R) : omega2 X Y = 0 := by
  unfold omega2
  exact tr_innerDerivation_zero X Y

/-- Antisymmetry readout of `omega2` via its zero form. -/
theorem omega2_antisymm_from_zero (X Y : M2R) :
    omega2 X Y = - omega2 Y X := by
  rw [omega2_zero, omega2_zero]
  ring

/-- Chevalley--Eilenberg 2-cocycle condition for the matrix Lie bracket. -/
def isLie2Cocycle (ω : M2R → M2R → ℝ) : Prop :=
  ∀ X Y Z,
    ω (innerDerivation X Y) Z +
      ω (innerDerivation Y Z) X +
      ω (innerDerivation Z X) Y = 0

/-- `omega2` satisfies the 2-cocycle condition (trivially, as it is zero). -/
theorem omega2_is2cocycle : isLie2Cocycle omega2 := by
  intro X Y Z
  rw [omega2_zero, omega2_zero, omega2_zero]
  ring

/-- `omega2` is alternating (antisymmetric). -/
theorem omega2_antisymm (X Y : M2R) :
    omega2 X Y = - omega2 Y X := by
  rw [omega2_zero, omega2_zero]
  ring

/--
Concrete cyclic 2-coboundary-style vanishing identity:
the cyclic sum of `omega2([·,·],·)` is zero.
-/
theorem omega2_cyclic_bracket_sum_zero (X Y Z : M2R) :
    omega2 (innerDerivation X Y) Z +
      omega2 (innerDerivation Y Z) X +
      omega2 (innerDerivation Z X) Y = 0 := by
  rw [omega2_zero, omega2_zero, omega2_zero]
  ring

/--
Concrete/abstract bridge: the explicit cyclic vanishing identity is exactly the
`isLie2Cocycle` condition for `omega2`.
-/
theorem omega2_is2cocycle_iff_cyclic :
    isLie2Cocycle omega2 ↔
      (∀ X Y Z,
        omega2 (innerDerivation X Y) Z +
          omega2 (innerDerivation Y Z) X +
          omega2 (innerDerivation Z X) Y = 0) := by
  rfl

/-- The invariant trace 3-cochain `tr(X [Y,Z])` on the matrix Lie algebra. -/
def omega3 (X Y Z : M2R) : ℝ :=
  tr (X * innerDerivation Y Z)

/--
Chevalley--Eilenberg 3-cocycle condition (scalar-valued, trivial module
convention) for the matrix Lie bracket.
-/
def isLie3Cocycle (τ : M2R → M2R → M2R → ℝ) : Prop :=
  ∀ W X Y Z,
      τ (innerDerivation W X) Y Z
    - τ (innerDerivation W Y) X Z
    + τ (innerDerivation W Z) X Y
    + τ (innerDerivation X Y) W Z
    - τ (innerDerivation X Z) W Y
    + τ (innerDerivation Y Z) W X = 0

/-- `omega3` satisfies the Chevalley--Eilenberg 3-cocycle identity. -/
theorem omega3_is3cocycle : isLie3Cocycle omega3 := by
  intro W X Y Z
  unfold omega3 innerDerivation tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
Concrete/abstract bridge for the 3-cocycle predicate:
`isLie3Cocycle omega3` is exactly its expanded six-term CE identity.
-/
theorem omega3_is3cocycle_iff_expanded :
    isLie3Cocycle omega3 ↔
      (∀ W X Y Z,
          omega3 (innerDerivation W X) Y Z
        - omega3 (innerDerivation W Y) X Z
        + omega3 (innerDerivation W Z) X Y
        + omega3 (innerDerivation X Y) W Z
        - omega3 (innerDerivation X Z) W Y
        + omega3 (innerDerivation Y Z) W X = 0) := by
  rfl

/--
Explicit six-term Chevalley--Eilenberg sum for `omega3` vanishes.
-/
theorem omega3_expanded_sum_zero (W X Y Z : M2R) :
      omega3 (innerDerivation W X) Y Z
    - omega3 (innerDerivation W Y) X Z
    + omega3 (innerDerivation W Z) X Y
    + omega3 (innerDerivation X Y) W Z
    - omega3 (innerDerivation X Z) W Y
    + omega3 (innerDerivation Y Z) W X = 0 := by
  exact omega3_is3cocycle W X Y Z

/-- The Tomita-Bregman operator lies in the kernel of the modular inner derivation. -/
theorem modular_derivation_bregman_invariant :
    innerDerivation K TomitaBregmanOp = 0 := by
  rw [tomita_bregman_diagonal, K_eval]
  unfold innerDerivation
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `2×2` trace is cyclic on products. -/
theorem tr_mul_comm (A B : M2R) :
    tr (A * B) = tr (B * A) := by
  unfold tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `2×2` trace is cyclic on triple products: `tr(ABC)=tr(BCA)`. -/
theorem tr_mul_cyclic (A B C : M2R) :
    tr ((A * B) * C) = tr ((B * C) * A) := by
  unfold tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
Trace-form invariance under inner derivations:
`⟨[X,Y], Z⟩ + ⟨Y, [X,Z]⟩ = 0`.
-/
theorem traceForm_innerDerivation_invariant (X Y Z : M2R) :
    traceForm (innerDerivation X Y) Z + traceForm Y (innerDerivation X Z) = 0 := by
  unfold traceForm innerDerivation tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Coordinate-free derived metric from the modular inner derivation. -/
noncomputable def gK (X Y : M2R) : ℝ :=
  tr (innerDerivation K X * innerDerivation K Y)

/-- Additivity in the left argument. -/
theorem gK_add_left (X₁ X₂ Y : M2R) :
    gK (X₁ + X₂) Y = gK X₁ Y + gK X₂ Y := by
  unfold gK innerDerivation tr
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, sub_eq_add_neg]
  ring

/-- Homogeneity in the left argument. -/
theorem gK_smul_left (c : ℝ) (X Y : M2R) :
    gK (c • X) Y = c * gK X Y := by
  unfold gK innerDerivation tr
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Symmetry of the derived metric on `M₂(ℝ)`. -/
theorem gK_symm (X Y : M2R) :
    gK X Y = gK Y X := by
  unfold gK
  simpa using tr_mul_comm (innerDerivation K X) (innerDerivation K Y)

/-- Additivity in the right argument. -/
theorem gK_add_right (X Y₁ Y₂ : M2R) :
    gK X (Y₁ + Y₂) = gK X Y₁ + gK X Y₂ := by
  calc
    gK X (Y₁ + Y₂) = gK (Y₁ + Y₂) X := gK_symm X (Y₁ + Y₂)
    _ = gK Y₁ X + gK Y₂ X := gK_add_left Y₁ Y₂ X
    _ = gK X Y₁ + gK X Y₂ := by rw [gK_symm Y₁ X, gK_symm Y₂ X]

/-- Homogeneity in the right argument. -/
theorem gK_smul_right (c : ℝ) (X Y : M2R) :
    gK X (c • Y) = c * gK X Y := by
  calc
    gK X (c • Y) = gK (c • Y) X := gK_symm X (c • Y)
    _ = c * gK Y X := gK_smul_left c Y X
    _ = c * gK X Y := by rw [gK_symm Y X]

/-- The Tomita-Bregman operator is orthogonal to every direction in `gK`. -/
theorem gK_TomitaBregman_zero (Y : M2R) :
    gK TomitaBregmanOp Y = 0 := by
  unfold gK
  have hcomm : innerDerivation K TomitaBregmanOp = 0 := by
    rw [tomita_bregman_diagonal]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [innerDerivation, K, InfoGeometry.Canonical.ModularLorentzBoost.K,
        E, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hcomm]
  unfold tr
  simp

/-- Zero in the left slot gives zero metric value. -/
theorem gK_zero_left (Y : M2R) :
    gK (0 : M2R) Y = 0 := by
  unfold gK innerDerivation tr
  simp

/-- Zero in the right slot gives zero metric value. -/
theorem gK_zero_right (X : M2R) :
    gK X (0 : M2R) = 0 := by
  rw [gK_symm]
  exact gK_zero_left X

/-- Full bilinear expansion over sums in both slots. -/
theorem gK_add_add (X₁ X₂ Y₁ Y₂ : M2R) :
    gK (X₁ + X₂) (Y₁ + Y₂) =
      gK X₁ Y₁ + gK X₁ Y₂ + gK X₂ Y₁ + gK X₂ Y₂ := by
  rw [gK_add_left]
  rw [gK_add_right X₁ Y₁ Y₂, gK_add_right X₂ Y₁ Y₂]
  ring

/-- Tomita-Bregman orthogonality is stable under right-slot addition. -/
theorem gK_TomitaBregman_zero_add (Y₁ Y₂ : M2R) :
    gK TomitaBregmanOp (Y₁ + Y₂) = 0 := by
  rw [gK_add_right, gK_TomitaBregman_zero, gK_TomitaBregman_zero]
  ring

/-- Tomita-Bregman orthogonality is stable under right-slot scaling. -/
theorem gK_TomitaBregman_zero_smul (c : ℝ) (Y : M2R) :
    gK TomitaBregmanOp (c • Y) = 0 := by
  rw [gK_smul_right, gK_TomitaBregman_zero]
  ring

/-- Tomita-Bregman orthogonality is stable under arbitrary linear combinations. -/
theorem gK_TomitaBregman_zero_lincomb
    (a b : ℝ) (Y₁ Y₂ : M2R) :
    gK TomitaBregmanOp (a • Y₁ + b • Y₂) = 0 := by
  rw [gK_add_right, gK_smul_right, gK_smul_right]
  rw [gK_TomitaBregman_zero, gK_TomitaBregman_zero]
  ring

/-- Left-slot linear closure against the Tomita-Bregman direction. -/
theorem gK_lincomb_TomitaBregman_zero
    (a b : ℝ) (X₁ X₂ : M2R) :
    gK (a • X₁ + b • X₂) TomitaBregmanOp = 0 := by
  rw [gK_symm]
  exact gK_TomitaBregman_zero_lincomb a b X₁ X₂

/--
Two-sided bilinear closure with Tomita-Bregman in one slot:
every bilinear pair of linear combinations remains zero when the opposite slot
is `TomitaBregmanOp`.
-/
theorem gK_bilinear_closure_with_Tomita
    (a b c d : ℝ) (X₁ X₂ Y₁ Y₂ : M2R) :
    gK (a • X₁ + b • X₂) TomitaBregmanOp
      + gK TomitaBregmanOp (c • Y₁ + d • Y₂) = 0 := by
  rw [gK_lincomb_TomitaBregman_zero, gK_TomitaBregman_zero_lincomb]
  ring

/--
Kernel-closure packet for the Tomita-right kernel:
`Y ↦ gK TomitaBregmanOp Y` is zero at `0`, closed under addition, and closed
under scalar multiplication.
-/
theorem gK_Tomita_kernel_closure
    (Y₁ Y₂ : M2R) (c : ℝ) :
    gK TomitaBregmanOp (0 : M2R) = 0 ∧
    gK TomitaBregmanOp (Y₁ + Y₂) = 0 ∧
    gK TomitaBregmanOp (c • Y₁) = 0 := by
  refine ⟨?h0, ?hadd, ?hsmul⟩
  · exact gK_zero_right TomitaBregmanOp
  · exact gK_TomitaBregman_zero_add Y₁ Y₂
  · exact gK_TomitaBregman_zero_smul c Y₁

/--
Commutator-derivation Jacobi identity in operator form:

`ad_X (ad_Y Z) - ad_Y (ad_X Z) = ad_[X,Y] Z`.
-/
theorem inner_derivation_jacobi_expanded (X Y Z : M2R) :
    innerDerivation X (innerDerivation Y Z) -
      innerDerivation Y (innerDerivation X Z) =
    innerDerivation (innerDerivation X Y) Z := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [innerDerivation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end InfoGeometry.Canonical.AlgebraicDerivations
