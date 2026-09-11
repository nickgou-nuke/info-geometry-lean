import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bilinear TKK input from the native symplectic Freudenthal carrier

This file exposes the existing rank-two symplectic operator as a bilinear
map into the existing zero-grade Lie subalgebra.  It is a prerequisite for a
later TKK bracket; it does not assert an `E₇` identification or Jacobi for a
new five-graded carrier.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev SymplecticTKKZero := symplecticOperatorLieSubalgebra D

def mixedSymplecticLinearLeft (Y : FreudenthalCharge J) :
    FreudenthalCharge J →ₗ[ℝ] SymplecticTKKZero D where
  toFun X := mixedSymplecticBracket D X Y
  map_add' X X' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro Z
    simp only [mixedSymplecticBracket_val]
    change symplecticRankTwo D (X + X') Y Z =
      symplecticRankTwo D X Y Z + symplecticRankTwo D X' Y Z
    simp only [symplecticRankTwo_apply]
    rw [symplecticForm_add_left]
    module
  map_smul' r X := by
    apply Subtype.ext
    apply LinearMap.ext
    intro Z
    simp only [mixedSymplecticBracket_val]
    change symplecticRankTwo D (r • X) Y Z =
      r • symplecticRankTwo D X Y Z
    simp only [symplecticRankTwo_apply]
    rw [symplecticForm_smul_left]
    module

def mixedSymplecticLinear :
    FreudenthalCharge J →ₗ[ℝ]
      FreudenthalCharge J →ₗ[ℝ] SymplecticTKKZero D where
  toFun X := mixedSymplecticLinearLeft D X
  map_add' X X' := by
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    apply LinearMap.ext
    intro Z
    dsimp [mixedSymplecticLinearLeft]
    change symplecticRankTwo D Y (X + X') Z =
      symplecticRankTwo D Y X Z + symplecticRankTwo D Y X' Z
    simp only [symplecticRankTwo_apply]
    rw [symplecticForm_add_left]
    module
  map_smul' r X := by
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    apply LinearMap.ext
    intro Z
    dsimp [mixedSymplecticLinearLeft]
    change symplecticRankTwo D Y (r • X) Z =
      r • symplecticRankTwo D Y X Z
    simp only [symplecticRankTwo_apply]
    rw [symplecticForm_smul_left]
    module

@[simp] theorem mixedSymplecticLinear_apply
    (X Y : FreudenthalCharge J) :
    mixedSymplecticLinear D X Y = mixedSymplecticBracket D X Y := by
  exact mixedSymplecticBracket_swap D X Y |>.symm

/-! The three bilinear pieces can now be packaged in the repository's
`TKKClosureDatum` signature.  This is still a closure datum, not yet a Lie
bracket on its total direct-sum carrier. -/

def symplecticZeroBracket :
    SymplecticTKKZero D →ₗ[ℝ]
      SymplecticTKKZero D →ₗ[ℝ] SymplecticTKKZero D where
  toFun T :=
    { toFun := fun U =>
        ⟨⁅(T : Module.End ℝ (FreudenthalCharge J)),
            (U : Module.End ℝ (FreudenthalCharge J))⁆,
          (symplecticOperatorLieSubalgebra D).lie_mem T.property U.property⟩
      map_add' := by
        intro U V
        apply Subtype.ext
        change ⁅(T : Module.End ℝ (FreudenthalCharge J)),
            (U : Module.End ℝ (FreudenthalCharge J)) + V⁆ =
          (⁅(T : Module.End ℝ (FreudenthalCharge J)),
            (U : Module.End ℝ (FreudenthalCharge J))⁆ : Module.End ℝ
              (FreudenthalCharge J)) +
          ⁅(T : Module.End ℝ (FreudenthalCharge J)),
            (V : Module.End ℝ (FreudenthalCharge J))⁆
        simp only [Ring.lie_def, add_mul, mul_add,
          sub_eq_add_neg]
        abel
      map_smul' := by
        intro r U
        apply Subtype.ext
        change ⁅(T : Module.End ℝ (FreudenthalCharge J)),
            r • (U : Module.End ℝ (FreudenthalCharge J))⁆ = _
        simp [Ring.lie_def, smul_add,
          sub_eq_add_neg] }
  map_add' T U := by
    apply LinearMap.ext
    intro V
    apply Subtype.ext
    change ⁅((T : Module.End ℝ (FreudenthalCharge J)) + U),
        (V : Module.End ℝ (FreudenthalCharge J))⁆ =
      ⁅(T : Module.End ℝ (FreudenthalCharge J)),
        (V : Module.End ℝ (FreudenthalCharge J))⁆ +
      ⁅(U : Module.End ℝ (FreudenthalCharge J)),
        (V : Module.End ℝ (FreudenthalCharge J))⁆
    simp only [Ring.lie_def, add_mul, mul_add,
      sub_eq_add_neg]
    abel
  map_smul' r T := by
    apply LinearMap.ext
    intro U
    apply Subtype.ext
    change ⁅r • (T : Module.End ℝ (FreudenthalCharge J)),
        (U : Module.End ℝ (FreudenthalCharge J))⁆ = _
    simp [Ring.lie_def, smul_add,
      sub_eq_add_neg]

def symplecticZeroAction :
    SymplecticTKKZero D →ₗ[ℝ]
      FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J where
  toFun T := T.1
  map_add' T U := by
    apply LinearMap.ext
    intro X
    rfl
  map_smul' r T := by
    apply LinearMap.ext
    intro X
    rfl

def symplecticTKKClosureDatum :
    TKKClosureDatum (FreudenthalCharge J) (SymplecticTKKZero D) where
  op_0_0 := symplecticZeroBracket D
  op_0_minus1 := symplecticZeroAction D
  op_0_plus1 := symplecticZeroAction D
  op_minus1_plus1 := mixedSymplecticLinear D

@[simp] theorem symplecticTKKClosureDatum_zeroBracket_val
    (T U : SymplecticTKKZero D) :
    ((symplecticTKKClosureDatum D).op_0_0 T U :
        Module.End ℝ (FreudenthalCharge J)) =
      ⁅(T : Module.End ℝ (FreudenthalCharge J)),
        (U : Module.End ℝ (FreudenthalCharge J))⁆ := by
  rfl

@[simp] theorem symplecticTKKClosureDatum_zeroBracket
    (T U : SymplecticTKKZero D) :
    (symplecticTKKClosureDatum D).op_0_0 T U = ⁅T, U⁆ := by
  rfl

theorem symplecticTKKClosureDatum_zeroAction_commutator
    (T U : SymplecticTKKZero D) (X : FreudenthalCharge J) :
    (symplecticTKKClosureDatum D).op_0_minus1
        ((symplecticTKKClosureDatum D).op_0_0 T U) X =
      (symplecticTKKClosureDatum D).op_0_minus1 T
          ((symplecticTKKClosureDatum D).op_0_minus1 U X) -
        (symplecticTKKClosureDatum D).op_0_minus1 U
          ((symplecticTKKClosureDatum D).op_0_minus1 T X) := by
  rfl

@[simp] theorem symplecticTKKClosureDatum_mixed
    (X Y : FreudenthalCharge J) :
    (symplecticTKKClosureDatum D).op_minus1_plus1 X Y =
      mixedSymplecticBracket D X Y := by
  exact mixedSymplecticLinear_apply D X Y

@[simp] theorem symplecticTKKClosureDatum_mixed_val
    (X Y : FreudenthalCharge J) :
    ((symplecticTKKClosureDatum D).op_minus1_plus1 X Y :
        Module.End ℝ (FreudenthalCharge J)) =
      symplecticRankTwo D X Y := by
  rw [symplecticTKKClosureDatum_mixed]
  rfl

@[simp] theorem symplecticTKKClosureDatum_zeroAction_minus1
    (T : SymplecticTKKZero D) (X : FreudenthalCharge J) :
    (symplecticTKKClosureDatum D).op_0_minus1 T X =
      (T : Module.End ℝ (FreudenthalCharge J)) X := by
  rfl

@[simp] theorem symplecticTKKClosureDatum_zeroAction_plus1
    (T : SymplecticTKKZero D) (X : FreudenthalCharge J) :
    (symplecticTKKClosureDatum D).op_0_plus1 T X =
      (T : Module.End ℝ (FreudenthalCharge J)) X := by
  rfl

/-! The closure datum exposes the already-proved zero-grade derivation law
without introducing a new total five-graded bracket. -/

theorem symplecticTKKClosureDatum_zeroGrade_mixed
    (T : SymplecticTKKZero D) (X Y : FreudenthalCharge J) :
    ⁅(T : Module.End ℝ (FreudenthalCharge J)),
        ((symplecticTKKClosureDatum D).op_minus1_plus1 X Y :
          Module.End ℝ (FreudenthalCharge J))⁆ =
      ((symplecticTKKClosureDatum D).op_minus1_plus1
        ((symplecticTKKClosureDatum D).op_0_minus1 T X) Y :
          Module.End ℝ (FreudenthalCharge J)) +
      ((symplecticTKKClosureDatum D).op_minus1_plus1 X
        ((symplecticTKKClosureDatum D).op_0_plus1 T Y) :
          Module.End ℝ (FreudenthalCharge J)) := by
  rw [symplecticTKKClosureDatum_mixed_val,
    symplecticTKKClosureDatum_mixed_val,
    symplecticTKKClosureDatum_mixed_val,
    symplecticTKKClosureDatum_zeroAction_minus1,
    symplecticTKKClosureDatum_zeroAction_plus1]
  have h := zeroGrade_action_mixedSymplecticBracket D T X Y
  have h' := congrArg
    (fun Z : SymplecticTKKZero D =>
      (Z : Module.End ℝ (FreudenthalCharge J))) h
  simpa only [mixedSymplecticBracket] using h'

theorem symplecticTKKClosureDatum_zeroGrade_jacobi
    (T U V : SymplecticTKKZero D) :
    ⁅(symplecticTKKClosureDatum D).op_0_0 T U, V⁆ +
        ⁅(symplecticTKKClosureDatum D).op_0_0 U V, T⁆ +
        ⁅(symplecticTKKClosureDatum D).op_0_0 V T, U⁆ = 0 := by
  rw [symplecticTKKClosureDatum_zeroBracket,
    symplecticTKKClosureDatum_zeroBracket,
    symplecticTKKClosureDatum_zeroBracket]
  have h := congrArg Neg.neg (lie_jacobi T U V)
  simp only [neg_add, neg_neg] at h
  simp only [lie_skew] at h ⊢
  abel_nf at h ⊢
  exact h

end InfoGeometry.Exceptional.Freudenthal
