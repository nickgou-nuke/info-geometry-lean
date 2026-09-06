import InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization
import InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Intrinsic active support of the off-diagonal imaginary ell operator

This owner works only with the already defined `lUnit`-based imaginary
commutator operator `imaginaryEllT` and the native determinant-polar bilinear
form.  Here `lUnit` is the off-diagonal split generator; it is not the
diagonal `diagEll = zornPlus - zornMinus` used by the axial Zorn/Klein owners.
Its active carrier is literally `range (T^2)`.  On that range the restricted
operator is an involution, is anti-isometric for the polar form, and generates
a nondegenerate alternating form.

No equality with the diagonal axial support, no root-channel subtype
decomposition, and no split `G₂` classification is introduced here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllSupport

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization
open InfoGeometry.Physics.Algebra

abbrev Imaginary := InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary
abbrev EndImaginary := Module.End ℝ Imaginary

theorem imaginaryEllT_val (X : Imaginary) :
    (imaginaryEllT X).1 = ellGrading X.1 := rfl

/-- The normalized imaginary commutator inherits the native cubic polynomial. -/
theorem imaginaryEllT_tripotent : imaginaryEllT ^ 3 = imaginaryEllT := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  have h := congrArg (fun F : Module.End ℝ CanonicalZorn => F X.1)
    ellGrading_tripotent
  simpa [pow_three, Module.End.mul_apply, imaginaryEllT_val] using h

/-- The intrinsic active imaginary carrier is the range of `T²`. -/
def ActiveSupport : Submodule ℝ Imaginary :=
  LinearMap.range (imaginaryEllT * imaginaryEllT)

abbrev Support := ActiveSupport

/-! ## Intrinsic kernel/support decomposition -/

theorem imaginaryEllT_kernel_component_mem (X : Imaginary) :
    X - imaginaryEllT (imaginaryEllT X) ∈ LinearMap.ker imaginaryEllT := by
  rw [LinearMap.mem_ker]
  have h := congrArg (fun F : EndImaginary => F X) imaginaryEllT_tripotent
  rw [map_sub]
  change imaginaryEllT X -
      imaginaryEllT (imaginaryEllT (imaginaryEllT X)) = 0
  have h' : imaginaryEllT (imaginaryEllT (imaginaryEllT X)) =
      imaginaryEllT X := by
    simpa [pow_three, Module.End.mul_apply] using h
  rw [h']
  exact sub_self _

theorem imaginaryEllT_support_component_mem (X : Imaginary) :
    imaginaryEllT (imaginaryEllT X) ∈ ActiveSupport := by
  exact ⟨X, rfl⟩

theorem imaginaryEllT_kernel_support_sup_eq_top :
    LinearMap.ker imaginaryEllT ⊔ ActiveSupport = ⊤ := by
  apply top_unique
  intro X _
  have hker : X - imaginaryEllT (imaginaryEllT X) ∈ LinearMap.ker imaginaryEllT :=
    imaginaryEllT_kernel_component_mem X
  have hsupp : imaginaryEllT (imaginaryEllT X) ∈ ActiveSupport :=
    imaginaryEllT_support_component_mem X
  have hsum :
      (X - imaginaryEllT (imaginaryEllT X)) + imaginaryEllT (imaginaryEllT X) = X := by
    abel
  rw [← hsum]
  exact Submodule.add_mem_sup hker hsupp

theorem imaginaryEllT_kernel_support_inf_eq_bot :
    LinearMap.ker imaginaryEllT ⊓ ActiveSupport = ⊥ := by
  apply le_antisymm
  · intro X hX
    rcases hX.2 with ⟨Y, hY⟩
    have hker : imaginaryEllT X = 0 := LinearMap.mem_ker.mp hX.1
    have htrip := congrArg (fun F : EndImaginary => F Y) imaginaryEllT_tripotent
    have hTY : imaginaryEllT Y = 0 := by
      rw [← hY] at hker
      change imaginaryEllT (imaginaryEllT (imaginaryEllT Y)) = 0 at hker
      have htrip' : imaginaryEllT (imaginaryEllT (imaginaryEllT Y)) =
          imaginaryEllT Y := by
        simpa [pow_three, Module.End.mul_apply] using htrip
      rw [htrip'] at hker
      exact hker
    have hzero : X = 0 := by
      rw [← hY]
      have hTT : imaginaryEllT (imaginaryEllT Y) = 0 := by
        rw [hTY, map_zero]
      simpa [Module.End.mul_apply] using hTT
    exact hzero
  · exact bot_le

/-- The kernel and intrinsic active support are complementary submodules. -/
theorem imaginaryEllT_kernel_support_isCompl :
    IsCompl (LinearMap.ker imaginaryEllT) ActiveSupport := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff_inf_le, imaginaryEllT_kernel_support_inf_eq_bot]
  · rw [codisjoint_iff]
    exact imaginaryEllT_kernel_support_sup_eq_top

theorem imaginaryEllT_decomposition (X : Imaginary) :
    X = (X - imaginaryEllT (imaginaryEllT X)) +
      imaginaryEllT (imaginaryEllT X) := by
  abel

/-- The imaginary ell operator restricted to its intrinsic active support. -/
def supportGrading : Module.End ℝ Support where
  toFun X := ⟨imaginaryEllT X.1, by
    rcases X.2 with ⟨Z, hZ⟩
    refine ⟨imaginaryEllT Z, ?_⟩
    have h := congrArg (fun F : EndImaginary => F Z) imaginaryEllT_tripotent
    change imaginaryEllT (imaginaryEllT (imaginaryEllT Z)) =
      imaginaryEllT X.1
    rw [← hZ]
    simpa [pow_three, Module.End.mul_apply] using congrArg imaginaryEllT h⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add imaginaryEllT X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact map_smul imaginaryEllT r X.1

@[simp] theorem supportGrading_val (X : Support) :
    (supportGrading X).1 = imaginaryEllT X.1 := rfl

theorem imaginaryEllT_sq_on_support (X : Support) :
    imaginaryEllT (imaginaryEllT X.1) = X.1 := by
  rcases X.2 with ⟨Z, hZ⟩
  have h := congrArg (fun F : EndImaginary => F Z) imaginaryEllT_tripotent
  rw [← hZ]
  simpa [pow_three, Module.End.mul_apply] using congrArg imaginaryEllT h

/-- `K² = I` on `range (T²)`. -/
theorem supportGrading_sq :
    supportGrading * supportGrading = 1 := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact imaginaryEllT_sq_on_support X

@[simp] theorem supportGrading_apply_sq (X : Support) :
    supportGrading (supportGrading X) = X := by
  have h := congrArg (fun F : Module.End ℝ Support => F X) supportGrading_sq
  simpa [Module.End.mul_apply] using h

/-- Skew-adjointness follows from the already proved alternating contraction. -/
theorem imaginaryEllT_skew_adjoint (X Y : Imaginary) :
    imaginaryPolarBilin (imaginaryEllT X) Y =
      -imaginaryPolarBilin X (imaginaryEllT Y) := by
  calc
    imaginaryPolarBilin (imaginaryEllT X) Y =
        imaginaryEllContraction X Y :=
      (imaginaryEllContraction_eq_polar_cross X Y).symm
    _ = -imaginaryEllContraction Y X := by
      rw [imaginaryEllContraction_swap]
    _ = -imaginaryPolarBilin (imaginaryEllT Y) X := by
      rw [imaginaryEllContraction_eq_polar_cross]
    _ = -imaginaryPolarBilin X (imaginaryEllT Y) := by
      rw [imaginaryPolarBilin_isSymm.eq (imaginaryEllT Y) X]

/-- Native polar metric restricted to the intrinsic support. -/
def supportMetric (X Y : Support) : ℝ :=
  imaginaryPolarBilin X.1 Y.1

theorem supportMetric_symm (X Y : Support) :
    supportMetric X Y = supportMetric Y X := by
  unfold supportMetric
  exact imaginaryPolarBilin_isSymm.eq X.1 Y.1

/-- The compatible two-form `omega(X,Y) = B(KX,Y)`. -/
def supportSymplectic (X Y : Support) : ℝ :=
  supportMetric (supportGrading X) Y

/-- On the intrinsic support the compatible two-form is literally the
restriction of the previously constructed three-form contraction. -/
theorem supportSymplectic_eq_ellContraction (X Y : Support) :
    supportSymplectic X Y = imaginaryEllContraction X.1 Y.1 := by
  exact imaginaryEllContraction_eq_polar_cross X.1 Y.1 |>.symm

theorem supportMetric_grading_anti_isometry (X Y : Support) :
    supportMetric (supportGrading X) (supportGrading Y) =
      -supportMetric X Y := by
  rw [supportMetric, supportGrading_val, supportGrading_val,
    imaginaryEllT_skew_adjoint]
  rw [imaginaryEllT_sq_on_support]
  rfl

theorem supportSymplectic_skew (X Y : Support) :
    supportSymplectic Y X = -supportSymplectic X Y := by
  unfold supportSymplectic supportMetric
  exact imaginaryEllContraction_swap X.1 Y.1

private def scalarAxis : Imaginary :=
  ⟨⟨1, -1, 0, 0⟩, by simp [mem_imaginary_iff, realZornTrace]⟩

private def upperAxis (i : Fin 3) : Imaginary :=
  ⟨chiralUpperBasis i, by simp [mem_imaginary_iff, realZornTrace,
    chiralUpperBasis]⟩

private def lowerAxis (i : Fin 3) : Imaginary :=
  ⟨chiralLowerBasis i, by simp [mem_imaginary_iff, realZornTrace,
    chiralLowerBasis]⟩

/-- The determinant-polar form is nondegenerate on the imaginary hyperplane. -/
theorem imaginaryPolarBilin_nondegenerate (X : Imaginary)
    (h : ∀ Y : Imaginary, imaginaryPolarBilin X Y = 0) : X = 0 := by
  have ha := h scalarAxis
  have hx (i : Fin 3) := h (lowerAxis i)
  have hy (i : Fin 3) := h (upperAxis i)
  have htrace := X.2
  change X.1.a + X.1.b = 0 at htrace
  have ha' : X.1.b - X.1.a = 0 := by
    simpa [scalarAxis, imaginaryPolarBilin, realZornTrace,
      mul_def, mul, dot, cross] using ha
  have ha0 : X.1.a = 0 := by linarith
  have hb0 : X.1.b = 0 := by linarith
  have hx0 : X.1.x 0 = 0 := by
    simpa [lowerAxis, imaginaryPolarBilin, realZornTrace,
      chiralLowerBasis, mul_def, mul, dot, cross] using hx 0
  have hx1 : X.1.x 1 = 0 := by
    simpa [lowerAxis, imaginaryPolarBilin, realZornTrace,
      chiralLowerBasis, mul_def, mul, dot, cross] using hx 1
  have hx2 : X.1.x 2 = 0 := by
    simpa [lowerAxis, imaginaryPolarBilin, realZornTrace,
      chiralLowerBasis, mul_def, mul, dot, cross] using hx 2
  have hy0 : X.1.y 0 = 0 := by
    simpa [upperAxis, imaginaryPolarBilin, realZornTrace,
      chiralUpperBasis, mul_def, mul, dot, cross] using hy 0
  have hy1 : X.1.y 1 = 0 := by
    simpa [upperAxis, imaginaryPolarBilin, realZornTrace,
      chiralUpperBasis, mul_def, mul, dot, cross] using hy 1
  have hy2 : X.1.y 2 = 0 := by
    simpa [upperAxis, imaginaryPolarBilin, realZornTrace,
      chiralUpperBasis, mul_def, mul, dot, cross] using hy 2
  apply Subtype.ext
  ext i
  · exact ha0
  · exact hb0
  · fin_cases i <;> assumption
  · fin_cases i <;> assumption

private def supportProject (Z : Imaginary) : Support :=
  ⟨(imaginaryEllT * imaginaryEllT) Z, ⟨Z, rfl⟩⟩

theorem supportProject_val (Z : Imaginary) :
    (supportProject Z).1 = imaginaryEllT (imaginaryEllT Z) := rfl

/-- The compatible alternating form is nondegenerate on the active support. -/
theorem supportSymplectic_nondegenerate (X : Support)
    (h : ∀ Y : Support, supportSymplectic X Y = 0) : X = 0 := by
  have hpolar : ∀ Z : Imaginary, imaginaryPolarBilin X.1 Z = 0 := by
    intro Z
    have hproj := h (supportGrading (supportProject Z))
    have hanti := supportMetric_grading_anti_isometry X (supportProject Z)
    have hXZQ : supportMetric X (supportProject Z) = 0 := by
      unfold supportSymplectic at hproj
      linarith
    have hself : imaginaryEllT (imaginaryEllT X.1) = X.1 :=
      imaginaryEllT_sq_on_support X
    calc
      imaginaryPolarBilin X.1 Z =
          imaginaryPolarBilin (imaginaryEllT (imaginaryEllT X.1)) Z := by
            rw [hself]
      _ = -imaginaryPolarBilin (imaginaryEllT X.1) (imaginaryEllT Z) := by
            rw [imaginaryEllT_skew_adjoint]
      _ = imaginaryPolarBilin X.1
          (imaginaryEllT (imaginaryEllT Z)) := by
            rw [imaginaryEllT_skew_adjoint]
            ring
      _ = 0 := by
        change supportMetric X (supportProject Z) = 0
        exact hXZQ
  apply Subtype.ext
  exact imaginaryPolarBilin_nondegenerate X.1 hpolar

/-- The native polar form is nondegenerate after restriction to the intrinsic
active support. -/
theorem supportMetric_nondegenerate (X : Support)
    (h : ∀ Y : Support, supportMetric X Y = 0) : X = 0 := by
  apply supportSymplectic_nondegenerate X
  intro Y
  unfold supportSymplectic supportMetric
  rw [supportGrading_val, imaginaryEllT_skew_adjoint]
  simpa [supportMetric, supportGrading_val] using
    congrArg (fun r : ℝ => -r) (h (supportGrading Y))

/-! ## Intrinsic positive and negative support halves -/

/-- The intrinsic `+1` eigenspace of the support involution. -/
def SupportPlus : Submodule ℝ Support :=
  Module.End.eigenspace supportGrading 1

/-- The intrinsic `-1` eigenspace of the support involution. -/
def SupportMinus : Submodule ℝ Support :=
  Module.End.eigenspace supportGrading (-1)

/-- Positive spectral projector on the intrinsic support. -/
def supportPPlus : Module.End ℝ Support := projPos supportGrading

/-- Negative spectral projector on the intrinsic support. -/
def supportPMinus : Module.End ℝ Support := projNeg supportGrading

theorem supportPPlus_add_supportPMinus :
    supportPPlus + supportPMinus = 1 := by
  rw [supportPPlus, supportPMinus, projPos_add_projNeg]
  exact supportGrading_sq

theorem supportPPlus_mem (X : Support) :
    supportPPlus X ∈ SupportPlus := by
  rw [SupportPlus, Module.End.mem_eigenspace_iff]
  change supportGrading (projPos supportGrading X) =
    (1 : ℝ) • projPos supportGrading X
  have hK : supportGrading * supportGrading * supportGrading = supportGrading := by
    rw [supportGrading_sq]
    rfl
  have h := congrArg (fun F : Module.End ℝ Support => F X) (mul_projPos hK)
  simpa [Module.End.mul_apply] using h

theorem supportPMinus_mem (X : Support) :
    supportPMinus X ∈ SupportMinus := by
  rw [SupportMinus, Module.End.mem_eigenspace_iff]
  change supportGrading (projNeg supportGrading X) =
    (-1 : ℝ) • projNeg supportGrading X
  have hK : supportGrading * supportGrading * supportGrading = supportGrading := by
    rw [supportGrading_sq]
    rfl
  have h := congrArg (fun F : Module.End ℝ Support => F X) (mul_projNeg hK)
  have h' : supportGrading (projNeg supportGrading X) =
      -(projNeg supportGrading X) := by
    simpa [Module.End.mul_apply] using h
  convert h' using 1 <;> module

@[simp] theorem supportGrading_apply_PPlus (X : Support) :
    supportGrading (supportPPlus X) = supportPPlus X := by
  have hK : supportGrading * supportGrading * supportGrading = supportGrading := by
    rw [supportGrading_sq]
    rfl
  have h := congrArg (fun F : Module.End ℝ Support => F X) (mul_projPos hK)
  simpa [Module.End.mul_apply] using h

@[simp] theorem supportGrading_apply_PMinus (X : Support) :
    supportGrading (supportPMinus X) = -supportPMinus X := by
  have hK : supportGrading * supportGrading * supportGrading = supportGrading := by
    rw [supportGrading_sq]
    rfl
  have h := congrArg (fun F : Module.End ℝ Support => F X) (mul_projNeg hK)
  simpa [Module.End.mul_apply] using h

/-- Every support vector is the sum of its intrinsic positive and negative
spectral components. -/
theorem support_eq_plus_add_minus (X : Support) :
    X = supportPPlus X + supportPMinus X := by
  have h := congrArg (fun F : Module.End ℝ Support => F X)
    supportPPlus_add_supportPMinus
  simpa using h.symm

/-- The support grading is the signed difference of its two spectral pieces. -/
theorem supportGrading_apply_decomposition (X : Support) :
    supportGrading X = supportPPlus X - supportPMinus X := by
  have h := congrArg (fun F : Module.End ℝ Support => F X)
    (projPos_sub_projNeg (T := supportGrading))
  change (projPos supportGrading) X - (projNeg supportGrading) X =
    supportGrading X at h
  exact h.symm

theorem support_eq_plus_add_minus_mem (X : Support) :
    supportPPlus X ∈ SupportPlus ∧ supportPMinus X ∈ SupportMinus :=
  ⟨supportPPlus_mem X, supportPMinus_mem X⟩

theorem supportPlus_sup_minus_eq_top :
    SupportPlus ⊔ SupportMinus = ⊤ := by
  apply top_unique
  intro X _
  rw [Submodule.mem_sup]
  refine ⟨supportPPlus X, supportPPlus_mem X,
    supportPMinus X, supportPMinus_mem X, ?_⟩
  exact (support_eq_plus_add_minus X).symm

theorem supportPlus_minus_disjoint :
    Disjoint SupportPlus SupportMinus := by
  refine Submodule.disjoint_def.2 ?_
  intro X hPlus hMinus
  rw [SupportPlus, Module.End.mem_eigenspace_iff] at hPlus
  rw [SupportMinus, Module.End.mem_eigenspace_iff] at hMinus
  have hzero : X + X = 0 := by
    calc
      X + X = supportGrading X + X := by rw [hPlus]; simp
      _ = -X + X := by rw [hMinus]; simp
      _ = 0 := by abel
  calc
    X = (1 / 2 : ℝ) • (X + X) := by module
    _ = 0 := by rw [hzero]; simp

theorem supportPlus_inf_minus_eq_bot :
    SupportPlus ⊓ SupportMinus = ⊥ := by
  apply le_antisymm
  · exact disjoint_iff_inf_le.mp supportPlus_minus_disjoint
  · exact bot_le

/-- The two intrinsic eigenspaces are complementary submodules. -/
theorem supportPlus_minus_isCompl :
    IsCompl SupportPlus SupportMinus := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff_inf_le, supportPlus_inf_minus_eq_bot]
  · rw [codisjoint_iff]
    exact supportPlus_sup_minus_eq_top

theorem supportMetric_plus_isotropic
    (X Y : Support) (hX : X ∈ SupportPlus) (hY : Y ∈ SupportPlus) :
    supportMetric X Y = 0 := by
  rw [SupportPlus, Module.End.mem_eigenspace_iff] at hX hY
  have hanti := supportMetric_grading_anti_isometry X Y
  simp only [hX, hY, one_smul] at hanti
  linarith

theorem supportMetric_minus_isotropic
    (X Y : Support) (hX : X ∈ SupportMinus) (hY : Y ∈ SupportMinus) :
    supportMetric X Y = 0 := by
  rw [SupportMinus, Module.End.mem_eigenspace_iff] at hX hY
  have hanti := supportMetric_grading_anti_isometry X Y
  simp only [hX, hY, neg_smul, one_smul] at hanti
  have hneg : supportMetric (-X) (-Y) = supportMetric X Y := by
    unfold supportMetric
    change imaginaryPolarBilin (-X.1) (-Y.1) =
      imaginaryPolarBilin X.1 Y.1
    calc
      imaginaryPolarBilin (-X.1) (-Y.1) =
          -(imaginaryPolarBilin X.1 (-Y.1)) := by
        have hm := congrArg (fun f : Imaginary →ₗ[ℝ] ℝ => f (-Y.1))
          (map_neg imaginaryPolarBilin X.1)
        simpa using hm
      _ = -(-(imaginaryPolarBilin X.1 Y.1)) := by
        rw [LinearMap.map_neg]
      _ = imaginaryPolarBilin X.1 Y.1 := neg_neg _
  rw [hneg] at hanti
  linarith

theorem supportSymplectic_plus_isotropic
    (X Y : Support) (hX : X ∈ SupportPlus) (hY : Y ∈ SupportPlus) :
    supportSymplectic X Y = 0 := by
  have hmetric := supportMetric_plus_isotropic X Y hX hY
  unfold supportSymplectic
  rw [SupportPlus, Module.End.mem_eigenspace_iff] at hX
  rw [hX]
  simpa using hmetric

theorem supportSymplectic_minus_isotropic
    (X Y : Support) (hX : X ∈ SupportMinus) (hY : Y ∈ SupportMinus) :
    supportSymplectic X Y = 0 := by
  have hmetric := supportMetric_minus_isotropic X Y hX hY
  unfold supportSymplectic
  rw [SupportMinus, Module.End.mem_eigenspace_iff] at hX
  rw [hX]
  simp only [neg_one_smul]
  unfold supportMetric
  simp only [Submodule.coe_neg]
  change imaginaryPolarBilin (-X.1) Y.1 = 0
  rw [map_neg]
  change -supportMetric X Y = 0
  rw [hmetric, neg_zero]

theorem supportSymplectic_self_zero (X : Support) :
    supportSymplectic X X = 0 := by
  have h := supportSymplectic_skew X X
  linarith

end InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
