import InfoGeometry.Canonical.ChiralZornFiniteSymmetry
import InfoGeometry.Canonical.NonAbelianDihedralSymmetry12
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Canonical/chiral Zorn coordinate equivalence

The repository contains two concrete presentations of the same eight-slot
Zorn multiplication.  This file supplies the missing native equivalence and
transports the already proved orientation-corrected colour automorphisms to
the canonical `ZornMatrix` carrier.  It does not identify the unsigned
hexagon reindexing with an algebra automorphism.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Physics.Octonion
open InfoGeometry.Physics.Octonion.ChiralZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

variable {R : Type*} [CommRing R]

/-- Coordinate identification between the canonical and chiral Zorn records. -/
def canonicalChiralLinearEquiv :
    ZornMatrix R ≃ₗ[R] ChiralZornMatrix R where
  toFun X :=
    { n_plus := X.a
      n_minus := X.b
      sigma_plus := X.x
      sigma_minus := X.y }
  invFun X :=
    { a := X.n_plus
      b := X.n_minus
      x := X.sigma_plus
      y := X.sigma_minus }
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl
  map_add' X Y := by cases X; cases Y; rfl
  map_smul' c X := by cases X; rfl

@[simp] theorem canonicalChiralLinearEquiv_apply (X : ZornMatrix R) :
    canonicalChiralLinearEquiv X =
      { n_plus := X.a, n_minus := X.b,
        sigma_plus := X.x, sigma_minus := X.y } := rfl

@[simp] theorem canonicalChiralLinearEquiv_symm_apply
    (X : ChiralZornMatrix R) :
    canonicalChiralLinearEquiv.symm X =
      { a := X.n_plus, b := X.n_minus,
        x := X.sigma_plus, y := X.sigma_minus } := rfl

theorem canonicalChiralLinearEquiv_mul (X Y : ZornMatrix R) :
    canonicalChiralLinearEquiv (X * Y) =
      canonicalChiralLinearEquiv X * canonicalChiralLinearEquiv Y := by
  apply ChiralZornMatrix.ext
  · simp [ZornMatrix.mul, ChiralZornMatrix.mul, colorDot,
      InfoGeometry.Canonical.ZornMatrix.dot, smul_eq_mul, mul_comm] <;> ring
  · simp [ZornMatrix.mul, ChiralZornMatrix.mul, colorDot,
      InfoGeometry.Canonical.ZornMatrix.dot, smul_eq_mul, mul_comm] <;> ring
  · funext c
    fin_cases c <;>
      simp [ZornMatrix.mul, ZornMatrix.cross, ChiralZornMatrix.mul,
        colorCross, nextColor, prevColor, smul_eq_mul, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail, mul_comm]
    <;> ring
  · funext c
    fin_cases c <;>
      simp [ZornMatrix.mul, ZornMatrix.cross, ChiralZornMatrix.mul,
        colorCross, nextColor, prevColor, smul_eq_mul, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail, mul_comm]
    <;> ring

/-- The coordinate equivalence is an actual nonassociative algebra equivalence. -/
def canonicalChiralMulEquiv :
    ZornMatrix R ≃* ChiralZornMatrix R where
  toEquiv := canonicalChiralLinearEquiv.toEquiv
  map_mul' := canonicalChiralLinearEquiv_mul

@[simp] theorem canonicalChiralMulEquiv_apply (X : ZornMatrix R) :
    canonicalChiralMulEquiv X = canonicalChiralLinearEquiv X := rfl

theorem canonicalChiralMulEquiv_map_mul (X Y : ZornMatrix R) :
    canonicalChiralMulEquiv (X * Y) =
      canonicalChiralMulEquiv X * canonicalChiralMulEquiv Y := by
  exact canonicalChiralLinearEquiv_mul X Y

/-- The native order-three colour automorphism on the canonical carrier. -/
def canonicalColorCycle : ZornMatrix R ≃* ZornMatrix R :=
  canonicalChiralMulEquiv.trans
    (rotateMulEquiv.trans canonicalChiralMulEquiv.symm)

/-- The native orientation-corrected reflection on the canonical carrier. -/
def canonicalColorReflection : ZornMatrix R ≃* ZornMatrix R :=
  canonicalChiralMulEquiv.trans
    (reflectMulEquiv.trans canonicalChiralMulEquiv.symm)

theorem canonicalColorCycle_map_mul (X Y : ZornMatrix R) :
    canonicalColorCycle (X * Y) =
      canonicalColorCycle X * canonicalColorCycle Y := by
  exact (canonicalColorCycle : ZornMatrix R ≃* ZornMatrix R).map_mul X Y

theorem canonicalColorReflection_map_mul (X Y : ZornMatrix R) :
    canonicalColorReflection (X * Y) =
      canonicalColorReflection X * canonicalColorReflection Y := by
  exact (canonicalColorReflection : ZornMatrix R ≃* ZornMatrix R).map_mul X Y

/-! ## Linear readout into the native composition-automorphism owner -/

/-- The canonical colour cycle is also real-linear.  The multiplicative
equivalence above is the algebraic source; this is only its native linear
readout needed by the composition-automorphism subgroup. -/
noncomputable def canonicalColorCycleLinearAut :
    CanonicalZorn ≃ₗ[ℝ] CanonicalZorn where
  toFun := canonicalColorCycle
  invFun := canonicalColorCycle.symm
  left_inv X := canonicalColorCycle.symm_apply_apply X
  right_inv X := canonicalColorCycle.apply_symm_apply X
  map_add' X Y := by
    ext <;>
      simp [canonicalColorCycle, canonicalChiralMulEquiv,
        ChiralZornMatrix.rotateMulEquiv_apply,
        ChiralZornMatrix.rotateColor, InfoGeometry.Physics.Octonion.prevColor]
  map_smul' r X := by
    change canonicalColorCycle (r • X) = r • canonicalColorCycle X
    change canonicalChiralMulEquiv.symm
      (rotateMulEquiv (canonicalChiralMulEquiv (r • X))) =
      r • canonicalChiralMulEquiv.symm
        (rotateMulEquiv (canonicalChiralMulEquiv X))
    ext <;>
      simp [canonicalChiralMulEquiv, ChiralZornMatrix.rotateMulEquiv_apply,
      ChiralZornMatrix.rotateColor, InfoGeometry.Physics.Octonion.prevColor,
      Equiv.smul_def, ZornMatrix.coordEquiv, Pi.smul_apply]

@[simp] theorem canonicalColorCycleLinearAut_apply (X : CanonicalZorn) :
    canonicalColorCycleLinearAut X = canonicalColorCycle X := rfl

/-- The canonical orientation-corrected reflection is also real-linear. -/
noncomputable def canonicalColorReflectionLinearAut :
    CanonicalZorn ≃ₗ[ℝ] CanonicalZorn where
  toFun := canonicalColorReflection
  invFun := canonicalColorReflection.symm
  left_inv X := canonicalColorReflection.symm_apply_apply X
  right_inv X := canonicalColorReflection.apply_symm_apply X
  map_add' X Y := by
    ext <;>
      simp [canonicalColorReflection, canonicalChiralMulEquiv,
        ChiralZornMatrix.reflectMulEquiv_apply,
        ChiralZornMatrix.reflect, ChiralZornMatrix.reflectColor]
  map_smul' r X := by
    change canonicalColorReflection (r • X) = r • canonicalColorReflection X
    change canonicalChiralMulEquiv.symm
      (reflectMulEquiv (canonicalChiralMulEquiv (r • X))) =
      r • canonicalChiralMulEquiv.symm
        (reflectMulEquiv (canonicalChiralMulEquiv X))
    ext <;>
      simp [canonicalChiralMulEquiv, ChiralZornMatrix.reflectMulEquiv_apply,
      ChiralZornMatrix.reflect, ChiralZornMatrix.reflectColor,
      Equiv.smul_def, ZornMatrix.coordEquiv, Pi.smul_apply]

@[simp] theorem canonicalColorReflectionLinearAut_apply (X : CanonicalZorn) :
    canonicalColorReflectionLinearAut X = canonicalColorReflection X := rfl

/-- The transported cycle is a member of the native canonical composition
automorphism subgroup. -/
noncomputable def canonicalColorCycleCompositionAut :
    realZornCompositionAut where
  val := canonicalColorCycleLinearAut
  property X Y := by
    simpa only [canonicalColorCycleLinearAut_apply] using
      canonicalColorCycle_map_mul X Y

@[simp] theorem canonicalColorCycleCompositionAut_apply (X : CanonicalZorn) :
    (canonicalColorCycleCompositionAut : CanonicalLinearAut) X =
      canonicalColorCycle X := rfl

/-- The transported reflection is a member of the native canonical
composition automorphism subgroup. -/
noncomputable def canonicalColorReflectionCompositionAut :
    realZornCompositionAut where
  val := canonicalColorReflectionLinearAut
  property X Y := by
    simpa only [canonicalColorReflectionLinearAut_apply] using
      canonicalColorReflection_map_mul X Y

@[simp] theorem canonicalColorReflectionCompositionAut_apply (X : CanonicalZorn) :
    (canonicalColorReflectionCompositionAut : CanonicalLinearAut) X =
      canonicalColorReflection X := rfl

@[simp] theorem canonicalColorCycleCompositionAut_preserves_detZ (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        ((canonicalColorCycleCompositionAut : CanonicalLinearAut) X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X :=
  realZornCompositionAut_preserves_det canonicalColorCycleCompositionAut X

@[simp] theorem canonicalColorReflectionCompositionAut_preserves_detZ
    (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        ((canonicalColorReflectionCompositionAut : CanonicalLinearAut) X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X :=
  realZornCompositionAut_preserves_det canonicalColorReflectionCompositionAut X

/-! ## The actual finite automorphism action

The native colour/sheet automorphisms generate the order-six dihedral action
(`DihedralGroup 3`).  This remains separate from the unsigned order-twelve
hexagon action on labels, which does not preserve circular multiplication.
-/

noncomputable def canonicalDihedralAction :
    DihedralGroup 3 →* (CanonicalZorn ≃* CanonicalZorn) where
  toFun g :=
    canonicalChiralMulEquiv.trans
      ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
        (A := ℝ) g).trans canonicalChiralMulEquiv.symm)
  map_one' := by
    change canonicalChiralMulEquiv.trans
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) 1).trans canonicalChiralMulEquiv.symm) = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    change canonicalChiralMulEquiv.trans
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) (g * h)).trans canonicalChiralMulEquiv.symm) =
      (canonicalChiralMulEquiv.trans
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) g).trans canonicalChiralMulEquiv.symm)) *
      (canonicalChiralMulEquiv.trans
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) h).trans canonicalChiralMulEquiv.symm))
    apply MulEquiv.ext
    intro X
    change canonicalChiralMulEquiv.symm
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) (g * h)) (canonicalChiralMulEquiv X)) =
      canonicalChiralMulEquiv.symm
        ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
          (A := ℝ) g)
          ((InfoGeometry.Physics.Octonion.ChiralZornMatrix.dihedralAction
            (A := ℝ) h) (canonicalChiralMulEquiv X)))
    rw [map_mul]
    rfl

@[simp] theorem canonicalDihedralAction_r (X : CanonicalZorn) :
    canonicalDihedralAction (.r 1) X = canonicalColorCycle X := by
  change canonicalChiralMulEquiv.symm
      (InfoGeometry.Physics.Octonion.ChiralZornMatrix.rotateMulEquiv
        (canonicalChiralMulEquiv X)) = _
  rfl

@[simp] theorem canonicalDihedralAction_sr_zero (X : CanonicalZorn) :
    canonicalDihedralAction (.sr 0) X = canonicalColorReflection X := by
  change canonicalChiralMulEquiv.symm
      (InfoGeometry.Physics.Octonion.ChiralZornMatrix.reflectMulEquiv
        (canonicalChiralMulEquiv X)) = _
  rfl

theorem canonicalColorCycle_order_three (X : ZornMatrix R) :
    canonicalColorCycle (canonicalColorCycle (canonicalColorCycle X)) = X := by
  change canonicalChiralMulEquiv.symm
      (rotateMulEquiv (canonicalChiralMulEquiv
        (canonicalChiralMulEquiv.symm
          (rotateMulEquiv (canonicalChiralMulEquiv
            (canonicalChiralMulEquiv.symm
              (rotateMulEquiv (canonicalChiralMulEquiv X)))))))) = X
  simp only [MulEquiv.apply_symm_apply]
  simp only [ChiralZornMatrix.rotateMulEquiv_apply]
  rw [ChiralZornMatrix.rotateColor_three]
  exact canonicalChiralMulEquiv.symm_apply_apply X

theorem canonicalColorReflection_involutive (X : ZornMatrix R) :
    canonicalColorReflection (canonicalColorReflection X) = X := by
  change canonicalChiralMulEquiv.symm
      (reflectMulEquiv (canonicalChiralMulEquiv
        (canonicalChiralMulEquiv.symm
          (reflectMulEquiv (canonicalChiralMulEquiv X))))) = X
  simp only [MulEquiv.apply_symm_apply]
  simp only [ChiralZornMatrix.reflectMulEquiv_apply]
  rw [ChiralZornMatrix.reflect_two]
  exact canonicalChiralMulEquiv.symm_apply_apply X

theorem canonicalColorReflection_cycle_reflection (X : ZornMatrix R) :
    canonicalColorReflection (canonicalColorCycle (canonicalColorReflection X)) =
      canonicalColorCycle (canonicalColorCycle X) := by
  change canonicalChiralMulEquiv.symm
      (reflectMulEquiv (rotateMulEquiv (reflectMulEquiv
        (canonicalChiralMulEquiv X)))) =
    canonicalChiralMulEquiv.symm
      (rotateMulEquiv (rotateMulEquiv (canonicalChiralMulEquiv X)))
  exact congrArg canonicalChiralMulEquiv.symm
    (ChiralZornMatrix.reflectMulEquiv_rotateMulEquiv_reflectMulEquiv_apply
      (canonicalChiralMulEquiv X))

theorem canonicalColorCycle_cube :
    canonicalColorCycle * canonicalColorCycle * canonicalColorCycle =
      (1 : ZornMatrix R ≃* ZornMatrix R) := by
  apply MulEquiv.ext
  intro X
  change canonicalColorCycle (canonicalColorCycle (canonicalColorCycle X)) = X
  exact canonicalColorCycle_order_three X

theorem canonicalColorReflection_square :
    canonicalColorReflection * canonicalColorReflection =
      (1 : ZornMatrix R ≃* ZornMatrix R) := by
  apply MulEquiv.ext
  intro X
  change canonicalColorReflection (canonicalColorReflection X) = X
  exact canonicalColorReflection_involutive X

theorem canonicalColorReflection_cycle_reflection_equiv :
    (canonicalColorReflection (R := R)) * (canonicalColorCycle (R := R)) *
        (canonicalColorReflection (R := R)) =
      (canonicalColorCycle (R := R)) * (canonicalColorCycle (R := R)) := by
  apply MulEquiv.ext
  intro X
  change canonicalColorReflection
      (canonicalColorCycle (canonicalColorReflection X)) =
    canonicalColorCycle (canonicalColorCycle X)
  exact canonicalColorReflection_cycle_reflection X

end
end InfoGeometry.Canonical
