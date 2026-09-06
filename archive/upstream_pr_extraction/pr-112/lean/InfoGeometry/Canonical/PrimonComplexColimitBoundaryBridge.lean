import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.BoundaryBondSquare
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-!
# Real-to-complex matrix-colimit and boundary bridge

The real Primon matrix tower and the complex canonical matrix tower have the
same prefix/block coordinates.  This file records their entrywise
complexification, its bonding compatibility, and the induced maps on the
existing algebraic colimits.  No completion or analytic identification is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimonComplexColimitBoundaryBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.BoundaryBondSquare
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-! The diagonal part is the canonical function-valued readout on the
prefix inverse-limit carrier.  This is intentionally separate from the full
matrix-to-boundary-operator representation above. -/

def diagonalCylinder (n : ℕ) (A : MatrixStage n) :
    (ℕ → Bool) → ℂ :=
  cylinder n (fun w => (A w w : ℂ))

@[simp] theorem diagonalCylinder_apply
    (n : ℕ) (A : MatrixStage n) (x : ℕ → Bool) :
    diagonalCylinder n A x = (A (boundaryPrefix n x) (boundaryPrefix n x) : ℂ) := rfl

theorem diagonalCylinder_bond_compatible
    (n : ℕ) (A : MatrixStage n) :
    diagonalCylinder (n + 1) (matrixBond n A) =
      diagonalCylinder n A := by
  funext x
  rw [diagonalCylinder_apply, diagonalCylinder_apply]
  simp [matrixBond, matrixBondFun]
  rw [boundaryPrefix_succ_eq_prefixSucc]

/-! Transport the cylinder readout to the actual categorical inverse-limit
object, not merely to its Cantor-space presentation. -/

def diagonalCylinderOnInverseLimit (n : ℕ) (A : MatrixStage n) :
    (↑(limit prefixDiagram) → ℂ) :=
  fun z => diagonalCylinder n A (prefixBoundaryLimitIso.inv z)

@[simp] theorem diagonalCylinderOnInverseLimit_apply
    (n : ℕ) (A : MatrixStage n) (z : ↑(limit prefixDiagram)) :
    diagonalCylinderOnInverseLimit n A z =
      diagonalCylinder n A (prefixBoundaryLimitIso.inv z) := rfl

theorem diagonalCylinderOnInverseLimit_bond_compatible
    (n : ℕ) (A : MatrixStage n) :
    diagonalCylinderOnInverseLimit (n + 1) (matrixBond n A) =
      diagonalCylinderOnInverseLimit n A := by
  funext z
  rw [diagonalCylinderOnInverseLimit_apply,
    diagonalCylinderOnInverseLimit_apply,
    diagonalCylinder_bond_compatible]

/-! The same inverse-limit readout for the canonical complex matrix tower. -/

def complexDiagonalCylinder (n : ℕ)
    (A : ComplexMatrixStage.Stage n) : (ℕ → Bool) → ℂ :=
  cylinder n (fun w => A w w)

@[simp] theorem complexDiagonalCylinder_apply
    (n : ℕ) (A : ComplexMatrixStage.Stage n) (x : ℕ → Bool) :
    complexDiagonalCylinder n A x =
      A (boundaryPrefix n x) (boundaryPrefix n x) := rfl

theorem complexDiagonalCylinder_bond_compatible
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    complexDiagonalCylinder (n + 1) (ComplexMatrixStage.bondFun n A) =
      complexDiagonalCylinder n A := by
  funext x
  rw [complexDiagonalCylinder_apply, complexDiagonalCylinder_apply]
  simp [ComplexMatrixStage.bondFun]
  rw [boundaryPrefix_succ_eq_prefixSucc]

def complexDiagonalCylinderOnInverseLimit (n : ℕ)
    (A : ComplexMatrixStage.Stage n) :
    (↑(limit prefixDiagram) → ℂ) :=
  fun z => complexDiagonalCylinder n A (prefixBoundaryLimitIso.inv z)

@[simp] theorem complexDiagonalCylinderOnInverseLimit_apply
    (n : ℕ) (A : ComplexMatrixStage.Stage n)
    (z : ↑(limit prefixDiagram)) :
    complexDiagonalCylinderOnInverseLimit n A z =
      complexDiagonalCylinder n A (prefixBoundaryLimitIso.inv z) := rfl

theorem complexDiagonalCylinderOnInverseLimit_bond_compatible
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    complexDiagonalCylinderOnInverseLimit (n + 1)
        (ComplexMatrixStage.bondFun n A) =
      complexDiagonalCylinderOnInverseLimit n A := by
  funext z
  rw [complexDiagonalCylinderOnInverseLimit_apply,
    complexDiagonalCylinderOnInverseLimit_apply,
    complexDiagonalCylinder_bond_compatible]

/-! A full-colimit readout: the canonical normalized trace is viewed as a
constant complex-valued function on the inverse-limit carrier. -/

abbrev InverseLimitFunction := (↑(limit prefixDiagram) → ℂ)

noncomputable def primonTraceOnInverseLimit :
    PrimonUHFAlgebra →ₗ[ℝ] InverseLimitFunction where
  toFun X := fun _ => (colimitTrace X : ℂ)
  map_add' X Y := by
    funext z
    simp [colimitTrace.map_add]
  map_smul' c X := by
    funext z
    simp [colimitTrace.map_smul]

@[simp] theorem primonTraceOnInverseLimit_stage
    (n : ℕ) (A : MatrixStage n) (z : ↑(limit prefixDiagram)) :
    primonTraceOnInverseLimit (toColimit n A) z =
      (normalizedTrace n A : ℂ) := by
  simp [primonTraceOnInverseLimit]

theorem primonTraceOnInverseLimit_bond
    (n : ℕ) (A : MatrixStage n) :
    primonTraceOnInverseLimit (toColimit (n + 1) (matrixBond n A)) =
      primonTraceOnInverseLimit (toColimit n A) := by
  rw [show toColimit (n + 1) (matrixBond n A) = toColimit n A by
    exact toColimit_bond n A]

noncomputable def complexTraceOnInverseLimit :
    ComplexMatrixStage.Colimit →ₗ[ℂ] InverseLimitFunction where
  toFun X := fun _ => normalizedTraceColimit X
  map_add' X Y := by
    funext z
    simp [normalizedTraceColimit.map_add]
  map_smul' c X := by
    funext z
    simp [normalizedTraceColimit.map_smul]

@[simp] theorem complexTraceOnInverseLimit_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n)
    (z : ↑(limit prefixDiagram)) :
      complexTraceOnInverseLimit
        (ComplexMatrixStage.toColimit n A) z =
      InfoGeometry.Canonical.GenuineMatrixStageMorphism.normalizedTrace n A := by
  simp [complexTraceOnInverseLimit]

theorem complexTraceOnInverseLimit_bond
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    complexTraceOnInverseLimit
        (ComplexMatrixStage.toColimit (n + 1)
          (ComplexMatrixStage.bondFun n A)) =
      complexTraceOnInverseLimit
        (ComplexMatrixStage.toColimit n A) := by
  rw [show ComplexMatrixStage.toColimit (n + 1)
        (ComplexMatrixStage.bondFun n A) =
      ComplexMatrixStage.toColimit n A by
    exact ComplexMatrixStage.toColimit_bond n A]

def complexifyStage (n : ℕ) : MatrixStage n →+* ComplexMatrixStage.Stage n where
  toFun A := fun i j => (A i j : ℂ)
  map_one' := by
    ext i j
    dsimp [Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' := by
    intro A B
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' := by
    intro A B
    ext i j
    simp

@[simp] theorem complexifyStage_apply
    (n : ℕ) (A : MatrixStage n) (i j : BitWord n) :
    complexifyStage n A i j = (A i j : ℂ) := rfl

theorem complexifyStage_bond_compatible
    (n : ℕ) (A : MatrixStage n) :
    complexifyStage (n + 1) (matrixBond n A) =
      ComplexMatrixStage.bondFun n (complexifyStage n A) := by
  ext v w
  dsimp [complexifyStage, matrixBond, matrixBondFun,
    ComplexMatrixStage.bondFun]
  split_ifs <;> rfl

def complexifyCone : ∀ n : ℕ,
    MatrixStage n →+* ComplexMatrixStage.Colimit :=
  fun n => (ComplexMatrixStage.toColimit n).comp (complexifyStage n)

theorem complexifyCone_compatible :
    CompatibleCone matrixBond complexifyCone := by
  intro n A
  change ComplexMatrixStage.toColimit (n + 1)
      (complexifyStage (n + 1) (matrixBond n A)) =
    ComplexMatrixStage.toColimit n (complexifyStage n A)
  rw [complexifyStage_bond_compatible n A]
  change ComplexMatrixStage.toColimit (n + 1)
      (ComplexMatrixStage.bond n (complexifyStage n A)) = _
  exact ComplexMatrixStage.toColimit_bond n (complexifyStage n A)

noncomputable def primonToComplexColimit :
    PrimonUHFAlgebra →+* ComplexMatrixStage.Colimit :=
  directLimitLift matrixBond complexifyCone complexifyCone_compatible

@[simp] theorem primonToComplexColimit_stage
    (n : ℕ) (A : MatrixStage n) :
    primonToComplexColimit (toColimit n A) =
      ComplexMatrixStage.toColimit n (complexifyStage n A) := by
  rfl

noncomputable def primonToBoundary :
    PrimonUHFAlgebra →+*
      InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.BoundaryOperator :=
  boundaryRepColimit.comp primonToComplexColimit

@[simp] theorem primonToBoundary_stage
    (n : ℕ) (A : MatrixStage n) :
    primonToBoundary (toColimit n A) =
      InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.boundaryRep n
        (complexifyStage n A) := by
  rfl

theorem primonTrace_complexification_matches_complexTrace
    (n : ℕ) (A : MatrixStage n) (z : ↑(limit prefixDiagram)) :
    primonTraceOnInverseLimit (toColimit n A) z =
      complexTraceOnInverseLimit
        (primonToComplexColimit (toColimit n A)) z := by
  rw [primonTraceOnInverseLimit_stage,
    primonToComplexColimit_stage,
    complexTraceOnInverseLimit_stage]
  simp [InfoGeometry.Algebra.PrimonColimitAlgebra.normalizedTrace,
    InfoGeometry.Algebra.PrimonColimitAlgebra.rawTrace,
    InfoGeometry.Canonical.GenuineMatrixStageMorphism.normalizedTrace,
    complexifyStage, Matrix.trace]

@[simp] theorem complexTraceOnInverseLimit_one
    (z : ↑(limit prefixDiagram)) :
    complexTraceOnInverseLimit (1 : ComplexMatrixStage.Colimit) z = 1 := by
  change normalizedTraceColimit (1 : ComplexMatrixStage.Colimit) = 1
  exact normalizedTraceColimit_one

theorem complexTraceOnInverseLimit_cyclic
    (X Y : ComplexMatrixStage.Colimit) (z : ↑(limit prefixDiagram)) :
    complexTraceOnInverseLimit (X * Y) z =
      complexTraceOnInverseLimit (Y * X) z := by
  change normalizedTraceColimit (X * Y) =
    normalizedTraceColimit (Y * X)
  exact normalizedTraceColimit_cyclic X Y

theorem complexTraceOnInverseLimit_star
    (X : ComplexMatrixStage.Colimit) (z : ↑(limit prefixDiagram)) :
    complexTraceOnInverseLimit (star X) z =
      starRingEnd ℂ (complexTraceOnInverseLimit X z) := by
  change normalizedTraceColimit (star X) =
    starRingEnd ℂ (normalizedTraceColimit X)
  exact normalizedTraceColimit_star X

theorem complexTraceOnInverseLimit_positive
    (X : ComplexMatrixStage.Colimit) (z : ↑(limit prefixDiagram)) :
    0 ≤ (complexTraceOnInverseLimit (star X * X) z).re := by
  change 0 ≤ (normalizedTraceColimit (star X * X)).re
  exact normalizedTraceColimit_positive X

theorem continuous_complexTraceOnInverseLimit
    (X : ComplexMatrixStage.Colimit) :
    Continuous (complexTraceOnInverseLimit X) := by
  exact continuous_const

theorem continuous_primonTraceOnInverseLimit
    (X : PrimonUHFAlgebra) :
    Continuous (primonTraceOnInverseLimit X) := by
  exact continuous_const

noncomputable def complexTraceOnInverseLimitTopCat
    (X : ComplexMatrixStage.Colimit) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℂ :=
  { hom' :=
      { toFun := complexTraceOnInverseLimit X
        continuous_toFun := continuous_complexTraceOnInverseLimit X } }

noncomputable def primonTraceOnInverseLimitTopCat
    (X : PrimonUHFAlgebra) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℂ :=
  { hom' :=
      { toFun := primonTraceOnInverseLimit X
        continuous_toFun := continuous_primonTraceOnInverseLimit X } }

@[simp] theorem complexTraceOnInverseLimitTopCat_apply
    (X : ComplexMatrixStage.Colimit) (z : ↑(limit prefixDiagram)) :
    complexTraceOnInverseLimitTopCat X z =
      complexTraceOnInverseLimit X z := rfl

@[simp] theorem primonTraceOnInverseLimitTopCat_apply
    (X : PrimonUHFAlgebra) (z : ↑(limit prefixDiagram)) :
    primonTraceOnInverseLimitTopCat X z =
      primonTraceOnInverseLimit X z := rfl

@[simp] theorem complexTraceOnInverseLimitTopCat_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n)
    (z : ↑(limit prefixDiagram)) :
    complexTraceOnInverseLimitTopCat
        (ComplexMatrixStage.toColimit n A) z =
      InfoGeometry.Canonical.GenuineMatrixStageMorphism.normalizedTrace n A := by
  exact complexTraceOnInverseLimit_stage n A z

@[simp] theorem primonTraceOnInverseLimitTopCat_stage
    (n : ℕ) (A : MatrixStage n) (z : ↑(limit prefixDiagram)) :
    primonTraceOnInverseLimitTopCat (toColimit n A) z =
      (normalizedTrace n A : ℂ) := by
  exact primonTraceOnInverseLimit_stage n A z

end InfoGeometry.Canonical.PrimonComplexColimitBoundaryBridge
