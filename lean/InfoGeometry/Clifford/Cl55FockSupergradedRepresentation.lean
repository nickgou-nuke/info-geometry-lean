import InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
import InfoGeometry.Clifford.Cl55SupergradedModularAction
import InfoGeometry.Krein.TwoSheetKreinIdealBridge
import InfoGeometry.Algebra.SupergradedBracket

/-!
# Supergraded Clifford action on the exterior spinor

This owner transports the existing Cl(5,5) operator-number grades and
superbracket to the native 32-dimensional exterior-spinor endomorphisms.  It
also records the algebraic conjugation law for any involutive grade-zero
symmetry.  A specific Krein fundamental symmetry and a TKK identification
remain separate obligations.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55FockSupergradedRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.OperatorAlgebra

/-- The canonical Cl(5,5) action on the coordinate realization of the
exterior spinor. -/
noncomputable def cl55FockAlgEquiv :
    Cl55 ≃ₐ[ℝ] Module.End ℝ SCoord :=
  neutralCliffordAlgEquiv.symm.trans neutralCliffordFockAlgEquiv

/-- The operator-number grade transported to exterior-spinor endomorphisms. -/
def fockGradeSubmodule (k : ℤ) :
    Submodule ℝ (Module.End ℝ SCoord) :=
  (cl55GradeSubmodule k).map cl55FockAlgEquiv.toLinearMap

/-- The superbracket representation on the exterior spinor preserves the
sum of the source operator-number grades. -/
theorem fock_superBracket_mem_grade_sum
    {k l : ℤ} {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    superBracket (cl55GradeParity k) (cl55GradeParity l)
        (cl55FockAlgEquiv X) (cl55FockAlgEquiv Y) ∈
      fockGradeSubmodule (k + l) := by
  have hbr :
      superBracket (cl55GradeParity k) (cl55GradeParity l)
          (cl55FockAlgEquiv X) (cl55FockAlgEquiv Y) =
        cl55FockAlgEquiv
          (superBracket (cl55GradeParity k) (cl55GradeParity l) X Y) := by
    cases cl55GradeParity k <;> cases cl55GradeParity l <;>
      simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
        InfoGeometry.Algebra.SupergradedBracket.commutator,
        InfoGeometry.Algebra.SupergradedBracket.anticommutator,
        map_mul]
  rw [hbr]
  exact Submodule.mem_map_of_mem
    (cl55_superBracket_mem_grade_sum hX hY)

/-- Algebraic involution conjugation transported to the exterior-spinor
endomorphisms. -/
def fockKreinConjugate (eta : Cl55)
    (T : Module.End ℝ SCoord) : Module.End ℝ SCoord :=
  cl55FockAlgEquiv eta * T * cl55FockAlgEquiv eta

@[simp] theorem fockKreinConjugate_apply (eta : Cl55)
    (T : Module.End ℝ SCoord) :
    fockKreinConjugate eta T =
      cl55FockAlgEquiv eta * T * cl55FockAlgEquiv eta := rfl

/-- Conjugation by an involution acts involutively on the represented spinor
endomorphisms. -/
theorem fockKreinConjugate_involutive (eta : Cl55)
    (heta : eta * eta = 1) (T : Module.End ℝ SCoord) :
    fockKreinConjugate eta (fockKreinConjugate eta T) = T := by
  have hetaF : cl55FockAlgEquiv eta * cl55FockAlgEquiv eta = 1 := by
    calc
      cl55FockAlgEquiv eta * cl55FockAlgEquiv eta =
          cl55FockAlgEquiv (eta * eta) := by simp [map_mul]
      _ = 1 := by simp [heta]
  change (cl55FockAlgEquiv eta) *
      ((cl55FockAlgEquiv eta) * T * (cl55FockAlgEquiv eta)) *
      (cl55FockAlgEquiv eta) = T
  calc
    _ = (cl55FockAlgEquiv eta * cl55FockAlgEquiv eta) * T *
        (cl55FockAlgEquiv eta * cl55FockAlgEquiv eta) := by noncomm_ring
    _ = T := by rw [hetaF, one_mul, mul_one]

/-- An involutive degree-zero conjugating element preserves every represented
operator-number grade. -/
theorem fockKreinConjugate_mem_grade
    (eta : Cl55) (heta0 : eta ∈ cl55GradeSubmodule 0)
    {k : ℤ} {X : Cl55} (hX : X ∈ cl55GradeSubmodule k) :
    fockKreinConjugate eta (cl55FockAlgEquiv X) ∈ fockGradeSubmodule k := by
  have heta' : HasOperatorGrade numberOperator55 eta 0 := heta0
  have hX' : HasOperatorGrade numberOperator55 X k := hX
  have hleft : HasOperatorGrade numberOperator55 (eta * X) k := by
    simpa using (grade_mul heta' hX')
  have hconj : HasOperatorGrade numberOperator55 (eta * X * eta) k := by
    simpa using (grade_mul hleft heta')
  have hconj' : eta * X * eta ∈ cl55GradeSubmodule k := by
    change HasOperatorGrade numberOperator55 (eta * X * eta) k
    exact hconj
  have hrepr : fockKreinConjugate eta (cl55FockAlgEquiv X) =
      cl55FockAlgEquiv (eta * X * eta) := by
    simp [fockKreinConjugate, map_mul]
  rw [hrepr]
  exact Submodule.mem_map_of_mem hconj'

/-- Additivity of the transported involution conjugation. -/
theorem kreinConjugate_add {A : Type*} [Ring A] (eta X Y : A) :
    InfoGeometry.Krein.kreinConjugate eta (X + Y) =
      InfoGeometry.Krein.kreinConjugate eta X +
        InfoGeometry.Krein.kreinConjugate eta Y := by
  simp [InfoGeometry.Krein.kreinConjugate, mul_add, add_mul]

theorem kreinConjugate_sub {A : Type*} [Ring A] (eta X Y : A) :
    InfoGeometry.Krein.kreinConjugate eta (X - Y) =
      InfoGeometry.Krein.kreinConjugate eta X -
        InfoGeometry.Krein.kreinConjugate eta Y := by
  simp [InfoGeometry.Krein.kreinConjugate, mul_sub, sub_mul]

theorem kreinConjugate_superBracket {A : Type*} [Ring A]
    (eta : A) (heta : eta * eta = 1) (px py : Bool)
    (X Y : A) :
    InfoGeometry.Krein.kreinConjugate eta
        (superBracket px py X Y) =
      superBracket px py
        (InfoGeometry.Krein.kreinConjugate eta X)
        (InfoGeometry.Krein.kreinConjugate eta Y) := by
  cases px <;> cases py <;>
    simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      kreinConjugate_add, kreinConjugate_sub,
      InfoGeometry.Krein.kreinConjugate_mul eta heta]

theorem fockKreinConjugate_superBracket
    (eta : Cl55) (heta : eta * eta = 1)
    (px py : Bool) (X Y : Cl55) :
    fockKreinConjugate eta
        (superBracket px py (cl55FockAlgEquiv X) (cl55FockAlgEquiv Y)) =
      superBracket px py
        (fockKreinConjugate eta (cl55FockAlgEquiv X))
        (fockKreinConjugate eta (cl55FockAlgEquiv Y)) := by
  have hetaF : cl55FockAlgEquiv eta * cl55FockAlgEquiv eta = 1 := by
    calc
      cl55FockAlgEquiv eta * cl55FockAlgEquiv eta =
          cl55FockAlgEquiv (eta * eta) := by simp [map_mul]
      _ = 1 := by simp [heta]
  exact kreinConjugate_superBracket (A := Module.End ℝ SCoord)
      (cl55FockAlgEquiv eta) hetaF px py
      (cl55FockAlgEquiv X) (cl55FockAlgEquiv Y)

end InfoGeometry.Clifford.Cl55FockSupergradedRepresentation
