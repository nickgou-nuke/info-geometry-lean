import Mathlib.Tactic
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure

open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
open InfoGeometry.MajoranaPfaffianNaturalClosure

namespace InfoGeometry.Quantum.AZDeclaredOneDimensionalTable

/-- Labels used in the declared one-dimensional AZ table. -/
inductive OneDimensionalTableEntry : Type
  | zero
  | zModTwo
  | integers

/-- The expected stable classification-group label assigned by the AZ table in
spatial dimension one.  This lookup is not yet a classifier of phases. -/
def declaredOneDimensionalEntry : AZClass → OneDimensionalTableEntry
  | AZClass.A    => .zero
  | AZClass.AIII => .integers
  | AZClass.AI   => .zero
  | AZClass.BDI  => .integers
  | AZClass.D    => .zModTwo
  | AZClass.DIII => .zModTwo
  | AZClass.AII  => .zero
  | AZClass.CII  => .integers
  | AZClass.C    => .zero
  | AZClass.CI   => .zero

/-- The class-D entry in the declared table is the `zModTwo` label. -/
theorem classD_declared_entry :
    declaredOneDimensionalEntry AZClass.D = .zModTwo := rfl

/-- The class-BDI entry in the declared table is the `integers` label. -/
theorem classBDI_declared_entry :
    declaredOneDimensionalEntry AZClass.BDI = .integers := rfl

/-- The concrete nilpotent CAR annihilation matrix. -/
abbrev boundaryAnnihilation : Matrix (Fin 2) (Fin 2) ℝ :=
  annihilationR

/-- The concrete CAR annihilation matrix squares to zero. -/
theorem boundary_annihilation_sq :
    boundaryAnnihilation * boundaryAnnihilation = 0 :=
  annihilationR_sq

end InfoGeometry.Quantum.AZDeclaredOneDimensionalTable
