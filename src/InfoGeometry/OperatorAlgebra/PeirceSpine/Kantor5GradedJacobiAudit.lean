/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

/-!
# Audit of the proposed five-graded Kantor bracket

The component formulas in `ZornNambuDeRhamDiracKahlerPoset` have specialized
Cartan closure identities. This audit checks whether they satisfy the ordinary
Jacobi identity even on the even grades. A concrete matrix-ring witness below
shows that they do not, so those formulas cannot be promoted as a Lie
superalgebra bracket over arbitrary rings.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.Kantor5GradedJacobiAudit

open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Kantor5Graded

abbrev R := Matrix (Fin 2) (Fin 2) (ZMod 3)

def E : R := !![1, 0; 0, 0]

def X : Kantor5Graded R := injM2 ⟨E, 0, 0⟩

def Y : Kantor5Graded R := injM2 ⟨0, E, 0⟩

def Z : Kantor5Graded R := injP2 ⟨E, 0, 0⟩

/-- The even-even-even Jacobi identity fails for the proposed `kantorBracket`
over the noncommutative ring of two-by-two matrices over `ZMod 3`. -/
theorem jacobi_failure :
    kantorBracket X (kantorBracket Y Z) ≠
      kantorBracket (kantorBracket X Y) Z + kantorBracket Y (kantorBracket X Z) := by
  intro h
  have hc := congrArg (fun A : Kantor5Graded R => A.gm2.y 0 0) h
  norm_num [X, Y, Z, E, injM2, injP2, kantorBracket, Vec3.smulLeft,
    Vec3.smulRight, Vec3.symCross, Vec3.adCross, Vec3.cross, Vec3.dot,
    Matrix.mul_apply, Fin.sum_univ_two] at hc
  have h₂ : (2 : ZMod 3) ≠ 0 := by decide
  exact h₂ hc

end InfoGeometry.OperatorAlgebra.PeirceSpine.Kantor5GradedJacobiAudit
