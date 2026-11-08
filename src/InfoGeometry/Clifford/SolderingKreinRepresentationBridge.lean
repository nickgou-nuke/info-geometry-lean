/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SolderingCl11MatrixBridge
import InfoGeometry.Clifford.SplitAtomInvolutions
import InfoGeometry.Krein.Clifford

/-!
# Soldering `Cl(1,1)` roots in the doubled-real Krein representation

The soldering owner identifies two Clifford elements with the real matrix
CAR roots. `Cl11Matrix` identifies its quadratic form with `splitQ11`, and
Mathlib's isometry equivalence transports the Clifford algebra to the native
split-form carrier. This file composes that transport with the repository's
operator representation on `HilbertDoubled`; the latter retains the doubled
real Krein structure.
-/

noncomputable section

namespace InfoGeometry.Clifford.SolderingKreinRepresentationBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.SolderingCl11MatrixBridge
open InfoGeometry.Projective.SplitQuaternionRankOneProjective
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The quaternion-defined `Cl(1,1)` algebra acts on the repository's
doubled-real Krein space by transport through the equality of quadratic forms. -/
def cl11KreinRep : CliffordAlgebra q11 →ₐ[ℝ]
    (HilbertDoubled E →L[ℝ] HilbertDoubled E) :=
  (cl11RepHilbert (E := E)).comp q11ToSplitClifford.toAlgHom

/-- The transport sends every `q11` generator to the same-coordinate generator
of the native `splitQ11` carrier before applying the Krein representation. -/
@[simp] theorem cl11KreinRep_ι (v : Vec11) :
    cl11KreinRep (E := E) (CliffordAlgebra.ι q11 v) =
      cl11RepHilbert (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) := by
  simp [cl11KreinRep]

/-- The raising soldering root acts square-zero on the doubled-real Krein
space, by transporting the already-proved Clifford CAR root. -/
theorem cl11KreinRep_rootPlus_sq :
    cl11KreinRep (E := E) rootPlusCl11 * cl11KreinRep (E := E) rootPlusCl11 = 0 := by
  have h := congrArg (cl11KreinRep (E := E)) rootPlusCl11_sq_zero
  simpa only [map_mul, map_zero] using h

/-- The lowering soldering root acts square-zero on the doubled-real Krein
space, by transporting the already-proved Clifford CAR root. -/
theorem cl11KreinRep_rootMinus_sq :
    cl11KreinRep (E := E) rootMinusCl11 * cl11KreinRep (E := E) rootMinusCl11 = 0 := by
  have h := congrArg (cl11KreinRep (E := E)) rootMinusCl11_sq_zero
  simpa only [map_mul, map_zero] using h

/-- The two soldering roots satisfy CAR as bounded operators on the doubled-real
Krein space. -/
theorem cl11KreinRep_root_anticommutator :
    cl11KreinRep (E := E) rootPlusCl11 * cl11KreinRep (E := E) rootMinusCl11 +
      cl11KreinRep (E := E) rootMinusCl11 * cl11KreinRep (E := E) rootPlusCl11 = 1 := by
  have h := congrArg (cl11KreinRep (E := E)) rootCl11_anticommutator
  simpa only [map_add, map_mul, map_one] using h

/-- The SplitAtom raising seed and the soldering raising root are the same
element of the native Clifford carrier. The comparison is made after mapping
to the shared real matrix carrier. -/
theorem splitAtom_raisingCl_eq_rootPlusCl11 :
    InfoGeometry.Clifford.SplitAtom.raisingCl = rootPlusCl11 := by
  have hmatrix : InfoGeometry.Clifford.SplitAtom.raising = rootPlus := by
    rw [InfoGeometry.Clifford.SplitAtom.raising_eq_half_I_sub_K, rootPlus_eq_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Clifford.SplitAtom.I,
        InfoGeometry.Clifford.SplitAtom.K, Eminus, J1,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  apply cl11EquivMat.injective
  calc
    cl11EquivMat InfoGeometry.Clifford.SplitAtom.raisingCl =
        InfoGeometry.Clifford.SplitAtom.raising := by
      simp [InfoGeometry.Clifford.SplitAtom.raisingCl]
    _ = rootPlus := hmatrix
    _ = cl11EquivMat rootPlusCl11 := cl11EquivMat_rootPlusCl11.symm

/-- The SplitAtom lowering seed agrees with the soldering lowering root. Both
are defined using the explicitly transported real matrix transpose dual. -/
theorem splitAtom_loweringCl_eq_rootMinusCl11 :
    InfoGeometry.Clifford.SplitAtom.loweringCl = rootMinusCl11 := by
  have hmatrix :
      star InfoGeometry.Clifford.SplitAtom.raising = rootMinus := by
    rw [InfoGeometry.Clifford.SplitAtom.raising_adjoint, rootMinus_eq_matrix]
  apply cl11EquivMat.injective
  calc
    cl11EquivMat InfoGeometry.Clifford.SplitAtom.loweringCl =
        star InfoGeometry.Clifford.SplitAtom.raising := by
      simp [InfoGeometry.Clifford.SplitAtom.loweringCl]
    _ = rootMinus := hmatrix
    _ = cl11EquivMat rootMinusCl11 := cl11EquivMat_rootMinusCl11.symm

/-- The doubled-real Krein representation sends the SplitAtom seeds to the
same operators as the soldering roots. This is an intertwining statement for
the selected matrix-transpose dual, not an identification with Clifford star. -/
theorem cl11KreinRep_splitAtom_roots :
    cl11KreinRep (E := E) InfoGeometry.Clifford.SplitAtom.raisingCl =
        cl11KreinRep (E := E) rootPlusCl11 ∧
      cl11KreinRep (E := E) InfoGeometry.Clifford.SplitAtom.loweringCl =
        cl11KreinRep (E := E) rootMinusCl11 := by
  exact ⟨congrArg (cl11KreinRep (E := E)) splitAtom_raisingCl_eq_rootPlusCl11,
    congrArg (cl11KreinRep (E := E)) splitAtom_loweringCl_eq_rootMinusCl11⟩

end InfoGeometry.Clifford.SolderingKreinRepresentationBridge

end
