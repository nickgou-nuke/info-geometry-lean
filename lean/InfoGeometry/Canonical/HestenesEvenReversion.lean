/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesClPlus14
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-! # Native reversion on the real even spacetime algebra

These definitions retain their established namespace and statements. They
are independent of a matrix representation.
-/

noncomputable section
namespace HestenesKreinMatrixBridge
open HestenesCl14

def reverseEven (x : ClPlus14) : ClPlus14 :=
  ⟨CliffordAlgebra.reverse (x : Cl14),
    (CliffordAlgebra.reverse_mem_evenOdd_iff (Q := Q14)).2 x.2⟩

@[simp] theorem reverseEven_add (x y : ClPlus14) :
    reverseEven (x + y) = reverseEven x + reverseEven y := by
  apply Subtype.ext
  simp [reverseEven, map_add]

@[simp] theorem reverseEven_smul (r : ℝ) (x : ClPlus14) :
    reverseEven (r • x) = r • reverseEven x := by
  apply Subtype.ext
  simp [reverseEven, map_smul]

@[simp] theorem reverseEven_mul (x y : ClPlus14) :
    reverseEven (x * y) = reverseEven y * reverseEven x := by
  apply Subtype.ext
  exact CliffordAlgebra.reverse.map_mul (x : Cl14) (y : Cl14)

end HestenesKreinMatrixBridge
