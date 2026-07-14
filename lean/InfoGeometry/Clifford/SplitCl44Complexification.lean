import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import InfoGeometry.Clifford.BottPeriodicity

/-!
# Split `Cl(4,4)` complexification

This file records the honest comparison theorem available from mathlib:

`CliffordAlgebra (SplitBottQuad 4).baseChange ℂ ≃ₐ[ℂ] ℂ ⊗[ℝ] Cl(4,4)`.

This is the clean algebraic form of the split-real to complexified Clifford
bridge.  It does not yet identify the complexified algebra with a specific
paper-named `C(8)` owner surface.
-/

open scoped TensorProduct

namespace SplitCl44Complexification

open InfoGeometry.Clifford.BottPeriodicity

/-- The complexified split `Cl(4,4)` Clifford algebra. -/
abbrev Cl44Complex : Type :=
  CliffordAlgebra ((SplitBottQuad 4).baseChange ℂ)

/-- The split `Cl(4,4)` complexification is the tensor-product form over `ℂ`. -/
noncomputable def cl44ComplexificationEquiv :
    Cl44Complex ≃ₐ[ℂ] ℂ ⊗[ℝ] Cl44 :=
  CliffordAlgebra.equivBaseChange (A := ℂ) (Q := SplitBottQuad 4)

@[simp] theorem cl44ComplexificationEquiv_apply_ι
    (z : ℂ) (v : Carrier44) :
    cl44ComplexificationEquiv
        (CliffordAlgebra.ι (Q := (SplitBottQuad 4).baseChange ℂ) (z ⊗ₜ v))
      =
    z ⊗ₜ CliffordAlgebra.ι (Q := SplitBottQuad 4) v := by
  simpa [cl44ComplexificationEquiv] using
    (CliffordAlgebra.toBaseChange_ι (A := ℂ) (Q := SplitBottQuad 4) z v)

@[simp] theorem cl44ComplexificationEquiv_symm_tmul_ι
    (z : ℂ) (v : Carrier44) :
    (cl44ComplexificationEquiv.symm (z ⊗ₜ CliffordAlgebra.ι (Q := SplitBottQuad 4) v))
      =
    CliffordAlgebra.ι (Q := (SplitBottQuad 4).baseChange ℂ) (z ⊗ₜ v) := by
  simpa [cl44ComplexificationEquiv] using
    (CliffordAlgebra.ofBaseChange_tmul_ι (A := ℂ) (Q := SplitBottQuad 4) z v)

end SplitCl44Complexification
