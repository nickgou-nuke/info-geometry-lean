import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
import InfoGeometry.Clifford.SplitCl44Complexification

open scoped TensorProduct

/-!
# Split Bott periodicity bridge

This file packages the repo-owned split Bott anchor without claiming any
K-theory suspension theorem that is not already present in source form.

The theorem surface is intentionally small:

* `Cl(4,4)` is the split Bott step at level `4`;
* the `ℂ`-base-change comparison is recorded separately;
* tensoring the `Cl(4,4)` anchor by `ℂ` preserves the split Bott step.
-/

namespace SplitBottPeriodicityBridge

open BottPeriodicity
open RealDoubledCliffordFiniteSpine
open SplitCl44Complexification

/-- The split Bott tensor target at level `3`. -/
abbrev BottTensor3 : Type :=
  BottTensor 3

/-- The `Cl(4,4)` anchor is exactly the split Bott step already owned by the tower. -/
noncomputable abbrev cl44_as_splitBottStep_anchor :
    SplitBottClifford 4 ≃ₐ[ℝ] BottTensor3 :=
  cl44_as_splitBottStep

theorem cl44_as_splitBottStep_anchor_eq_owner :
    cl44_as_splitBottStep_anchor = cl44_as_splitBottStep :=
  rfl

/-- The tensorized `ℂ`-extension of the `Cl(4,4)` anchor is available. -/
noncomputable abbrev cl44_complexification_tensor_anchor :
    ℂ ⊗[ℝ] SplitBottClifford 4 ≃ₐ[ℝ] ℂ ⊗[ℝ] BottTensor3 :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)
    cl44_as_splitBottStep

theorem cl44_complexification_tensor_anchor_eq_owner :
    cl44_complexification_tensor_anchor =
      Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)
        cl44_as_splitBottStep :=
  rfl

/-- The split `Cl(4,4)` complexification comparison is the owner base-change
equivalence, kept separate from the split Bott step. -/
noncomputable abbrev cl44_complexification_anchor :
    Cl44Complex ≃ₐ[ℂ] ℂ ⊗[ℝ] Cl44 :=
  cl44ComplexificationEquiv

theorem cl44_complexification_anchor_eq_owner :
    cl44_complexification_anchor = cl44ComplexificationEquiv :=
  rfl

/--
The split Bott `Cl(4,4)` anchor, its separate `ℂ`-comparison, and the
tensorized `ℂ`-comparison as concrete repo-owned equivalence data.
-/
noncomputable def splitBott_anchor_and_complexification :
    (SplitBottClifford 4 ≃ₐ[ℝ] BottTensor3) ×
      (ℂ ⊗[ℝ] SplitBottClifford 4 ≃ₐ[ℝ] ℂ ⊗[ℝ] BottTensor3) ×
        (Cl44Complex ≃ₐ[ℂ] ℂ ⊗[ℝ] Cl44) :=
  (cl44_as_splitBottStep_anchor,
    cl44_complexification_tensor_anchor,
    cl44_complexification_anchor)

end SplitBottPeriodicityBridge
