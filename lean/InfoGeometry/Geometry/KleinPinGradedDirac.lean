/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.KleinPinDirac

/-!
# A graded geometric operator on the two smooth Klein sectors

The two actual smooth equivariance sectors form a real module. The grading
is positive on the first and negative on the second. The proved differential
Dirac maps between the sectors give an off-diagonal endomorphism of this
module. Its oddness is a native linear-map equality.

This is a grading of the doubled space of smooth cover sections. It is not
an assertion that the original irreducible spinor fibre carries the ambient
Clifford grading, and no Hilbert completion or closed-operator assertion is
inferred from the smooth-domain construction.
-/

noncomputable section

namespace InfoGeometry.Geometry.KleinPinDirac

open InfoGeometry.Topology.KleinAssociatedSpinors

/-- Expose the native additive groups of the two nested submodule carriers.
Both layers retain their inherited pointwise operations. -/
instance smoothSectionsAddCommGroup (sector : Bool) :
    AddCommGroup (smoothSections sector) := by
  letI : AddCommGroup (equivariantSections (monodromy sector)) :=
    Submodule.addCommGroup (equivariantSections (monodromy sector))
  exact Submodule.addCommGroup (smoothSections sector)

/-- The actual invariant smooth domain, retaining both deck-equivariance
sectors as separate summands. -/
abbrev TotalSections := smoothSections false × smoothSections true

/-- The explicit involutive grading of the doubled smooth-section domain. -/
def grading : Module.End ℝ TotalSections where
  toFun ψ := (ψ.1, -ψ.2)
  map_add' ψ χ := by
    apply Prod.ext
    · rfl
    · exact neg_add ψ.2 χ.2
  map_smul' r ψ := by
    apply Prod.ext
    · rfl
    · exact (smul_neg r ψ.2).symm

/-- The differential operator is off diagonal because its equivariance
sector interchange was proved from the chain rule. -/
def gradedDirac : Module.End ℝ TotalSections where
  toFun ψ := (diracSmoothLinear true ψ.2, diracSmoothLinear false ψ.1)
  map_add' ψ χ := by apply Prod.ext <;> simp
  map_smul' r ψ := by apply Prod.ext <;> simp

@[simp] theorem grading_apply (ψ : TotalSections) :
    grading ψ = (ψ.1, -ψ.2) := rfl

@[simp] theorem gradedDirac_apply (ψ : TotalSections) :
    gradedDirac ψ = (diracSmoothLinear true ψ.2, diracSmoothLinear false ψ.1) := rfl

/-- The grading really squares to the identity endomorphism. -/
theorem grading_sq : grading * grading = (1 : Module.End ℝ TotalSections) := by
  apply LinearMap.ext
  intro ψ
  apply Prod.ext
  · rfl
  · change - -ψ.2 = ψ.2
    exact neg_neg ψ.2

/-- The constructed differential operator is odd for the constructed
grading, with no supplied anticommutation hypothesis. -/
theorem grading_dirac_anticommute :
    grading * gradedDirac = -(gradedDirac * grading) := by
  apply LinearMap.ext
  intro ψ
  apply Prod.ext
  · change diracSmoothLinear true ψ.2 = -(diracSmoothLinear true (-ψ.2))
    rw [map_neg, neg_neg]
  · rfl

/-- The nonconstant smooth section from the differential owner gives an
explicit nonzero value of the graded differential operator. -/
theorem gradedDirac_cosine_nonzero :
    gradedDirac (cosineSmoothSection, 0) ≠ 0 := by
  intro h
  have hvalue := congrArg
    (fun ψ : TotalSections => ψ.2.val.val (1 / 4, 0)) h
  apply dirac_cosineField_nonzero
  simpa [gradedDirac, diracSmoothLinear, diracSection, cosineSmoothSection,
    cosineSection] using hvalue

theorem gradedDirac_ne_zero : gradedDirac ≠ 0 := by
  intro h
  apply gradedDirac_cosine_nonzero
  simp [h]

end InfoGeometry.Geometry.KleinPinDirac

end
