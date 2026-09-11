import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs

/-!
# Checked Freudenthal identities for the cubic Jordan/Albert layer

This file contains only kernel-checked Freudenthal infrastructure:

* the Freudenthal identity `(X#)# = N(X) • X` on the diagonal cubic Jordan
  subalgebra, imported from `CubicJordanOs` and restated here;
* the order-three cyclic coordinate symmetry of Albert matrices;
* the explicit quadratic polarization cross-term definition.

The non-diagonal split-octonionic Albert identity is not asserted here without
its missing representative and orbit proofs.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanFreudenthal

/-- Cyclic shift of Albert matrix entries. -/
def cyclicShift (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₂
    α₂ := X.α₃
    α₃ := X.α₁
    z₁ := X.z₂
    z₂ := X.z₃
    z₃ := X.z₁ }

/-- The cyclic Albert shift has order three. -/
theorem cyclicShift_three (X : AlbertMatrix) :
    cyclicShift (cyclicShift (cyclicShift X)) = X := by
  apply ext_albert <;> rfl

/-- The cyclic Albert shift is injective. -/
theorem cyclicShift_injective : Function.Injective cyclicShift := by
  intro X Y h
  have h3 : cyclicShift (cyclicShift (cyclicShift X)) =
      cyclicShift (cyclicShift (cyclicShift Y)) := by rw [h]
  simpa [cyclicShift_three] using h3

/-- Componentwise addition of Albert matrices. -/
def addAlbert (X Y : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₁ + Y.α₁
    α₂ := X.α₂ + Y.α₂
    α₃ := X.α₃ + Y.α₃
    z₁ := subZ X.z₁ (negZ Y.z₁)
    z₂ := subZ X.z₂ (negZ Y.z₂)
    z₃ := subZ X.z₃ (negZ Y.z₃) }

/-- Componentwise subtraction of Albert matrices. -/
def subAlbert (X Y : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₁ - Y.α₁
    α₂ := X.α₂ - Y.α₂
    α₃ := X.α₃ - Y.α₃
    z₁ := subZ X.z₁ Y.z₁
    z₂ := subZ X.z₂ Y.z₂
    z₃ := subZ X.z₃ Y.z₃ }

/-- Polarized adjoint cross-term, defined by the standard quadratic polarization formula. -/
def crossProduct (X Y : AlbertMatrix) : AlbertMatrix :=
  subAlbert (adjointQuad (addAlbert X Y))
    (addAlbert (adjointQuad X) (adjointQuad Y))

/-- Definitional polarization identity for the adjoint quadratic map. -/
theorem adjointQuad_polarization (X Y : AlbertMatrix) :
    crossProduct X Y =
      subAlbert (adjointQuad (addAlbert X Y))
        (addAlbert (adjointQuad X) (adjointQuad Y)) := by
  rfl

/-- The Freudenthal identity on the diagonal cubic Jordan subalgebra. -/
theorem freudenthal_diagonal (α₁ α₂ α₃ : ℝ) :
    adjointQuad (adjointQuad
      { α₁ := α₁, α₂ := α₂, α₃ := α₃,
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
      (normCubic
        { α₁ := α₁, α₂ := α₂, α₃ := α₃,
          z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
      { α₁ := α₁, α₂ := α₂, α₃ := α₃,
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  exact freudenthal_identity_diagonal
    { α₁ := α₁, α₂ := α₂, α₃ := α₃,
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } rfl rfl rfl

/-- Checked Freudenthal architecture: diagonal identity, cyclic order-three symmetry,
and the explicit polarization definition are all kernel proofs. -/
theorem freudenthal_architecture :
    (∀ α₁ α₂ α₃ : ℝ,
      adjointQuad (adjointQuad
        { α₁ := α₁, α₂ := α₂, α₃ := α₃,
          z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
        (normCubic
          { α₁ := α₁, α₂ := α₂, α₃ := α₃,
            z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
        { α₁ := α₁, α₂ := α₂, α₃ := α₃,
          z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) ∧
    (∀ X : AlbertMatrix, cyclicShift (cyclicShift (cyclicShift X)) = X) ∧
    Function.Injective cyclicShift ∧
    (∀ X Y : AlbertMatrix,
      crossProduct X Y =
        subAlbert (adjointQuad (addAlbert X Y))
          (addAlbert (adjointQuad X) (adjointQuad Y))) := by
  exact ⟨freudenthal_diagonal, cyclicShift_three, cyclicShift_injective,
    adjointQuad_polarization⟩

end InfoGeometry.Algebra.CubicJordanFreudenthal
