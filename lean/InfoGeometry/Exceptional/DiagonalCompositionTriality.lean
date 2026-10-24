/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.CompositionTriality
import Mathlib.Algebra.Lie.Subalgebra

/-! # The diagonal Lie subalgebra of linear local-triality triples -/

namespace InfoGeometry.Exceptional.CompositionTriality.TrialityTriple

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)

/-- The equal-component locus is a genuine Lie subalgebra. No cyclic action is assumed. -/
def diagonalLieSubalgebra : LieSubalgebra R (TrialityTriple mul) where
  carrier := {T | T.t₁ = T.t₂ ∧ T.t₁ = T.t₃}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro T U hT hU
    change T.t₁ + U.t₁ = T.t₂ + U.t₂ ∧ T.t₁ + U.t₁ = T.t₃ + U.t₃
    exact ⟨congrArg₂ HAdd.hAdd hT.1 hU.1, congrArg₂ HAdd.hAdd hT.2 hU.2⟩
  smul_mem' := by
    intro r T hT
    change r • T.t₁ = r • T.t₂ ∧ r • T.t₁ = r • T.t₃
    exact ⟨congrArg (r • ·) hT.1, congrArg (r • ·) hT.2⟩
  lie_mem' := by
    intro T U hT hU
    change T.t₁ * U.t₁ - U.t₁ * T.t₁ = T.t₂ * U.t₂ - U.t₂ * T.t₂ ∧
      T.t₁ * U.t₁ - U.t₁ * T.t₁ = T.t₃ * U.t₃ - U.t₃ * T.t₃
    exact ⟨congrArg₂ (fun a b : Module.End R A => a*b-b*a) hT.1 hU.1,
      congrArg₂ (fun a b : Module.End R A => a*b-b*a) hT.2 hU.2⟩

/-- Two scalar directions satisfy local triality without being norm-skew. -/
def scalarTriple (a b : R) : TrialityTriple mul where
  t₁ := (a + b) • LinearMap.id
  t₂ := a • LinearMap.id
  t₃ := b • LinearMap.id
  triality x y := by
    change (a + b) • mul x y = mul (a • x) y + mul x (b • y)
    simp [map_smul, add_smul]

end InfoGeometry.Exceptional.CompositionTriality.TrialityTriple
