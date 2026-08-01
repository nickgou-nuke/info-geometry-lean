import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ChainCovectorContractionBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ExteriorContractionCARBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Contraction Annihilation Operator ι_λ on 1-forms. -/
def contraction1 (lambda : V →ₗ[R] R) (v : V) : R :=
  lambda v

/-- **Definition**: Iterated Contraction Annihilation Operator ι_λ ι_μ on 2-forms. -/
def contraction2 (lambda mu : V →ₗ[R] R) (v1 v2 : V) : R :=
  lambda v1 * mu v2 - lambda v2 * mu v1

/-- **Theorem**: Contraction Annihilation Operator Nilpotency ι_λ ι_λ = 0. -/
theorem contraction_sq_zero (lambda : V →ₗ[R] R) (v1 v2 : V) :
    contraction2 lambda lambda v1 v2 = 0 := by
  dsimp [contraction2]
  ring

/-- **Theorem**: Contraction Annihilation Anti-Commutativity {ι_λ, ι_μ} = 0. -/
theorem contraction_contraction_anticommute
    (lambda mu : V →ₗ[R] R) (v1 v2 : V) :
    contraction2 lambda mu v1 v2 + contraction2 mu lambda v1 v2 = 0 := by
  dsimp [contraction2]
  ring


end InfoGeometry.Canonical.ExteriorContractionCARBridge
