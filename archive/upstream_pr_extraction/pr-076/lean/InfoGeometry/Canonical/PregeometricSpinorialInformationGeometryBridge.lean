import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.Canonical.PregeometricSpinorialInformationGeometryBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Pre-Geometric Spinorial Prima Materia Algebraic Carrier Space S = ExteriorAlgebra R V. -/
def SpinorialPrimaMateria (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  ExteriorAlgebra R V

/-- **Definition**: Pre-Geometric Spinorial Linear Observable Endomorphism O ∈ Module.End R S. -/
def SpinorialObservable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  Module.End R (ExteriorAlgebra R V)

/-- **Definition**: Symmetric Logarithmic Derivative (SLD) Condition for Parametric Spinorial State Family ρ:
    2 • ∂_i ρ = ρ * L_i + L_i * ρ. -/
def IsSymmetricLogarithmicDerivative
    (d_rho : Module.End R (ExteriorAlgebra R V))
    (rho : Module.End R (ExteriorAlgebra R V))
    (L_i : Module.End R (ExteriorAlgebra R V)) : Prop :=
  (2 : R) • d_rho = rho.comp L_i + L_i.comp rho

/-- **Definition**: Pre-Geometric Quantum Fisher Information Candidate Form g_{ij}(ρ) = Tr(ρ * {L_i, L_j}).
    Operates via linear trace functional Tr : Module.End R S →ₗ[R] R. -/
def spinorialQFICandidateForm
    (tr : Module.End R (ExteriorAlgebra R V) →ₗ[R] R)
    (rho : Module.End R (ExteriorAlgebra R V))
    (L_i L_j : Module.End R (ExteriorAlgebra R V)) : R :=
  tr (rho.comp (L_i.comp L_j + L_j.comp L_i))

/-- **Theorem**: Symmetry of Pre-Geometric Quantum Fisher Information Candidate Form g_{ij}(ρ) = g_{ji}(ρ). -/
theorem spinorialQFICandidateForm_symmetric
    (tr : Module.End R (ExteriorAlgebra R V) →ₗ[R] R)
    (rho : Module.End R (ExteriorAlgebra R V))
    (L_i L_j : Module.End R (ExteriorAlgebra R V)) :
    spinorialQFICandidateForm tr rho L_i L_j = spinorialQFICandidateForm tr rho L_j L_i := by
  dsimp [spinorialQFICandidateForm]
  congr 1
  congr 1
  exact add_comm (L_i.comp L_j) (L_j.comp L_i)

/-- **Definition**: Pre-Geometric Spinorial Paired Entropy Expression S(ρ, ℓ) = -Tr(ρ * ℓ). -/
def spinorialPairedEntropy
    (tr : Module.End R (ExteriorAlgebra R V) →ₗ[R] R)
    (rho : Module.End R (ExteriorAlgebra R V))
    (ell : Module.End R (ExteriorAlgebra R V)) : R :=
  - tr (rho.comp ell)

/-- **Theorem**: Similarity Invariance of Pre-Geometric Spinorial Paired Entropy S(U ρ U⁻¹, U ℓ U⁻¹) = S(ρ, ℓ) under Two-Sided Invertibility and Cyclic Trace. -/
theorem spinorialPairedEntropy_similarity_invariant
    (tr : Module.End R (ExteriorAlgebra R V) →ₗ[R] R)
    (h_cyclic : ∀ A B : Module.End R (ExteriorAlgebra R V), tr (A.comp B) = tr (B.comp A))
    (rho ell U U_inv : Module.End R (ExteriorAlgebra R V))
    (h_left : U_inv.comp U = 1) :
    spinorialPairedEntropy tr (U.comp (rho.comp U_inv)) (U.comp (ell.comp U_inv)) =
      spinorialPairedEntropy tr rho ell := by
  dsimp [spinorialPairedEntropy]
  congr 1
  have h_comp : (U.comp (rho.comp U_inv)).comp (U.comp (ell.comp U_inv)) =
                U.comp ((rho.comp ell).comp U_inv) := by
    ext x
    dsimp
    rw [← LinearMap.comp_apply U_inv U]
    rw [h_left]
    rfl
  rw [h_comp]
  rw [h_cyclic U ((rho.comp ell).comp U_inv)]
  rw [LinearMap.comp_assoc]
  rw [h_left]
  have h_id : (rho.comp ell).comp (1 : Module.End R (ExteriorAlgebra R V)) = rho.comp ell := by
    ext x
    rfl
  rw [h_id]

end InfoGeometry.Canonical.PregeometricSpinorialInformationGeometryBridge
