import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Eigenspace.Basic
import InfoGeometry.Algebra.FourthRootSpectralProjectors
import InfoGeometry.Dynamics.CyclicRotatingProfile

namespace InfoGeometry.Algebra.CyclotomicPhaseReadout

noncomputable section

def phase (order : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (order : ℂ))

theorem phase_primitive (order : ℕ) (nonzero : order ≠ 0) :
    IsPrimitiveRoot (phase order) order :=
  Complex.isPrimitiveRoot_exp order nonzero

theorem phase_pow_order (order : ℕ) (positive : 0 < order) :
    phase order ^ order = 1 :=
  (phase_primitive order (Nat.ne_of_gt positive)).pow_eq_one

theorem phase_ne_one (order : ℕ) (nontrivial : 1 < order) :
    phase order ≠ 1 :=
  (phase_primitive order (by omega)).ne_one nontrivial

theorem phase_sum (order : ℕ) (nontrivial : 1 < order) :
    ∑ exponent ∈ Finset.range order, phase order ^ exponent = 0 :=
  (phase_primitive order (by omega)).geom_sum_eq_zero nontrivial

theorem triangular_phase : phase 3 ^ 2 + phase 3 + 1 = 0 :=
  InfoGeometry.Dynamics.CyclicRotatingProfile.triangular_phase_equation
    (phase_primitive 3 (by norm_num))

def phaseWeight (order exponent : ℕ) : ℂ :=
  (order : ℂ)⁻¹ * phase order ^ exponent

theorem phaseWeight_sum (order : ℕ) (nontrivial : 1 < order) :
    ∑ exponent ∈ Finset.range order, phaseWeight order exponent = 0 := by
  unfold phaseWeight
  rw [← Finset.mul_sum, phase_sum order nontrivial, mul_zero]

theorem scalar_weight_not_idempotent :
    phaseWeight 3 0 * phaseWeight 3 0 ≠ phaseWeight 3 0 := by
  norm_num [phaseWeight]

open FourthRootSpectralProjectors

variable {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
variable [IsScalarTower ℂ ℂ Space]

theorem projector_range_eq_eigenspace (operator : Module.End ℂ Space)
    (periodic : operator ^ 4 = 1) (sector : Fin 4) :
    LinearMap.range (projector operator sector) =
      Module.End.eigenspace operator (root4 sector) := by
  ext vector
  constructor
  · rintro ⟨preimage, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    have eigen := congrArg (fun linear : Module.End ℂ Space => linear preimage)
      (generator_mul_projector operator periodic sector)
    exact eigen
  · intro membership
    refine ⟨vector, ?_⟩
    exact (projector_fixed_iff operator periodic sector vector).mpr
      (Module.End.mem_eigenspace_iff.mp membership)

end

end InfoGeometry.Algebra.CyclotomicPhaseReadout
