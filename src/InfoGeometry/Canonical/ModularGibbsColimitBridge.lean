import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Modular Gibbs Colimit Bridge

Routes the algebraic translation of the Gibbs physical Hamiltonian into the
relative modular Hamiltonian (negative log density) $K = H + \Phi I$ through
the repository's Hestenes--Krein/categorical direct-colimit lane.

Instead of adding an external continuum equivalence, we pull the strict
algebraic identity from the finite
prime/matrix stage `A n` through the categorical direct limit into `A_inf`.
-/

namespace InfoGeometry.Canonical.ModularGibbsColimitBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)] [∀ n, Module ℝ (A n)] [∀ n, One (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf] [Module ℝ A_inf] [One A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

/-- A compatible sequence of Modular Hamiltonians along the tensor tower. -/
structure CompatibleModularTower where
  stage : ∀ n, ModularHamiltonianData (A n)
  inf : ModularHamiltonianData A_inf
  /-- The modular Hamiltonian (negative log density) commutes with the colimit injection. -/
  modular_compat : ∀ n,
    inf.negativeLogDensity = psi n ((stage n).negativeLogDensity)
  /-- The physical Gibbs Hamiltonian commutes with the colimit injection. -/
  gibbs_compat : ∀ n,
    inf.gibbsHamiltonian = psi n ((stage n).gibbsHamiltonian)
  /-- The scalar partition potential is preserved universally. -/
  scalar_compat : ∀ n,
    inf.logPartitionScalar = (stage n).logPartitionScalar
  /-- The colimit injection preserves the algebraic identity operator. -/
  identity_compat : ∀ n,
    psi n (1 : A n) = (1 : A_inf)
  /-- The colimit injection is a real linear map, preserving scalar multiplication. -/
  linear_compat : ∀ (n : ℕ) (c : ℝ) (x : A n),
    psi n (c • x) = c • psi n x

/--
The repository closure route for the Relative Modular Law:
if the relative modular Hamiltonian identity `K = H + Φ I` holds algebraically
at the finite matrix/quantum stage `n`, the categorical direct colimit
transports this exact algebraic translation into `A_inf` without proving or
postulating an external continuum theorem.
-/
theorem relative_modular_survives_colimit 
    (tower : CompatibleModularTower A A_inf psi)
    (n : ℕ)
    (h_finite_modular : (tower.stage n).negativeLogDensity = 
        (tower.stage n).gibbsHamiltonian + (tower.stage n).logPartitionScalar • (1 : A n)) :
    tower.inf.negativeLogDensity = 
        tower.inf.gibbsHamiltonian + tower.inf.logPartitionScalar • (1 : A_inf) := by
  -- Expand the infinite expressions back to the finite colimit injections
  rw [tower.modular_compat n]
  rw [tower.gibbs_compat n]
  rw [tower.scalar_compat n]
  -- Use the finite algebraic identity
  rw [h_finite_modular]
  -- Push the linear operations through the colimit map
  simp only [map_add]
  rw [tower.linear_compat n]
  rw [tower.identity_compat n]

end InfoGeometry.Canonical.ModularGibbsColimitBridge
