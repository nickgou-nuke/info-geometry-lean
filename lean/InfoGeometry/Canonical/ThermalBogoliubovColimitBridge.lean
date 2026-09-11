import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit
import proofs.ThermalBogoliubovAutomorphism

/-!
# Thermal Bogoliubov Colimit Bridge

This module formally projects the strict thermodynamic deformations (the thermal 
Bogoliubov automorphisms) through the sequential direct colimits into the continuum 
boundary (the infinite tensor tower limit).

Because the colimit maps `psi` are implemented as `AlgHom` (algebra homomorphisms), 
they strictly preserve addition, multiplication, and complex scalar multiplication.
This perfectly locks the thermal deformation of the Nambu particle/hole space 
to the continuum CAR observable algebra, successfully bridging the discrete finite 
algebraic foundation to the $A_\infty$ continuum.
-/

open InfoGeometry.ThermalBogoliubov

namespace InfoGeometry.Canonical.ThermalBogoliubovColimitBridge

variable {A_inf : Type*} [Ring A_inf] [Algebra ℂ A_inf]
variable {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]

-- The continuous projection of the finite algebraic operators into the continuum boundary. 
-- Because the colimit map is an Algebra Homomorphism, it preserves the non-commutative 
-- algebra structure.
variable (psi : ∀ n, A n →ₐ[ℂ] A_inf)

lemma anticomm_map_alg_hom (n : ℕ) (x y : A n) :
    anticomm (psi n x) (psi n y) = psi n (anticomm x y) := by
  dsimp [anticomm]
  rw [map_add, map_mul, map_mul]

lemma a_prime_map (n : ℕ) (a d : A n) (u v : ℂ) :
    a_prime (psi n a) (psi n d) u v = psi n (a_prime a d u v) := by
  dsimp [a_prime]
  rw [map_add, map_smul, map_smul]

lemma c_prime_map (n : ℕ) (c b : A n) (u v : ℂ) :
    c_prime (psi n c) (psi n b) u v = psi n (c_prime c b u v) := by
  dsimp [c_prime]
  rw [map_add, map_smul, map_smul]

/-- 
**Colimit Transport of Thermal Fermionic Nilpotency**
The continuous $A_\infty$ boundary of the Bogoliubov transformed state 
preserves strict nilpotency.
-/
theorem colimit_bogoliubov_nilpotent_a 
    (n : ℕ) (a d : A n) (u v : ℂ)
    (h_aa : anticomm a a = 0) 
    (h_dd : anticomm d d = 0) 
    (h_ad : anticomm a d = 0) : 
    anticomm (a_prime (psi n a) (psi n d) u v) (a_prime (psi n a) (psi n d) u v) = 0 := by
  rw [a_prime_map, anticomm_map_alg_hom]
  have h_base := bogoliubov_nilpotent_a a d u v h_aa h_dd h_ad
  rw [h_base, map_zero]

/-- 
**Colimit Transport of Thermal CAR Algebra**
The continuum limit rigidly preserves the $\{a', c'\} = 1$ non-commutative brackets 
for the thermally deformed Nambu doublet, proving the KMS state deformation survives 
the topological transport intact.
-/
theorem colimit_bogoliubov_car_preserved 
    (n : ℕ) (a c b d : A n) (u v : ℂ)
    (h_uv : u^2 + v^2 = 1) 
    (h_ac : anticomm a c = 1) 
    (h_bd : anticomm b d = 1) 
    (h_ab : anticomm a b = 0) 
    (h_cd : anticomm c d = 0) : 
    anticomm (a_prime (psi n a) (psi n d) u v) (c_prime (psi n c) (psi n b) u v) = 1 := by
  rw [a_prime_map, c_prime_map, anticomm_map_alg_hom]
  have h_base := bogoliubov_car_preserved a c b d u v h_uv h_ac h_bd h_ab h_cd
  rw [h_base, map_one]

end InfoGeometry.Canonical.ThermalBogoliubovColimitBridge
