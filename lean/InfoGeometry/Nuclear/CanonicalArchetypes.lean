import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.DirectSum.Basic

/-!
# Canonical Mathematical Archetypes of Chiral Non-Degeneracy

This module distills the "stream of consciousness" from the physical narrative 
into pure, canonical mathematical structures in Lean 4. It extracts the raw 
phenomenological concepts (e.g., QPNM, Nieh-Yan anomaly, frame dragging) 
and synthesizes them as properly ordered algebraic archetypes in a Mathlib-compatible style.

## Archetypes Extracted:
1. `KreinSpace`: The indefinite $\mathrm{Cl}(5,5)$ phase space geometry.
2. `FiveGradedLieAlgebra`: The 5-graded Cartan/Soloviev Lie algebra.
3. `TorsionalVolume`: The topological invariant as a trilinear volume form.
4. `TopologicalMassGap`: The non-degeneracy theorem formulated as a strict positivity bound.
-/

namespace InfoGeometry.Nuclear.CanonicalArchetypes

section KreinSpace

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/--
  ARCHETYPE 1: The Krein Space.
  Physically: The indefinite phase space enforcing the QRPA normalization $X^2 - Y^2 = 1$.
  Mathematically: A vector space equipped with an indefinite symmetric bilinear form, 
  which introduces a fundamental $\mathbb{Z}_2$ time-reversal asymmetry into the norm.
-/
structure KreinSpace where
  -- A bilinear map representing the indefinite metric signature.
  form : V →ₗ[K] V →ₗ[K] K

end KreinSpace

section GradedLieStructure

variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]

/--
  ARCHETYPE 2: The Cartan 5-Grading.
  Physically: The Soloviev QPNM grading from pair annihilation (-2) to pair creation (+2).
  Mathematically: A $\mathbb{Z}$-grading of a Lie algebra supported precisely on $\{-2, -1, 0, 1, 2\}$, 
  modeled here as a `Fin 5` indexed direct sum decomposition.
-/
structure FiveGradedLieAlgebra where
  grade : Fin 5 → Submodule R L
  -- Compatibility with the Lie bracket: [L_i, L_j] ⊆ L_{i+j}
  -- The index addition is modulated by the finite bound.
  bracket_compat : ∀ i j k : Fin 5, (i.val + j.val = k.val + 2) →
    ∀ x ∈ grade i, ∀ y ∈ grade j, ⁅x, y⁆ ∈ grade k

end GradedLieStructure

section TorsionalVolume

/--
  ARCHETYPE 3: The Nieh-Yan Torsional Volume.
  Physically: The emergent spacetime torsion contracted with the rotating frame connection.
  Mathematically: The scalar triple product interpreted algebraically as an alternating 
  trilinear form on a 3-dimensional module.
-/
def torsional_volume_form (omega j_pi j_nu : Fin 3 → ℝ) : ℝ :=
  omega 0 * (j_pi 1 * j_nu 2 - j_pi 2 * j_nu 1) +
  omega 1 * (j_pi 2 * j_nu 0 - j_pi 0 * j_nu 2) +
  omega 2 * (j_pi 0 * j_nu 1 - j_pi 1 * j_nu 0)

/--
  ARCHETYPE 4: The Massive Gap Bound (Symmetry Breaking).
  Physically: The topological mass gap mathematically forbidding Goldstone softening.
  Mathematically: A strict positivity bound derived from a non-vanishing trilinear volume.
-/
theorem strict_positivity_of_biased_dispersion
    (omega j_pi j_nu : Fin 3 → ℝ)
    (h_vol : torsional_volume_form omega j_pi j_nu ≠ 0)
    (G_eff : ℝ) (h_G : G_eff > 0)
    (omega_0 : ℝ)
    (omega_obs : ℝ)
    (h_dispersion : omega_obs^2 = omega_0^2 + (G_eff * torsional_volume_form omega j_pi j_nu)^2) :
    omega_obs^2 > 0 := by
  
  -- The effective anomalous bias is strictly non-zero
  have h_bias_ne_zero : G_eff * torsional_volume_form omega j_pi j_nu ≠ 0 :=
    mul_ne_zero (ne_of_gt h_G) h_vol
    
  -- The square of a non-zero real number is strictly positive
  have h_bias_sq_pos : (G_eff * torsional_volume_form omega j_pi j_nu)^2 > 0 :=
    sq_pos_of_ne_zero h_bias_ne_zero
    
  -- The mean-field symmetric potential is non-negative
  have h_omega_0_sq_nonneg : 0 ≤ omega_0^2 := sq_nonneg omega_0
  
  -- Therefore, the total observable mass gap squared must be strictly positive
  linarith

end TorsionalVolume

end InfoGeometry.Nuclear.CanonicalArchetypes
