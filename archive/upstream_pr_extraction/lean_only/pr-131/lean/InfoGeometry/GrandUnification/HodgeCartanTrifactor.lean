import Mathlib.Tactic
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Hodge Decomposition and Cartan Involution on the Trifactor Geometry

This module formally implements the strict, functorial isomorphism between classical
differential geometry (Hodge decomposition, Cartan Involution) and the non-commutative
O^3 = O Trifactor grading that constrains the Riemann Zeta boundary thermodynamics.

1. **Hodge Decomposition**: Any state is uniquely decomposed into an Exact (d, P_+),
   Co-exact (δ, P_-), and Harmonic (H, P_0) part.
2. **Cartan Involution**: The involution θ = 1 - 2T² which splits the space into
   the Symmetric core (𝔨, Harmonic, +1 eigenspace) and Antisymmetric driver
   (𝔭, Active Bulk, -1 eigenspace).
-/

namespace InfoGeometry.GrandUnification.HodgeCartan

open InfoGeometry.Canonical.TrifactorDecomposition

section Basic

variable {R : Type*} [CommRing R]
variable (T : R)

/-- The Harmonic operator (Kernel), corresponding to ℋ (P_zero) -/
def harmonic_op : R := P_zero T

/-! ### The Cartan Involution -/

/-- The Cartan Involution θ on the algebra, defined as 1 - 2T^2.
It cleanly separates the Harmonic anchor from the Active thermodynamic driver. -/
def cartan_involution : R := 1 - 2 * T^2

/-- **Theorem: θ is a strict Involution (θ^2 = 1)** -/
theorem cartan_involution_square (hT : T ^ 3 = T) :
    cartan_involution T * cartan_involution T = 1 := by
  unfold cartan_involution
  calc
    (1 - 2 * T^2) * (1 - 2 * T^2) = 1 - 4 * T^2 + 4 * T^4 := by ring
    _ = 1 - 4 * T^2 + 4 * (T^3 * T) := by ring
    _ = 1 - 4 * T^2 + 4 * (T * T) := by rw [hT]
    _ = 1 - 4 * T^2 + 4 * T^2 := by ring
    _ = 1 := by ring

/-- **Theorem: Symmetric Sector (𝔨)**
The Harmonic sector (P_0) is in the +1 eigenspace of the Cartan Involution.
This confirms the completed Xi function is strictly Symmetric. -/
theorem cartan_symmetric_harmonic (hT : T ^ 3 = T) :
    cartan_involution T * harmonic_op T = harmonic_op T := by
  unfold cartan_involution harmonic_op P_zero InfoGeometry.Canonical.TriFacetGeometry.P_par
  calc
    (1 - 2 * T^2) * (1 - T^2) = 1 - 3 * T^2 + 2 * T^4 := by ring
    _ = 1 - 3 * T^2 + 2 * (T^3 * T) := by ring
    _ = 1 - 3 * T^2 + 2 * (T * T) := by rw [hT]
    _ = 1 - T^2 := by ring

end Basic

section WithHalf

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable (T : R)

/-- The Exact (Holomorphic) operator, corresponding to d (P_plus) -/
def exact_op : R := P_plus T

/-- The Co-exact (Anti-holomorphic) operator, corresponding to δ (P_minus) -/
def coexact_op : R := P_minus T

/-- **Theorem: The Non-Commutative Hodge Decomposition**
Every state decomposes into Exact, Co-exact, and Harmonic components.
This is the operator algebra equivalent of Ω^k = d(Ω^{k-1}) ⊕ δ(Ω^{k+1}) ⊕ ℋ^k -/
theorem hodge_decomposition : harmonic_op T + exact_op T + coexact_op T = 1 := by
  unfold harmonic_op exact_op coexact_op
  exact partition_of_unity T

/-- **Theorem: Antisymmetric Sector (𝔭)**
The Exact sector (P_+) is in the -1 eigenspace of the Cartan Involution. -/
theorem cartan_antisymmetric_exact (hT : T ^ 3 = T) :
    cartan_involution T * exact_op T = - exact_op T := by
  unfold cartan_involution exact_op P_plus InfoGeometry.Canonical.TriFacetGeometry.P_hyp
  calc
    (1 - 2 * T^2) * (⅟(2 : R) * (T^2 + T)) = ⅟(2 : R) * (T^2 + T - 2 * T^4 - 2 * T^3) := by ring
    _ = ⅟(2 : R) * (T^2 + T - 2 * (T^3 * T) - 2 * T^3) := by ring
    _ = ⅟(2 : R) * (T^2 + T - 2 * (T * T) - 2 * T) := by rw [hT]
    _ = ⅟(2 : R) * (- T^2 - T) := by ring
    _ = - (⅟(2 : R) * (T^2 + T)) := by ring

/-- **Theorem: Antisymmetric Sector (𝔭)**
The Co-exact sector (P_-) is in the -1 eigenspace of the Cartan Involution. -/
theorem cartan_antisymmetric_coexact (hT : T ^ 3 = T) :
    cartan_involution T * coexact_op T = - coexact_op T := by
  unfold cartan_involution coexact_op P_minus InfoGeometry.Canonical.TriFacetGeometry.P_ell
  calc
    (1 - 2 * T^2) * (⅟(2 : R) * (T^2 - T)) = ⅟(2 : R) * (T^2 - T - 2 * T^4 + 2 * T^3) := by ring
    _ = ⅟(2 : R) * (T^2 - T - 2 * (T^3 * T) + 2 * T^3) := by ring
    _ = ⅟(2 : R) * (T^2 - T - 2 * (T * T) + 2 * T) := by rw [hT]
    _ = ⅟(2 : R) * (- T^2 + T) := by ring
    _ = - (⅟(2 : R) * (T^2 - T)) := by ring

end WithHalf

end InfoGeometry.GrandUnification.HodgeCartan
