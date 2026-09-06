import Mathlib
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Canonical.Cl11CommonFockCarrier

/-!
# Disjoint CAR bilinears

The CAR source supplies anticommutation between distinct sites.  The elementary
associative-algebra consequence below is the precise theorem-safe meaning of
disjoint even bilinears commuting.  No canonical CCR identification is made.
-/

namespace InfoGeometry.Canonical.DisjointCARBilinear

open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
open InfoGeometry.Canonical.Cl11CommonFockCarrier

variable {A : Type*} [Ring A]

/-- Two quadratic CAR monomials commute when every generator in one monomial
anticommutes with every generator in the other. -/
theorem mul_mul_comm_of_four_anticommute
    (a b c d : A)
    (hac : a * c + c * a = 0)
    (had : a * d + d * a = 0)
    (hbc : b * c + c * b = 0)
    (hbd : b * d + d * b = 0) :
    (a * b) * (c * d) = (c * d) * (a * b) := by
  have hac' : a * c = -(c * a) := by
    exact eq_neg_of_add_eq_zero_left hac
  have had' : a * d = -(d * a) := by
    exact eq_neg_of_add_eq_zero_left had
  have hbc' : b * c = -(c * b) := by
    exact eq_neg_of_add_eq_zero_left hbc
  have hbd' : b * d = -(d * b) := by
    exact eq_neg_of_add_eq_zero_left hbd
  calc
    (a * b) * (c * d) = a * (b * c) * d := by noncomm_ring
    _ = a * (-(c * b)) * d := by rw [hbc']
    _ = -(a * c) * b * d := by noncomm_ring
    _ = -(-(c * a)) * b * d := by rw [hac']
    _ = c * a * b * d := by noncomm_ring
    _ = c * a * (b * d) := by noncomm_ring
    _ = c * a * (-(d * b)) := by rw [hbd']
    _ = -(c * a * d) * b := by noncomm_ring
    _ = - (c * (-(d * a))) * b := by
      rw [show c * a * d = c * (a * d) by noncomm_ring, had']
    _ = (c * d) * (a * b) := by noncomm_ring

/-! The concrete Jordan--Wigner specialization. -/

theorem jw_pair_bilinears_commute_of_disjoint
    (n : ℕ) (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (jwCreation n i * jwAnnihilation n j) *
        (jwCreation n k * jwAnnihilation n l) =
      (jwCreation n k * jwAnnihilation n l) *
        (jwCreation n i * jwAnnihilation n j) := by
  apply mul_mul_comm_of_four_anticommute
  · exact creation_cross_site_anticommute n i k hik
  · exact creation_annihilation_cross_site_anticommute n i l hil
  · exact annihilation_creation_cross_site_anticommute n j k hjk
  · exact annihilation_cross_site_anticommute n j l hjl

theorem jw_pair_bilinear_commutes_globalChirality
    (n : ℕ) (i j : Fin n) :
    globalChirality n * (jwCreation n i * jwAnnihilation n j) =
      (jwCreation n i * jwAnnihilation n j) * globalChirality n := by
  have hi := globalChirality_anticomm_jwCreation n i
  have hj := globalChirality_anticomm_jwAnnihilation n j
  calc
    globalChirality n * (jwCreation n i * jwAnnihilation n j) =
        (globalChirality n * jwCreation n i) * jwAnnihilation n j := by noncomm_ring
    _ = (-(jwCreation n i * globalChirality n)) * jwAnnihilation n j := by
      rw [eq_neg_of_add_eq_zero_left hi]
    _ = -(jwCreation n i * (globalChirality n * jwAnnihilation n j)) := by
      noncomm_ring
    _ = -(jwCreation n i * (-(jwAnnihilation n j * globalChirality n))) := by
      rw [eq_neg_of_add_eq_zero_left hj]
    _ = (jwCreation n i * jwAnnihilation n j) * globalChirality n := by
      noncomm_ring

theorem commonFock_pair_bilinears_commute_of_disjoint
    (i j k l : ℕ)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (modeCreationOperator i * modeAnnihilationOperator j) *
        (modeCreationOperator k * modeAnnihilationOperator l) =
      (modeCreationOperator k * modeAnnihilationOperator l) *
        (modeCreationOperator i * modeAnnihilationOperator j) := by
  apply mul_mul_comm_of_four_anticommute
  · exact modeCreationOperator_creationOperator_anticomm i k
  · exact modeCreationOperator_annihilationOperator_cross_site_anticomm i l hil
  · exact modeAnnihilationOperator_creationOperator_cross_site_anticomm j k hjk
  · exact modeAnnihilationOperator_annihilationOperator_anticomm j l

end InfoGeometry.Canonical.DisjointCARBilinear
