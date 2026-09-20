import InfoGeometry.EmergentVacuum.SplitChiralBdGCompatibility
import InfoGeometry.EmergentVacuum.MajoranaBraidCompatibility
import InfoGeometry.EmergentVacuum.KreinMetricStabilizer
import InfoGeometry.CliffordWeyl.KreinIdealBilinears
import InfoGeometry.CliffordWeyl.DiracBilinearChannels
import InfoGeometry.Physics.FierzIdentities

noncomputable section

namespace InfoGeometry.EmergentVacuum.CompatibilityTests

open SplitChiralBdGCompatibility
open InfoGeometry.Canonical.ZornBdGHamiltonianChiral
open InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
open InfoGeometry.CliffordWeyl.DiracBilinearChannels
open InfoGeometry.Clifford.CrawfordDiracBispinorDensities
open InfoGeometry.Physics.ChiralCausalCone

example : zornBdG (0 : ℝ) 0 0 = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [zornBdG]

example : zornBdG (3 : ℝ) 4 4 * zornBdG 3 4 4 = (25 : ℝ) • (1 : Mat2) := by
  rw [bdg_square]
  norm_num

example : (Finset.univ.filter fun index : Fin 16 =>
    cliffordDegree (finToDiracBilinearLabel index) = 2).card = 6 := by decide

example (left right : DiracSpinor) :
    diracDyad left right = ∑ index : Fin 16,
      (bilinear left (indexedChannel index).conjTranspose right / 4) • indexedChannel index :=
  fierz_dyad_reconstruction left right

example : σPlus ^ 3 = 0 := by
  rw [pow_succ, pow_two, σPlus_sq, zero_mul]

def tripleRaising := Matrix.kroneckerMap (fun first second : ℂ => first * second)
  (Matrix.kroneckerMap (fun first second : ℂ => first * second) σPlus σPlus) σPlus

example : tripleRaising ≠ 0 := by
  intro vanishes
  have entry := congrArg (fun operator => operator ((0, 0), 0) ((1, 1), 1)) vanishes
  norm_num [tripleRaising, Matrix.kroneckerMap, σPlus] at entry

example : (1 : ℂ) ^ 3 = 1 ∧ (1 : ℂ) ^ 2 + 1 + 1 ≠ 0 := by norm_num

example (size : ℕ) :
    (1 : Matrix.GeneralLinearGroup (Fin size ⊕ Fin size) ℂ) ∈
      KreinMetricStabilizer.specialPseudoUnitary size :=
  (KreinMetricStabilizer.specialPseudoUnitary size).one_mem

#print axioms left_projector_eq_peirce
#print axioms pairing_swaps_projectors
#print axioms equilibrium_bdg_square
#print axioms secular_pairing_lower_bound
#print axioms MajoranaBraidCompatibility.braid_fourth_power
#print axioms MajoranaBraidCompatibility.braid_eighth_power
#print axioms KreinMetricStabilizer.metricStabilizer
#print axioms KreinMetricStabilizer.mem_specialMetricStabilizer
#print axioms InfoGeometry.CliffordWeyl.KreinIdealBilinears.adjoint_sandwich
#print axioms InfoGeometry.CliffordWeyl.KreinIdealBilinears.sandwich_supported
#print axioms channel_reconstruction
#print axioms coefficients_injective
#print axioms fierz_dyad_reconstruction
#print axioms channel_chirality
#print axioms vector_current_cross_corners_zero
#print axioms InfoGeometry.CliffordWeyl.SpinorBilinearSelection.scalar_cross_corner_ne_zero

end InfoGeometry.EmergentVacuum.CompatibilityTests
