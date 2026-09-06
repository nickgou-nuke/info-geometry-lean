import InfoGeometry.Clifford.Cl55WittProjectors
import InfoGeometry.Clifford.Cl55RealSplitPinVolumeAnticommutation

/-!
# Noncommutative `Z₂` adjoint gradings in `Cl(5,5)`

The grading acts by conjugation inside the Clifford algebra.  The carrier is
therefore the algebra `Cl(5,5)` itself; no diagonal matrix model is used.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.KoszulFoundation

/-! The ordered ten-vector volume has square `1`. -/
private theorem cl55WittVolumeList_pairwise_operator_grading :
    cl55WittVolumeList.Pairwise (QuadraticMap.IsOrtho Q55) := by
  rw [cl55WittVolumeList, List.pairwise_ofFn]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [QuadraticMap.isOrtho_def, cl55WittBasisFin, wittBasis,
      Q55_apply, e_pos, f_neg, Fin.sum_univ_succ] <;> native_decide

private theorem cl55WittVolumeList_even_operator_grading :
    Even cl55WittVolumeList.length := by
  norm_num [cl55WittVolumeList]

theorem cl55WittVolume_sq :
    cl55WittVolume * cl55WittVolume = (1 : Cl55) := by
  rw [cl55WittVolume,
    cliffordVolumeElement_sq_of_pairwise cl55WittVolumeList
      cl55WittVolumeList_pairwise_operator_grading]
  norm_num [cl55WittVolumeList, cl55WittBasisFin,
    cliffordVolumeSquareScalar, wittBasis, Q55_apply, e_pos, f_neg,
    Fin.sum_univ_succ]

theorem cl55WittVolume_anticommutes_hyperbolicAxis (i : Fin 5) :
    hyperbolicAxis55 i * cl55WittVolume =
      -(cl55WittVolume * hyperbolicAxis55 i) := by
  unfold hyperbolicAxis55 creation55 annihilation55
  have hn := cl55WittVolume_anticommutes (n_pair i)
  have hnb := cl55WittVolume_anticommutes (nbar_pair i)
  have hn' : ((1 / 2 : ℝ) • ι55 (n_pair i)) * cl55WittVolume =
      -(cl55WittVolume * ((1 / 2 : ℝ) • ι55 (n_pair i))) := by
    rw [smul_mul_assoc, mul_smul_comm, hn]
    simp
  have hnb' : ((1 / 2 : ℝ) • ι55 (nbar_pair i)) * cl55WittVolume =
      -(cl55WittVolume * ((1 / 2 : ℝ) • ι55 (nbar_pair i))) := by
    rw [smul_mul_assoc, mul_smul_comm, hnb]
    simp
  rw [add_mul, mul_add, hn', hnb']
  module

theorem hyperbolicAxis55_anticommute_distinct
    {i j : Fin 5} (hij : i ≠ j) :
    hyperbolicAxis55 i * hyperbolicAxis55 j +
        hyperbolicAxis55 j * hyperbolicAxis55 i = 0 := by
  unfold hyperbolicAxis55
  have haa := annihilation55_anticommutator i j
  have hcc := creation55_anticommutator i j
  have hac := annihilation55_creation55_anticommutator_eq i j
  have hca := annihilation55_creation55_anticommutator_eq j i
  simp [hij] at hac
  have hji : j ≠ i := Ne.symm hij
  simp [hji] at hca
  have hca' : creation55 i * annihilation55 j +
      annihilation55 j * creation55 i = 0 := by
    simpa [add_comm] using hca
  calc
    (creation55 i + annihilation55 i) * (creation55 j + annihilation55 j) +
        (creation55 j + annihilation55 j) * (creation55 i + annihilation55 i) =
      (creation55 i * creation55 j + creation55 j * creation55 i) +
        (annihilation55 i * annihilation55 j + annihilation55 j * annihilation55 i) +
        (creation55 i * annihilation55 j + annihilation55 j * creation55 i) +
        (annihilation55 i * creation55 j + creation55 j * annihilation55 i) := by
          noncomm_ring
    _ = 0 := by rw [hcc, haa, hca', hac]; simp

def adjointParity55 (g x : Cl55) : Cl55 := g * x * g

theorem adjointParity55_apply_one (g : Cl55) (hg : g * g = 1) :
    adjointParity55 g 1 = 1 := by
  unfold adjointParity55
  simp [hg]

theorem adjointParity55_apply_apply (g x : Cl55) (hg : g * g = 1) :
    adjointParity55 g (adjointParity55 g x) = x := by
  unfold adjointParity55
  calc
    g * (g * x * g) * g = (g * g) * x * (g * g) := by noncomm_ring
    _ = x := by rw [hg]; simp

theorem adjointParity55_commute_of_commute
    (g h x : Cl55) (hgh : g * h = h * g) :
    adjointParity55 g (adjointParity55 h x) =
      adjointParity55 h (adjointParity55 g x) := by
  unfold adjointParity55
  calc
    g * (h * x * h) * g = (g * h) * x * (h * g) := by noncomm_ring
    _ = (h * g) * x * (g * h) := by rw [hgh]
    _ = h * (g * x * g) * h := by noncomm_ring

theorem adjointParity55_commute_of_anticommute
    (g h x : Cl55) (hgh : g * h = -(h * g)) :
    adjointParity55 g (adjointParity55 h x) =
      adjointParity55 h (adjointParity55 g x) := by
  unfold adjointParity55
  have hgh' : h * g = -(g * h) := by
    calc
      h * g = -(-(h * g)) := by simp
      _ = -(g * h) := by rw [← hgh]
  calc
    g * (h * x * h) * g = (g * h) * x * (h * g) := by noncomm_ring
    _ = (-(h * g)) * x * (h * g) := by rw [hgh]
    _ = (h * g) * x * (g * h) := by
      rw [hgh']
      simp [neg_mul, mul_neg]
    _ = h * (g * x * g) * h := by noncomm_ring

def wedgeGrading55 : Cl55 := hyperbolicAxis55 0

def chiralGrading55 : Cl55 := hyperbolicAxis55 1

def nambuGrading55 : Cl55 := cl55WittVolume

theorem wedgeGrading55_sq : wedgeGrading55 * wedgeGrading55 = (1 : Cl55) := by
  exact hyperbolicAxis55_sq 0

theorem chiralGrading55_sq : chiralGrading55 * chiralGrading55 = (1 : Cl55) := by
  exact hyperbolicAxis55_sq 1

theorem nambuGrading55_sq : nambuGrading55 * nambuGrading55 = (1 : Cl55) := by
  exact cl55WittVolume_sq

theorem wedge_chiral_gradings_anticommute :
    wedgeGrading55 * chiralGrading55 =
      -(chiralGrading55 * wedgeGrading55) := by
  have h := hyperbolicAxis55_anticommute_distinct
    (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  exact eq_neg_of_add_eq_zero_left h

theorem chiral_nambu_gradings_anticommute :
    chiralGrading55 * nambuGrading55 =
      -(nambuGrading55 * chiralGrading55) := by
  have h := cl55WittVolume_anticommutes_hyperbolicAxis 1
  calc
    chiralGrading55 * nambuGrading55 = hyperbolicAxis55 1 * cl55WittVolume := rfl
    _ = -(cl55WittVolume * hyperbolicAxis55 1) := h
    _ = -(nambuGrading55 * chiralGrading55) := by rfl

theorem nambu_wedge_gradings_anticommute :
    nambuGrading55 * wedgeGrading55 =
      -(wedgeGrading55 * nambuGrading55) := by
  have h := cl55WittVolume_anticommutes_hyperbolicAxis 0
  calc
    nambuGrading55 * wedgeGrading55 = cl55WittVolume * hyperbolicAxis55 0 := rfl
    _ = -(hyperbolicAxis55 0 * cl55WittVolume) := by
      calc
        cl55WittVolume * hyperbolicAxis55 0 =
            -(-(cl55WittVolume * hyperbolicAxis55 0)) := by simp
        _ = -(hyperbolicAxis55 0 * cl55WittVolume) := by rw [← h]
    _ = -(wedgeGrading55 * nambuGrading55) := by rfl

theorem adjoint_gradings_pairwise_commute (x : Cl55) :
    adjointParity55 wedgeGrading55
        (adjointParity55 chiralGrading55
          (adjointParity55 nambuGrading55 x)) =
      adjointParity55 nambuGrading55
        (adjointParity55 chiralGrading55
          (adjointParity55 wedgeGrading55 x)) := by
  have hrev : wedgeGrading55 * nambuGrading55 =
      -(nambuGrading55 * wedgeGrading55) := by
    have h := nambu_wedge_gradings_anticommute
    have hs : wedgeGrading55 * nambuGrading55 +
        nambuGrading55 * wedgeGrading55 = 0 := by
      rw [h]
      simp
    exact eq_neg_of_add_eq_zero_left hs
  calc
    _ = adjointParity55 wedgeGrading55
        (adjointParity55 nambuGrading55
          (adjointParity55 chiralGrading55 x)) := by
      rw [adjointParity55_commute_of_anticommute
        chiralGrading55 nambuGrading55 x chiral_nambu_gradings_anticommute]
    _ = adjointParity55 nambuGrading55
        (adjointParity55 wedgeGrading55
          (adjointParity55 chiralGrading55 x)) := by
      rw [adjointParity55_commute_of_anticommute
        wedgeGrading55 nambuGrading55
        (adjointParity55 chiralGrading55 x)
        hrev]
    _ = adjointParity55 nambuGrading55
        (adjointParity55 chiralGrading55
          (adjointParity55 wedgeGrading55 x)) := by
      rw [adjointParity55_commute_of_anticommute
        wedgeGrading55 chiralGrading55 x wedge_chiral_gradings_anticommute]

end InfoGeometry.Clifford.Clifford55
