import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionRightRegularBraid

open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev EndCZ := InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.EndCZ

def majorana (mode : Fin 3) : EndCZ :=
  rightRegular (rootPlus mode) + rightRegular (rootMinus mode)

theorem majorana_sq (mode : Fin 3) : majorana mode * majorana mode = 1 := by
  unfold majorana
  simp only [add_mul, mul_add, rightRegular_rootPlus_sq, rightRegular_rootMinus_sq]
  simpa only [zero_add, add_zero, add_comm] using rightRegular_root_CAR mode

theorem majorana_anticommute {first second : Fin 3} (distinct : first ≠ second) :
    majorana first * majorana second + majorana second * majorana first = 0 := by
  apply add_add_anticommute_of_pairwise
  · exact rightRegular_rootPlus_anticommutator first second
  · simpa only [add_comm] using rightRegular_root_anticommutator_off_diagonal distinct
  · exact rightRegular_root_anticommutator_off_diagonal (Ne.symm distinct)
  · exact rightRegular_rootMinus_anticommutator first second

def bivector (index : Fin 2) : EndCZ :=
  majorana index.castSucc * majorana index.succ

theorem bivector_sq (index : Fin 2) : bivector index * bivector index = -1 := by
  have swap : majorana index.succ * majorana index.castSucc =
      -(majorana index.castSucc * majorana index.succ) :=
    eq_neg_of_add_eq_zero_left (by
      simpa only [add_comm] using
        (majorana_anticommute (first := index.castSucc) (second := index.succ) (by
          intro equality
          have values := congrArg Fin.val equality
          simp only [Fin.val_castSucc, Fin.val_succ] at values
          omega)))
  calc
    bivector index * bivector index =
        majorana index.castSucc * (majorana index.succ * majorana index.castSucc) *
          majorana index.succ := by simp only [bivector, mul_assoc]
    _ = -(majorana index.castSucc * majorana index.castSucc) *
        (majorana index.succ * majorana index.succ) := by rw [swap]; noncomm_ring
    _ = -1 := by rw [majorana_sq, majorana_sq]; simp

def braidUnit (index : Fin 2) : EndCZˣ where
  val := 1 + bivector index
  inv := algebraMap ℝ EndCZ (1 / 2) * (1 - bivector index)
  val_inv := by
    rw [mul_smul_comm]
    have product : (1 + bivector index) * (1 - bivector index) =
        (2 : ℝ) • (1 : EndCZ) := by
      calc
        _ = 1 - bivector index * bivector index := by noncomm_ring
        _ = _ := by rw [bivector_sq]; simp [two_smul]
    rw [product, smul_smul]
    norm_num
  inv_val := by
    rw [smul_mul_assoc]
    have product : (1 - bivector index) * (1 + bivector index) =
        (2 : ℝ) • (1 : EndCZ) := by
      calc
        _ = 1 - bivector index * bivector index := by noncomm_ring
        _ = _ := by rw [bivector_sq]; simp [two_smul]
    rw [product, smul_smul]
    norm_num

theorem braidUnit_artin :
    braidUnit 0 * braidUnit 1 * braidUnit 0 = braidUnit 1 * braidUnit 0 * braidUnit 1 := by
  apply Units.ext
  exact adjacent_majorana_artin (majorana 0) (majorana 1) (majorana 2)
    (majorana_sq 0) (majorana_sq 1) (majorana_sq 2)
    (majorana_anticommute (by decide)) (majorana_anticommute (by decide))
    (majorana_anticommute (by decide))

theorem braidUnit_relations :
    ∀ relation ∈ artinRelations 2, FreeGroup.lift braidUnit relation = 1 := by
  intro relation membership
  rcases membership with adjacent | distant
  · rcases adjacent with ⟨first, second, consecutive, rfl⟩
    have first_zero : first = 0 := by apply Fin.ext; omega
    have second_one : second = 1 := by apply Fin.ext; omega
    subst first
    subst second
    simp only [adjacentWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [braidUnit_artin, mul_inv_cancel]
  · rcases distant with ⟨first, second, separated, equality⟩
    omega

def braidRepresentation : ArtinBraid 2 →* EndCZˣ :=
  PresentedGroup.toGroup braidUnit_relations

@[simp] theorem braidRepresentation_generator (index : Fin 2) :
    braidRepresentation (PresentedGroup.of index) = braidUnit index :=
  PresentedGroup.toGroup.of braidUnit_relations

def braidConjugation (braid : ArtinBraid 2) : EndCZ ≃ₐ[ℝ] EndCZ :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (braidRepresentation braid)).conjAlgEquiv ℝ

theorem braidConjugation_apply (braid : ArtinBraid 2) (operator : EndCZ) :
    braidConjugation braid operator =
      (braidRepresentation braid : EndCZ) * operator *
        (↑((braidRepresentation braid)⁻¹) : EndCZ) := by
  rfl

theorem braidConjugation_one (operator : EndCZ) :
    braidConjugation 1 operator = operator := by
  simp [braidConjugation_apply]

theorem braidConjugation_mul (first second : ArtinBraid 2) (operator : EndCZ) :
    braidConjugation (first * second) operator =
      braidConjugation first (braidConjugation second operator) := by
  simp [braidConjugation_apply, map_mul, mul_assoc]

theorem braidRepresentation_artin :
    braidRepresentation (PresentedGroup.of (0 : Fin 2) * PresentedGroup.of (1 : Fin 2) *
        PresentedGroup.of (0 : Fin 2)) =
      braidRepresentation (PresentedGroup.of (1 : Fin 2) * PresentedGroup.of (0 : Fin 2) *
        PresentedGroup.of (1 : Fin 2)) := by
  simpa only [map_mul, braidRepresentation_generator] using braidUnit_artin

end InfoGeometry.Canonical.SplitOctonionRightRegularBraid
