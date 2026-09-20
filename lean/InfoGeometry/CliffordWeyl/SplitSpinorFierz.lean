import InfoGeometry.CliffordWeyl.SplitCliffordGrades
import InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration

noncomputable section

namespace InfoGeometry.CliffordWeyl.SplitSpinorFierz

open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordWeyl.SplitCliffordGrades
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem representation_finrank_eq (stages : ℕ) :
    Module.finrank ℝ (Cl_split stages) = Module.finrank ℝ (SpinorMatrix stages) := by
  calc
    Module.finrank ℝ (Cl_split stages) = 2 ^ (2 * stages) := clifford_finrank stages
    _ = (2 ^ stages) * (2 ^ stages) := by
      rw [show 2 * stages = stages + stages by omega, pow_add]
    _ = Module.finrank ℝ (SpinorMatrix stages) := by
      simp [SpinorMatrix, Matrix, Module.finrank_pi]

def spinorEquiv (stages : ℕ) : Cl_split stages ≃ₐ[ℝ] SpinorMatrix stages := by
  apply AlgEquiv.ofBijective (spinorRepresentation stages)
  have onto := InfoGeometry.Clifford.Clifford55.splitSpinorRepresentation_surjective_of_gammaTensor
    stages
  have injective : Function.Injective (spinorRepresentation stages).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (representation_finrank_eq stages)).mpr onto
  exact ⟨injective, onto⟩

def channelBasis (stages : ℕ) :
    Module.Basis (Finset (Fin (2 * stages))) ℝ (SpinorMatrix stages) :=
  (cliffordBasis stages).map (spinorEquiv stages).toLinearEquiv

def channelCoefficient (stages : ℕ) (metric : SpinorMatrix stages)
    (left right : SpinorSpace stages) (blade : Finset (Fin (2 * stages))) : ℝ :=
  (channelBasis stages).repr (solder metric left right) blade

theorem all_grade_fierz_reconstruction (stages : ℕ) (metric : SpinorMatrix stages)
    (left right : SpinorSpace stages) :
    ∑ blade, channelCoefficient stages metric left right blade • channelBasis stages blade =
      solder metric left right :=
  solder_basis_reconstruction (channelBasis stages) metric left right

theorem all_grade_fierz_product (stages : ℕ) (metric : SpinorMatrix stages)
    (first second third fourth : SpinorSpace stages) (blade : Finset (Fin (2 * stages))) :
    (channelBasis stages).repr (solder metric first second * solder metric third fourth) blade =
      (dotProduct (diracRow metric second) third) *
        channelCoefficient stages metric first fourth blade :=
  fierz_coefficient_relation (channelBasis stages) metric first second third fourth blade

end InfoGeometry.CliffordWeyl.SplitSpinorFierz
