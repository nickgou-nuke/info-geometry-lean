import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import InfoGeometry.QuantumGeometry.Projective.QGT

noncomputable section

namespace InfoGeometry.Canonical.MassieuQGTBridge

open scoped BigOperators InnerProductSpace
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.QuantumGeometry.Projective

variable {State : Type*} [Fintype State] [Nonempty State]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def massieuPotential (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) : ℝ :=
  souriauMassieu D beta

def chargeCovariance (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  fisherSouriauMatrix D beta i j

theorem massieu_hessian_eq_chargeCovariance
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => massieuPotential D (betaSlice beta i t')) t) (beta i) =
      chargeCovariance D beta i i := by
  exact fisherSouriauMatrix_eq_massieuHessian D beta i

theorem chargeCovariance_eq_fisherSouriauMatrix
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i j : Fin 2) :
    chargeCovariance D beta i j = fisherSouriauMatrix D beta i j :=
  rfl

theorem massieu_hessian_eq_qgt_real
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2)
    (ψ : NormalizedState H) (X : H →L[ℂ] H)
    (hQ : fubiniStudyMetric ψ X X = fisherSouriauMatrix D beta i i) :
    deriv (fun t => deriv
      (fun t' => massieuPotential D (betaSlice beta i t')) t) (beta i) =
      (QGT ψ X X).re := by
  calc
    deriv (fun t => deriv
        (fun t' => massieuPotential D (betaSlice beta i t')) t) (beta i) =
        fisherSouriauMatrix D beta i i :=
      fisherSouriauMatrix_eq_massieuHessian D beta i
    _ = fubiniStudyMetric ψ X X := hQ.symm
    _ = (QGT ψ X X).re := rfl

end InfoGeometry.Canonical.MassieuQGTBridge

end
