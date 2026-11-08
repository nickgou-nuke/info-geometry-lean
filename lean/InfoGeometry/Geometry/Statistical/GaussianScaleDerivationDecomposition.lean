import InfoGeometry.Geometry.Statistical.GaussianSplitOctonionDerivationField
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge

/-!
# Scale/derivation decomposition of the supplied Gaussian carrier

The scalar coordinate is the central Weyl/scale direction.  The remaining
fourteen coordinates are transported through the native canonical derivation
equivalence.  This owner records only the resulting endomorphism identities;
it does not choose a Gaussian measure or impose covariance independence.
-/

namespace InfoGeometry.Geometry.Statistical.GaussianScaleDerivationDecomposition

noncomputable section

open InfoGeometry.Geometry.Statistical
open InfoGeometry.Geometry.Statistical.GaussianSplitOctonionDerivationField
open InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge

abbrev ScaleDerivationParams := ℝ × (Fin 14 → ℝ)

def scaleDerivationOperator (p : ScaleDerivationParams) : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ :=
  p.1 • LinearMap.id -
    (2 : ℝ) • derivationRepresentation (derivationOfCoordinates p.2)

theorem scaleDerivationOperator_central_shift
    (p : ScaleDerivationParams) (c : ℝ) :
    scaleDerivationOperator (p.1 + c, p.2) =
      scaleDerivationOperator p + c • LinearMap.id := by
  unfold scaleDerivationOperator
  rw [add_smul]
  module

theorem scaleDerivationOperator_commutator (p q : ScaleDerivationParams) :
    operatorCommutator (scaleDerivationOperator p)
        (scaleDerivationOperator q) =
      (4 : ℝ) • operatorCommutator
        (derivationRepresentation (derivationOfCoordinates p.2))
        (derivationRepresentation (derivationOfCoordinates q.2)) := by
  let Dp : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ := derivationRepresentation (derivationOfCoordinates p.2)
  let Dq : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ := derivationRepresentation (derivationOfCoordinates q.2)
  have hp : scaleDerivationOperator p = p.1 • LinearMap.id + (-2 : ℝ) • Dp := by
    simpa [scaleDerivationOperator, Dp, sub_eq_add_neg]
  have hq : scaleDerivationOperator q = q.1 • LinearMap.id + (-2 : ℝ) • Dq := by
    simpa [scaleDerivationOperator, Dq, sub_eq_add_neg]
  rw [hp, hq]
  calc
    operatorCommutator
        (p.1 • LinearMap.id + (-2 : ℝ) • Dp)
        (q.1 • LinearMap.id + (-2 : ℝ) • Dq) =
      operatorCommutator ((-2 : ℝ) • Dp) ((-2 : ℝ) • Dq) :=
        operatorCommutator_add_smul_id p.1 q.1
          ((-2 : ℝ) • Dp) ((-2 : ℝ) • Dq)
    _ = (4 : ℝ) • operatorCommutator Dp Dq := by
      apply LinearMap.ext
      intro z
      simp only [operatorCommutator, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_smul]
      simp only [map_smul, smul_sub, smul_smul, mul_comm]
      norm_num

theorem scaleDerivationOperator_commutator_eq_derivation_bracket
    (p q : ScaleDerivationParams) :
    operatorCommutator (scaleDerivationOperator p)
        (scaleDerivationOperator q) =
      (4 : ℝ) •
        ((⁅(derivationOfCoordinates p.2 :
              InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations),
            (derivationOfCoordinates q.2 :
              InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)⁆ :
            InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := by
  rw [scaleDerivationOperator_commutator]
  have h := derivation_bracket_coe
    (derivationOfCoordinates p.2 :
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)
    (derivationOfCoordinates q.2 :
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)
  exact congrArg (fun D : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ => (4 : ℝ) • D) h.symm

theorem scaleDerivationOperator_commutator_scale_invariant
    (a b : ℝ) (p q : (Fin 14 → ℝ)) :
    operatorCommutator (scaleDerivationOperator (a, p))
        (scaleDerivationOperator (b, q)) =
      operatorCommutator (scaleDerivationOperator (0, p))
        (scaleDerivationOperator (0, q)) := by
  rw [scaleDerivationOperator_commutator,
    scaleDerivationOperator_commutator]

theorem scaleDerivationOperator_commutator_self (p : ScaleDerivationParams) :
    operatorCommutator (scaleDerivationOperator p)
        (scaleDerivationOperator p) = 0 := by
  simp [operatorCommutator]

end
end InfoGeometry.Geometry.Statistical.GaussianScaleDerivationDecomposition
