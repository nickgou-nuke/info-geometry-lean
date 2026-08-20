import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric

/-!
# Certified finite Cartan--Gibbs--Massieu interface

This owner records only finite statements supplied by the native Cartan
character and Souriau owners.  It does not assert a global quotient
construction, a KKS form, or an identification with a Riemannian symmetric
space; those require additional mathematical data.
-/

noncomputable section

namespace InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

abbrev G2Cartan := CanonicalZornG2CartanSouriauCharacterBridge.G2Cartan

theorem gibbsKernel_cartanCharacter {State : Type*}
    (D : CartanSouriauDatum State) (x : State) :
    unnormalizedGibbsKernel D x =
      rankTwoCartanMellinCharacter D.beta (D.momentMap x) :=
  unnormalizedGibbsKernel_eq_cartanCharacter D x

theorem canonicalCartanKernel_eq_canonicalG2Character (x : G2Cartan) :
    unnormalizedGibbsKernel canonicalCartanSouriauDatum x =
      canonicalG2CartanMellinCharacter (fun _ => Complex.I) x := by
  exact canonicalCartanKernel_eq_canonicalG2Character x

theorem souriauMassieu_gibbsLogPartition
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    souriauMassieu D beta = Real.log (realGibbsPartition D beta) :=
  rfl

theorem souriauMassieu_gradient_eq_neg_meanCharge
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i) =
      -souriauChargeMean D beta i :=
  InfoGeometry.Lie.souriauMassieu_gradient_eq_neg_meanCharge D beta i

theorem souriauMassieu_secondDeriv_eq_chargeVariance
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) =
      souriauChargeVariance D beta i :=
  InfoGeometry.Lie.souriauMassieu_secondDeriv_eq_chargeVariance D beta i

theorem souriauMassieu_secondDeriv_nonneg
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) :=
  InfoGeometry.Lie.souriauMassieu_secondDeriv_nonneg D beta i

theorem fisherSouriau_directional_nonneg
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta v : Fin 2 → ℝ) :
    0 ≤ fisherSouriauQuadratic D beta v := by
  exact souriauMassieu_directionalSecondDeriv_nonneg D beta v

end InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification

end noncomputable section
