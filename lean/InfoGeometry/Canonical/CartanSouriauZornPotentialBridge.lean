import InfoGeometry.Canonical.ApolloniusZornPotential
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu

/-! A finite bridge from the native Cartan--Souriau Massieu potential to the
native Zorn potential embedding.  The auxiliary phase and `χ` coordinates are
explicit inputs; no Fisher or spacetime interpretation is added here. -/

noncomputable section

namespace InfoGeometry.Canonical.CartanSouriauZornPotentialBridge

open InfoGeometry.Canonical.ApolloniusZornPotential
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

abbrev Parameter := Fin 2 → ℝ

variable {State : Type*} [Fintype State] [Nonempty State]

def cartanSouriauPotentialZorn
    (D : CartanSouriauDatum State) (β : Parameter) (θ χ : ℝ) :
    InfoGeometry.Algebra.ZornMatrix ℝ :=
  apolloniusPotentialZorn (souriauMassieu D β) θ χ

@[simp] theorem cartanSouriauPotentialZorn_trace
    (D : CartanSouriauDatum State) (β : Parameter) (θ χ : ℝ) :
    InfoGeometry.Algebra.ZornMatrix.zornTrace
        (cartanSouriauPotentialZorn D β θ χ) = 0 := by
  exact InfoGeometry.Canonical.ApolloniusZornPotential.apolloniusPotentialZorn_trace _ _ _

theorem cartanSouriauPotentialZorn_norm
    (D : CartanSouriauDatum State) (β : Parameter) (θ χ : ℝ) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm (cartanSouriauPotentialZorn D β θ χ) =
      θ ^ 2 + χ ^ 2 - 2 * (souriauMassieu D β) ^ 2 := by
  exact InfoGeometry.Canonical.ApolloniusZornPotential.apolloniusPotentialZorn_norm _ _ _

theorem cartanSouriauPotentialZorn_scalar
    (D : CartanSouriauDatum State) (β : Parameter) (θ χ : ℝ) :
    (cartanSouriauPotentialZorn D β θ χ).a = souriauMassieu D β := by
  rfl

theorem cartanSouriauPotentialZorn_scalar_zero_iff
    (D : CartanSouriauDatum State) (β : Parameter) (θ χ : ℝ) :
    (cartanSouriauPotentialZorn D β θ χ).a = 0 ↔ souriauMassieu D β = 0 := by
  exact InfoGeometry.Canonical.ApolloniusZornPotential.apolloniusPotentialZorn_scalar_zero_iff _ _ _

end InfoGeometry.Canonical.CartanSouriauZornPotentialBridge
end noncomputable section
