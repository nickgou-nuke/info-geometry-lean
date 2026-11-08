import InfoGeometry.Canonical.KreinDrazinBoundarySupport
import InfoGeometry.HodgeCohomology.KreinDrazinGreen

namespace InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization

open InfoGeometry.Canonical InfoGeometry.Krein
open Drazin KreinSpace KreinDrazinBoundarySupport

def algebraicSplit {Algebra : Type*} [Ring Algebra]
    (operator green : Algebra) {index : ℕ} (inverse : IsDrazinInverse operator green index) :
    AlgebraicDrazinSplit Algebra where
  A := operator
  AD := green
  index := index
  hDrazin := inverse
  p := IsDrazinInverse.projection operator green
  q := IsDrazinInverse.complementaryProjection operator green
  p_def := rfl
  q_def := rfl
  p_idempotent := IsDrazinInverse.projection_is_idempotent inverse
  q_idempotent := IsDrazinInverse.complementaryProjection_is_idempotent inverse
  pq_zero := IsDrazinInverse.projection_mul_complementaryProjection inverse
  qp_zero := IsDrazinInverse.complementaryProjection_mul_projection inverse

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]

noncomputable def carrier : DoubledKreinCarrier Space (Space →L[ℝ] Space) where
  act := fun operator state => operator state
  kreinForm := kreinInner
  zero := 0

noncomputable def adjointData : KreinAdjointData (Space →L[ℝ] Space) where
  sharp := kreinAdjoint
  sharp_involutive := kreinAdjoint_involutive
  sharp_mul := kreinAdjoint_mul
  sharp_add := kreinAdjoint_add

noncomputable def carrierAdjointData :
    CarrierKreinAdjointData Space (Space →L[ℝ] Space) (carrier (Space := Space)) where
  sharp := kreinAdjoint
  isCarrierKreinAdjoint := kreinInner_kreinAdjoint

noncomputable def boundarySupport (operator green : Space →L[ℝ] Space) {index : ℕ}
    (inverse : IsDrazinInverse operator green index) (self_adjoint : IsKreinSelfAdjoint operator) :
    KreinDrazinBoundarySupport Space (Space →L[ℝ] Space) where
  carrier := carrier
  adjoint := adjointData
  drazin := algebraicSplit operator green inverse
  p_sharp := KreinDrazinGreen.regular_projector_krein_adjoint inverse self_adjoint
  q_sharp := KreinDrazinGreen.complementary_projector_krein_adjoint inverse self_adjoint
  generalized_zero_sector_zero := map_zero _
  inverse_on_regular_sector := by
    change (operator * green) * operator * green = operator * green
    rw [mul_assoc]
    exact IsDrazinInverse.projection_is_idempotent inverse

noncomputable def compatibleComplement
    (data : AlgebraicDrazinData (Space →L[ℝ] Space))
    (self_adjoint : IsKreinSelfAdjoint data.L) :
    KreinCompatibleDrazinComplement Space (Space →L[ℝ] Space)
      (carrier (Space := Space)) data carrierAdjointData where
  H_krein_self_adjoint := by
    change kreinAdjoint data.H = data.H
    rw [data.H_def]
    exact KreinDrazinGreen.complementary_projector_krein_adjoint data.isDrazinInverse self_adjoint

end InfoGeometry.HodgeCohomology.KreinDrazinBoundaryRealization
