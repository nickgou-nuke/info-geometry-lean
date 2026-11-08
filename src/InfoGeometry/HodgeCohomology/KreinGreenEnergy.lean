import InfoGeometry.Canonical.HodgeGreenProjectorConstruction
import InfoGeometry.Canonical.DrazinPairingAdjunction
import InfoGeometry.HodgeCohomology.KreinHodgeDirac

namespace InfoGeometry.HodgeCohomology.KreinGreenEnergy

open InfoGeometry.Canonical
open HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction Drazin

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
variable (pairing : LinearMap.BilinForm ℝ Space)

theorem product_green_adjoint (differential codifferential green : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential)
    (reverse : LinearMap.IsAdjointPair pairing pairing codifferential differential)
    (green_adjoint : LinearMap.IsAdjointPair pairing pairing green green)
    (commutes_d : green * differential = differential * green)
    (commutes_cod : green * codifferential = codifferential * green) :
    LinearMap.IsAdjointPair pairing pairing (differential * codifferential * green)
      (differential * codifferential * green) := by
  have commute_product : green * (differential * codifferential) =
      differential * codifferential * green := by
    calc
      green * (differential * codifferential) = (green * differential) * codifferential :=
        (mul_assoc _ _ _).symm
      _ = (differential * green) * codifferential := by rw [commutes_d]
      _ = differential * (green * codifferential) := mul_assoc _ _ _
      _ = differential * (codifferential * green) := by rw [commutes_cod]
      _ = differential * codifferential * green := (mul_assoc _ _ _).symm
  have product_adjoint := (adjunction.mul reverse).mul green_adjoint
  simpa only [commute_product] using product_adjoint

theorem orthogonal_projector_images
    (first second : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing first first)
    (annihilates : first * second = 0) (left right : Space) :
    pairing (first left) (second right) = 0 := by
  rw [adjunction]
  have composition_zero : first (second right) = 0 := LinearMap.congr_fun annihilates right
  rw [composition_zero, map_zero]

theorem signed_projector_energy
    (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Space))
    (exact_adjoint : LinearMap.IsAdjointPair pairing pairing packet.Pex packet.Pex)
    (coexact_adjoint : LinearMap.IsAdjointPair pairing pairing packet.Pcoex packet.Pcoex)
    (harmonic_adjoint : LinearMap.IsAdjointPair pairing pairing packet.Pharm packet.Pharm)
    (state : Space) :
    pairing state state = pairing (packet.Pex state) (packet.Pex state) +
      pairing (packet.Pcoex state) (packet.Pcoex state) +
      pairing (packet.Pharm state) (packet.Pharm state) := by
  have exact_energy : pairing (packet.Pex state) (packet.Pex state) =
      pairing state (packet.Pex state) := by
    rw [exact_adjoint]
    rw [show packet.Pex (packet.Pex state) = packet.Pex state from
      LinearMap.congr_fun packet.Pex_idem state]
  have coexact_energy : pairing (packet.Pcoex state) (packet.Pcoex state) =
      pairing state (packet.Pcoex state) := by
    rw [coexact_adjoint]
    rw [show packet.Pcoex (packet.Pcoex state) = packet.Pcoex state from
      LinearMap.congr_fun packet.Pcoex_idem state]
  have harmonic_energy : pairing (packet.Pharm state) (packet.Pharm state) =
      pairing state (packet.Pharm state) := by
    rw [harmonic_adjoint]
    rw [show packet.Pharm (packet.Pharm state) = packet.Pharm state from
      LinearMap.congr_fun packet.Pharm_idem state]
  rw [exact_energy, coexact_energy, harmonic_energy, ← map_add, ← map_add,
    ← packet.decompose state]

section Construction

variable (system : HodgePacket (R := ℝ) (V := Space))
variable (green : Module.End ℝ Space) {index : ℕ}
variable (inverse : IsDrazinInverse system.Δ green index)
variable (commutes_d : green * system.d = system.d * green)
variable (commutes_cod : green * system.δ = system.δ * green)
variable (symmetric : pairing.IsSymm)
variable (adjunction : LinearMap.IsAdjointPair pairing pairing system.d system.δ)

include symmetric adjunction

theorem laplacian_adjoint :
    LinearMap.IsAdjointPair pairing pairing system.Δ system.Δ := by
  have reverse := KreinHodgeDirac.reverse_adjunction pairing symmetric system.d system.δ adjunction
  rw [system.Δ_def]
  exact (adjunction.mul reverse).add (reverse.mul adjunction)

include inverse in
theorem green_adjoint : LinearMap.IsAdjointPair pairing pairing green green :=
  DrazinPairingAdjunction.inverse_adjoint pairing
    (laplacian_adjoint pairing system symmetric adjunction) inverse

theorem constructed_projectors_adjoint :
    let packet := decompositionFromGreen system green inverse commutes_d commutes_cod
    LinearMap.IsAdjointPair pairing pairing packet.Pex packet.Pex ∧
      LinearMap.IsAdjointPair pairing pairing packet.Pcoex packet.Pcoex ∧
      LinearMap.IsAdjointPair pairing pairing packet.Pharm packet.Pharm := by
  let packet := decompositionFromGreen system green inverse commutes_d commutes_cod
  have reverse := KreinHodgeDirac.reverse_adjunction pairing symmetric system.d system.δ adjunction
  have green_relation := green_adjoint pairing system green inverse symmetric adjunction
  have exact_adjoint : LinearMap.IsAdjointPair pairing pairing packet.Pex packet.Pex :=
    product_green_adjoint pairing system.d system.δ green adjunction reverse green_relation
      commutes_d commutes_cod
  have coexact_adjoint : LinearMap.IsAdjointPair pairing pairing packet.Pcoex packet.Pcoex :=
    product_green_adjoint pairing system.δ system.d green reverse adjunction green_relation
      commutes_cod commutes_d
  refine ⟨exact_adjoint, coexact_adjoint, ?_⟩
  have complement := (LinearMap.isAdjointPair_one (B := pairing)).sub
    (exact_adjoint.add coexact_adjoint)
  exact complement

theorem constructed_signed_energy (state : Space) :
    let packet := decompositionFromGreen system green inverse commutes_d commutes_cod
    pairing state state = pairing (packet.Pex state) (packet.Pex state) +
      pairing (packet.Pcoex state) (packet.Pcoex state) +
      pairing (packet.Pharm state) (packet.Pharm state) := by
  obtain ⟨exact_adjoint, coexact_adjoint, harmonic_adjoint⟩ :=
    constructed_projectors_adjoint pairing system green inverse commutes_d commutes_cod
      symmetric adjunction
  exact signed_projector_energy pairing
    (decompositionFromGreen system green inverse commutes_d commutes_cod)
    exact_adjoint coexact_adjoint harmonic_adjoint state

end Construction

end InfoGeometry.HodgeCohomology.KreinGreenEnergy
