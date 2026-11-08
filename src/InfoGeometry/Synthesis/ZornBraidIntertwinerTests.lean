import InfoGeometry.Synthesis.ZornBraidIntertwiner

namespace InfoGeometry.Synthesis.ZornBraidIntertwiner.Tests

open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Physics.B3PresentedGroup (B3 B3Gen)
open InfoGeometry.Physics.YangBaxterZornBridge (zornPhi zornPhi_sig0 zornPhi_sig1)

example :
    (zornColimitBraidRepresentation (PresentedGroup.of B3Gen.sig0) :
      Module.End ℂ ZornColimit) = zornBraidGeneratorColimit1 :=
  by
    change zornColimitMatrixAction
      (zornPhi (PresentedGroup.of B3Gen.sig0 : B3) : Matrix (Fin 8) (Fin 8) ℂ) = _
    rw [zornPhi_sig0]
    rfl

example :
    (zornColimitBraidRepresentation (PresentedGroup.of B3Gen.sig1) :
      Module.End ℂ ZornColimit) = zornBraidGeneratorColimit2 :=
  by
    change zornColimitMatrixAction
      (zornPhi (PresentedGroup.of B3Gen.sig1 : B3) : Matrix (Fin 8) (Fin 8) ℂ) = _
    rw [zornPhi_sig1]
    rfl

example (braid : B3) :
    zornColimitBraidRepresentation braid * zornColimitBraidRepresentation braid⁻¹ = 1 := by
  rw [map_inv, mul_inv_cancel]

#print axioms zornColimitBraidRepresentation
#print axioms automorphism_braid_generator_covariance
#print axioms canonical_braid_colimit_intertwines
#print axioms canonical_inverse_braid_colimit_intertwines

end InfoGeometry.Synthesis.ZornBraidIntertwiner.Tests
