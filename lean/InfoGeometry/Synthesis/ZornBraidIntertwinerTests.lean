import InfoGeometry.Synthesis.ZornBraidIntertwiner

namespace InfoGeometry.Synthesis.ZornBraidIntertwiner.Tests

open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Physics.B3PresentedGroup (B3 B3Gen)

example :
    (zornColimitBraidRepresentation (PresentedGroup.of B3Gen.sig0) :
      Module.End ℂ ZornColimit) = zornBraidGeneratorColimit1 :=
  zornColimitBraidRepresentation_sig0

example :
    (zornColimitBraidRepresentation (PresentedGroup.of B3Gen.sig1) :
      Module.End ℂ ZornColimit) = zornBraidGeneratorColimit2 :=
  zornColimitBraidRepresentation_sig1

example (braid : B3) :
    zornColimitBraidRepresentation braid * zornColimitBraidRepresentation braid⁻¹ = 1 := by
  rw [map_inv, mul_inv_cancel]

#print axioms zornColimitBraidRepresentation
#print axioms automorphism_braid_generator_covariance
#print axioms canonical_braid_colimit_intertwines
#print axioms canonical_inverse_braid_colimit_intertwines

end InfoGeometry.Synthesis.ZornBraidIntertwiner.Tests
