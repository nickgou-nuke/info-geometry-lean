import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation

/-!
# Null Zorn vectors and the native Clifford/Dirac nilpotent closure

This module records the consequence of the existing Zorn quadratic form and
the existing Clifford representation: a null typed Zorn vector gives a
square-zero degree-one Clifford generator, and its Dirac action is
square-zero on the full doubled chiral carrier.

No new Zorn carrier, projective quotient, or Goldstone/representation claim is
introduced here.  The statements use the native `QuadraticForm`,
`CliffordAlgebra`, and `Module.End` objects owned upstream.
-/

noncomputable section

namespace CanonicalZornNullCliffordClosure

open CanonicalZornCliffordRepresentation

theorem zorn_null_clifford_generator_sq
    (V : CanonicalZornCompositionTriality.Vector8)
    (hV : vectorQuadratic V = 0) :
    CliffordAlgebra.ι vectorQuadratic V *
        CliffordAlgebra.ι vectorQuadratic V = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, hV]
  simp

theorem zorn_null_dirac_gamma_sq
    (V : CanonicalZornCompositionTriality.Vector8)
    (hV : vectorQuadratic V = 0) :
    diracGamma V * diracGamma V = 0 := by
  rw [diracGamma_sq, hV]
  simp

theorem zorn_null_dirac_gamma_apply_sq
    (V : CanonicalZornCompositionTriality.Vector8)
    (hV : vectorQuadratic V = 0)
    (Psi : DiracSpinor16) :
    diracGamma V (diracGamma V Psi) = 0 := by
  have h := diracGamma_sq_apply V Psi
  rw [hV] at h
  simpa using h

theorem zorn_null_clifford_representation_sq
    (V : CanonicalZornCompositionTriality.Vector8)
    (hV : vectorQuadratic V = 0) :
    zornCliffordRepresentation
        (CliffordAlgebra.ι vectorQuadratic V) *
      zornCliffordRepresentation
        (CliffordAlgebra.ι vectorQuadratic V) = 0 := by
  rw [zornCliffordRepresentation_ι, zorn_null_dirac_gamma_sq V hV]

theorem zorn_null_clifford_representation_apply_sq
    (V : CanonicalZornCompositionTriality.Vector8)
    (hV : vectorQuadratic V = 0)
    (Psi : DiracSpinor16) :
    zornCliffordRepresentation
        (CliffordAlgebra.ι vectorQuadratic V)
        (zornCliffordRepresentation
          (CliffordAlgebra.ι vectorQuadratic V) Psi) = 0 := by
  have h := congrArg
    (fun A : Module.End ℂ DiracSpinor16 => A Psi)
    (zorn_null_clifford_representation_sq V hV)
  simpa [Module.End.mul_apply] using h

end CanonicalZornNullCliffordClosure

end
