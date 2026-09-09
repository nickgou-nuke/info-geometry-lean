import InfoGeometry.NCG.BlockSupermatrixGradedTrace

/-! Canonical export surface for the universal associative superbracket laws.
The finite block realization remains owned by the NCG module. -/

namespace InfoGeometry.Canonical.GLSupermatrixGradedLieBridge

open InfoGeometry.NCG.BlockSupermatrixGradedTrace

abbrev Parity := InfoGeometry.NCG.BlockSupermatrixGradedTrace.Parity

theorem graded_super_jacobi
    {A : Type*} [Ring A] (pX pY pZ : Parity) (X Y Z : A) :
    Parity.sign A pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
      Parity.sign A pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
      Parity.sign A pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 :=
  InfoGeometry.NCG.BlockSupermatrixGradedTrace.graded_super_jacobi pX pY pZ X Y Z

theorem super_adjoint_derivation
    {A : Type*} [Ring A] (pX pY pZ : Parity) (X Y Z : A) :
    ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) =
      ringSuperbracket (pX + pY) pZ (ringSuperbracket pX pY X Y) Z +
        Parity.sign A pX pY *
          ringSuperbracket pY (pX + pZ) Y (ringSuperbracket pX pZ X Z) :=
  InfoGeometry.NCG.BlockSupermatrixGradedTrace.super_adjoint_derivation
    pX pY pZ X Y Z

end InfoGeometry.Canonical.GLSupermatrixGradedLieBridge
