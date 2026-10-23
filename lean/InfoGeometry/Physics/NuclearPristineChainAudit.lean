/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra
import InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier

/-!
# Constructive contact and finite nuclear operator audit

The contact bracket on the existing five-graded carrier has native Mathlib Lie
instances, obtained from its faithful representation. Jacobi does not require
homogeneous-cell hypotheses for the legacy bracket.

The finite nuclear operator facts are audited separately. These checks do not
identify the two carriers or supply a grade-preserving intertwiner between them.
See `docs/FREUDENTHAL_CONTACT_CONSUMER_REALIGNMENT.md` for the source contract.
-/

#print axioms InfoGeometry.Exceptional.Freudenthal.symplecticContactLieRing
#print axioms InfoGeometry.Exceptional.Freudenthal.symplecticContactLieAlgebra
#print axioms InfoGeometry.Exceptional.Freudenthal.symplecticContactRepresentationLieHom
#print axioms InfoGeometry.Exceptional.Freudenthal.symplecticContactRepresentationLieHom_injective
#print axioms InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represent_hasGrade
#print axioms InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.represented_commutator_hasGrade
#print axioms InfoGeometry.Physics.NuclearBdGSolovievCompression.bdgBlock_sq
#print axioms InfoGeometry.Physics.NuclearBdGSolovievCompression.solovievBlock_eq_center_add_bdg
#print axioms InfoGeometry.Physics.NuclearCARPhononCommonCarrier.compressedOscillatorHamiltonian_eq_soloviev

namespace InfoGeometry.Physics.NuclearPristineChainAudit

open InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

-- Global Jacobi for the corrected bracket, on its actual carrier.
example (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (symplecticContactBracket D v w) +
      symplecticContactBracket D v (symplecticContactBracket D w u) +
      symplecticContactBracket D w (symplecticContactBracket D u v) = 0 :=
  lie_jacobi u v w

-- The extreme/charge configuration that fails for the legacy bracket now closes.
example :
    ⁅genEminus D 1, ⁅injChargeMinus D (alphaCharge (J := J)), genEplus D 1⁆⁆ +
      ⁅injChargeMinus D (alphaCharge (J := J)), ⁅genEplus D 1, genEminus D 1⁆⁆ +
      ⁅genEplus D 1, ⁅genEminus D 1, injChargeMinus D (alphaCharge (J := J))⁆⁆ = 0 :=
  lie_jacobi _ _ _

end InfoGeometry.Physics.NuclearPristineChainAudit
