import InfoGeometry.Canonical.DiracSouriauOperator
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.KKTClosureSymmetry

/-!
# InfoGeometry.Canonical.DiracSouriauKKTChiralContext

Explicit context bridge between the finite `4×4` Dirac-Souriau block sector and
the existing KKT/chiral operator lane.

This file intentionally does not identify the finite matrix blocks with the
KKT operators.  It records the exact context needed to use both surfaces
together: a local Drazin witness for one Dirac-Souriau sector, and a certified
inverse-kernel carrier whose supercharge already satisfies the KKT/chiral
closure theorems.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DiracSouriau

open InfoGeometry.Canonical.KKTClosure
open InfoGeometry.Canonical.ChiralOperatorConeClosure
open InfoGeometry.Canonical.DrazinSupercharge

section KKTChiral

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Context joining one concrete finite Dirac-Souriau sector to one certified
KKT/chiral operator carrier.
-/
structure KKTChiralContext (S : DiracSouriauSector ℝ) where
  CIK : CertifiedInverseKernel E
  drazin : DiracSouriauSector.DrazinWitnessContext S

/--
Construct the KKT/chiral bridge context for a real finite Dirac-Souriau sector
without requiring an externally supplied Drazin witness.  The Drazin component
is built from the field-level finite-dimensional Drazin existence theorem.
-/
noncomputable def KKTChiralContext.ofField
    (S : DiracSouriauSector ℝ) (CIK : CertifiedInverseKernel E) :
    KKTChiralContext (E := E) S where
  CIK := CIK
  drazin := DiracSouriauSector.DrazinWitnessContext.ofField S

/-- The field-constructed context carries the canonical Drazin witness. -/
theorem hasDrazinInverse_of_kktChiralContext_ofField
    (S : DiracSouriauSector ℝ) (CIK : CertifiedInverseKernel E) :
    S.HasDrazinInverse
      (KKTChiralContext.ofField (E := E) S CIK).drazin.k :=
  DiracSouriauSector.hasDrazinInverse_of_fieldContext S

/-- The context carries the local Dirac-Souriau Drazin hypothesis. -/
theorem hasDrazinInverse_of_kktChiralContext
    {S : DiracSouriauSector ℝ} (Ctxt : KKTChiralContext (E := E) S) :
    S.HasDrazinInverse Ctxt.drazin.k :=
  DiracSouriauSector.hasDrazinInverse_of_context Ctxt.drazin

/-- The certified supercharge in the context is in the chiral operator cone. -/
theorem supercharge_mem_chiralOperatorCone_of_kktChiralContext
    {S : DiracSouriauSector ℝ} (Ctxt : KKTChiralContext (E := E) S) :
    IsInChiralOperatorCone Ctxt.CIK
      (DrazinSupercharge.CertifiedInverseKernel.supercharge Ctxt.CIK) :=
  supercharge_mem_chiralOperatorCone Ctxt.CIK

/-- The certified supercharge in the context satisfies the KKT odd-odd closure. -/
theorem anticommutator_QD_QD_eq_two_smul_HD_of_kktChiralContext
    {S : DiracSouriauSector ℝ} (Ctxt : KKTChiralContext (E := E) S) :
    DrazinSupercharge.anticommutator (QD Ctxt.CIK) (QD Ctxt.CIK) =
      (2 : ℝ) • HD Ctxt.CIK :=
  anticommutator_QD_QD_eq_two_smul_HD Ctxt.CIK

end KKTChiral

end InfoGeometry.Canonical.DiracSouriau
