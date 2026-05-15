import Mathlib
import InfoGeometry.Singular.Drazin
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.SchurDrazinMoorePenrose

/-!
# InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy

The spectral theorem is the clean regular-sector law:

```text
normal/self-adjoint operator
  -> orthogonal spectral projectors
  -> mode-by-mode functional calculus.
```

This file places that clean layer above the existing Schur/Drazin/Moore--Penrose
stack:

```text
spectral theorem     : orthogonal diagonalization in normal regular sectors;
Schur decomposition  : triangular fallback for non-normal finite operators;
Drazin inverse       : surgery at the zero/generalized-zero spectrum;
Moore--Penrose       : metric/SVD readout of observable range and kernel.
```

Krein, Jordan, and automorphic spectral decompositions are recorded as separate
witness packets.  This module does not prove a Hilbert spectral theorem, a Krein
spectral theorem, a Jordan spectral theorem, or an automorphic Plancherel/Hecke
theorem.  It packages the hierarchy so downstream bridge files cannot confuse
the clean diagonal case with Schur fallback or Drazin singular surgery.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy

set_option linter.dupNamespace false

open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

/-! ## 1. Clean Hilbert spectral layer -/

/--
Witness packet for the finite Hilbert spectral-theorem regime.

`Proj` is the carrier for spectral projectors and `Scalar` is the eigenvalue
carrier.  Orthogonality, self-adjointness, completeness, and diagonalization are
stored as certified laws because this module is only the hierarchy socket.
-/
structure HilbertSpectralTheoremPacket
    (Op Scalar Proj : Type*) where
  /-- Operator being decomposed. -/
  A : Op
  /-- Spectral labels. -/
  Spectrum : Type*
  /-- Eigenvalue readout. -/
  eigenvalue : Spectrum → Scalar
  /-- Spectral projector readout. -/
  projector : Spectrum → Proj
  /-- Normal/self-adjoint hypothesis supplying the clean spectral theorem. -/
  normalOrSelfAdjointWitness : Type*
  /-- Orthogonal projector laws: `PλPμ = δλμPλ`, `Pλ* = Pλ`. -/
  orthogonalProjectorLaw : Prop
  /-- Completeness law: the projectors sum to identity. -/
  completeProjectorLaw : Prop
  /-- Diagonalization law: `A = Σ λ Pλ`. -/
  diagonalizationLaw : Prop
  /-- Functional calculus law: `f(A) = Σ f(λ)Pλ`. -/
  functionalCalculusLaw : Prop
  /-- Dynamics law: `exp(tA) = Σ exp(tλ)Pλ`, when that readout is supplied. -/
  dynamicsLaw : Prop
  /-- Certificate for orthogonal projector laws. -/
  orthogonalProjectorCertificate : orthogonalProjectorLaw
  /-- Certificate for completeness. -/
  completeProjectorCertificate : completeProjectorLaw
  /-- Certificate for diagonalization. -/
  diagonalizationCertificate : diagonalizationLaw

namespace HilbertSpectralTheoremPacket

variable {Op Scalar Proj : Type*}

/-- Re-export the clean spectral diagonalization law. -/
theorem diagonalization
    (S : HilbertSpectralTheoremPacket Op Scalar Proj) :
    S.diagonalizationLaw :=
  S.diagonalizationCertificate

/-- Re-export orthogonality/completeness as the clean spectral-mode guardrail. -/
theorem orthogonal_and_complete
    (S : HilbertSpectralTheoremPacket Op Scalar Proj) :
    S.orthogonalProjectorLaw ∧ S.completeProjectorLaw :=
  ⟨S.orthogonalProjectorCertificate, S.completeProjectorCertificate⟩

end HilbertSpectralTheoremPacket

/-! ## 2. Schur fallback layer -/

/--
Schur fallback packet for non-normal or not-yet-normalized finite operators.

When the spectral theorem applies, the triangular form is expected to collapse
to a diagonal chart.  In the non-normal case, the off-diagonal triangular part
records transient coupling/Jordan-chain behavior.
-/
structure SchurFallbackPacket
    (Op Triangular Change : Type*) where
  /-- Input operator. -/
  A : Op
  /-- Upper-triangular Schur form. -/
  T : Triangular
  /-- Change-of-basis/unitary chart carrier. -/
  Q : Change
  /-- Factorization law, morally `A = Q T Q*`. -/
  factorizationLaw : Prop
  /-- Upper-triangular law for the Schur chart. -/
  triangularLaw : Prop
  /-- Off-diagonal/transient coupling readout. -/
  offDiagonalCouplingWitness : Type*
  /-- Certificate of factorization. -/
  factorizationCertificate : factorizationLaw
  /-- Certificate of triangularity. -/
  triangularCertificate : triangularLaw

/--
Compatibility witness that Schur collapses to the spectral theorem in the clean
normal/self-adjoint regime.
-/
structure SpectralSchurCollapse
    (Op Scalar Proj Triangular Change : Type*)
    (S : HilbertSpectralTheoremPacket Op Scalar Proj)
    (Q : SchurFallbackPacket Op Triangular Change) where
  /-- The Schur triangular form is diagonal in the spectral regime. -/
  triangular_is_diagonal : Prop
  /-- The diagonal readout agrees with the spectral eigenvalue readout. -/
  diagonal_agrees_with_spectrum : Prop
  /-- Certificate for diagonal Schur collapse. -/
  triangular_is_diagonal_holds : triangular_is_diagonal
  /-- Certificate for spectral/Schur diagonal agreement. -/
  diagonal_agrees_with_spectrum_holds : diagonal_agrees_with_spectrum

/-! ## 3. Drazin and Moore--Penrose readout layers -/

/--
Drazin zero-spectrum surgery packet.

The Drazin inverse remains algebraic.  It cuts the regular core from the
generalized-zero/nilpotent sector.
-/
structure DrazinZeroSurgeryPacket
    (Op : Type*) [Ring Op] where
  /-- Operator. -/
  A : Op
  /-- Algebraic Drazin inverse candidate. -/
  AD : Op
  /-- Drazin index. -/
  index : ℕ
  /-- Algebraic Drazin equations. -/
  isDrazin : IsDrazinInverse A AD index
  /-- Regular projector, morally `A * AD`. -/
  regularProjector : Op
  /-- Nil/generalized-zero projector, morally `1 - A * AD`. -/
  nilProjector : Op
  /-- Regular projector definition/readout. -/
  regularProjectorLaw : Prop
  /-- Nil projector definition/readout. -/
  nilProjectorLaw : Prop
  /-- Certificate for the regular projector readout. -/
  regularProjectorCertificate : regularProjectorLaw
  /-- Certificate for the nil projector readout. -/
  nilProjectorCertificate : nilProjectorLaw

namespace DrazinZeroSurgeryPacket

variable {Op : Type*} [Ring Op]

/-- The Drazin equations remain the algebraic owner of zero-spectrum surgery. -/
theorem drazin_laws (D : DrazinZeroSurgeryPacket Op) :
    IsDrazinInverse D.A D.AD D.index :=
  D.isDrazin

end DrazinZeroSurgeryPacket

/--
Moore--Penrose metric readout packet.

The Moore--Penrose inverse is the metric/SVD observable-range layer, not the
same object as Drazin unless an extra normal/regular-sector compatibility
witness is supplied.
-/
structure MoorePenroseMetricReadoutPacket
    (Op : Type*) [Ring Op] [StarRing Op] where
  /-- Operator. -/
  A : Op
  /-- Moore--Penrose inverse candidate. -/
  Aplus : Op
  /-- Penrose equations. -/
  isMoorePenrose : IsMoorePenroseInverse A Aplus
  /-- Range projector, morally `A * A+`. -/
  rangeProjector : Op
  /-- Domain/kernel-complement projector, morally `A+ * A`. -/
  domainProjector : Op
  /-- Range projector readout law. -/
  rangeProjectorLaw : Prop
  /-- Domain projector readout law. -/
  domainProjectorLaw : Prop
  /-- Certificate for range projector readout. -/
  rangeProjectorCertificate : rangeProjectorLaw
  /-- Certificate for domain projector readout. -/
  domainProjectorCertificate : domainProjectorLaw

namespace MoorePenroseMetricReadoutPacket

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The Penrose equations remain the owner of metric observable readout. -/
theorem penrose_laws (M : MoorePenroseMetricReadoutPacket Op) :
    IsMoorePenroseInverse M.A M.Aplus :=
  M.isMoorePenrose

end MoorePenroseMetricReadoutPacket

/--
Compatibility witness for the ideal normal/self-adjoint regular sector.

In that clean regime the spectral zero projector, Drazin nil projector, and
Moore--Penrose kernel projector can be identified.  This is not automatic in
non-normal or indefinite/Krein settings.
-/
structure NormalSectorInverseCompatibility
    (Op Scalar Proj : Type*) [Ring Op] [StarRing Op]
    (S : HilbertSpectralTheoremPacket Op Scalar Proj)
    (D : DrazinZeroSurgeryPacket Op)
    (M : MoorePenroseMetricReadoutPacket Op) where
  /-- The Drazin and Moore--Penrose inverse candidates agree in the normal sector. -/
  drazin_eq_moorePenrose : Prop
  /-- The regular projectors agree. -/
  regularProjectorsAgree : Prop
  /-- The singular/kernel projectors agree with the spectral zero projector. -/
  zeroProjectorsAgree : Prop
  /-- Certificate for inverse equality. -/
  drazin_eq_moorePenrose_holds : drazin_eq_moorePenrose
  /-- Certificate for regular-projector agreement. -/
  regularProjectorsAgree_holds : regularProjectorsAgree
  /-- Certificate for zero-projector agreement. -/
  zeroProjectorsAgree_holds : zeroProjectorsAgree

namespace NormalSectorInverseCompatibility

variable {Op Scalar Proj : Type*} [Ring Op] [StarRing Op]
variable {S : HilbertSpectralTheoremPacket Op Scalar Proj}
variable {D : DrazinZeroSurgeryPacket Op}
variable {M : MoorePenroseMetricReadoutPacket Op}

/-- In the clean normal sector, Drazin and Moore--Penrose are compatible by witness. -/
theorem inverse_and_projector_agreement
    (C : NormalSectorInverseCompatibility Op Scalar Proj S D M) :
    C.drazin_eq_moorePenrose ∧ C.regularProjectorsAgree ∧ C.zeroProjectorsAgree :=
  ⟨C.drazin_eq_moorePenrose_holds,
    C.regularProjectorsAgree_holds,
    C.zeroProjectorsAgree_holds⟩

end NormalSectorInverseCompatibility

/-! ## 4. Krein, Jordan, and automorphic spectral packets -/

/--
Krein/split-signature spectral packet.

Krein-self-adjointness does not imply the positive Hilbert spectral theorem.
Definitizability, controlled non-isotropic eigenspaces, or diagonalizability
must be supplied explicitly.
-/
structure KreinSpectralAnalysisPacket
    (Op Mode : Type*) where
  /-- Operator in a Krein/split-signature sector. -/
  A : Op
  /-- Indefinite spectral mode carrier. -/
  mode : Type*
  /-- Mode readout. -/
  modeReadout : mode → Mode
  /-- Krein-self-adjointness witness, e.g. `A♯ = A`. -/
  kreinSelfAdjointWitness : Type*
  /-- Additional definitizability/diagonalizability control. -/
  spectralControlWitness : Type*
  /-- Exceptional/Jordan-block sector witness, if present. -/
  exceptionalSectorWitness : Type*

/--
Jordan spectral chamber packet.

For Euclidean Jordan algebras this represents the usual spectral decomposition
`X = Σ λᵢ eᵢ`.  For split Jordan algebras it is only a semisimple-chamber
witness; rank-deficient/nilpotent boundaries belong to Drazin--Schur surgery.
-/
structure JordanSpectralChamberPacket
    (J Scalar Frame : Type*) where
  /-- Jordan element. -/
  X : J
  /-- Frame index carrier. -/
  Index : Type*
  /-- Eigenvalue/Jordan root readout. -/
  eigenvalue : Index → Scalar
  /-- Jordan-frame idempotent readout. -/
  frameIdempotent : Index → Frame
  /-- Spectral expansion law `X = Σ λᵢ eᵢ`. -/
  spectralExpansionLaw : Prop
  /-- Jordan-frame orthogonality/completeness law. -/
  jordanFrameLaw : Prop
  /-- Norm determinant/product law, e.g. `N_J(X) = Π λᵢ`. -/
  normProductLaw : Prop
  /-- Semisimple chamber control; split/rank-boundary cases need extra data. -/
  semisimpleChamberWitness : Type*
  /-- Certificate for spectral expansion. -/
  spectralExpansionCertificate : spectralExpansionLaw

/--
Automorphic Siegel--Hecke spectral packet.

The Siegel constant term extracts boundary/Eisenstein data.  Hecke/Laplace
spectral decomposition diagonalizes the commuting arithmetic operators.  This
packet records that analytic spectral theorem as supplied data.
-/
structure AutomorphicSiegelHeckeSpectralPacket
    (Bulk Boundary Eigenpacket : Type*) where
  /-- Bulk automorphic datum. -/
  bulk : Bulk
  /-- Siegel constant-term/boundary readout. -/
  constantTerm : Bulk → Boundary
  /-- Hecke/Laplace eigenpacket readout of the boundary term. -/
  heckeSpectralReadout : Boundary → Eigenpacket
  /-- Cusp/residual/Eisenstein decomposition law. -/
  automorphicDecompositionLaw : Prop
  /-- Boundary scattering/eigenmode law. -/
  boundarySpectralLaw : Prop
  /-- L-function/scattering normalization witness. -/
  lFunctionNormalizationWitness : Type*
  /-- Certificate for automorphic decomposition. -/
  automorphicDecompositionCertificate : automorphicDecompositionLaw

/-! ## 5. Full hierarchy packet -/

/--
Complete hierarchy packet.

The order is:

1. spectral theorem for the clean normal/self-adjoint regular sector;
2. Schur fallback when normality fails;
3. Drazin zero/generalized-zero surgery;
4. Moore--Penrose metric observable readout;
5. Jordan and automorphic spectral analogues as separate witness layers.
-/
structure SpectralSchurDrazinPenroseHierarchy
    (Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket : Type*)
    [Ring Op] [StarRing Op] where
  /-- Clean Hilbert spectral theorem packet. -/
  spectral :
    HilbertSpectralTheoremPacket Op Scalar Proj
  /-- Schur fallback packet. -/
  schur :
    SchurFallbackPacket Op Triangular Change
  /-- Witness that Schur collapses to spectral diagonalization in the clean case. -/
  spectralSchurCollapse :
    SpectralSchurCollapse Op Scalar Proj Triangular Change spectral schur
  /-- Drazin zero-spectrum surgery packet. -/
  drazin :
    DrazinZeroSurgeryPacket Op
  /-- Moore--Penrose metric readout packet. -/
  moorePenrose :
    MoorePenroseMetricReadoutPacket Op
  /-- Normal-sector compatibility of spectral/Drazin/Moore--Penrose projectors. -/
  normalSectorCompatibility :
    NormalSectorInverseCompatibility Op Scalar Proj spectral drazin moorePenrose
  /-- Krein/split-signature spectral packet. -/
  krein :
    KreinSpectralAnalysisPacket Op Mode
  /-- Jordan semisimple-chamber spectral packet. -/
  jordan :
    JordanSpectralChamberPacket J Scalar Frame
  /-- Automorphic Siegel--Hecke spectral packet. -/
  automorphic :
    AutomorphicSiegelHeckeSpectralPacket Bulk Boundary Eigenpacket
  /-- Guardrail: spectral theorem is the clean regular-phase law, not Drazin surgery. -/
  spectralAboveSchurGuard : Type*
  /-- Guardrail: Drazin and Moore--Penrose agree only under explicit compatibility. -/
  inverseCompatibilityGuard : Type*
  /-- Guardrail: Krein and automorphic spectral theorems are separate witness layers. -/
  nonHilbertSpectralGuard : Type*

namespace SpectralSchurDrazinPenroseHierarchy

variable {Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket : Type*}
variable [Ring Op] [StarRing Op]

/-- Read back the clean spectral diagonalization law from the hierarchy. -/
theorem spectral_diagonalization
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    H.spectral.diagonalizationLaw :=
  H.spectral.diagonalizationCertificate

/-- Read back the Schur triangular fallback law from the hierarchy. -/
theorem schur_triangular_fallback
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    H.schur.triangularLaw :=
  H.schur.triangularCertificate

/-- Read back algebraic Drazin surgery from the hierarchy. -/
theorem drazin_zero_surgery
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    IsDrazinInverse H.drazin.A H.drazin.AD H.drazin.index :=
  H.drazin.isDrazin

/-- Read back Moore--Penrose metric observable laws from the hierarchy. -/
theorem moorePenrose_metric_readout
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    IsMoorePenroseInverse H.moorePenrose.A H.moorePenrose.Aplus :=
  H.moorePenrose.isMoorePenrose

/-- In the clean normal sector, inverse/projector agreement is supplied explicitly. -/
theorem normal_sector_inverse_projector_agreement
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    H.normalSectorCompatibility.drazin_eq_moorePenrose ∧
      H.normalSectorCompatibility.regularProjectorsAgree ∧
        H.normalSectorCompatibility.zeroProjectorsAgree :=
  NormalSectorInverseCompatibility.inverse_and_projector_agreement H.normalSectorCompatibility

end SpectralSchurDrazinPenroseHierarchy

end InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy
