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
Data packet for the finite Hilbert spectral-theorem regime.

`Proj` is the carrier for spectral projectors and `Scalar` is the eigenvalue
carrier.  This module does not prove orthogonality, completeness, or
diagonalization for these abstract carriers.
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

namespace HilbertSpectralTheoremPacket

variable {Op Scalar Proj : Type*}

/-- Carrier readout for the supplied clean-sector spectral witness. -/
abbrev diagonalizationWitnessCarrier
    (S : HilbertSpectralTheoremPacket Op Scalar Proj) :
    Type* :=
  S.normalOrSelfAdjointWitness

/-- Carrier readout for the orthogonality/completeness witness slot. -/
abbrev orthogonalCompletenessWitnessCarrier
    (S : HilbertSpectralTheoremPacket Op Scalar Proj) :
    Type* :=
  S.normalOrSelfAdjointWitness

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
  /-- Off-diagonal/transient coupling readout. -/
  offDiagonalCouplingWitness : Type*

/--
Compatibility witness that Schur collapses to the spectral theorem in the clean
normal/self-adjoint regime.
-/
structure SpectralSchurCollapse
    (Op Scalar Proj Triangular Change : Type*)
    (S : HilbertSpectralTheoremPacket Op Scalar Proj)
    (Q : SchurFallbackPacket Op Triangular Change) where
  /-- Guardrail: the Schur/spectral collapse theorem is not proved here. -/
  collapseDebtGuard : Type*

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

namespace MoorePenroseMetricReadoutPacket

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The Penrose equations remain the owner of metric observable readout. -/
theorem penrose_laws (M : MoorePenroseMetricReadoutPacket Op) :
    IsMoorePenroseInverse M.A M.Aplus :=
  M.isMoorePenrose

end MoorePenroseMetricReadoutPacket

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
  /-- Semisimple chamber control; split/rank-boundary cases need extra data. -/
  semisimpleChamberWitness : Type*

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
  /-- L-function/scattering normalization witness. -/
  lFunctionNormalizationWitness : Type*

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
  /-- Guardrail: Krein and automorphic spectral theorems are separate witness layers. -/
  nonHilbertSpectralGuard : Type*

namespace SpectralSchurDrazinPenroseHierarchy

variable {Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket : Type*}
variable [Ring Op] [StarRing Op]

/-- Read back the clean-sector spectral witness carrier from the hierarchy. -/
abbrev spectral_diagonalizationWitnessCarrier
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    Type* :=
  HilbertSpectralTheoremPacket.diagonalizationWitnessCarrier H.spectral

/-- Read back the Schur fallback coupling witness carrier from the hierarchy. -/
abbrev schur_triangularFallbackWitnessCarrier
    (H :
      SpectralSchurDrazinPenroseHierarchy
        Op Scalar Proj Triangular Change Mode J Frame Bulk Boundary Eigenpacket) :
    Type* :=
  H.schur.offDiagonalCouplingWitness

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

end SpectralSchurDrazinPenroseHierarchy

end InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy
