import Mathlib
import InfoGeometry.Singular.Drazin
import InfoGeometry.Singular.MoorePenrose

/-!
# InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy

This module keeps the theorem-backed part of the former spectral/Schur/Drazin/
Moore--Penrose hierarchy:

* algebraic Drazin zero-spectrum surgery, backed by `IsDrazinInverse`;
* Moore--Penrose metric readout, backed by `IsMoorePenroseInverse`.

It deliberately does not package Hilbert spectral, Schur collapse, Krein,
Jordan, or automorphic spectral theorem claims as abstract placeholder carriers.
Those results must enter through their own owner files with explicit theorem
statements.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy

open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

/-! ## Drazin and Moore--Penrose readout layers -/

/--
Drazin zero-spectrum surgery data.

The Drazin inverse remains algebraic. It cuts the regular core from the
generalized-zero/nilpotent sector, and the Drazin equations are stored as an
actual `IsDrazinInverse` proof.
-/
structure DrazinZeroSurgery
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

namespace DrazinZeroSurgery

variable {Op : Type*} [Ring Op]

/-- The Drazin equations remain the algebraic owner of zero-spectrum surgery. -/
theorem drazin_laws (D : DrazinZeroSurgery Op) :
    IsDrazinInverse D.A D.AD D.index :=
  D.isDrazin

end DrazinZeroSurgery

/--
Moore--Penrose metric readout data.

The Moore--Penrose inverse is the metric/SVD observable-range layer, not the
same object as Drazin unless an extra normal/regular-sector compatibility
theorem is supplied by another owner.
-/
structure MoorePenroseMetricReadout
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

namespace MoorePenroseMetricReadout

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The Penrose equations remain the owner of metric observable readout. -/
theorem penrose_laws (M : MoorePenroseMetricReadout Op) :
    IsMoorePenroseInverse M.A M.Aplus :=
  M.isMoorePenrose

end MoorePenroseMetricReadout

end InfoGeometry.Canonical.SpectralSchurDrazinPenroseHierarchy
