/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracTraceCovariance
import InfoGeometry.NCG.BerezinianSuperdeterminant

/-! The existing block supertrace applied to arbitrary Dirac ket–bras.
No block-diagonality, homogeneity, or commutation with the metric is required.
This is a trace pairing theorem, not a Berezinian or Pfaffian identity.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix
variable {R ι : Type*} [CommRing R] [StarRing R] [Fintype ι] [DecidableEq ι]

theorem solder_supertrace_readout (η A : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
    (l r : (ι ⊕ ι) → R) :
    InfoGeometry.NCG.superTrace (A * solder η l r) =
      bilinear η (InfoGeometry.NCG.Gamma * A) r l := by
  unfold InfoGeometry.NCG.superTrace
  rw [← mul_assoc]
  exact solder_trace_readout η (InfoGeometry.NCG.Gamma * A) l r

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
