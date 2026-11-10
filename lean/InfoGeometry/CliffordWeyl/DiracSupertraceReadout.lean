/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracTraceCovariance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.NCG.BerezinianSuperdeterminant

/-! The existing block supertrace applied to arbitrary Dirac ket–bras.
No block-diagonality, homogeneity, or commutation with the metric is required.
This is a trace pairing theorem, not a Berezinian or Pfaffian identity.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem diracSupertraceReadout_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Over any non-commutative `*-ring` `[Ring B] [StarRing B]`, left multiplication by `Gamma`
associates across `A * solder η l r`. -/
theorem solder_Gamma_mul_assoc {B ι : Type*} [Ring B] [StarRing B] [Fintype ι] [DecidableEq ι]
    (η A : Matrix (ι ⊕ ι) (ι ⊕ ι) B) (l r : (ι ⊕ ι) → B) :
    InfoGeometry.NCG.Gamma * (A * solder η l r) =
      (InfoGeometry.NCG.Gamma * A) * solder η l r :=
  (mul_assoc InfoGeometry.NCG.Gamma A (solder η l r)).symm

variable {R ι : Type*} [CommRing R] [StarRing R] [Fintype ι] [DecidableEq ι]

theorem solder_supertrace_readout (η A : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
    (l r : (ι ⊕ ι) → R) :
    InfoGeometry.NCG.superTrace (A * solder η l r) =
      bilinear η (InfoGeometry.NCG.Gamma * A) r l := by
  unfold InfoGeometry.NCG.superTrace
  rw [← mul_assoc]
  exact solder_trace_readout η (InfoGeometry.NCG.Gamma * A) l r

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
