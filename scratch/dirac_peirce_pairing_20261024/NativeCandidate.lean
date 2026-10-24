/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracPeircePairing
import InfoGeometry.SuperMetriplectic.WittCyclotomicBridge

/-! The actual neutral frame defines existing Krein data. The actual Witt
support is an idempotent fixed by its Dirac adjoint, and trace pairing within
its off-diagonal Peirce corner separates arbitrary supported full matrices.
-/
namespace InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open Matrix InfoGeometry.Physics

def neutralKreinData (n : ℕ) : KasparovKreinData (Matrix2 n) :=
  ⟨{ eta := kreinMetric n, gamma := grading n }, by
    refine ⟨kreinMetric_sq n, ?_, grading_sq n, ?_⟩
    · change (kreinMetric n).conjTranspose = kreinMetric n
      rw [conjTranspose_eq_transpose_of_trivial, kreinMetric_transpose]
    · change (grading n).conjTranspose = grading n
      rw [conjTranspose_eq_transpose_of_trivial]
      simp [grading, Matrix.fromBlocks_transpose]⟩

end InfoGeometry.Quantum.NeutralKreinMajoranaFrame

namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.Core.PeirceDecomposition

theorem witt_support_idempotent (n : ℕ) :
    (wittAnnihilator n * wittCreator n) * (wittAnnihilator n * wittCreator n) =
      wittAnnihilator n * wittCreator n := by
  rw [← mul_assoc, wittAnnihilator_inner_inverse]

theorem witt_support_diracAdjoint (n : ℕ) :
    (neutralKreinData n).diracAdjoint (wittAnnihilator n * wittCreator n) =
      wittAnnihilator n * wittCreator n := by
  rw [InfoGeometry.Physics.KasparovKreinData.diracAdjoint_mul]
  change (kreinMetric n * (wittCreator n).conjTranspose * kreinMetric n) *
    (kreinMetric n * (wittAnnihilator n).conjTranspose * kreinMetric n) = _
  rw [wittCreator_metric_adjoint, wittAnnihilator_metric_adjoint, neg_mul_neg]

theorem witt_component10_eq_zero_of_dirac_trace_pairing (n : ℕ) (X : Matrix2 n)
    (hX : component10 (wittAnnihilator n * wittCreator n) X = X)
    (h : ∀ Y : Matrix2 n, trace (X * (neutralKreinData n).diracAdjoint
      (component10 (wittAnnihilator n * wittCreator n) Y)) = 0) : X = 0 :=
  (neutralKreinData n).component10_eq_zero_of_dirac_trace_pairing _ X
    (witt_support_diracAdjoint n) hX h

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
