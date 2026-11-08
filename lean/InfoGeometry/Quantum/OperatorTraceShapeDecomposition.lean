import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scalar volume and traceless shape parts of an endomorphism

The trace decomposition is algebraic and does not assume an operator
logarithm, positivity, or a determinant.  It is therefore the safe common
owner for later Weyl/shape surprisal readouts.
-/

namespace InfoGeometry.Quantum.OperatorTraceShapeDecomposition

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
  [Module.Free ℝ H] [Module.Finite ℝ H]

noncomputable def scalarTracePart (A : Module.End ℝ H) : Module.End ℝ H :=
  (((Module.finrank ℝ H : ℝ)⁻¹) * LinearMap.trace ℝ H A) • LinearMap.id

noncomputable def shapePart (A : Module.End ℝ H) : Module.End ℝ H :=
  A - scalarTracePart A

theorem trace_smul_id (k : ℝ) :
    LinearMap.trace ℝ H (k • LinearMap.id) =
      k * (Module.finrank ℝ H : ℝ) := by
  rw [map_smul, LinearMap.trace_id, smul_eq_mul]

theorem trace_smul_id_add (k : ℝ) (A : Module.End ℝ H) :
    LinearMap.trace ℝ H (k • LinearMap.id + A) =
      k * (Module.finrank ℝ H : ℝ) + LinearMap.trace ℝ H A := by
  rw [map_add, trace_smul_id]

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem scalarTracePart_eq_zero_of_trace_zero
    (A : Module.End ℝ H)
    (hA : LinearMap.trace ℝ H A = 0) :
    scalarTracePart A = 0 := by
  simp [scalarTracePart, hA]

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem shapePart_eq_self_of_trace_zero
    (A : Module.End ℝ H)
    (hA : LinearMap.trace ℝ H A = 0) :
    shapePart A = A := by
  simp [shapePart, scalarTracePart_eq_zero_of_trace_zero A hA]

noncomputable def pairedTrace (Aplus Aminus : Module.End ℝ H) : ℝ :=
  LinearMap.trace ℝ H Aplus + LinearMap.trace ℝ H Aminus

noncomputable def pairedSupertrace (Aplus Aminus : Module.End ℝ H) : ℝ :=
  LinearMap.trace ℝ H Aplus - LinearMap.trace ℝ H Aminus

theorem pairedTrace_smul_id (kplus kminus : ℝ) :
    pairedTrace (kplus • (LinearMap.id : Module.End ℝ H))
        (kminus • (LinearMap.id : Module.End ℝ H)) =
      (kplus + kminus) * (Module.finrank ℝ H : ℝ) := by
  simp [pairedTrace, trace_smul_id (H := H)]
  ring

theorem pairedSupertrace_smul_id (kplus kminus : ℝ) :
    pairedSupertrace (kplus • (LinearMap.id : Module.End ℝ H))
        (kminus • (LinearMap.id : Module.End ℝ H)) =
      (kplus - kminus) * (Module.finrank ℝ H : ℝ) := by
  simp [pairedSupertrace, trace_smul_id (H := H)]
  ring

theorem pairedSupertrace_common_smul (k : ℝ) :
    pairedSupertrace (k • (LinearMap.id : Module.End ℝ H))
        (k • (LinearMap.id : Module.End ℝ H)) = 0 := by
  simp [pairedSupertrace]

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem pairedTrace_swap (Aplus Aminus : Module.End ℝ H) :
    pairedTrace Aminus Aplus = pairedTrace Aplus Aminus := by
  simp [pairedTrace, add_comm]

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem pairedSupertrace_swap (Aplus Aminus : Module.End ℝ H) :
    pairedSupertrace Aminus Aplus = -pairedSupertrace Aplus Aminus := by
  simp [pairedSupertrace, sub_eq_add_neg]

theorem trace_shapePart
    (A : Module.End ℝ H)
    (hH : Module.finrank ℝ H ≠ 0) :
    LinearMap.trace ℝ H (shapePart A) = 0 := by
  rw [shapePart, map_sub, scalarTracePart, map_smul, LinearMap.trace_id]
  have hcast : (Module.finrank ℝ H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH
  simp only [smul_eq_mul]
  field_simp
  ring

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem decomposition_eq
    (A : Module.End ℝ H) :
    scalarTracePart A + shapePart A = A := by
  simp [shapePart]

theorem trace_scalarTracePart
    (A : Module.End ℝ H)
    (hH : Module.finrank ℝ H ≠ 0) :
    LinearMap.trace ℝ H (scalarTracePart A) =
      LinearMap.trace ℝ H A := by
  rw [scalarTracePart, map_smul, LinearMap.trace_id]
  have hcast : (Module.finrank ℝ H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH
  simp only [smul_eq_mul]
  field_simp

structure PairedEnd where
  plus : Module.End ℝ H
  minus : Module.End ℝ H

instance : Add (PairedEnd (H := H)) where
  add A B := { plus := A.plus + B.plus, minus := A.minus + B.minus }

instance : SMul ℝ (PairedEnd (H := H)) where
  smul k A := { plus := k • A.plus, minus := k • A.minus }

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem pairedEnd_ext {A B : PairedEnd (H := H)}
    (hplus : A.plus = B.plus) (hminus : A.minus = B.minus) : A = B := by
  cases A
  cases B
  simp_all

noncomputable def pairedCommonCoefficient (Aplus Aminus : Module.End ℝ H) : ℝ :=
  ((pairedTrace Aplus Aminus) / (2 * (Module.finrank ℝ H : ℝ)))

noncomputable def pairedRelativeCoefficient (Aplus Aminus : Module.End ℝ H) : ℝ :=
  ((pairedSupertrace Aplus Aminus) / (2 * (Module.finrank ℝ H : ℝ)))

theorem pairedCommonCoefficient_smul_id
    (kplus kminus : ℝ)
    (hH : Module.finrank ℝ H ≠ 0) :
    pairedCommonCoefficient
        (kplus • (LinearMap.id : Module.End ℝ H))
        (kminus • (LinearMap.id : Module.End ℝ H)) =
      (kplus + kminus) / 2 := by
  unfold pairedCommonCoefficient
  rw [pairedTrace_smul_id]
  have hcast : (Module.finrank ℝ H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hH
  field_simp

theorem pairedRelativeCoefficient_smul_id
    (kplus kminus : ℝ)
    (hH : Module.finrank ℝ H ≠ 0) :
    pairedRelativeCoefficient
        (kplus • (LinearMap.id : Module.End ℝ H))
        (kminus • (LinearMap.id : Module.End ℝ H)) =
      (kplus - kminus) / 2 := by
  unfold pairedRelativeCoefficient
  rw [pairedSupertrace_smul_id]
  have hcast : (Module.finrank ℝ H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hH
  field_simp

noncomputable def pairedShapePart (Aplus Aminus : Module.End ℝ H) :
    PairedEnd (H := H) where
  plus := Aplus -
      (pairedCommonCoefficient Aplus Aminus +
        pairedRelativeCoefficient Aplus Aminus) • LinearMap.id
  minus := Aminus -
      (pairedCommonCoefficient Aplus Aminus -
        pairedRelativeCoefficient Aplus Aminus) • LinearMap.id

theorem pairedShapePart_smul_id
    (kplus kminus : ℝ)
    (hH : Module.finrank ℝ H ≠ 0) :
    pairedShapePart
        (kplus • (LinearMap.id : Module.End ℝ H))
        (kminus • (LinearMap.id : Module.End ℝ H)) =
      { plus := 0, minus := 0 } := by
  apply pairedEnd_ext
  · simp [pairedShapePart,
      pairedCommonCoefficient_smul_id kplus kminus hH,
      pairedRelativeCoefficient_smul_id kplus kminus hH]
    module
  · simp [pairedShapePart,
      pairedCommonCoefficient_smul_id kplus kminus hH,
      pairedRelativeCoefficient_smul_id kplus kminus hH]
    module

def pairedIdentity : PairedEnd (H := H) where
  plus := LinearMap.id
  minus := LinearMap.id

def pairedGrading : PairedEnd (H := H) where
  plus := LinearMap.id
  minus := -LinearMap.id

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem paired_decomposition
    (Aplus Aminus : Module.End ℝ H) :
    Aplus =
        (pairedCommonCoefficient Aplus Aminus +
          pairedRelativeCoefficient Aplus Aminus) • LinearMap.id +
          (pairedShapePart Aplus Aminus).plus ∧
    Aminus =
          (pairedCommonCoefficient Aplus Aminus -
            pairedRelativeCoefficient Aplus Aminus) • LinearMap.id +
          (pairedShapePart Aplus Aminus).minus := by
  constructor <;> simp [pairedShapePart]

omit [Module.Free ℝ H] [Module.Finite ℝ H] in
theorem paired_decomposition_bundled
    (Aplus Aminus : Module.End ℝ H) :
    ({ plus := Aplus, minus := Aminus } : PairedEnd (H := H)) =
      (pairedCommonCoefficient Aplus Aminus) • pairedIdentity +
        (pairedRelativeCoefficient Aplus Aminus) • pairedGrading +
        pairedShapePart Aplus Aminus := by
  apply pairedEnd_ext
  · change Aplus =
      (pairedCommonCoefficient Aplus Aminus • LinearMap.id +
        pairedRelativeCoefficient Aplus Aminus • LinearMap.id) +
        (Aplus -
          (pairedCommonCoefficient Aplus Aminus +
            pairedRelativeCoefficient Aplus Aminus) • LinearMap.id)
    module
  · change Aminus =
      (pairedCommonCoefficient Aplus Aminus • LinearMap.id +
        pairedRelativeCoefficient Aplus Aminus • (-LinearMap.id)) +
        (Aminus -
          (pairedCommonCoefficient Aplus Aminus -
            pairedRelativeCoefficient Aplus Aminus) • LinearMap.id)
    module

theorem pairedShapePart_trace_zero
    (Aplus Aminus : Module.End ℝ H)
    (hH : Module.finrank ℝ H ≠ 0) :
    pairedTrace (pairedShapePart Aplus Aminus).plus
        (pairedShapePart Aplus Aminus).minus = 0 := by
  unfold pairedTrace pairedShapePart
  simp only [map_sub, map_smul, LinearMap.trace_id, smul_eq_mul]
  unfold pairedCommonCoefficient pairedRelativeCoefficient pairedTrace
    pairedSupertrace at *
  field_simp
  ring_nf

theorem pairedShapePart_supertrace_zero
    (Aplus Aminus : Module.End ℝ H)
    (hH : Module.finrank ℝ H ≠ 0) :
    pairedSupertrace (pairedShapePart Aplus Aminus).plus
        (pairedShapePart Aplus Aminus).minus = 0 := by
  unfold pairedSupertrace pairedShapePart
  simp only [map_sub, map_smul, LinearMap.trace_id, smul_eq_mul]
  unfold pairedCommonCoefficient pairedRelativeCoefficient pairedTrace
    pairedSupertrace
  field_simp
  ring_nf

end InfoGeometry.Quantum.OperatorTraceShapeDecomposition
