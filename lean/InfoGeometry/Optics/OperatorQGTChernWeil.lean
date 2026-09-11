import InfoGeometry.Optics.OperatorQGTGaugeInvariants
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Operator QGT Bianchi and Chern--Weil bridge

The adjoint Bianchi equation already controls the complete noncommutative
curvature.  Cyclicity of the native finite-rank linear trace removes its
commutator channel.  Consequently both the traced curvature derivative and
the traced quadratic-curvature derivative vanish, and the first derivative
readout is preserved by local gauge transport.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTChernWeil

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeAdjointAction
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.LocalGaugeGroupAction
open InfoGeometry.Optics.OperatorQGTGaugeInvariants
open InfoGeometry.Optics.OperatorQGTGaugeModuli
open InfoGeometry.Optics.OperatorValuedConnection

variable {V Point Tangent : Type*} [AddCommGroup V] [Module ℂ V]

/-- The native linear trace annihilates an associative operator commutator. -/
theorem trace_associativeCommutator_zero
    (A B : Module.End ℂ V) :
    LinearMap.trace ℂ V (associativeCommutator A B) = 0 := by
  unfold associativeCommutator
  rw [map_sub, LinearMap.trace_mul_comm]
  exact sub_self _

/-- Tracing an adjoint covariant derivative removes precisely its connection
commutator, leaving the trace of the supplied ordinary derivative channel. -/
theorem trace_adjointCovariantDerivative
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := Module.End ℂ V))
    (p : Point) (X : Tangent) :
    LinearMap.trace ℂ V (adjointCovariantDerivative C s p X) =
      LinearMap.trace ℂ V (s.derivative p X) := by
  unfold adjointCovariantDerivative
  rw [map_add, trace_associativeCommutator_zero, add_zero]

/-- The adjoint Bianchi equation implies closedness of the degree-one traced
curvature readout in every supplied tangent direction. -/
theorem trace_curvatureDerivative_zero_of_bianchi
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U W : Tangent) :
    LinearMap.trace ℂ V (dF p X U W) = 0 := by
  have h := congrArg (LinearMap.trace ℂ V) (hBianchi p X U W)
  rw [trace_adjointCovariantDerivative] at h
  simpa using h

/-- Differential field of the quadratic curvature `F(U,W)^2`, with the
ordinary derivative supplied by the noncommutative Leibniz rule. -/
def curvatureSquareDifferentialField
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (U W : Tangent) :
    AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := Module.End ℂ V) where
  value p := curvature C p U W * curvature C p U W
  derivative p X :=
    dF p X U W * curvature C p U W +
      curvature C p U W * dF p X U W

@[simp] theorem curvatureSquareDifferentialField_value
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (p : Point) (U W : Tangent) :
    (curvatureSquareDifferentialField C dF U W).value p =
      curvature C p U W * curvature C p U W :=
  rfl

@[simp] theorem curvatureSquareDifferentialField_derivative
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (p : Point) (X U W : Tangent) :
    (curvatureSquareDifferentialField C dF U W).derivative p X =
      dF p X U W * curvature C p U W +
        curvature C p U W * dF p X U W :=
  rfl

/-- Covariant constancy of curvature propagates to its noncommutative square
by the ordinary Leibniz rule and the inner-commutator derivation law. -/
theorem adjointCovariantDerivative_curvatureSquare_eq_zero
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U W : Tangent) :
    adjointCovariantDerivative C
      (curvatureSquareDifferentialField C dF U W) p X = 0 := by
  have h := hBianchi p X U W
  change
    dF p X U W +
      associativeCommutator (C.form p X) (curvature C p U W) = 0 at h
  have hd : dF p X U W =
      -associativeCommutator (C.form p X) (curvature C p U W) :=
    eq_neg_of_add_eq_zero_left h
  change
    (dF p X U W * curvature C p U W +
        curvature C p U W * dF p X U W) +
      associativeCommutator (C.form p X)
        (curvature C p U W * curvature C p U W) = 0
  rw [hd]
  unfold associativeCommutator
  noncomm_ring

/-- The degree-two Chern--Weil readout is closed whenever the operator
curvature satisfies the adjoint Bianchi equation. -/
theorem trace_curvatureSquareDerivative_zero_of_bianchi
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U W : Tangent) :
    LinearMap.trace ℂ V
        (dF p X U W * curvature C p U W +
          curvature C p U W * dF p X U W) = 0 := by
  have h := congrArg (LinearMap.trace ℂ V)
    (adjointCovariantDerivative_curvatureSquare_eq_zero C dF hBianchi p X U W)
  rw [trace_adjointCovariantDerivative] at h
  rw [map_zero] at h
  exact h

/-! ## All curvature powers -/

/-- Algebraic noncommutative derivative of `F ^ n` in direction `dF`.
The recursion is the genuine ordered Leibniz rule
`D(F^(n+1)) = D(F^n) F + F^n D(F)`. -/
def operatorPowerDerivative {A : Type*} [Ring A] : ℕ → A → A → A
  | 0, _, _ => 0
  | n + 1, F, dF => operatorPowerDerivative n F dF * F + F ^ n * dF

@[simp] theorem operatorPowerDerivative_zero
    {A : Type*} [Ring A] (F dF : A) :
    operatorPowerDerivative 0 F dF = 0 :=
  rfl

@[simp] theorem operatorPowerDerivative_succ
    {A : Type*} [Ring A] (n : ℕ) (F dF : A) :
    operatorPowerDerivative (n + 1) F dF =
      operatorPowerDerivative n F dF * F + F ^ n * dF :=
  rfl

/-- The ordered noncommutative power derivative is functorial under every
ring homomorphism. -/
theorem map_operatorPowerDerivative
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (n : ℕ) (F dF : A) :
    φ (operatorPowerDerivative n F dF) =
      operatorPowerDerivative n (φ F) (φ dF) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [operatorPowerDerivative_succ, map_add, map_mul, map_pow, ih]

theorem operatorPowerDerivative_neg
    {A : Type*} [Ring A] (n : ℕ) (F dF : A) :
    operatorPowerDerivative n F (-dF) =
      -operatorPowerDerivative n F dF := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [operatorPowerDerivative_succ, operatorPowerDerivative_succ, ih]
      noncomm_ring

/-- Inner derivations differentiate every noncommutative power into the inner
commutator of that power. -/
theorem operatorPowerDerivative_associativeCommutator
    {A : Type*} [Ring A] (n : ℕ) (connection F : A) :
    operatorPowerDerivative n F
        (associativeCommutator connection F) =
      associativeCommutator connection (F ^ n) := by
  induction n with
  | zero =>
      simp [operatorPowerDerivative, associativeCommutator]
  | succ n ih =>
      rw [operatorPowerDerivative_succ, ih, pow_succ]
      unfold associativeCommutator
      noncomm_ring

/-- Differential field for the arbitrary curvature power `F(U,W)^n`. -/
def curvaturePowerDifferentialField
    (n : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (U W : Tangent) :
    AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := Module.End ℂ V) where
  value p := curvature C p U W ^ n
  derivative p X := operatorPowerDerivative n (curvature C p U W) (dF p X U W)

@[simp] theorem curvaturePowerDifferentialField_value
    (n : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (p : Point) (U W : Tangent) :
    (curvaturePowerDifferentialField n C dF U W).value p =
      curvature C p U W ^ n :=
  rfl

@[simp] theorem curvaturePowerDifferentialField_derivative
    (n : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (p : Point) (X U W : Tangent) :
    (curvaturePowerDifferentialField n C dF U W).derivative p X =
      operatorPowerDerivative n (curvature C p U W) (dF p X U W) :=
  rfl

/-- The Bianchi identity propagates from curvature to every ordered power of
curvature, with no commutativity hypothesis on the operator coefficients. -/
theorem adjointCovariantDerivative_curvaturePower_eq_zero
    (n : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U W : Tangent) :
    adjointCovariantDerivative C
      (curvaturePowerDifferentialField n C dF U W) p X = 0 := by
  have h := hBianchi p X U W
  change
    dF p X U W +
      associativeCommutator (C.form p X) (curvature C p U W) = 0 at h
  have hd : dF p X U W =
      -associativeCommutator (C.form p X) (curvature C p U W) :=
    eq_neg_of_add_eq_zero_left h
  change
    operatorPowerDerivative n (curvature C p U W) (dF p X U W) +
      associativeCommutator (C.form p X) (curvature C p U W ^ n) = 0
  rw [hd, operatorPowerDerivative_neg,
    operatorPowerDerivative_associativeCommutator]
  exact neg_add_cancel _

/-- Full algebraic Chern--Weil closedness: the trace of the ordered derivative
of `F ^ n` vanishes for every degree `n`. -/
theorem trace_curvaturePowerDerivative_zero_of_bianchi
    (n : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := Module.End ℂ V))
    (dF : Point → Tangent → Tangent → Tangent → Module.End ℂ V)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U W : Tangent) :
    LinearMap.trace ℂ V
      (operatorPowerDerivative n (curvature C p U W) (dF p X U W)) = 0 := by
  have h := congrArg (LinearMap.trace ℂ V)
    (adjointCovariantDerivative_curvaturePower_eq_zero n C dF hBianchi p X U W)
  rw [trace_adjointCovariantDerivative, map_zero] at h
  exact h

theorem operatorPowerDerivative_two
    {A : Type*} [Ring A] (F dF : A) :
    operatorPowerDerivative 2 F dF = dF * F + F * dF := by
  simp [operatorPowerDerivative]

section QGT

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The trace of the transported ordinary curvature derivative is unchanged:
the Maurer--Cartan correction is a commutator and hence traceless. -/
theorem trace_gaugeCurvatureDerivative
    (G : QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (dF : Point → Tangent → Tangent → Tangent →
      DoubledInternalEnd (W := W))
    (p : Point) (X U Z : Tangent) :
    LinearMap.trace ℂ (Fin 2 → W)
        (gaugeCurvatureDerivative G C dF p X U Z) =
      LinearMap.trace ℂ (Fin 2 → W) (dF p X U Z) := by
  change LinearMap.trace ℂ (Fin 2 → W)
      ((localGaugeField G (curvatureDifferentialField C dF U Z)).derivative p X) = _
  rw [localGaugeField_derivative, map_add,
    trace_innerConjugation, trace_associativeCommutator_zero, add_zero]
  rfl

/-- Bianchi closedness of the traced QGT curvature derivative is therefore
stable under the complete point-dependent local gauge action. -/
theorem trace_gaugeCurvatureDerivative_zero_of_bianchi
    (G : QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (dF : Point → Tangent → Tangent → Tangent →
      DoubledInternalEnd (W := W))
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U Z : Tangent) :
    LinearMap.trace ℂ (Fin 2 → W)
        (gaugeCurvatureDerivative G C dF p X U Z) = 0 := by
  rw [trace_gaugeCurvatureDerivative]
  exact trace_curvatureDerivative_zero_of_bianchi C dF hBianchi p X U Z

/-- Every traced curvature-power derivative remains closed after the full
local QGT gauge action. -/
theorem trace_curvaturePowerDerivative_zero_after_gauge
    (n : ℕ)
    (G : QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent))
    (dF : Point → Tangent → Tangent → Tangent →
      DoubledInternalEnd (W := W))
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U Z : Tangent) :
    LinearMap.trace ℂ (Fin 2 → W)
      (operatorPowerDerivative n
        (curvature (G • C) p U Z)
        (gaugeCurvatureDerivative G C dF p X U Z)) = 0 := by
  apply trace_curvaturePowerDerivative_zero_of_bianchi n
    (G • C) (gaugeCurvatureDerivative G C dF)
  exact (satisfiesAdjointBianchi_smul_iff G C dF).2 hBianchi

end QGT

end InfoGeometry.Optics.OperatorQGTChernWeil
