import InfoGeometry.Optics.OperatorQGTConnectionCovariance

/-!
# Point-dependent gauge covariance of operator QGT connections

The connection owner stores an abstract antisymmetric exterior-derivative
channel rather than a manifold differential.  Accordingly, a point-dependent
frame transformation is represented by its right logarithmic one-form
`θ = du·u⁻¹` and the corresponding Maurer--Cartan-corrected derivative
formula.  The resulting theorem proves algebraically that every inhomogeneous
term cancels and the full curvature is conjugated pointwise.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeQGTCovariance

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Unified

section Ring

variable {Point Tangent A : Type*} [Ring A]

/-- A point-dependent invertible frame together with its right logarithmic
Maurer--Cartan one-form. -/
structure RightMaurerCartanFrame where
  frame : Point → Aˣ
  theta : OperatorOneForm Point Tangent A

/-- Pointwise homogeneous conjugation of a connection one-form. -/
def conjugatedOneForm
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    OperatorOneForm Point Tangent A :=
  fun p X => innerConjugation (G.frame p) (C.form p X)

@[simp] theorem conjugatedOneForm_apply
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    conjugatedOneForm G C p X =
      innerConjugation (G.frame p) (C.form p X) :=
  rfl

/-- Pointwise inner conjugation transports the noncommutative wedge square. -/
theorem conjugatedOneForm_wedgeSquare
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    wedgeSquare (conjugatedOneForm G C) p X Y =
      innerConjugation (G.frame p) (wedgeSquare C.form p X Y) := by
  change
    innerConjugation (G.frame p) (C.form p X) *
          innerConjugation (G.frame p) (C.form p Y) -
        innerConjugation (G.frame p) (C.form p Y) *
          innerConjugation (G.frame p) (C.form p X) =
      innerConjugation (G.frame p)
        (C.form p X * C.form p Y - C.form p Y * C.form p X)
  change _ = (innerConjugationRingEquiv (G.frame p))
    (C.form p X * C.form p Y - C.form p Y * C.form p X)
  rw [map_sub, map_mul, map_mul]
  rfl

/-- Cross term produced by differentiating the pointwise conjugated one-form. -/
def gaugeCrossTerm
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) : A :=
  (G.theta p X * conjugatedOneForm G C p Y -
      conjugatedOneForm G C p Y * G.theta p X) -
    (G.theta p Y * conjugatedOneForm G C p X -
      conjugatedOneForm G C p X * G.theta p Y)

/-- The local gauge-transformed connection in the right Maurer--Cartan
convention `Ωᵘ = uΩu⁻¹ - du·u⁻¹`.

Its derivative field is the explicit Leibniz derivative of `uΩu⁻¹`
minus the right Maurer--Cartan identity `dθ = θ∧θ`. -/
def localGaugeConnection
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    Connection (Point := Point) (Tangent := Tangent) (Value := A) where
  form p X := conjugatedOneForm G C p X - G.theta p X
  derivative p X Y :=
    innerConjugation (G.frame p) (C.derivative p X Y) +
      gaugeCrossTerm G C p X Y - wedgeSquare G.theta p X Y
  derivative_swap := by
    intro p X Y
    rw [C.derivative_swap]
    have hneg :
        innerConjugation (G.frame p) (-C.derivative p X Y) =
          -innerConjugation (G.frame p) (C.derivative p X Y) := by
      simpa only [innerConjugationRingEquiv_apply] using
        (map_neg (innerConjugationRingEquiv (G.frame p)) (C.derivative p X Y))
    rw [hneg]
    unfold gaugeCrossTerm wedgeSquare
    noncomm_ring
  derivative_same := by
    intro p X
    rw [C.derivative_same]
    have hzero : innerConjugation (G.frame p) 0 = 0 :=
      map_zero (innerConjugationRingEquiv (G.frame p))
    rw [hzero]
    unfold gaugeCrossTerm wedgeSquare
    noncomm_ring

@[simp] theorem localGaugeConnection_form
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (localGaugeConnection G C).form p X =
      innerConjugation (G.frame p) (C.form p X) - G.theta p X :=
  rfl

/-- Full point-dependent noncommutative gauge covariance:
`F(Ωᵘ) = u F(Ω) u⁻¹`. -/
theorem localGaugeConnection_curvature
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (localGaugeConnection G C) p X Y =
      innerConjugation (G.frame p) (curvature C p X Y) := by
  have hAdCurvature :
      innerConjugation (G.frame p) (curvature C p X Y) =
        innerConjugation (G.frame p) (C.derivative p X Y) +
          wedgeSquare (conjugatedOneForm G C) p X Y := by
    change (innerConjugationRingEquiv (G.frame p))
        (C.derivative p X Y + wedgeSquare C.form p X Y) = _
    rw [map_add, conjugatedOneForm_wedgeSquare]
    rfl
  rw [hAdCurvature]
  unfold curvature localGaugeConnection gaugeCrossTerm wedgeSquare
  noncomm_ring

/-- Point-dependent frame transformation preserves and reflects flatness. -/
theorem localGaugeConnection_isFlat_iff
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    IsFlat (localGaugeConnection G C) ↔ IsFlat C := by
  constructor
  · intro h p X Y
    apply (innerConjugationRingEquiv (G.frame p)).injective
    change innerConjugation (G.frame p) (curvature C p X Y) =
      innerConjugation (G.frame p) 0
    rw [← localGaugeConnection_curvature, h p X Y]
    exact (map_zero (innerConjugationRingEquiv (G.frame p))).symm
  · intro h p X Y
    rw [localGaugeConnection_curvature, h p X Y]
    exact map_zero (innerConjugationRingEquiv (G.frame p))

end Ring

/-! ## Internal doubled-sheet/QGT specialization -/

section QGT

variable {W Point Tangent : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW := Module.End ℂ W
abbrev DoubledEndW := Module.End ℂ (Fin 2 → W)

/-- A point-dependent internal frame on `W`, represented identically on both
causal sheets, together with its doubled right Maurer--Cartan form. -/
def internalRightMaurerCartanFrame
    (u : Point → (EndW (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledEndW (W := W))) :
    RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := DoubledEndW (W := W)) where
  frame p := doubledInternalUnit (u p)
  theta := theta

/-- Local internal gauge transformation of a QGT-soldered connection. -/
def localInternalQGTConnection
    (u : Point → (EndW (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledEndW (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W)) :=
  localGaugeConnection
    (internalRightMaurerCartanFrame u theta)
    (solderedQGTConnection Q dQ dQ_swap dQ_same)

/-- The transformed QGT connection one-form contains the genuine
inhomogeneous right Maurer--Cartan term. -/
theorem localInternalQGTConnection_form
    (u : Point → (EndW (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledEndW (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X : Tangent) :
    (localInternalQGTConnection u theta Q dQ dQ_swap dQ_same).form p X =
      QGTSoldering (qgtInternalConjugation (u p) (Q p X)) - theta p X := by
  rw [localInternalQGTConnection, localGaugeConnection_form,
    solderedQGTConnection_form, internalRightMaurerCartanFrame,
    QGTSoldering_internalConjugation]

/-- The complete point-dependent QGT curvature is conjugated by the induced
doubled internal frame; all `du·u⁻¹` terms cancel. -/
theorem localInternalQGTConnection_curvature
    (u : Point → (EndW (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledEndW (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (localInternalQGTConnection u theta Q dQ dQ_swap dQ_same) p X Y =
      innerConjugation (doubledInternalUnit (u p))
        (curvature (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y) :=
  localGaugeConnection_curvature
    (internalRightMaurerCartanFrame u theta)
    (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y

end QGT

end InfoGeometry.Optics.LocalGaugeQGTCovariance
