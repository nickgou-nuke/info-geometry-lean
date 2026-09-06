import InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
import InfoGeometry.Optics.OperatorDerivationForms

/-!
# Operator QGT connection covariance

This file promotes internal Bogoliubov covariance from a single soldered QGT
operator to a complete operator-valued connection.  Constant invertible frame
changes act by inner conjugation and therefore carry the full curvature
two-form by the same conjugation.  The infinitesimal statement is realized by
a native continuous Fréchet inner derivation on every normed operator algebra.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTConnectionCovariance

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Unified

/-! ## Generic finite inner covariance -/

section Ring

variable {Point Tangent A : Type*} [Ring A]

/-- A constant invertible frame acts on a connection by the native inner
automorphism of its value algebra. -/
def innerConjugateConnection
    (u : Aˣ)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    Connection (Point := Point) (Tangent := Tangent) (Value := A) :=
  mapConnection (innerConjugationRingEquiv u).toRingHom C

@[simp] theorem innerConjugateConnection_form
    (u : Aˣ)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (innerConjugateConnection u C).form p X =
      innerConjugation u (C.form p X) :=
  rfl

@[simp] theorem innerConjugateConnection_derivative
    (u : Aˣ)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    (innerConjugateConnection u C).derivative p X Y =
      innerConjugation u (C.derivative p X Y) :=
  rfl

/-- A constant finite frame transformation conjugates the complete curvature,
including both the exterior derivative and noncommutative wedge-square terms. -/
theorem innerConjugateConnection_curvature
    (u : Aˣ)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (innerConjugateConnection u C) p X Y =
      innerConjugation u (curvature C p X Y) := by
  exact (mapConnection_curvature
    (innerConjugationRingEquiv u).toRingHom C p X Y).symm

/-- Flatness is invariant under a constant invertible frame transformation. -/
theorem innerConjugateConnection_isFlat_iff
    (u : Aˣ)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    IsFlat (innerConjugateConnection u C) ↔ IsFlat C := by
  constructor
  · intro h p X Y
    have hConj : innerConjugation u (curvature C p X Y) = 0 := by
      rw [← innerConjugateConnection_curvature]
      exact h p X Y
    apply (innerConjugationRingEquiv u).injective
    change innerConjugation u (curvature C p X Y) = innerConjugation u 0
    rw [hConj]
    exact (map_zero (innerConjugationRingEquiv u)).symm
  · intro h p X Y
    rw [innerConjugateConnection_curvature, h p X Y]
    exact map_zero (innerConjugationRingEquiv u)

end Ring

/-! ## The induced doubled-sheet internal frame -/

section DoubledCarrier

variable {W Point Tangent : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW := Module.End ℂ W
abbrev DoubledEndW := Module.End ℂ (Fin 2 → W)

/-- Transform a doubled-carrier connection by the same internal frame on both
causal sheets. -/
def internalFrameConnection
    (u : (EndW (W := W))ˣ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W))) :
    Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W)) :=
  innerConjugateConnection (doubledInternalUnit u) C

@[simp] theorem internalFrameConnection_form
    (u : (EndW (W := W))ˣ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W)))
    (p : Point) (X : Tangent) :
    (internalFrameConnection u C).form p X =
      innerConjugation (doubledInternalUnit u) (C.form p X) :=
  rfl

/-- Curvature on the doubled carrier is conjugated by the induced internal
Bogoliubov frame. -/
theorem internalFrameConnection_curvature
    (u : (EndW (W := W))ˣ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W)))
    (p : Point) (X Y : Tangent) :
    curvature (internalFrameConnection u C) p X Y =
      innerConjugation (doubledInternalUnit u) (curvature C p X Y) :=
  innerConjugateConnection_curvature (doubledInternalUnit u) C p X Y

/-- Build a doubled-carrier connection whose one-form is the soldering of an
operator-valued QGT field.  The exterior derivative channel remains explicit
and antisymmetric, as required by the connection owner. -/
def solderedQGTConnection
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    Connection
      (Point := Point) (Tangent := Tangent) (Value := DoubledEndW (W := W)) where
  form p X := QGTSoldering (Q p X)
  derivative := dQ
  derivative_swap := dQ_swap
  derivative_same := dQ_same

@[simp] theorem solderedQGTConnection_form
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X : Tangent) :
    (solderedQGTConnection Q dQ dQ_swap dQ_same).form p X =
      QGTSoldering (Q p X) :=
  rfl

/-- On a QGT-soldered connection, finite frame transformation of the one-form
is exactly QGT conjugation before soldering. -/
theorem internalFrameConnection_solderedQGT_form
    (u : (EndW (W := W))ˣ)
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X : Tangent) :
    (internalFrameConnection u
      (solderedQGTConnection Q dQ dQ_swap dQ_same)).form p X =
        QGTSoldering (qgtInternalConjugation u (Q p X)) := by
  rw [internalFrameConnection_form, solderedQGTConnection_form,
    QGTSoldering_internalConjugation]

/-- The complete curvature of a QGT-soldered connection transforms by the
same doubled internal frame as each soldered QGT coefficient. -/
theorem internalFrameConnection_solderedQGT_curvature
    (u : (EndW (W := W))ˣ)
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledEndW (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (internalFrameConnection u
          (solderedQGTConnection Q dQ dQ_swap dQ_same)) p X Y =
      innerConjugation (doubledInternalUnit u)
        (curvature (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y) :=
  internalFrameConnection_curvature u
    (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y

end DoubledCarrier

/-! ## Infinitesimal Fréchet inner covariance -/

section Frechet

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The continuous inner derivation `A ↦ XA - AX`. -/
def innerFrechetOperatorDerivation
    (X : A) : FrechetOperatorDerivation 𝕜 A where
  toContinuousLinearMap :=
    ContinuousLinearMap.mul 𝕜 A X - (ContinuousLinearMap.mul 𝕜 A).flip X
  leibniz := by
    intro a b
    simp
    noncomm_ring

@[simp] theorem innerFrechetOperatorDerivation_apply
    (X A₀ : A) :
    innerFrechetOperatorDerivation (𝕜 := 𝕜) X A₀ = X * A₀ - A₀ * X :=
  rfl

/-- The inner derivation differentiates curvature as the commutator with the
curvature itself. -/
theorem innerFrechetOperatorDerivation_curvature
    {Point Tangent : Type*}
    (X : A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (U V : Tangent) :
    innerFrechetOperatorDerivation (𝕜 := 𝕜) X (curvature C p U V) =
      X * curvature C p U V - curvature C p U V * X :=
  rfl

/-- Expanded Fréchet product rule for the curvature two-operator form under
an infinitesimal inner Bogoliubov generator. -/
theorem innerFrechetOperatorDerivation_curvature_explicit
    {Point Tangent : Type*}
    (X : A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (U V : Tangent) :
    innerFrechetOperatorDerivation (𝕜 := 𝕜) X (curvature C p U V) =
      (X * C.derivative p U V - C.derivative p U V * X) +
        (((X * C.form p U - C.form p U * X) * C.form p V +
            C.form p U * (X * C.form p V - C.form p V * X)) -
          ((X * C.form p V - C.form p V * X) * C.form p U +
            C.form p V * (X * C.form p U - C.form p U * X))) := by
  simpa only [innerFrechetOperatorDerivation_apply] using
    (FrechetOperatorDerivation.map_curvature
      (innerFrechetOperatorDerivation (𝕜 := 𝕜) X) C p U V)

end Frechet

end InfoGeometry.Optics.OperatorQGTConnectionCovariance
