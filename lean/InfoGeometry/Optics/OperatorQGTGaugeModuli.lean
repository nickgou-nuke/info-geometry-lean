import InfoGeometry.Optics.LocalGaugeAdjointAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Gauge classes of operator-valued QGT connections

The local gauge group is specialized to the doubled internal QGT carrier.
Its native orbit setoid defines a quotient of complete soldered connections,
and flatness descends because curvature transforms by invertible conjugation.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTGaugeModuli

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeGroupAction
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Unified

variable {W Point Tangent : Type*} [AddCommGroup W] [Module ℂ W]

abbrev InternalEnd := Module.End ℂ W
abbrev DoubledInternalEnd := Module.End ℂ (Fin 2 → W)

abbrev QGTConnection := Connection
  (Point := Point) (Tangent := Tangent) (Value := DoubledInternalEnd (W := W))

abbrev QGTGaugeGroup := RightGaugeGroup
  (Point := Point) (Tangent := Tangent) (A := DoubledInternalEnd (W := W))

/-- Embed an internal frame acting identically on both sheets into the full
doubled-carrier gauge group. -/
def internalQGTGaugeFrame
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W))) :
    QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent) :=
  internalRightMaurerCartanFrame u theta

@[simp] theorem internalQGTGaugeFrame_frame
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W)))
    (p : Point) :
    (internalQGTGaugeFrame u theta).frame p = doubledInternalUnit (u p) := rfl

@[simp] theorem internalQGTGaugeFrame_theta
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W)))
    (p : Point) (X : Tangent) :
    (internalQGTGaugeFrame u theta).theta p X = theta p X := rfl

/-- The earlier local QGT construction is exactly the native group action. -/
theorem internalQGTGaugeFrame_smul_soldered
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledInternalEnd (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    internalQGTGaugeFrame u theta • solderedQGTConnection Q dQ dQ_swap dQ_same =
      localInternalQGTConnection u theta Q dQ dQ_swap dQ_same := rfl

theorem internalQGTGaugeFrame_smul_soldered_form
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledInternalEnd (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X : Tangent) :
    (internalQGTGaugeFrame u theta •
        solderedQGTConnection Q dQ dQ_swap dQ_same).form p X =
      QGTSoldering (qgtInternalConjugation (u p) (Q p X)) - theta p X := by
  rw [internalQGTGaugeFrame_smul_soldered]
  exact localInternalQGTConnection_form u theta Q dQ dQ_swap dQ_same p X

theorem internalQGTGaugeFrame_smul_soldered_curvature
    (u : Point → (InternalEnd (W := W))ˣ)
    (theta : OperatorOneForm Point Tangent (DoubledInternalEnd (W := W)))
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → DoubledInternalEnd (W := W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature (internalQGTGaugeFrame u theta •
        solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y =
      innerConjugation (doubledInternalUnit (u p))
        (curvature (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y) := by
  rw [internalQGTGaugeFrame_smul_soldered]
  exact localInternalQGTConnection_curvature u theta Q dQ dQ_swap dQ_same p X Y

/-- Orbit setoid of complete QGT connections under local gauge transport. -/
def qgtGaugeSetoid : Setoid
    (QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) :=
  MulAction.orbitRel
    (QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (QGTConnection (W := W) (Point := Point) (Tangent := Tangent))

def QGTGaugeEquivalent
    (C D : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) : Prop :=
  (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent)).r C D

theorem qgtGaugeEquivalent_refl
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) :
    QGTGaugeEquivalent C C := by
  unfold QGTGaugeEquivalent
  exact (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent)).refl C

theorem qgtGaugeEquivalent_symm
    {C D : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)}
    (h : QGTGaugeEquivalent C D) : QGTGaugeEquivalent D C := by
  unfold QGTGaugeEquivalent at h ⊢
  exact (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent)).symm h

theorem qgtGaugeEquivalent_trans
    {C D E : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)}
    (hCD : QGTGaugeEquivalent C D) (hDE : QGTGaugeEquivalent D E) :
    QGTGaugeEquivalent C E := by
  unfold QGTGaugeEquivalent at hCD hDE ⊢
  exact (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent)).trans hCD hDE

theorem qgtGaugeEquivalent_smul
    (G : QGTGaugeGroup (W := W) (Point := Point) (Tangent := Tangent))
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) :
    QGTGaugeEquivalent (G • C) C := by
  unfold QGTGaugeEquivalent qgtGaugeSetoid MulAction.orbitRel
  exact ⟨G, rfl⟩

/-- Flatness is constant on gauge-equivalence classes. -/
theorem qgtGaugeEquivalent_isFlat_iff
    {C D : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)}
    (h : QGTGaugeEquivalent C D) : IsFlat C ↔ IsFlat D := by
  unfold QGTGaugeEquivalent qgtGaugeSetoid MulAction.orbitRel at h
  rcases h with ⟨G, rfl⟩
  exact localGaugeConnection_isFlat_iff G D

/-- Moduli carrier of complete operator-valued QGT connections. -/
abbrev QGTGaugeModuli := Quotient
  (qgtGaugeSetoid (W := W) (Point := Point) (Tangent := Tangent))

/-- Flatness descends to the gauge quotient. -/
def flatGaugeClass :
    QGTGaugeModuli (W := W) (Point := Point) (Tangent := Tangent) → Prop :=
  Quotient.lift IsFlat (by
    intro C D h
    apply propext
    apply qgtGaugeEquivalent_isFlat_iff
    exact h)

@[simp] theorem flatGaugeClass_mk
    (C : QGTConnection (W := W) (Point := Point) (Tangent := Tangent)) :
    flatGaugeClass
        (Quotient.mk (qgtGaugeSetoid
          (W := W) (Point := Point) (Tangent := Tangent)) C) ↔ IsFlat C :=
  Iff.rfl

end InfoGeometry.Optics.OperatorQGTGaugeModuli
