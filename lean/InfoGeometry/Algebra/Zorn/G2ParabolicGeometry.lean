import InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The certified finite parabolic incidence geometry of `G₂(2)`

This owner exposes the CAS incidence table as a mathematical interface.  The
table has 63 points, 63 lines, degree three on both sides, and 189 flags.
It does not yet identify this finite geometry with automorphism orbits.
-/

namespace InfoGeometry.Algebra.Zorn.G2ParabolicGeometry

open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

abbrev Point := Fin 63
abbrev Line := Fin 63

/-- Incidence between a parabolic point and a parabolic line. -/
def Incident (p : Point) (ℓ : Line) : Prop := ℓ ∈ incidence p

instance : DecidablePred (fun f : Point × Line => Incident f.1 f.2) := by
  intro f
  unfold Incident
  infer_instance

instance (ℓ : Line) : DecidablePred (fun p : Point => Incident p ℓ) := by
  intro p
  unfold Incident
  infer_instance

/-- The points incident with a fixed line. -/
def pointsOn (ℓ : Line) : Finset Point :=
  Finset.univ.filter (fun p => Incident p ℓ)

/-- The finite set of incident point-line flags. -/
def flags : Finset (Point × Line) :=
  Finset.univ.filter (fun f => Incident f.1 f.2)

theorem point_degree (p : Point) : (incidence p).card = 3 :=
  incidence_card p

theorem line_degree (ℓ : Line) : (pointsOn ℓ).card = 3 := by
  fin_cases ℓ <;> native_decide

theorem flag_card : flags.card = 189 := by
  native_decide

theorem flags_nonempty : flags.Nonempty := by
  exact Finset.card_pos.mp (by rw [flag_card]; decide)

end InfoGeometry.Algebra.Zorn.G2ParabolicGeometry
