import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Central even sector of the algebraic Klein relation

The defining relation `a b a⁻¹ = b⁻¹` implies that the square of `a`
commutes with `b`.  This is the algebraic even-sector statement only; no
identification with the center of a presented group or with a crossed-product
operator algebra is made here.
-/

namespace InfoGeometry.Canonical.KleinMonodromyCentralEvenSector

open InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

variable {G : Type*} [Group G]

theorem square_a_commutes_b (rho : KleinMonodromyPair G) :
    (rho.a * rho.a) * rho.b = rho.b * (rho.a * rho.a) := by
  have hab : rho.a * rho.b = rho.b⁻¹ * rho.a := by
    calc
      rho.a * rho.b = (rho.a * rho.b * rho.a⁻¹) * rho.a := by
        simp [mul_assoc]
      _ = rho.b⁻¹ * rho.a := by rw [rho.relation]
  have hainv : rho.a * rho.b⁻¹ = rho.b * rho.a := by
    calc
      rho.a * rho.b⁻¹ = (rho.a * rho.b⁻¹ * rho.a⁻¹) * rho.a := by
        simp [mul_assoc]
      _ = rho.b * rho.a := by rw [rho.two_cycle_on_b]
  calc
    (rho.a * rho.a) * rho.b = rho.a * (rho.a * rho.b) := by
      rw [mul_assoc]
    _ = rho.a * (rho.b⁻¹ * rho.a) := by rw [hab]
    _ = (rho.a * rho.b⁻¹) * rho.a := by rw [mul_assoc]
    _ = (rho.b * rho.a) * rho.a := by rw [hainv]
    _ = rho.b * (rho.a * rho.a) := by rw [mul_assoc]

end InfoGeometry.Canonical.KleinMonodromyCentralEvenSector
