import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Klein-bottle twisted commutant algebra

For a ring automorphism `α` with `α² = 1`, this owner records the algebraic
even/odd commutant split behind the Klein-bottle relation.  The statements are
set-level ring facts; no crossed-product C*-algebra or topological quotient is
introduced here.
-/

namespace InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge

variable {R : Type*} [Ring R]

def ordinaryCommutant (S : Set R) : Set R :=
  {x | ∀ a ∈ S, x * a = a * x}

def twistedCommutant (S : Set R) (α : R ≃+* R) : Set R :=
  {x | ∀ a ∈ S, x * a = α a * x}

theorem mem_ordinaryCommutant_iff
    {S : Set R} {x : R} :
    x ∈ ordinaryCommutant S ↔ ∀ a ∈ S, x * a = a * x :=
  Iff.rfl

theorem mem_twistedCommutant_iff
    {S : Set R} {α : R ≃+* R} {x : R} :
    x ∈ twistedCommutant S α ↔ ∀ a ∈ S, x * a = α a * x :=
  Iff.rfl

theorem zero_mem_ordinaryCommutant (S : Set R) :
    (0 : R) ∈ ordinaryCommutant S := by
  intro a ha
  simp

theorem zero_mem_twistedCommutant (S : Set R) (α : R ≃+* R) :
    (0 : R) ∈ twistedCommutant S α := by
  intro a ha
  simp

theorem ordinary_add_ordinary
    {S : Set R} {x y : R}
    (hx : x ∈ ordinaryCommutant S)
    (hy : y ∈ ordinaryCommutant S) :
    x + y ∈ ordinaryCommutant S := by
  intro a ha
  rw [add_mul, mul_add, hx a ha, hy a ha]

theorem ordinary_neg
    {S : Set R} {x : R}
    (hx : x ∈ ordinaryCommutant S) :
    -x ∈ ordinaryCommutant S := by
  intro a ha
  rw [neg_mul, mul_neg, hx a ha]

theorem twisted_add_twisted
    {S : Set R} {α : R ≃+* R} {x y : R}
    (hx : x ∈ twistedCommutant S α)
    (hy : y ∈ twistedCommutant S α) :
    x + y ∈ twistedCommutant S α := by
  intro a ha
  rw [add_mul, mul_add, hx a ha, hy a ha]

theorem twisted_neg
    {S : Set R} {α : R ≃+* R} {x : R}
    (hx : x ∈ twistedCommutant S α) :
    -x ∈ twistedCommutant S α := by
  intro a ha
  rw [neg_mul, mul_neg, hx a ha]

/-! The additive closure facts package canonically as `AddSubgroup`s.  This
does not assert multiplicative closure of the twisted sector. -/

def ordinaryCommutantAddSubgroup (S : Set R) : AddSubgroup R where
  carrier := ordinaryCommutant S
  zero_mem' := zero_mem_ordinaryCommutant S
  add_mem' hx hy := ordinary_add_ordinary hx hy
  neg_mem' hx := ordinary_neg hx

@[simp] theorem mem_ordinaryCommutantAddSubgroup_iff
    {S : Set R} {x : R} :
    x ∈ ordinaryCommutantAddSubgroup S ↔ x ∈ ordinaryCommutant S :=
  Iff.rfl

def twistedCommutantAddSubgroup (S : Set R) (α : R ≃+* R) : AddSubgroup R where
  carrier := twistedCommutant S α
  zero_mem' := zero_mem_twistedCommutant S α
  add_mem' hx hy := twisted_add_twisted hx hy
  neg_mem' hx := twisted_neg hx

@[simp] theorem mem_twistedCommutantAddSubgroup_iff
    {S : Set R} {α : R ≃+* R} {x : R} :
    x ∈ twistedCommutantAddSubgroup S α ↔ x ∈ twistedCommutant S α :=
  Iff.rfl

theorem ordinary_mul_ordinary
    {S : Set R} {x y : R}
    (hx : x ∈ ordinaryCommutant S)
    (hy : y ∈ ordinaryCommutant S) :
    x * y ∈ ordinaryCommutant S := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := by rw [mul_assoc]
    _ = x * (a * y) := by rw [hy a ha]
    _ = (x * a) * y := by rw [← mul_assoc]
    _ = (a * x) * y := by rw [hx a ha]
    _ = a * (x * y) := by rw [mul_assoc]

theorem ordinary_mul_twisted
    {S : Set R} {α : R ≃+* R} {x y : R}
    (hS : ∀ a ∈ S, α a ∈ S)
    (hx : x ∈ ordinaryCommutant S)
    (hy : y ∈ twistedCommutant S α) :
    x * y ∈ twistedCommutant S α := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := by rw [mul_assoc]
    _ = x * (α a * y) := by rw [hy a ha]
    _ = (x * α a) * y := by rw [← mul_assoc]
    _ = (α a * x) * y := by rw [hx (α a) (hS a ha)]
    _ = α a * (x * y) := by rw [mul_assoc]

theorem twisted_mul_ordinary
    {S : Set R} {α : R ≃+* R} {x y : R}
    (hx : x ∈ twistedCommutant S α)
    (hy : y ∈ ordinaryCommutant S) :
    x * y ∈ twistedCommutant S α := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := by rw [mul_assoc]
    _ = x * (a * y) := by rw [hy a ha]
    _ = (x * a) * y := by rw [← mul_assoc]
    _ = (α a * x) * y := by rw [hx a ha]
    _ = α a * (x * y) := by rw [mul_assoc]

theorem twisted_mul_twisted
    {S : Set R} {α : R ≃+* R} {x y : R}
    (hα : Function.Involutive α)
    (hS : ∀ a ∈ S, α a ∈ S)
    (hx : x ∈ twistedCommutant S α)
    (hy : y ∈ twistedCommutant S α) :
    x * y ∈ ordinaryCommutant S := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := by rw [mul_assoc]
    _ = x * (α a * y) := by rw [hy a ha]
    _ = (x * α a) * y := by rw [← mul_assoc]
    _ = (α (α a) * x) * y := by rw [hx (α a) (hS a ha)]
    _ = (a * x) * y := by rw [hα a]
    _ = a * (x * y) := by rw [mul_assoc]

theorem square_mem_ordinary_of_mem_twisted
    {S : Set R} {α : R ≃+* R} {u : R}
    (hα : Function.Involutive α)
    (hS : ∀ a ∈ S, α a ∈ S)
    (hu : u ∈ twistedCommutant S α) :
    u * u ∈ ordinaryCommutant S :=
  twisted_mul_twisted hα hS hu hu

theorem square_commutes_of_mem_twisted
    {S : Set R} {α : R ≃+* R} {u : R}
    (hα : Function.Involutive α)
    (hS : ∀ a ∈ S, α a ∈ S)
    (hu : u ∈ twistedCommutant S α) :
    ∀ a ∈ S, (u * u) * a = a * (u * u) := by
  intro a ha
  exact (twisted_mul_twisted hα hS hu hu) a ha

theorem square_unit_conjugation_eq_id
    {S : Set R} {α : R ≃+* R} {u : Units R}
    (hα : Function.Involutive α)
    (hS : ∀ a ∈ S, α a ∈ S)
    (hu : (u : R) ∈ twistedCommutant S α) :
    ∀ a ∈ S,
      (u * u : Units R) * a * (↑((u * u)⁻¹) : R) = a := by
  intro a ha
  have hcomm : ((u * u : Units R) : R) * a =
      a * ((u * u : Units R) : R) := by
    simpa [mul_assoc] using
      (square_commutes_of_mem_twisted hα hS hu a ha)
  calc
    ((u * u : Units R) : R) * a * (↑((u * u)⁻¹) : R) =
        (a * ((u * u : Units R) : R)) * (↑((u * u)⁻¹) : R) := by
      rw [hcomm]
    _ = a := by
      rw [mul_assoc, Units.mul_inv, mul_one]

theorem twisted_mem_normalizer
    {S : Set R} {α : R ≃+* R} {u : Units R}
    (hu : (u : R) ∈ twistedCommutant S α) :
    ∀ a ∈ S, (u : R) * a * (↑(u⁻¹) : R) = α a := by
  intro a ha
  calc
    (u : R) * a * (↑(u⁻¹) : R) = (α a * (u : R)) * (↑(u⁻¹) : R) := by
      rw [hu a ha]
    _ = α a * ((u : R) * (↑(u⁻¹) : R)) := by rw [mul_assoc]
    _ = α a := by
      rw [Units.mul_inv, mul_one]

end InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge
