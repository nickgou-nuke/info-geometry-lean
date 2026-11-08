import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
Degreewise rational differentials.  The carrier is ℕ-graded, while every
individual map is a native Mathlib `LinearMap`; nilpotence is stated with the
correct source and target degrees rather than by forcing all degrees into one
untyped endomorphism.
-/

structure GradedRationalDifferential
    (V : ℕ → Type*)
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)] where
  d : ∀ p, V p →ₗ[ℚ] V (p + 1)
  d_sq_zero :
    ∀ p (x : V p), d (p + 1) (d p x) = 0

structure GradedRationalCodifferential
    (V : ℕ → Type*)
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)] where
  cod : ∀ p, V (p + 1) →ₗ[ℚ] V p
  cod_sq_zero :
    ∀ p (x : V (p + 2)), cod p (cod (p + 1) x) = 0

def gradedIsExact
    {V : ℕ → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (D : GradedRationalDifferential V)
    (p : ℕ) (x : V (p + 1)) : Prop :=
  ∃ y : V p, D.d p y = x

def gradedIsCoexact
    {V : ℕ → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (C : GradedRationalCodifferential V)
    (p : ℕ) (x : V p) : Prop :=
  ∃ y : V (p + 1), C.cod p y = x

theorem graded_exact_closed
    {V : ℕ → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (D : GradedRationalDifferential V)
    (p : ℕ) {x : V (p + 1)}
    (hx : gradedIsExact D p x) :
    D.d (p + 1) x = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact D.d_sq_zero p y

theorem graded_coexact_coclosed
    {V : ℕ → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (C : GradedRationalCodifferential V)
    (p : ℕ) {x : V (p + 1)}
    (hx : gradedIsCoexact C (p + 1) x) :
    C.cod p x = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact C.cod_sq_zero p y

def cellularRationalDifferential
    (K : FiniteOrientedCellComplex) :
    GradedRationalDifferential (RationalColorCochain K) where
  d := rationalCoboundary K
  d_sq_zero := by
    intro p x
    have h := congrArg
      (fun f : RationalColorCochain K p →ₗ[ℚ]
        RationalColorCochain K (p + 2) => f x)
      (rationalCoboundary_sq_zero K p)
    simpa [LinearMap.comp_apply] using h

theorem cellularRationalDifferential_exact_closed
    (K : FiniteOrientedCellComplex)
    (p : ℕ) {x : RationalColorCochain K (p + 1)}
    (hx : gradedIsExact (cellularRationalDifferential K) p x) :
    rationalCoboundary K (p + 1) x = 0 :=
  graded_exact_closed (cellularRationalDifferential K) p hx

end InfoGeometry.Canonical
