import InfoGeometry.Spectral.Algebra.ExactCouple

/-!
# Spectral Sequence Pages

This file keeps only the theorem-safe algebraic surface currently owned by the
repository: pages with square-zero differentials, and the page obtained from an
exact couple by `d = j ∘ k`.
-/

namespace InfoGeometry.Spectral.Algebra

universe u

/-- A single bigraded page with a differential of index shift `δ`. -/
structure SpectralSequencePage (R : Type u) [Ring R]
    (E : Z2 → Type u)
    [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
    (δ : Z2 → Z2) where
  d : ∀ x, E x →ₗ[R] E (δ x)
  d_comp_d : ∀ x, (d (δ x)).comp (d x) = 0

namespace SpectralSequencePage

variable {R : Type u} [Ring R]
variable {E : Z2 → Type u}
variable [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
variable {δ : Z2 → Z2}

/-- The square-zero law packaged as a theorem for page consumers. -/
theorem differential_sq_zero (P : SpectralSequencePage R E δ) (x : Z2) :
    (P.d (δ x)).comp (P.d x) = 0 :=
  P.d_comp_d x

end SpectralSequencePage

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/-- The exact-couple differential as a square-zero spectral page. -/
def toPage (C : ExactCouple R D E) :
    SpectralSequencePage R E shiftK where
  d := C.differential
  d_comp_d := C.differential_comp_differential

/-- Read back the page differential as the exact-couple differential. -/
@[simp]
theorem toPage_d (C : ExactCouple R D E) (pq : Z2) :
    C.toPage.d pq = C.differential pq :=
  rfl

/-- The exact-couple page has square-zero differential. -/
theorem toPage_differential_sq_zero (C : ExactCouple R D E) (pq : Z2) :
    (C.toPage.d (shiftK pq)).comp (C.toPage.d pq) = 0 :=
  C.toPage.differential_sq_zero pq

end ExactCouple

/-! ## Convergence data

The old HoTT port used a convergence record to keep page construction,
stabilisation, and the abutment separate.  The Lean 4 version records exactly
those interfaces and does not assert convergence from an exact couple alone.
-/

universe v

/-- Witness data for a convergent spectral-sequence tower.

`stable` records eventual page stabilisation at each bidegree.  The current
page carrier is fixed, so homology-page equivalences are intentionally left to
the existing derived-couple owners.  `abutment` is supplied as data: an exact
couple by itself does not construct the required filtration or its abutment.
-/
structure ConvergentSpectralSequence (R : Type u) [Ring R]
    (E : Z2 → Type u)
    [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
    (δ : Z2 → Z2)
    (A : Z2 → Type v) where
  page : ℕ → SpectralSequencePage R E δ
  abutment : ∀ x, A x
  stable : ∀ x, ∃ N, ∀ n, N ≤ n →
    (page n).d x = (page N).d x

namespace ConvergentSpectralSequence

variable {R : Type u} [Ring R]
variable {E : Z2 → Type u}
variable [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
variable {δ : Z2 → Z2} {A : Z2 → Type v}

@[simp]
theorem differential_sq_zero
    (C : ConvergentSpectralSequence R E δ A)
    (n : ℕ) (x : Z2) :
    ((C.page n).d (δ x)).comp ((C.page n).d x) = 0 :=
  (C.page n).differential_sq_zero x

theorem stable_at
    (C : ConvergentSpectralSequence R E δ A)
    (x : Z2) :
    ∃ N, ∀ n, N ≤ n → (C.page n).d x = (C.page N).d x :=
  C.stable x

end ConvergentSpectralSequence

end InfoGeometry.Spectral.Algebra
