import InfoGeometry.Spectral.Cohomology.Basic

/-!
# Long exact sequences for the spectral port

This is the algebraic interface corresponding to the long-exact-sequence
part of the old Spectral project.  The construction of connecting maps from
topological cofiber data is deliberately separate: this file records exactly
the data and consequences needed by downstream spectral arguments.
-/

namespace InfoGeometry.Spectral.Cohomology.LongExact

universe u

/-- A bi-infinite long exact sequence of additive commutative groups.

`shift` is the degree of the next term.  The contract records both the
complex condition and exactness at every term, so no hidden topological
construction is smuggled into the algebraic layer.
-/
structure LongExactSequence (shift : ℤ) where
  carrier : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  next : ∀ n : ℤ, AddMonoidHom (carrier n) (carrier (Int.add n shift))
  next_next : ∀ (n : ℤ) (x : carrier n), next (n + shift) (next n x) = 0
  exact : ∀ (n : ℤ) (y : carrier (n + shift)),
    next (n + shift) y = 0 → ∃ x : carrier n, next n x = y

namespace LongExactSequence

variable {shift : ℤ} (L : LongExactSequence shift)

attribute [instance] LongExactSequence.addCommGroup

@[simp]
theorem next_next_apply (n : ℤ) (x : L.carrier n) :
    L.next (n + shift) (L.next n x) = 0 :=
  L.next_next n x

theorem exact_at (n : ℤ) (y : L.carrier (n + shift))
    (hy : L.next (n + shift) y = 0) :
    ∃ x : L.carrier n, L.next n x = y :=
  L.exact n y hy

/-- The next map is zero on the range of the preceding map. -/
theorem range_mem_kernel (n : ℤ) (x : L.carrier n) :
    L.next (n + shift) (L.next n x) = 0 :=
  L.next_next n x

end LongExactSequence

end InfoGeometry.Spectral.Cohomology.LongExact
