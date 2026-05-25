import Mathlib.Tactic

/-!
# InfoGeometry.Clifford.QuadraticPolarBridge

Quadratic polar form and Clifford anticommutator bridge.

If a generator map `iota` satisfies the Clifford square relation

  `iota v * iota v = algebraMap R A (Q v)`,

then the anticommutator is the polar expression:

  `iota x * iota y + iota y * iota x
    = algebraMap R A (Q (x + y) - Q x - Q y)`.
-/

namespace InfoGeometry.Clifford

/--
The polarization expression associated to a quadratic function `Q`.
-/
def polarFromQuadratic
    {R V : Type*} [Sub R] [Add V]
    (Q : V → R) (x y : V) : R :=
  Q (x + y) - Q x - Q y

/--
Clifford anticommutator from the square relation.
-/
theorem clifford_anticommutator_from_square_relation
    {R V A : Type*}
    [CommRing R]
    [AddCommGroup V]
    [Ring A] [Algebra R A]
    (Q : V → R)
    (iota : V → A)
    (hadd : ∀ x y : V, iota (x + y) = iota x + iota y)
    (hsq : ∀ v : V, iota v * iota v = algebraMap R A (Q v))
    (x y : V) :
    iota x * iota y + iota y * iota x =
      algebraMap R A (polarFromQuadratic Q x y) := by
  unfold polarFromQuadratic

  have hxy := hsq (x + y)
  rw [hadd x y] at hxy

  have hexpand :
      (iota x + iota y) * (iota x + iota y) =
        iota x * iota x + (iota x * iota y + iota y * iota x) + iota y * iota y := by
    noncomm_ring

  have hsum :
      iota x * iota x + (iota x * iota y + iota y * iota x) + iota y * iota y =
        algebraMap R A (Q (x + y)) := by
    rw [← hxy]
    exact hexpand.symm

  calc
    iota x * iota y + iota y * iota x =
      (iota x * iota x + (iota x * iota y + iota y * iota x) + iota y * iota y) -
        iota x * iota x - iota y * iota y := by
      abel
    _ = algebraMap R A (Q (x + y)) - algebraMap R A (Q x) - algebraMap R A (Q y) := by
      rw [hsum, hsq x, hsq y]
    _ = algebraMap R A (Q (x + y) - Q x - Q y) := by
      rw [map_sub, map_sub]

end InfoGeometry.Clifford

