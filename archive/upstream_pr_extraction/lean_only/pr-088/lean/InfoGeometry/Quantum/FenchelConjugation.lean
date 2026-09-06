import InfoGeometry.Quantum.HurwitzFenchel

/-!
# InfoGeometry.Quantum.FenchelConjugation

This file formalizes the coordinate conjugation involution used by the finite
Fenchel readout.

In standard optimization, mapping a vector to its dual coordinate relies on the gradient:
$y = \nabla f(x)$.

In the non-associative Hurwitz setting, this is achieved structurally via the 
order-two antiautomorphism (conjugation):
$\overline{x} = \langle x, 1 \rangle 1 - x$

This transformation acts as the Operatorial Fenchel Loop:
$x \mapsto \overline{x}$
Because it is an involution ($\overline{\overline{x}} = x$), it perfectly mirrors
the Fenchel transform's reflexivity property $f^{**} = f$.
-/

namespace InfoGeometry.Quantum

/-- 
The explicit geometric reflection formula for Hurwitz conjugation.
$\overline{x} = 2 \langle x, 1 \rangle 1 - x$
-/
noncomputable def fenchel_conjugation (x : ComplexCoordinate) : ComplexCoordinate :=
  let tr := 2 * hurwitz_inner x hurwitz_one
  (tr - x.1, -x.2)

/-- The coordinate reflection matches the algebraic conjugation operation. -/
theorem fenchel_conjugation_eq_coordinate_conj (x : ComplexCoordinate) :
    fenchel_conjugation x = hurwitz_conj x := by
  ext
  · dsimp [fenchel_conjugation, hurwitz_inner, hurwitz_one, hurwitz_conj]
    ring
  · dsimp [fenchel_conjugation, hurwitz_conj]

/-- Conjugation is involutive in the finite coordinate model. -/
theorem fenchel_loop_reflexivity (x : ComplexCoordinate) :
    fenchel_conjugation (fenchel_conjugation x) = x := by
  ext
  · dsimp [fenchel_conjugation, hurwitz_inner, hurwitz_one]
    ring
  · dsimp [fenchel_conjugation]
    ring

end InfoGeometry.Quantum
