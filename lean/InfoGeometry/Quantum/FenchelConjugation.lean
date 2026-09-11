import InfoGeometry.Quantum.HurwitzFenchel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Quantum.FenchelConjugation

This file formalizes the geometric reflection (conjugation) as the exact
operatorial coordinate swap of the Fenchel-Legendre transform.

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
noncomputable def fenchel_conjugation (x : HurwitzSpace) : HurwitzSpace :=
  let tr := 2 * hurwitz_inner x hurwitz_one
  (tr - x.1, -x.2)

/--
HONEST THEOREM DEBT:
The geometric reflection perfectly matches the algebraic conjugation operation.

-- DEBT_KIND: SORRY
-/
theorem fenchel_conjugation_eq_hurwitz_conj (x : HurwitzSpace) :
    fenchel_conjugation x = hurwitz_conj x := by
  ext
  · dsimp [fenchel_conjugation, hurwitz_inner, hurwitz_one, hurwitz_conj]
    ring
  · dsimp [fenchel_conjugation, hurwitz_conj]

/--
HONEST THEOREM DEBT:
The Operatorial Fenchel Loop evaluates reflexivity directly.
$\overline{\overline{x}} = x$
-/
theorem fenchel_loop_reflexivity (x : HurwitzSpace) :
    fenchel_conjugation (fenchel_conjugation x) = x := by
  ext
  · dsimp [fenchel_conjugation, hurwitz_inner, hurwitz_one]
    ring
  · dsimp [fenchel_conjugation]
    ring

end InfoGeometry.Quantum
