/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

/-!
# Arnold--Kohno / para-Kähler connection interface

This owner is deliberately an interface between the repository's native
Arnold--Cohen relations and its finite para-Kähler datum.  It does not
identify an arbitrary KZ connection with a metric, nor does it assert a
general configuration-space theorem without an indexed residue carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

open InfoGeometry.Canonical.ArnoldCohenBCFWBridge
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

/-- A finite commutator connection is flat when its coefficient values
commute.  The exterior/formal differential part is kept separate from this
algebraic curvature statement. -/
structure CommutatorConnection (A V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] where
  coefficient : V → A

/-- The curvature of a pair of coefficients is their commutator. -/
def commutatorCurvature {A V : Type*} [Ring A] [AddCommGroup V]
    [Module A V] (C : CommutatorConnection A V) (u v : V) : A :=
  C.coefficient u * C.coefficient v -
    C.coefficient v * C.coefficient u

theorem commutatorCurvature_eq_zero_of_commuting
    {A V : Type*} [Ring A] [AddCommGroup V] [Module A V]
    (C : CommutatorConnection A V)
    (hcomm : ∀ u v, C.coefficient u * C.coefficient v =
      C.coefficient v * C.coefficient u) (u v : V) :
    commutatorCurvature C u v = 0 := by
  simp [commutatorCurvature, hcomm u v]

/-- Scalar coefficients give a canonical flat commutator connection. -/
theorem scalar_commutator_curvature_zero
    {R A V : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup V] [Module R V]
    (f : V → R) (u v : V) :
    (algebraMap R A (f u)) * algebraMap R A (f v) -
      algebraMap R A (f v) * algebraMap R A (f u) = 0 := by
  exact sub_eq_zero.mpr (Algebra.commutes (f u) (algebraMap R A (f v)))

end InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
