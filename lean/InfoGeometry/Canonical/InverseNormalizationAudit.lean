/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.MoorePenroseDrazinObstruction
import Mathlib.Tactic

/-!
# Drazin and Moore--Penrose inverse normalization audit

A quadratic relation `X² = λ X` does NOT make `X` its own Drazin
inverse. In particular `diag(2, 0)` is not its own generalized inverse.

The unscaled adjoint of a nonunit-norm rank-one operator likewise need not
satisfy the first Moore--Penrose equation. These finite matrix witnesses
delimit what an abstract Peirce-factorization theorem can assert.
-/

namespace InfoGeometry.Canonical.InverseNormalizationAudit

open Matrix

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

def nonunitCore : Mat2Z := !![2, 0; 0, 0]
def coreProjection : Mat2Z := !![1, 0; 0, 0]

/-- Nonunit core multiplier in the quadratic relation. -/
theorem nonunitCore_square :
    nonunitCore * nonunitCore = (2 : ℤ) • nonunitCore := by
  decide

/-- The candidate `D = X` fails the reflexive generalized-inverse equation. -/
theorem nonunitCore_not_self_inverse :
    nonunitCore * nonunitCore * nonunitCore ≠ nonunitCore := by
  decide

/-- The candidate `D = X` is not a Drazin inverse even at index one. -/
theorem nonunitCore_not_index_one_drazin :
    ¬ (nonunitCore * nonunitCore * nonunitCore = nonunitCore ∧
        nonunitCore * nonunitCore = nonunitCore * nonunitCore) := by
  intro h
  exact nonunitCore_not_self_inverse h.1

/-- Unit-normalized projection is an idempotent. -/
theorem coreProjection_idempotent :
    coreProjection * coreProjection = coreProjection := by
  decide

/-- The projection gives a commuting, reflexive core inverse after scaling. -/
theorem coreProjection_normalizes_nonunitCore :
    nonunitCore * coreProjection = nonunitCore ∧
    coreProjection * nonunitCore = nonunitCore ∧
    nonunitCore * coreProjection = coreProjection * nonunitCore := by
  decide

/-- An unnormalized adjoint candidate need not solve the Penrose equations. -/
theorem unscaled_adjoint_not_moore_penrose :
    ¬ (nonunitCore * nonunitCore * nonunitCore = nonunitCore) :=
  nonunitCore_not_self_inverse

end InfoGeometry.Canonical.InverseNormalizationAudit
