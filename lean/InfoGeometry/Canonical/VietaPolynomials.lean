/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- VietaPolynomials.lean
-- Elementary symmetric (Vieta) polynomials for a quintic.

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Fin.Tuple

open Polynomial

namespace InfoGeometry.Canonical

-- Let `R` be a commutative ring.
variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial `e_i` in variables `r₀ … r₄`.
    `i` ranges from 1 to 5. -/

def ei (i : Fin 5) (r : Fin 5 → R) : R :=
  ((Finset.univ.filter (fun s : Finset (Fin 5) => s.card = i.succ)).sum fun s =>
    s.attach.prod fun j => r j.1)

-- Convenience definitions for each `e_i`.

def e1 (r : Fin 5 → R) : R := ei 0 r

def e2 (r : Fin 5 → R) : R := ei 1 r

def e3 (r : Fin 5 → R) : R := ei 2 r

def e4 (r : Fin 5 → R) : R := ei 3 r

def e5 (r : Fin 5 → R) : R := ei 4 r

-- Lemma: the monic quintic polynomial with roots `r` expands to the Vieta form.

def monicQuintic (r : Fin 5 → R) : Polynomial R :=
  (X - C (r 0)) * (X - C (r 1)) * (X - C (r 2)) * (X - C (r 3)) * (X - C (r 4))

@[simp] lemma monicQuintic_eq_Vieta (r : Fin 5 → R) :
    monicQuintic r =
      X ^ 5 - C (e1 r) * X ^ 4 + C (e2 r) * X ^ 3 - C (e3 r) * X ^ 2 + C (e4 r) * X - C (e5 r) := by
  -- Expand step by step using `Polynomial.expand_mul` lemmas.
  -- The proof proceeds by `ring` after `simp`.
  classical
  have : (∀ i, (X - C (r i)) = X + (-C (r i))) := fun i => by simp
  simpa [monicQuintic, this] using
    (by
      ring)

end InfoGeometry.Canonical
