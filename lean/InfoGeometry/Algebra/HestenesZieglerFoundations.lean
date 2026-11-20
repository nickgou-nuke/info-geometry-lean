/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.CliffordGA

/-!
# Hestenes–Ziegler projective-geometry foundations

Source: D. Hestenes and R. Ziegler, *Projective Geometry with Clifford Algebra*,
Acta Appl. Math. 23 (1991) 25–63, §2.4, Eqs. (2.24)–(2.26).

The paper's commutator product `M × N = ½(MN − NM)` is exactly the existing
`InfoGeometry.Algebra.CliffordGA.antiPart`; no parallel operation is introduced.
This file adds its antisymmetry, derivation, and Jacobi laws for an arbitrary
associative ring with `2` invertible.  The projective incidence owners continue
to use the exterior algebra; these identities are metric-independent.
-/

namespace InfoGeometry.Algebra.HestenesZieglerFoundations

open InfoGeometry.Algebra.CliffordGA

variable {A : Type*} [Ring A] [Invertible (2 : A)]

/-- Hestenes–Ziegler (2.24): the commutator product is antisymmetric. -/
theorem antiPart_antisymm (x y : A) : antiPart y x = -antiPart x y := by
  unfold antiPart
  noncomm_ring

/-- Hestenes–Ziegler (2.25): the commutator product acts as a derivation of the
associative product. -/
theorem antiPart_mul_derivation (L M N : A) :
    antiPart L (M * N) = antiPart L M * N + M * antiPart L N := by
  unfold antiPart
  have hM : M * (⅟(2 : A) * (L * N - N * L)) =
      ⅟(2 : A) * (M * (L * N - N * L)) := by
    rw [← mul_assoc, ← commute_invOf_two M, mul_assoc]
  rw [hM]
  noncomm_ring

/-- Hestenes–Ziegler (2.26): Jacobi's identity for the commutator product. -/
theorem antiPart_jacobi (L M N : A) :
    antiPart L (antiPart M N) =
      antiPart (antiPart L M) N + antiPart M (antiPart L N) := by
  unfold antiPart
  have hM (X : A) : M * (⅟(2 : A) * X) = ⅟(2 : A) * (M * X) := by
    rw [← mul_assoc, ← commute_invOf_two M, mul_assoc]
  have hL (X : A) : L * (⅟(2 : A) * X) = ⅟(2 : A) * (L * X) := by
    rw [← mul_assoc, ← commute_invOf_two L, mul_assoc]
  have hN (X : A) : N * (⅟(2 : A) * X) = ⅟(2 : A) * (N * X) := by
    rw [← mul_assoc, ← commute_invOf_two N, mul_assoc]
  rw [hM, hL, hN]
  noncomm_ring

/-- The unnormalized commutator `MN − NM` satisfies the same derivation law
without any invertibility assumption on `2`. -/
theorem unnormalized_commutator_mul_derivation {A : Type*} [Ring A] (L M N : A) :
    L * M * N - M * N * L =
      (L * M - M * L) * N + M * (L * N - N * L) := by
  noncomm_ring

end InfoGeometry.Algebra.HestenesZieglerFoundations
