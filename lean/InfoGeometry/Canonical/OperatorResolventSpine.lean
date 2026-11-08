/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.GeomSum
import InfoGeometry.Cantor.CliffordMarkovOperators

/-!
# Finite noncommutative operator resolvents

The arithmetic stream and the operator stream have distinct foundations.
Dirichlet convolution and Möbius inversion govern arithmetic coefficients;
the finite geometric identity below governs resolvents in an associative
operator algebra. A bridge between them requires a specified representation
or trace and is not inferred from matching partition-function terminology.

The dependency order for the operator branch is:

1. an operator in an associative ring;
2. its finite geometric sum;
3. the resolvent factorization;
4. under nilpotence, a left inverse for `1 - T`.

The carrier used in the Cantor specialization is the actual endomorphism ring
of the split-Clifford Fock module. No diagonalization or commutativity
assumption is used.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.OperatorResolventSpine

/-- The order-`m` truncation of the operator geometric series. -/
def partialResolvent {A : Type*} [Ring A] (T : A) (m : ℕ) : A :=
  ∑ k ∈ Finset.range m, T ^ k

/-- The finite resolvent factorization in an arbitrary, possibly
noncommutative, ring. -/
theorem left_resolvent_factorization {A : Type*} [Ring A]
    (T : A) (m : ℕ) :
    (1 - T) * partialResolvent T m = 1 - T ^ m := by
  simpa [partialResolvent] using (mul_neg_geom_sum T m)

/-- If an operator is nilpotent at order `m`, the truncated series is a left
inverse for `1 - T`. -/
theorem partialResolvent_left_inverse_of_pow_eq_zero {A : Type*} [Ring A]
    (T : A) (m : ℕ) (hT : T ^ m = 0) :
    (1 - T) * partialResolvent T m = 1 := by
  rw [left_resolvent_factorization, hT, sub_zero]

/-- The resolvent identity for two invertible operator denominators.  The
factor order is part of the statement; no commutativity is assumed. -/
theorem resolvent_difference {A : Type*} [Ring A] (S T : A)
    (u v : Aˣ) (hu : (u : A) = 1 - S) (hv : (v : A) = 1 - T) :
    (↑u⁻¹ : A) - (↑v⁻¹ : A) =
      (↑u⁻¹ : A) * (S - T) * (↑v⁻¹ : A) := by
  have hfactor : (↑u⁻¹ : A) - (↑v⁻¹ : A) =
      (↑u⁻¹ : A) * ((v : A) - (u : A)) * (↑v⁻¹ : A) := by
    calc
      (↑u⁻¹ : A) - (↑v⁻¹ : A) =
          (↑u⁻¹ : A) * (↑v : A) * (↑v⁻¹ : A) -
            (↑u⁻¹ : A) * (↑u : A) * (↑v⁻¹ : A) := by
              simp [mul_assoc]
      _ = (↑u⁻¹ : A) * ((v : A) - (u : A)) * (↑v⁻¹ : A) := by
            noncomm_ring
  have hdiff : (v : A) - (u : A) = S - T := by
    rw [hv, hu]
    abel
  rw [hfactor, hdiff]

open InfoGeometry.Cantor.CliffordMarkovOperators
open InfoGeometry.Clifford.ClNNFockRepresentation
open InfoGeometry.Clifford.FockSpaceCAR

/-- The same noncommutative resolvent identity on the Cantor split-Clifford
Fock operator carrier. -/
theorem cantor_fock_left_resolvent_factorization
    (n m : ℕ) (T : Module.End ℝ (FockSpace (PrimalSheet n))) :
    (1 - T) * partialResolvent T m = 1 - T ^ m :=
  left_resolvent_factorization T m

/-- A nilpotent Cantor Fock operator has an explicit finite left resolvent. -/
theorem cantor_fock_partial_resolvent_left_inverse
    (n m : ℕ) (T : Module.End ℝ (FockSpace (PrimalSheet n)))
    (hT : T ^ m = 0) :
    (1 - T) * partialResolvent T m = 1 :=
  partialResolvent_left_inverse_of_pow_eq_zero T m hT

/-- The ordered resolvent difference identity on the Cantor split-Clifford
Fock endomorphism ring. -/
theorem cantor_fock_resolvent_difference
    (n : ℕ) (S T : Module.End ℝ (FockSpace (PrimalSheet n)))
    (u v : (Module.End ℝ (FockSpace (PrimalSheet n)))ˣ)
    (hu : (u : Module.End ℝ (FockSpace (PrimalSheet n))) = 1 - S)
    (hv : (v : Module.End ℝ (FockSpace (PrimalSheet n))) = 1 - T) :
    (↑u⁻¹ : Module.End ℝ (FockSpace (PrimalSheet n))) -
        (↑v⁻¹ : Module.End ℝ (FockSpace (PrimalSheet n))) =
      (↑u⁻¹ : Module.End ℝ (FockSpace (PrimalSheet n))) * (S - T) *
        (↑v⁻¹ : Module.End ℝ (FockSpace (PrimalSheet n))) :=
  resolvent_difference S T u v hu hv

end InfoGeometry.Canonical.OperatorResolventSpine
