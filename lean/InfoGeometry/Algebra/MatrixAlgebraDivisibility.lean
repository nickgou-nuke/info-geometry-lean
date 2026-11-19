/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Trace

/-!
# Dimension divisibility for finite matrix algebra representations

A unital algebra representation of a full matrix algebra has dimension a
multiple of the matrix size. The proof uses the images of actual matrix
units: their diagonal idempotents have equal traces, and their sum is the
identity. Native algebraic projection trace identifies the common trace
with the dimension of one range. No self-adjointness of the images is assumed.

The characteristic-zero hypothesis allows the resulting scalar equality to
be read as an equality of natural-number dimensions. The dyadic consequences
exclude unital algebra maps into finite binary matrix stages. They make no
claim about a norm completion or a represented weak closure.
-/

noncomputable section

namespace InfoGeometry.Algebra.MatrixAlgebraDivisibility

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- The dimension of a matrix-algebra representation is the matrix size
times the dimension of the range of any diagonal matrix unit. -/
theorem finrank_eq_card_mul_finrank_range_matrixUnit
    {n V : Type*} [Fintype n] [DecidableEq n]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Matrix n n K →ₐ[K] Module.End K V) (i : n) :
    Module.finrank K V = Fintype.card n *
      Module.finrank K (LinearMap.range (ρ (Matrix.single i i 1))) := by
  classical
  have hidem (j : n) : IsIdempotentElem (ρ (Matrix.single j j 1)) := by
    change ρ (Matrix.single j j 1) * ρ (Matrix.single j j 1) =
      ρ (Matrix.single j j 1)
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  have htrace (j : n) :
      LinearMap.trace K V (ρ (Matrix.single j j 1)) =
        LinearMap.trace K V (ρ (Matrix.single i i 1)) := by
    calc
      LinearMap.trace K V (ρ (Matrix.single j j 1)) =
          LinearMap.trace K V
            (ρ (Matrix.single j i 1) * ρ (Matrix.single i j 1)) := by
        rw [← map_mul, Matrix.single_mul_single_same, one_mul]
      _ = LinearMap.trace K V
          (ρ (Matrix.single i j 1) * ρ (Matrix.single j i 1)) :=
        LinearMap.trace_mul_comm K _ _
      _ = LinearMap.trace K V (ρ (Matrix.single i i 1)) := by
        rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  have hsum : (∑ j : n, ρ (Matrix.single j j 1)) = 1 := by
    rw [← map_sum, Matrix.sum_single_one, map_one]
  have hdim : (Module.finrank K V : K) = (Fintype.card n : K) *
      (Module.finrank K (LinearMap.range (ρ (Matrix.single i i 1))) : K) := by
    calc
      (Module.finrank K V : K) =
          LinearMap.trace K V (1 : Module.End K V) :=
        (LinearMap.trace_one (R := K) (M := V)).symm
      _ = LinearMap.trace K V (∑ j : n, ρ (Matrix.single j j 1)) :=
        congrArg (LinearMap.trace K V) hsum.symm
      _ = ∑ j : n, LinearMap.trace K V (ρ (Matrix.single j j 1)) := by
        rw [map_sum]
      _ = ∑ _j : n, LinearMap.trace K V (ρ (Matrix.single i i 1)) :=
        Finset.sum_congr rfl fun j _ => htrace j
      _ = (Fintype.card n : K) *
          LinearMap.trace K V (ρ (Matrix.single i i 1)) := by
        simp [nsmul_eq_mul]
      _ = (Fintype.card n : K) *
          (Module.finrank K (LinearMap.range (ρ (Matrix.single i i 1))) : K) := by
        rw [LinearMap.IsProj.trace
          (LinearMap.IsIdempotentElem.isProj_range _ (hidem i))]
  apply Nat.cast_injective (R := K)
  simpa only [Nat.cast_mul] using hdim

/-- A unital algebra map between finite full matrix algebras forces the
source matrix size to divide the target matrix size. -/
theorem card_dvd_card_of_algHom
    {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m]
    (φ : Matrix n n K →ₐ[K] Matrix m m K) :
    Fintype.card n ∣ Fintype.card m := by
  classical
  let ρ : Matrix n n K →ₐ[K] Module.End K (m → K) :=
    (Matrix.toLinAlgEquiv' : Matrix m m K ≃ₐ[K] Module.End K (m → K)).toAlgHom.comp φ
  let i : n := Classical.choice (inferInstance : Nonempty n)
  refine ⟨Module.finrank K (LinearMap.range (ρ (Matrix.single i i 1))), ?_⟩
  simpa only [Module.finrank_pi] using
    finrank_eq_card_mul_finrank_range_matrixUnit ρ i

/-- A prime factor other than two in the source matrix size prevents any
unital algebra map to a finite binary matrix stage. -/
theorem isEmpty_algHom_dyadic_of_prime_dvd
    {d p : ℕ} [NeZero d] (k : ℕ) (hp : Nat.Prime p)
    (hp_two : p ≠ 2) (hpd : p ∣ d) :
    IsEmpty (Matrix (Fin d) (Fin d) K →ₐ[K]
      Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) K) := by
  refine ⟨fun φ => ?_⟩
  have hdim : d ∣ 2 ^ k := by
    simpa only [Fintype.card_fin] using card_dvd_card_of_algHom φ
  have hptwo : p ∣ 2 := hp.dvd_of_dvd_pow (dvd_trans hpd hdim)
  exact hp_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hptwo)

/-- The algebra of twelve-by-twelve matrices cannot map unitally into
any finite binary matrix stage. -/
theorem no_twelve_algHom_dyadic (k : ℕ) :
    IsEmpty (Matrix (Fin 12) (Fin 12) K →ₐ[K]
      Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) K) :=
  isEmpty_algHom_dyadic_of_prime_dvd (K := K) (p := 3) k
    (by decide) (by decide) (by decide)

/-- The algebra of twenty-four-by-twenty-four matrices cannot map unitally
into any finite binary matrix stage. -/
theorem no_twentyfour_algHom_dyadic (k : ℕ) :
    IsEmpty (Matrix (Fin 24) (Fin 24) K →ₐ[K]
      Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) K) :=
  isEmpty_algHom_dyadic_of_prime_dvd (K := K) (p := 3) k
    (by decide) (by decide) (by decide)

end InfoGeometry.Algebra.MatrixAlgebraDivisibility
