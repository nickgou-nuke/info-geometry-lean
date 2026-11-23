/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Shirokov's covariantly constant Yang--Mills transfer

This owner formalizes the finite-coordinate algebraic core of Shirokov's
Theorem 4.1. A flat background potential `C` and a `C`-parallel field `K`
give `B = C + K` with curvature `-[K_i,K_j]`; its covariant divergence is the
double-commutator current. The index contraction here is the unweighted finite
sum; a separate pseudo-Euclidean current raises both contracted indices using
diagonal metric signs. The Clifford specialization is a separate theorem.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.ShirokovYangMillsTransfer

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]

/-- The associative-algebra commutator with Shirokov's sign convention. -/
def commutator (a b : A) : A := a * b - b * a

/-- A finite family of derivations of an associative coefficient ring. -/
structure DerivationFamily where
  apply : ι → A → A
  map_add : ∀ i a b, apply i (a + b) = apply i a + apply i b
  map_mul : ∀ i a b, apply i (a * b) = apply i a * b + a * apply i b

namespace DerivationFamily

theorem map_zero (D : DerivationFamily (ι := ι) (A := A)) (i : ι) :
    D.apply i 0 = 0 := by
  have h := D.map_add i 0 0
  have h' := congrArg (fun z : A => z - D.apply i 0) h
  simpa using h'.symm

theorem map_neg (D : DerivationFamily (ι := ι) (A := A)) (i : ι) (a : A) :
    D.apply i (-a) = -D.apply i a := by
  have h := D.map_add i a (-a)
  rw [add_neg_cancel, D.map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem map_sub (D : DerivationFamily (ι := ι) (A := A)) (i : ι) (a b : A) :
    D.apply i (a - b) = D.apply i a - D.apply i b := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, sub_eq_add_neg]

theorem map_commutator (D : DerivationFamily (ι := ι) (A := A))
    (i : ι) (a b : A) :
    D.apply i (commutator a b) =
      commutator (D.apply i a) b + commutator a (D.apply i b) := by
  simp only [commutator, D.map_sub, D.map_mul]
  noncomm_ring

end DerivationFamily

/-- Curvature with the sign convention in Shirokov's equations (4.3), (5.15). -/
def fieldStrength (D : DerivationFamily (ι := ι) (A := A))
    (B : ι → A) (i j : ι) : A :=
  D.apply i (B j) - D.apply j (B i) - commutator (B i) (B j)

/-- The coordinate divergence `D_i F_{ij} - [B_i,F_{ij}]`. -/
def yangMillsCurrent (D : DerivationFamily (ι := ι) (A := A))
    (B : ι → A) (F : ι → ι → A) (j : ι) : A :=
  ∑ i, (D.apply i (F i j) - commutator (B i) (F i j))

/-- Flatness of the background and parallelness of `K` make the curvature of
`B = C + K` equal to the algebraic term `-[K_i,K_j]`. -/
theorem fieldStrength_background_plus_parallel
    (D : DerivationFamily (ι := ι) (A := A)) (C K : ι → A)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j, D.apply i (K j) = commutator (C i) (K j))
    (i j : ι) :
    fieldStrength D (fun k => C k + K k) i j = -commutator (K i) (K j) := by
  simp only [fieldStrength, Pi.add_apply]
  rw [D.map_add, D.map_add, hparallel i j, hparallel j i]
  calc
    D.apply i (C j) + commutator (C i) (K j) -
        (D.apply j (C i) + commutator (C j) (K i)) -
        commutator (C i + K i) (C j + K j) =
      (D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j)) -
        commutator (K i) (K j) := by
          simp only [commutator]
          noncomm_ring
    _ = -commutator (K i) (K j) := by rw [hflat i j]; noncomm_ring

theorem yangMillsCurrentTerm_background_plus_parallel
    (D : DerivationFamily (ι := ι) (A := A)) (C K : ι → A)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j, D.apply i (K j) = commutator (C i) (K j))
    (i j : ι) :
    D.apply i (fieldStrength D (fun k => C k + K k) i j) -
      commutator (C i + K i) (fieldStrength D (fun k => C k + K k) i j) =
        commutator (K i) (commutator (K i) (K j)) := by
  rw [fieldStrength_background_plus_parallel D C K hflat hparallel i j]
  have hJacobi :
      commutator (C i) (commutator (K i) (K j)) =
        commutator (commutator (C i) (K i)) (K j) +
          commutator (K i) (commutator (C i) (K j)) := by
    simp only [commutator]
    noncomm_ring
  calc
    D.apply i (-commutator (K i) (K j)) -
        commutator (C i + K i) (-commutator (K i) (K j)) =
      -(commutator (commutator (C i) (K i)) (K j) +
        commutator (K i) (commutator (C i) (K j))) +
        commutator (C i) (commutator (K i) (K j)) +
        commutator (K i) (commutator (K i) (K j)) := by
          rw [D.map_neg, D.map_commutator, hparallel i i, hparallel i j]
          simp only [commutator]
          noncomm_ring
    _ = commutator (K i) (commutator (K i) (K j)) := by
      rw [← hJacobi]
      abel

/-- The Yang--Mills current of `C + K` is the double-commutator current when
`C` is flat and `K` is covariantly constant. -/
theorem yangMillsCurrent_background_plus_parallel
    (D : DerivationFamily (ι := ι) (A := A)) (C K : ι → A)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j, D.apply i (K j) = commutator (C i) (K j))
    (j : ι) :
    yangMillsCurrent D (fun k => C k + K k)
      (fieldStrength D (fun k => C k + K k)) j =
        ∑ i, commutator (K i) (commutator (K i) (K j)) := by
  unfold yangMillsCurrent
  apply Finset.sum_congr rfl
  intro i hi
  exact yangMillsCurrentTerm_background_plus_parallel D C K hflat hparallel i j

/-- Metric-raised pseudo-Euclidean divergence. `ε i` is the diagonal metric
sign; both contracted indices of `F^{ij}` and the outer divergence are raised. -/
def pseudoYangMillsCurrent {R : Type*} [CommRing R] [Algebra R A]
    (D : DerivationFamily (ι := ι) (A := A)) (ε : ι → R)
    (B : ι → A) (F : ι → ι → A) (j : ι) : A :=
  ε j • ∑ i, ε i • (D.apply i (F i j) - commutator (B i) (F i j))

/-- Raising the pseudo-Euclidean indices in Shirokov's coordinate current
transports `C + K` to the correspondingly signed double-commutator sum. -/
theorem pseudoYangMillsCurrent_background_plus_parallel
    {R : Type*} [CommRing R] [Algebra R A]
    (D : DerivationFamily (ι := ι) (A := A)) (C K : ι → A)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j, D.apply i (K j) = commutator (C i) (K j))
    (ε : ι → R) (j : ι) :
    pseudoYangMillsCurrent D ε (fun k => C k + K k)
      (fieldStrength D (fun k => C k + K k)) j =
        ε j • ∑ i, ε i • commutator (K i) (commutator (K i) (K j)) := by
  unfold pseudoYangMillsCurrent
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [yangMillsCurrentTerm_background_plus_parallel D C K hflat hparallel i j]

end InfoGeometry.Canonical.ShirokovYangMillsTransfer
