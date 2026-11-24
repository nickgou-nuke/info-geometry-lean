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

/-- The zero family is a concrete inhabitant of the derivation-family carrier. -/
def zeroDerivationFamily : DerivationFamily (ι := ι) (A := A) where
  apply _ _ := 0
  map_add _ _ _ := by simp
  map_mul _ _ _ := by simp

namespace DerivationFamily

omit [Fintype ι] [DecidableEq ι] in
theorem map_zero (D : DerivationFamily (ι := ι) (A := A)) (i : ι) :
    D.apply i 0 = 0 := by
  have h := D.map_add i 0 0
  have h' := congrArg (fun z : A => z - D.apply i 0) h
  simpa using h'.symm

omit [Fintype ι] [DecidableEq ι] in
theorem map_neg (D : DerivationFamily (ι := ι) (A := A)) (i : ι) (a : A) :
    D.apply i (-a) = -D.apply i a := by
  have h := D.map_add i a (-a)
  rw [add_neg_cancel, D.map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

omit [Fintype ι] [DecidableEq ι] in
theorem map_sub (D : DerivationFamily (ι := ι) (A := A)) (i : ι) (a b : A) :
    D.apply i (a - b) = D.apply i a - D.apply i b := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, sub_eq_add_neg]

omit [Fintype ι] [DecidableEq ι] in
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

/-- Shirokov's covariant derivative convention on coefficient fields:
`∇ᵢ a = Dᵢ a - [Bᵢ,a]`. -/
def covariantDerivative (D : DerivationFamily (ι := ι) (A := A))
    (B : ι → A) (i : ι) (a : A) : A :=
  D.apply i a - commutator (B i) a

omit [Fintype ι] [DecidableEq ι] in
theorem covariantDerivative_add
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (i : ι) (a b : A) :
    covariantDerivative D B i (a + b) =
      covariantDerivative D B i a + covariantDerivative D B i b := by
  simp only [covariantDerivative, D.map_add, commutator]
  noncomm_ring

omit [Fintype ι] [DecidableEq ι] in
theorem covariantDerivative_neg
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (i : ι) (a : A) :
    covariantDerivative D B i (-a) = -covariantDerivative D B i a := by
  simp only [covariantDerivative, D.map_neg, commutator]
  noncomm_ring

omit [Fintype ι] in
theorem covariantDerivative_sum
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (i : ι) (s : Finset ι) (f : ι → A) :
    covariantDerivative D B i (∑ j ∈ s, f j) =
      ∑ j ∈ s, covariantDerivative D B i (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [covariantDerivative, commutator, DerivationFamily.map_zero]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        covariantDerivative_add, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem fieldStrength_antisymm
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (i j : ι) : fieldStrength D B j i = -fieldStrength D B i j := by
  simp only [fieldStrength, commutator]
  noncomm_ring

omit [Fintype ι] [DecidableEq ι] in
theorem covariantDerivative_commutator
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (hcomm : ∀ i j a, D.apply i (D.apply j a) = D.apply j (D.apply i a))
    (i j : ι) (a : A) :
    covariantDerivative D B i (covariantDerivative D B j a) -
      covariantDerivative D B j (covariantDerivative D B i a) =
        -commutator (fieldStrength D B i j) a := by
  simp only [covariantDerivative, D.map_sub]
  rw [D.map_commutator i (B j) a, D.map_commutator j (B i) a]
  rw [hcomm i j a]
  simp only [fieldStrength, commutator]
  noncomm_ring

/-- Equation (4.4) of Shirokov: the covariant divergence of the current
`Jⱼ = Σᵢ ∇ᵢ Fᵢⱼ` vanishes for a finite unweighted coordinate contraction.
The proof uses commuting coordinate derivations and the real scalar action to
cancel the factor two obtained from antisymmetry. -/
theorem nonabelian_current_conservation
    [Algebra ℝ A]
    (D : DerivationFamily (ι := ι) (A := A)) (B : ι → A)
    (hcomm : ∀ i j a, D.apply i (D.apply j a) = D.apply j (D.apply i a)) :
    ∑ j, covariantDerivative D B j
      (∑ i, covariantDerivative D B i (fieldStrength D B i j)) = 0 := by
  classical
  let S : A := ∑ j, ∑ i,
    covariantDerivative D B j
      (covariantDerivative D B i (fieldStrength D B i j))
  let T : A := ∑ i, ∑ j,
    covariantDerivative D B i
      (covariantDerivative D B j (fieldStrength D B i j))
  have hST : S = T := by
    dsimp [S, T]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hcurv := covariantDerivative_commutator D B hcomm j i
      (fieldStrength D B i j)
    rw [fieldStrength_antisymm D B i j] at hcurv
    have hbracket : commutator (-fieldStrength D B i j)
        (fieldStrength D B i j) = 0 := by
      simp [commutator]
    rw [hbracket, neg_zero, sub_eq_zero] at hcurv
    exact hcurv
  have hSnegT : S = -T := by
    dsimp [S, T]
    calc
      (∑ j, ∑ i, covariantDerivative D B j
          (covariantDerivative D B i (fieldStrength D B i j))) =
        ∑ i, ∑ j, covariantDerivative D B i
          (covariantDerivative D B j (fieldStrength D B j i)) := by
            rw [← Fintype.sum_prod_type']
      _ = ∑ i, ∑ j, -(covariantDerivative D B i
          (covariantDerivative D B j (fieldStrength D B i j))) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [fieldStrength_antisymm D B i j,
              covariantDerivative_neg, covariantDerivative_neg]
      _ = -∑ i, ∑ j, covariantDerivative D B i
          (covariantDerivative D B j (fieldStrength D B i j)) := by
            simp only [Finset.sum_neg_distrib]
  have hSS : S + S = 0 := by
    have hneg : S = -S := by rwa [← hST] at hSnegT
    calc
      S + S = S + -S := congrArg (fun x : A => S + x) hneg
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • S = 0 := by
    simpa [two_smul] using hSS
  have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hSzero : S = 0 := (smul_eq_zero.mp htwo).resolve_left htwo_ne
  simpa [S, covariantDerivative_sum] using hSzero

/-- The coordinate divergence `D_i F_{ij} - [B_i,F_{ij}]`. -/
def yangMillsCurrent (D : DerivationFamily (ι := ι) (A := A))
    (B : ι → A) (F : ι → ι → A) (j : ι) : A :=
  ∑ i, (D.apply i (F i j) - commutator (B i) (F i j))

omit [Fintype ι] [DecidableEq ι] in
/-- Flatness of the background and parallelness of `K` make the curvature of
`B = C + K` equal to the algebraic term `-[K_i,K_j]`. -/
theorem fieldStrength_background_plus_parallel
    (D : DerivationFamily (ι := ι) (A := A)) (C K : ι → A)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j, D.apply i (K j) = commutator (C i) (K j))
    (i j : ι) :
    fieldStrength D (fun k => C k + K k) i j = -commutator (K i) (K j) := by
  simp only [fieldStrength]
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

omit [Fintype ι] [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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
