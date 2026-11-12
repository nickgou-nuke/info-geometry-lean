/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.MatrixAmplificationTower
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.FinCases

/-!
# An outer symmetry of the recursive binary matrix colimit

The carrier, full matrix stages, bonds and inclusions are exactly those of
`MatrixAmplificationTower`. At every successor stage the previous symmetry
acts entrywise, followed by conjugation by the fresh sign unit `diag(1,-1)`.
The compatible stage involutions descend through the existing direct-limit
endomorphism construction to a ring equivalence of the actual colimit.

Every finite stage has a fresh off-diagonal matrix unit which commutes with
its entire image and is negated by the symmetry. A colimit unit has a
finite-stage representative, so its inner conjugation fixes that fresh
element. For a nontrivial seed in which two is invertible this proves that
the colimit symmetry is not conjugation by any colimit unit. No norm,
completion, trace, modular identification or classification is assumed.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Categorical.MatrixAmplificationShellSymmetry

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

variable (A : Type) [Ring A]

/-- The existing full binary matrix stage, with no change of carrier. -/
abbrev Stage (n : ℕ) : Type := MatrixAmplificationTower.stage (Fin 2) (RingCat.of A) n

/-- The existing algebraic colimit of the full binary matrix tower. -/
abbrev Carrier : Type := MatrixAmplificationTower.Limit (Fin 2) (RingCat.of A)

/-- The fresh diagonal sign matrix is a unit, equal to its own inverse. -/
def shellSignUnit (R : Type) [Ring R] : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := Matrix.diagonal (fun i => if i = 0 then 1 else -1)
  inv := Matrix.diagonal (fun i => if i = 0 then 1 else -1)
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]

/-- Native conjugation by the sign unit on one fresh shell. -/
def shellConjugation (R : Type) [Ring R] :
    Matrix (Fin 2) (Fin 2) R ≃+* Matrix (Fin 2) (Fin 2) R :=
  MulSemiringAction.toRingEquiv
    (ConjAct (Matrix (Fin 2) (Fin 2) R)ˣ) (Matrix (Fin 2) (Fin 2) R)
    (ConjAct.toConjAct (shellSignUnit R))

/-- The two endpoint signs retain their ordered positions around an entry. -/
theorem shellConjugation_apply (R : Type) [Ring R]
    (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    shellConjugation R M i j =
      (if i = 0 then (1 : R) else -1) * M i j *
        (if j = 0 then (1 : R) else -1) := by
  change ((Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 : R) else -1)) *
    M * (Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 : R) else -1))) i j = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Apply the preceding symmetry entrywise and the fresh sign conjugation
on every successor shell. Stage zero is the identity of the arbitrary seed. -/
def stageSymmetry : (n : ℕ) → Stage A n ≃+* Stage A n :=
  Nat.rec (motive := fun n => Stage A n ≃+* Stage A n)
    (RingEquiv.refl A)
    (fun n e => e.mapMatrix.trans (shellConjugation (Stage A n)))

/-- Entrywise computation of the recursively constructed stage symmetry. -/
theorem stageSymmetry_succ_apply (n : ℕ) (M : Stage A (n + 1)) (i j : Fin 2) :
    stageSymmetry A (n + 1) M i j =
      (if i = 0 then (1 : Stage A n) else -1) *
        stageSymmetry A n (M i j) *
        (if j = 0 then (1 : Stage A n) else -1) := by
  change shellConjugation (Stage A n) ((stageSymmetry A n).mapMatrix M) i j = _
  simpa only [shellConjugation_apply]

/-- Diagonal entries are changed only by the preceding stage symmetry. -/
@[simp]
theorem stageSymmetry_succ_diagonal (n : ℕ) (M : Stage A (n + 1)) (i : Fin 2) :
    stageSymmetry A (n + 1) M i i = stageSymmetry A n (M i i) := by
  rw [stageSymmetry_succ_apply]
  fin_cases i <;> simp

/-- The ordinary matrix trace of one shell is equivariant. Its value remains
in the preceding, possibly noncommutative, coefficient ring. -/
theorem trace_stageSymmetry_succ (n : ℕ) (M : Stage A (n + 1)) :
    Matrix.trace (stageSymmetry A (n + 1) M) =
      stageSymmetry A n (Matrix.trace M) := by
  simp only [Matrix.trace, stageSymmetry_succ_diagonal, map_sum]

/-- Every stage symmetry squares to the identity. -/
theorem stageSymmetry_involutive (n : ℕ) : Function.Involutive (stageSymmetry A n) := by
  induction n with
  | zero => intro X; rfl
  | succ n ih =>
    intro M
    ext i j
    simp only [stageSymmetry_succ_apply]
    fin_cases i <;> fin_cases j <;> simp [map_mul, ih]

/-- The stage ring equivalences commute with the actual successor bond. -/
theorem stageSymmetry_bond (n : ℕ) (X : Stage A n) :
    stageSymmetry A (n + 1) (MatrixAmplificationTower.bond (Fin 2) (RingCat.of A) n X) =
      MatrixAmplificationTower.bond (Fin 2) (RingCat.of A) n (stageSymmetry A n X) := by
  change stageSymmetry A (n + 1) (Matrix.scalar (Fin 2) X) =
    Matrix.scalar (Fin 2) (stageSymmetry A n X)
  ext i j
  rw [stageSymmetry_succ_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

/-- The existing direct-limit construction descends the coherent family. -/
def colimitSymmetryHom : Carrier A →+* Carrier A :=
  directLimitEndomorphism (MatrixAmplificationTower.bond (Fin 2) (RingCat.of A))
    (fun n => (stageSymmetry A n).toRingHom) (stageSymmetry_bond A)

/-- The induced homomorphism computes on every actual stage inclusion. -/
@[simp]
theorem colimitSymmetryHom_inclusion (n : ℕ) (X : Stage A n) :
    colimitSymmetryHom A (MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) n X) =
      MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) n (stageSymmetry A n X) :=
  directLimitEndomorphism_of (MatrixAmplificationTower.bond (Fin 2) (RingCat.of A))
    (fun n => (stageSymmetry A n).toRingHom) (stageSymmetry_bond A) n X

/-- The descended compatible family is also its own inverse on the colimit. -/
theorem colimitSymmetryHom_involutive : Function.Involutive (colimitSymmetryHom A) := by
  intro X
  obtain ⟨n, x, rfl⟩ := MatrixAmplificationTower.exists_stage (Fin 2) (RingCat.of A) X
  rw [colimitSymmetryHom_inclusion, colimitSymmetryHom_inclusion,
    stageSymmetry_involutive]

/-- The actual ring equivalence of the existing algebraic colimit. -/
def colimitSymmetry : Carrier A ≃+* Carrier A where
  toFun := colimitSymmetryHom A
  invFun := colimitSymmetryHom A
  left_inv := colimitSymmetryHom_involutive A
  right_inv := colimitSymmetryHom_involutive A
  map_mul' := (colimitSymmetryHom A).map_mul
  map_add' := (colimitSymmetryHom A).map_add

@[simp]
theorem colimitSymmetry_inclusion (n : ℕ) (X : Stage A n) :
    colimitSymmetry A (MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) n X) =
      MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) n (stageSymmetry A n X) :=
  colimitSymmetryHom_inclusion A n X

/-- The new off-diagonal matrix unit at shell `n + 1`, inserted in the
existing colimit. Its coefficient is the identity of the full stage `n`. -/
def freshShell (n : ℕ) : Carrier A :=
  MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) (n + 1)
    (Matrix.single 0 1 (1 : Stage A n))

/-- The fresh matrix unit is negated at its finite stage. -/
theorem stageSymmetry_fresh (n : ℕ) :
    stageSymmetry A (n + 1) (Matrix.single 0 1 (1 : Stage A n)) =
      -Matrix.single 0 1 (1 : Stage A n) := by
  ext i j
  rw [stageSymmetry_succ_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

/-- The descended symmetry negates every fresh-shell witness. -/
@[simp]
theorem colimitSymmetry_freshShell (n : ℕ) :
    colimitSymmetry A (freshShell A n) = -freshShell A n := by
  simp only [freshShell, colimitSymmetry_inclusion, stageSymmetry_fresh, map_neg]

/-- A fresh scalar-coefficient matrix unit commutes with the entire preceding
stage, even when that coefficient ring is noncommutative. -/
theorem fresh_commute_scalar (R : Type) [Ring R] (x : R) :
    Commute (Matrix.single 0 1 (1 : R)) (Matrix.scalar (Fin 2) x) := by
  change Matrix.single 0 1 (1 : R) * Matrix.scalar (Fin 2) x =
    Matrix.scalar (Fin 2) x * Matrix.single 0 1 (1 : R)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.single_apply]

/-- The fresh witness commutes with every element in the whole image of
stage `n`; no commutation assumption is imposed on that stage. -/
theorem freshShell_commute_inclusion (n : ℕ) (X : Stage A n) :
    Commute (freshShell A n) (MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) n X) := by
  rw [← directLimitOf_bond (MatrixAmplificationTower.bond (Fin 2) (RingCat.of A)) n X]
  exact (fresh_commute_scalar (Stage A n) X).map
    (MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of A) (n + 1))

/-- Faithfulness keeps the new matrix unit nonzero in the colimit. -/
theorem freshShell_ne_zero [Nontrivial A] (n : ℕ) : freshShell A n ≠ 0 := by
  intro h
  have hm : (Matrix.single 0 1 (1 : Stage A n) : Stage A (n + 1)) = 0 := by
    apply MatrixAmplificationTower.inclusion_injective (Fin 2) (RingCat.of A) (n + 1)
    simpa only [freshShell, map_zero] using h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Stage A n) => M 0 1) hm
  exact (one_ne_zero : (1 : Stage A n) ≠ 0) (by simpa using he)

/-- Invertibility of two excludes equality of the fresh matrix unit and its negative.
Only the original seed needs an invertibility assumption. -/
theorem freshShell_ne_neg [Nontrivial A] [Invertible (2 : A)] (n : ℕ) :
    freshShell A n ≠ -freshShell A n := by
  intro h
  have hm : (Matrix.single 0 1 (1 : Stage A n) : Stage A (n + 1)) =
      -Matrix.single 0 1 (1 : Stage A n) := by
    apply MatrixAmplificationTower.inclusion_injective (Fin 2) (RingCat.of A) (n + 1)
    simpa only [freshShell, map_neg] using h
  have he : (1 : Stage A n) = -1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (Stage A n) => M 0 1) hm
  have htwo : (2 : Stage A n) = 0 := by
    simpa only [one_add_one_eq_two, neg_add_cancel] using
      congrArg (fun z : Stage A n => z + 1) he
  have hseed : (2 : A) = 0 := by
    apply MatrixAmplificationTower.transition_injective (Fin 2) (RingCat.of A) 0 n (Nat.zero_le n)
    simpa using htwo
  exact Invertible.ne_zero (2 : A) hseed

/-- No unit of the actual algebraic colimit implements the shell symmetry.
The proof represents only the underlying value of that unit at a finite stage. -/
theorem colimitSymmetry_ne_inner [Nontrivial A] [Invertible (2 : A)]
    (u : (Carrier A)ˣ) :
    colimitSymmetry A ≠
      MulSemiringAction.toRingEquiv (ConjAct (Carrier A)ˣ) (Carrier A)
        (ConjAct.toConjAct u) := by
  intro hinner
  obtain ⟨n, x, hx⟩ := MatrixAmplificationTower.exists_stage (Fin 2) (RingCat.of A) (u : Carrier A)
  have hcomm : Commute (u : Carrier A) (freshShell A n) := by
    rw [← hx]
    exact (freshShell_commute_inclusion A n x).symm
  have hfixed : colimitSymmetry A (freshShell A n) = freshShell A n := by
    rw [hinner]
    change (u : Carrier A) * freshShell A n * (↑(u⁻¹) : Carrier A) = freshShell A n
    rw [hcomm.eq, mul_assoc, Units.val_inv, mul_one]
  exact freshShell_ne_neg A n (hfixed.symm.trans (colimitSymmetry_freshShell A n))

end InfoGeometry.Categorical.MatrixAmplificationShellSymmetry
