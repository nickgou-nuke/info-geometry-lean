import InfoGeometry.External.Auto.AlgebraicCuntzToeplitzInductive
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral Cuntz--Toeplitz induction

The unital Cuntz partition is not preserved by the naive `n → n+1` generator
inclusion.  The induction that is canonical at the algebraic level is the
Cuntz--Toeplitz inclusion; to keep chiral balance, add modes in even/odd pairs
and embed

`Fin (2*n) → Fin (2*(n+1))`.

This file proves the finite parity-preserving induction map and its induced
algebra homomorphism on the tensor-algebra/RingQuot Cuntz--Toeplitz stages.
The old range projections form a corner in the next stage, not the global unit.
-/

noncomputable section

namespace ChiralCuntzInductive

open AlgebraicCuntzToeplitzInductive
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- Chiral parity of a finite mode: even/odd index. -/
def chiralParity {m : ℕ} (i : Fin m) : ℕ := i.val % 2

/-- The parity-preserving inclusion obtained by adding one even/odd pair. -/
def chiralStep (n : ℕ) : Fin (2 * n) → Fin (2 * (n + 1)) :=
  fun i => ⟨i.val, by
    have hi : i.val < 2 * n := i.isLt
    omega⟩

@[simp] theorem chiralStep_val (n : ℕ) (i : Fin (2 * n)) :
    (chiralStep n i).val = i.val := rfl

/-- The chiral induction preserves parity exactly. -/
theorem chiralStep_parity_preserving (n : ℕ) (i : Fin (2 * n)) :
    chiralParity (chiralStep n i) = chiralParity i := rfl

/-- The chiral step is injective. -/
theorem chiralStep_injective (n : ℕ) : Function.Injective (chiralStep n) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (2 * (n + 1)) => x.val) h)

/-- Algebraic Cuntz--Toeplitz chiral induction: old generators map to old-parity
slots in the next even/odd-balanced stage. -/
def chiralStepHom (n : ℕ) :
    CTAlg R (Fin (2 * n)) →ₐ[R] CTAlg R (Fin (2 * (n + 1))) :=
  lift (R := R) (A := CTAlg R (Fin (2 * (n + 1))))
    (fun i : Fin (2 * n) => S (R := R) (chiralStep n i))
    (fun i : Fin (2 * n) => T (R := R) (chiralStep n i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hstep : chiralStep n i ≠ chiralStep n j := fun hc => h ((chiralStep_injective n) hc)
        simp [h, hstep])

@[simp] theorem chiralStepHom_S (n : ℕ) (i : Fin (2 * n)) :
    chiralStepHom (R := R) n (S (R := R) i) = S (R := R) (chiralStep n i) := by
  exact lift_S (R := R) (A := CTAlg R (Fin (2 * (n + 1))))
    (fun i : Fin (2 * n) => S (R := R) (chiralStep n i))
    (fun i : Fin (2 * n) => T (R := R) (chiralStep n i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hstep : chiralStep n i ≠ chiralStep n j := fun hc => h ((chiralStep_injective n) hc)
        simp [h, hstep]) i

@[simp] theorem chiralStepHom_T (n : ℕ) (i : Fin (2 * n)) :
    chiralStepHom (R := R) n (T (R := R) i) = T (R := R) (chiralStep n i) := by
  exact lift_T (R := R) (A := CTAlg R (Fin (2 * (n + 1))))
    (fun i : Fin (2 * n) => S (R := R) (chiralStep n i))
    (fun i : Fin (2 * n) => T (R := R) (chiralStep n i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hstep : chiralStep n i ≠ chiralStep n j := fun hc => h ((chiralStep_injective n) hc)
        simp [h, hstep]) i

/-- Range projection for one Cuntz--Toeplitz mode. -/
def rangeProj {m : ℕ} (i : Fin m) : CTAlg R (Fin m) :=
  S (R := R) i * T (R := R) i

/-- Even chiral corner at stage `2*n`. -/
def evenCorner (n : ℕ) : CTAlg R (Fin (2 * n)) :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * n) => chiralParity i = 0)), rangeProj (R := R) i

/-- Odd chiral corner at stage `2*n`. -/
def oddCorner (n : ℕ) : CTAlg R (Fin (2 * n)) :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * n) => chiralParity i = 1)), rangeProj (R := R) i

/-- Old range projection corner inside the next chiral stage.  This is the
correct invariant substitute for the global Cuntz partition. -/
def oldChiralCorner (n : ℕ) : CTAlg R (Fin (2 * (n + 1))) :=
  ∑ i : Fin (2 * n), rangeProj (R := R) (chiralStep n i)

/-- Old even corner embedded into the next chiral stage. -/
def oldEvenCorner (n : ℕ) : CTAlg R (Fin (2 * (n + 1))) :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * n) => chiralParity i = 0)),
    rangeProj (R := R) (chiralStep n i)

/-- Old odd corner embedded into the next chiral stage. -/
def oldOddCorner (n : ℕ) : CTAlg R (Fin (2 * (n + 1))) :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * n) => chiralParity i = 1)),
    rangeProj (R := R) (chiralStep n i)

/-- Image of the finite old range-projection sum is the old corner in the next stage. -/
theorem chiralStepHom_range_sum (n : ℕ) :
    chiralStepHom (R := R) n
      (∑ i : Fin (2 * n), rangeProj (R := R) i) = oldChiralCorner (R := R) n := by
  simp [oldChiralCorner, rangeProj, map_sum, map_mul]

/-- Image of the old even chiral corner is the old even corner in the next stage. -/
theorem chiralStepHom_evenCorner (n : ℕ) :
    chiralStepHom (R := R) n (evenCorner (R := R) n) = oldEvenCorner (R := R) n := by
  simp [evenCorner, oldEvenCorner, rangeProj, map_sum, map_mul]

/-- Image of the old odd chiral corner is the old odd corner in the next stage. -/
theorem chiralStepHom_oddCorner (n : ℕ) :
    chiralStepHom (R := R) n (oddCorner (R := R) n) = oldOddCorner (R := R) n := by
  simp [oddCorner, oldOddCorner, rangeProj, map_sum, map_mul]

/-- The old corner is chiral-parity balanced: every embedded old index has the
same even/odd label it had before induction. -/
theorem oldCorner_parity_balanced (n : ℕ) :
    ∀ i : Fin (2 * n), chiralParity (chiralStep n i) = chiralParity i :=
  chiralStep_parity_preserving n

end ChiralCuntzInductive
