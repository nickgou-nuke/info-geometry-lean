import Mathlib.Tactic

/-!
# Horadam `2^k`-ion matrix methods: finite coordinate layer

This module is a theorem-safe first formal slice of
`preprints201906.0303.v1`, *Horadam 2^k-ions*.

It formalizes only the finite coordinate recurrence and companion-matrix method:

* scalar Horadam recurrence `W_{n+2}=p W_{n+1}+q W_n`;
* coordinate/`2^k`-ion lift `Ŵ_n=(W_n,...,W_{n+N-1})`;
* componentwise recurrence `Ŵ_{n+2}=p Ŵ_{n+1}+q Ŵ_n`;
* companion one-step state update;
* the one-step Horadam-ion matrix update behind Theorem 8.

It does **not** formalize Cayley-Dickson multiplication, nonassociative
identities, Binet formulas over radicals, Catalan/Cassini identities, or norm
formulas.  Those require separate owner files.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonMatrixMethods

open Matrix
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- Horadam scalar sequence with parameters `(a,b,p,q)`. -/
def horadam (a b p q : R) : ℕ → R
  | 0 => a
  | 1 => b
  | n + 2 => p * horadam a b p q (n + 1) + q * horadam a b p q n

/-- Recurrence readback for the scalar Horadam sequence. -/
theorem horadam_succ_succ (a b p q : R) (n : ℕ) :
    horadam a b p q (n + 2) =
      p * horadam a b p q (n + 1) + q * horadam a b p q n := by
  rfl

/-- Finite coordinate carrier for the `N`-component Horadam `2^k`-ion shadow. -/
abbrev Ion (N : ℕ) (R : Type*) := Fin N → R

/-- Constant coordinate packet. -/
def constIon {N : ℕ} (c : R) : Ion N R := fun _ => c

/-- Scalar multiplication of a coordinate packet by a base-ring scalar. -/
def ionScale {N : ℕ} (c : R) (X : Ion N R) : Ion N R := fun s => c * X s

/-- Coordinate Horadam `2^k`-ion shadow: `Ŵ_n(s)=W_{n+s}`. -/
def horadamIon {N : ℕ} (a b p q : R) (n : ℕ) : Ion N R :=
  fun s => horadam a b p q (n + s.val)

/-- The Horadam recurrence lifts componentwise to every finite coordinate packet. -/
theorem horadamIon_recurrence {N : ℕ} (a b p q : R) (n : ℕ) :
    horadamIon (N := N) a b p q (n + 2) =
      ionScale p (horadamIon (N := N) a b p q (n + 1)) +
        ionScale q (horadamIon (N := N) a b p q n) := by
  ext s
  simp [horadamIon, ionScale]
  rw [show n + 2 + s.val = n + s.val + 2 by omega]
  rw [show n + 1 + s.val = n + s.val + 1 by omega]
  exact horadam_succ_succ a b p q (n + s.val)

/-- Fundamental Horadam sequence `U_n = W_n(0,1,p,q)`. -/
def U (p q : R) : ℕ → R := horadam 0 1 p q

/-- The `2 × 2` companion matrix `[[p,q],[1,0]]`. -/
def companion (p q : R) : Matrix (Fin 2) (Fin 2) R := !![p, q; 1, 0]

/-- State vector `[U_{n+1}, U_n]^T`. -/
def fundamentalState (p q : R) (n : ℕ) : Fin 2 → R := ![U p q (n + 1), U p q n]

/-- The companion matrix advances the fundamental state by one step. -/
theorem companion_mul_fundamentalState (p q : R) (n : ℕ) :
    (companion p q).mulVec (fundamentalState p q n) = fundamentalState p q (n + 1) := by
  ext i
  fin_cases i
  · simp [companion, fundamentalState, U, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact horadam_succ_succ (0 : R) 1 p q n
  · simp [companion, fundamentalState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Companion matrix with entries lifted as constant coordinate packets. -/
def companionIon {N : ℕ} (p q : R) : Matrix (Fin 2) (Fin 2) (Ion N R) :=
  !![constIon p, constIon q; constIon 1, constIon 0]

/-- Horadam-ion matrix packet from paper equation (4.5), shifted to index `n`. -/
def horadamIonMatrix {N : ℕ} (a b p q : R) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (Ion N R) :=
  !![horadamIon (N := N) a b p q (n + 2), ionScale q (horadamIon (N := N) a b p q (n + 1));
     horadamIon (N := N) a b p q (n + 1), ionScale q (horadamIon (N := N) a b p q n)]

/-- One-step Horadam-ion matrix method behind Theorem 8. -/
theorem horadamIonMatrix_mul_companionIon {N : ℕ} (a b p q : R) (n : ℕ) :
    horadamIonMatrix (N := N) a b p q n * companionIon (N := N) p q =
      horadamIonMatrix (N := N) a b p q (n + 1) := by
  ext i j s
  fin_cases i <;> fin_cases j <;>
    simp [horadamIonMatrix, companionIon, horadamIon, ionScale, constIon,
      Matrix.mul_apply, Fin.sum_univ_two]
  · rw [show n + 3 + s.val = n + 1 + s.val + 2 by omega]
    rw [show n + 2 + s.val = n + 1 + s.val + 1 by omega]
    calc
      horadam a b p q (n + 1 + s.val + 1) * p +
          q * horadam a b p q (n + 1 + s.val) =
          p * horadam a b p q (n + 1 + s.val + 1) +
            q * horadam a b p q (n + 1 + s.val) := by ring
      _ = horadam a b p q (n + 1 + s.val + 2) := by
          rw [← horadam_succ_succ a b p q (n + 1 + s.val)]
  · ring_nf
  · rw [show n + 2 + s.val = n + s.val + 2 by omega]
    rw [show n + 1 + s.val = n + s.val + 1 by omega]
    calc
      horadam a b p q (n + s.val + 1) * p +
          q * horadam a b p q (n + s.val) =
          p * horadam a b p q (n + s.val + 1) +
            q * horadam a b p q (n + s.val) := by ring
      _ = horadam a b p q (n + s.val + 2) := by
          rw [← horadam_succ_succ a b p q (n + s.val)]
  · ring

/-- Consolidated finite packet for the first formal slice of the paper. -/
theorem horadam_ion_matrix_methods_packet {N : ℕ} (a b p q : R) :
    (∀ n : ℕ,
      horadam a b p q (n + 2) =
        p * horadam a b p q (n + 1) + q * horadam a b p q n) ∧
    (∀ n : ℕ,
      horadamIon (N := N) a b p q (n + 2) =
        ionScale p (horadamIon (N := N) a b p q (n + 1)) +
          ionScale q (horadamIon (N := N) a b p q n)) ∧
    (∀ n : ℕ,
      (companion p q).mulVec (fundamentalState p q n) = fundamentalState p q (n + 1)) ∧
    (∀ n : ℕ,
      horadamIonMatrix (N := N) a b p q n * companionIon (N := N) p q =
        horadamIonMatrix (N := N) a b p q (n + 1)) := by
  exact ⟨horadam_succ_succ a b p q,
    horadamIon_recurrence a b p q,
    companion_mul_fundamentalState p q,
    horadamIonMatrix_mul_companionIon a b p q⟩

end InfoGeometry.Arithmetic.HoradamIonMatrixMethods

end noncomputable section
