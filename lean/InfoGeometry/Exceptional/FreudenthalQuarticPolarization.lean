import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Algebra.H3ZornFreudenthalPolarizedIdentity

/-!
# Canonical four-linear polarization of a Freudenthal quartic

The quartic invariant and its four-linear polarization are kept separate.
This owner supplies the normalization theorem from an actual symmetric
four-linear form; it does not manufacture an H₃(Zorn) form from the diagonal
polynomial.  The latter is the remaining coordinate bridge.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure SymmetricQuarticForm (V : Type*) [AddCommGroup V] [Module ℝ V]
    where
  value : V → V → V → V → ℝ
  map_add_left : ∀ a b c x y, value (x + y) a b c = value x a b c + value y a b c
  map_smul_left : ∀ (r : ℝ) a b c x, value (r • x) a b c = r * value x a b c
  symmetric : ∀ (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → V),
    value (x 0) (x 1) (x 2) (x 3) =
      value (x (σ 0)) (x (σ 1)) (x (σ 2)) (x (σ 3))

def SymmetricQuarticForm.polarize
    (B : SymmetricQuarticForm V) (Q : Fin 4 → V) : ℝ :=
  (1 / 24 : ℝ) * ∑ σ : Equiv.Perm (Fin 4),
    B.value (Q (σ 0)) (Q (σ 1)) (Q (σ 2)) (Q (σ 3))

theorem SymmetricQuarticForm.polarize_eq
    (B : SymmetricQuarticForm V) (Q : Fin 4 → V) :
    B.polarize Q = B.value (Q 0) (Q 1) (Q 2) (Q 3) := by
  unfold SymmetricQuarticForm.polarize
  have hσ (σ : Equiv.Perm (Fin 4)) :
      B.value (Q (σ 0)) (Q (σ 1)) (Q (σ 2)) (Q (σ 3)) =
        B.value (Q 0) (Q 1) (Q 2) (Q 3) := by
    symm
    exact B.symmetric σ Q
  simp_rw [hσ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  norm_num [Fintype.card_fin, div_eq_mul_inv]
  ring

theorem SymmetricQuarticForm.polarize_diagonal
    (B : SymmetricQuarticForm V) (x : V) :
    B.polarize (fun _ : Fin 4 => x) = B.value x x x x := by
  simpa using B.polarize_eq (fun _ : Fin 4 => x)

def SymmetricQuarticForm.diagonal
    (B : SymmetricQuarticForm V) (x : V) : ℝ := B.value x x x x

theorem SymmetricQuarticForm.polarize_diagonal_eq_diagonal
    (B : SymmetricQuarticForm V) (x : V) :
    B.polarize (fun _ : Fin 4 => x) = B.diagonal x := by
  exact B.polarize_diagonal x

end InfoGeometry.Exceptional.Freudenthal
