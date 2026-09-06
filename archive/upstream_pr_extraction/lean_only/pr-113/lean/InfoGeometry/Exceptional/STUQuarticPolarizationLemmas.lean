import InfoGeometry.Exceptional.STUQuarticPolarization
import InfoGeometry.Exceptional.FreudenthalFiniteDifferencePolarization

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open scoped BigOperators
open InfoGeometry.Exceptional.Freudenthal

def fin4BoolFinsetEquiv :
    (Fin 4 → Bool) ≃ Finset (Fin 4) where
  toFun f := Finset.univ.filter (fun i => f i = true)
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    simp
  right_inv s := by
    ext i
    simp

def finiteDifferenceQuarticPolarizationBits
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : V → ℝ) (Q : Fin 4 → V) : ℝ :=
  (1 / 24 : ℝ) * ∑ b : Fin 4 → Bool,
    (-1 : ℝ) ^ (4 - (fin4BoolFinsetEquiv b).card) *
      P (∑ i ∈ fin4BoolFinsetEquiv b, Q i)

theorem finiteDifferenceQuarticPolarizationBits_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : V → ℝ) (Q : Fin 4 → V) :
    finiteDifferenceQuarticPolarizationBits P Q =
      finiteDifferenceQuarticPolarization P Q := by
  unfold finiteDifferenceQuarticPolarizationBits
  unfold finiteDifferenceQuarticPolarization
  rw [Fintype.sum_equiv fin4BoolFinsetEquiv]
  intro
  rfl

theorem finsetFin4_card : Fintype.card (Finset (Fin 4)) = 16 := by
  rw [← Fintype.card_congr fin4BoolFinsetEquiv]
  simp

theorem fin4PermutationProduct_invariant (a : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin 4)) :
    a (σ 0) * a (σ 1) * a (σ 2) * a (σ 3) =
      a 0 * a 1 * a 2 * a 3 := by
  have h := Fintype.prod_equiv σ
    (fun i : Fin 4 => a (σ i)) (fun i : Fin 4 => a i) (fun _ => rfl)
  convert h using 1 <;> simp [Fin.prod_univ_succ] <;> ring

theorem fin4PolarizedProduct_diag (a : Fin 4 → ℝ) :
    fin4PolarizedProduct a a a a =
      a 0 * a 1 * a 2 * a 3 := by
  unfold fin4PolarizedProduct
  simp_rw [show ∀ σ : Equiv.Perm (Fin 4),
      a (σ 0) * a (σ 1) * a (σ 2) * a (σ 3) =
        a 0 * a 1 * a 2 * a 3 from
      fun σ => fin4PermutationProduct_invariant a σ]
  norm_num [Fintype.card_perm]
  ring

end InfoGeometry.Exceptional.STUDatum
