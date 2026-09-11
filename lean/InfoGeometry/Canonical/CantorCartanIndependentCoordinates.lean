import InfoGeometry.Canonical.CantorCartanTorusLaplaceMellin
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open scoped BigOperators

theorem cartanCoordinates_laplaceKernel
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) := by
  unfold cartanLaplaceKernel cartanCoordinates
  congr 1
  simp [Fin.sum_univ_succ]
  ring

theorem cartanCoordinates_logarithmicMellinKernel
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLogarithmicMellinKernel s (cartanCoordinates u v) =
      Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) := by
  rw [cartanLaplace_eq_logarithmicMellin]
  exact cartanCoordinates_laplaceKernel s u v

theorem cartanLaplaceKernel_traceZero_shift
    (s t : Fin 3 → ℝ) (ht : cartanTraceZero t) (c : ℝ) :
    cartanLaplaceKernel (fun i => s i + c) t =
      cartanLaplaceKernel s t := by
  unfold cartanLaplaceKernel
  congr 1
  simp only [Fin.sum_univ_three]
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [cartanTraceZero, Fin.sum_univ_three] using ht
  have hmul : c * (t 0 + t 1 + t 2) = 0 := by
    rw [hsum, mul_zero]
  ring_nf
  nlinarith [hmul]

theorem cartanTorusCoordinates_cartanCoordinates_log
    (u v : ℝ) (i : Fin 3) :
    Real.log (cartanTorusCoordinates (cartanCoordinates u v) i) =
      2 * cartanCoordinates u v i := by
  simp [cartanTorusCoordinates]

theorem cartanTorusCoordinates_cartanCoordinates_product_eq_one
    (u v : ℝ) :
    ∏ i : Fin 3, cartanTorusCoordinates (cartanCoordinates u v) i = 1 := by
  exact cartanTorusCoordinates_product_eq_one
    (cartanCoordinates_traceZero u v)

theorem cartanLaplaceKernel_eq_cartanTorusCoordinates_rpow
    (s t : Fin 3 → ℝ) :
    cartanLaplaceKernel s t =
      ∏ i : Fin 3,
        cartanTorusCoordinates t i ^ (-s i / 2 : ℝ) := by
  rw [← cartanLaplace_eq_logarithmicMellin s t]
  unfold cartanLogarithmicMellinKernel
  change Real.exp (∑ i : Fin 3,
      (-s i / 2) * Real.log (cartanTorusCoordinates t i)) =
    ∏ i : Fin 3, cartanTorusCoordinates t i ^ (-s i / 2 : ℝ)
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (cartanTorusCoordinates_pos t i)]
  ring_nf

theorem cartanLaplaceKernel_cartanCoordinates_reduced
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) := by
  unfold cartanLaplaceKernel cartanCoordinates
  simp only [Fin.sum_univ_three]
  simp
  ring_nf

theorem cartanLaplaceKernel_cartanCoordinates_spectral_differences
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      Real.exp (-(s 0 - s 2) * u) *
        Real.exp (-(s 1 - s 2) * v) := by
  rw [cartanLaplaceKernel_cartanCoordinates_reduced]
  calc
    Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) =
        Real.exp (-(s 0 - s 2) * u) *
          Real.exp (-(s 1 - s 2) * v) := by
            rw [← Real.exp_add]
            congr 1
            ring

theorem cartanLaplaceKernel_eq_cartanTorusCoordinates_rpow_spectral_differences
    (s t : Fin 3 → ℝ) (ht : cartanTraceZero t) :
    cartanLaplaceKernel s t =
      cartanTorusCoordinates t 0 ^ (-(s 0 - s 2) / 2 : ℝ) *
        cartanTorusCoordinates t 1 ^ (-(s 1 - s 2) / 2 : ℝ) := by
  obtain ⟨u, v, huv⟩ := exists_cartanCoordinates_of_traceZero ht
  rw [← huv]
  rw [cartanLaplaceKernel_cartanCoordinates_reduced]
  rw [Real.rpow_def_of_pos (cartanTorusCoordinates_pos _ 0),
    Real.rpow_def_of_pos (cartanTorusCoordinates_pos _ 1)]
  rw [cartanTorusCoordinates_log, cartanTorusCoordinates_log]
  rw [← Real.exp_add]
  simp [cartanCoordinates]
  ring

theorem cartanLaplaceKernel_cartanCoordinates_exp_spectral_differences
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      Real.exp (-(s 0 - s 2) * u - (s 1 - s 2) * v) := by
  rw [cartanLaplaceKernel_cartanCoordinates_reduced]
  calc
    Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) =
        Real.exp (-(s 0 - s 2) * u - (s 1 - s 2) * v) := by
          congr 1
          ring

theorem cartanLaplaceKernel_cartanCoordinates_two_coordinate_mellin
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      cartanTorusCoordinates (cartanCoordinates u v) 0 ^
          (-(s 0 - s 2) / 2 : ℝ) *
        cartanTorusCoordinates (cartanCoordinates u v) 1 ^
          (-(s 1 - s 2) / 2 : ℝ) := by
  rw [cartanLaplaceKernel_cartanCoordinates_reduced]
  rw [Real.rpow_def_of_pos
      (cartanTorusCoordinates_pos (cartanCoordinates u v) 0),
    Real.rpow_def_of_pos
      (cartanTorusCoordinates_pos (cartanCoordinates u v) 1)]
  rw [cartanTorusCoordinates_log, cartanTorusCoordinates_log]
  rw [← Real.exp_add]
  simp [cartanCoordinates]
  ring

theorem cartanTorusCoordinates_cartanCoordinates_third
    (u v : ℝ) :
    cartanTorusCoordinates (cartanCoordinates u v) 2 =
      (cartanTorusCoordinates (cartanCoordinates u v) 0 *
        cartanTorusCoordinates (cartanCoordinates u v) 1)⁻¹ := by
  have hprod := cartanTorusCoordinates_cartanCoordinates_product_eq_one u v
  rw [Fin.prod_univ_three] at hprod
  have h0 := cartanTorusCoordinates_pos (cartanCoordinates u v) 0
  have h1 := cartanTorusCoordinates_pos (cartanCoordinates u v) 1
  have h2 := cartanTorusCoordinates_pos (cartanCoordinates u v) 2
  field_simp [ne_of_gt h0, ne_of_gt h1, ne_of_gt h2] at hprod ⊢
  nlinarith

end InfoGeometry.Canonical
