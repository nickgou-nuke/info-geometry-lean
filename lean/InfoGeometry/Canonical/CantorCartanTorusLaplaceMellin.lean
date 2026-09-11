import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open scoped BigOperators

/-!
# Trace-zero Cartan torus and its Laplace/Mellin kernel

The finite content here is the determinant-one three-weight torus.  No
three-dimensional spectral parameter is retained: the additive parameter is
the trace-zero plane, and the multiplicative parameter is its positive
exponential image.
-/

def cartanTraceZero (t : Fin 3 → ℝ) : Prop :=
  ∑ i : Fin 3, t i = 0

def cartanCoordinates (u v : ℝ) : Fin 3 → ℝ :=
  ![u, v, -u - v]

theorem cartanCoordinates_traceZero (u v : ℝ) :
    cartanTraceZero (cartanCoordinates u v) := by
  simp [cartanTraceZero, cartanCoordinates, Fin.sum_univ_three]

theorem cartanTraceZero_add
    {s t : Fin 3 → ℝ}
    (hs : cartanTraceZero s) (ht : cartanTraceZero t) :
    cartanTraceZero (fun i => s i + t i) := by
  unfold cartanTraceZero at hs ht ⊢
  change (∑ i : Fin 3, (s i + t i)) = 0
  rw [Finset.sum_add_distrib, hs, ht, add_zero]

theorem cartanTraceZero_neg
    {t : Fin 3 → ℝ}
    (ht : cartanTraceZero t) :
    cartanTraceZero (fun i => -t i) := by
  unfold cartanTraceZero at ht ⊢
  change (∑ i : Fin 3, (-t i)) = 0
  rw [Finset.sum_neg_distrib, ht, neg_zero]

theorem cartanCoordinates_eq_iff {u v u' v' : ℝ} :
    cartanCoordinates u v = cartanCoordinates u' v' ↔
      u = u' ∧ v = v' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem exists_cartanCoordinates_of_traceZero
    {t : Fin 3 → ℝ} (ht : cartanTraceZero t) :
    ∃ u v : ℝ, cartanCoordinates u v = t := by
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [cartanTraceZero, Fin.sum_univ_three] using ht
  refine ⟨t 0, t 1, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp [cartanCoordinates]
    linarith

theorem cartanTraceZero_iff_exists_coordinates (t : Fin 3 → ℝ) :
    cartanTraceZero t ↔ ∃ u v : ℝ, cartanCoordinates u v = t := by
  constructor
  · exact exists_cartanCoordinates_of_traceZero
  · rintro ⟨u, v, rfl⟩
    exact cartanCoordinates_traceZero u v

noncomputable def cartanTorusCoordinates (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => Real.exp (2 * t i)

theorem cartanTorusCoordinates_pos (t : Fin 3 → ℝ) (i : Fin 3) :
    0 < cartanTorusCoordinates t i := by
  exact Real.exp_pos _

theorem cartanTorusCoordinates_log (t : Fin 3 → ℝ) (i : Fin 3) :
    Real.log (cartanTorusCoordinates t i) = 2 * t i := by
  simp [cartanTorusCoordinates]

theorem cartanTorusCoordinates_add (s t : Fin 3 → ℝ) (i : Fin 3) :
    cartanTorusCoordinates (fun j => s j + t j) i =
      cartanTorusCoordinates s i * cartanTorusCoordinates t i := by
  change Real.exp (2 * (s i + t i)) =
    Real.exp (2 * s i) * Real.exp (2 * t i)
  rw [show 2 * (s i + t i) = 2 * s i + 2 * t i by ring, Real.exp_add]

theorem cartanTorusCoordinates_neg (t : Fin 3 → ℝ) (i : Fin 3) :
    cartanTorusCoordinates (fun j => -t j) i =
      (cartanTorusCoordinates t i)⁻¹ := by
  change Real.exp (2 * (-t i)) = (Real.exp (2 * t i))⁻¹
  rw [show 2 * (-t i) = -(2 * t i) by ring, Real.exp_neg]

theorem cartanTorusCoordinates_zero (i : Fin 3) :
    cartanTorusCoordinates (fun _ => 0) i = 1 := by
  simp [cartanTorusCoordinates]

theorem cartanTorusCoordinates_sub
    (s t : Fin 3 → ℝ) (i : Fin 3) :
    cartanTorusCoordinates (fun j => s j - t j) i =
      cartanTorusCoordinates s i * (cartanTorusCoordinates t i)⁻¹ := by
  change Real.exp (2 * (s i - t i)) =
    Real.exp (2 * s i) * (Real.exp (2 * t i))⁻¹
  rw [show 2 * (s i - t i) = 2 * s i - 2 * t i by ring,
    Real.exp_sub]
  simp [div_eq_mul_inv]

theorem cartanTorusCoordinates_add_function
    (s t : Fin 3 → ℝ) :
    cartanTorusCoordinates (fun j => s j + t j) =
      fun i => cartanTorusCoordinates s i * cartanTorusCoordinates t i := by
  funext i
  exact cartanTorusCoordinates_add s t i

theorem cartanTorusCoordinates_neg_function
    (t : Fin 3 → ℝ) :
    cartanTorusCoordinates (fun j => -t j) =
      fun i => (cartanTorusCoordinates t i)⁻¹ := by
  funext i
  exact cartanTorusCoordinates_neg t i

theorem cartanTorusCoordinates_sub_function
    (s t : Fin 3 → ℝ) :
    cartanTorusCoordinates (fun j => s j - t j) =
      fun i => cartanTorusCoordinates s i *
        (cartanTorusCoordinates t i)⁻¹ := by
  funext i
  exact cartanTorusCoordinates_sub s t i

theorem cartanTorusCoordinates_injective :
    Function.Injective cartanTorusCoordinates := by
  intro s t h
  funext i
  have hi' : 2 * s i = 2 * t i := by
    simpa [cartanTorusCoordinates] using
      congrArg Real.log (congrFun h i)
  calc
    s i = (2 * s i) / 2 := by ring_nf
    _ = (2 * t i) / 2 := by rw [hi']
    _ = t i := by ring_nf

theorem cartanTorusCoordinates_product_eq_one
    {t : Fin 3 → ℝ} (ht : cartanTraceZero t) :
    ∏ i : Fin 3, cartanTorusCoordinates t i = 1 := by
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [cartanTraceZero, Fin.sum_univ_three] using ht
  calc
    ∏ i : Fin 3, cartanTorusCoordinates t i =
        Real.exp (∑ i : Fin 3, 2 * t i) := by
          rw [Fin.prod_univ_three]
          simp only [cartanTorusCoordinates]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          simp only [Fin.sum_univ_three]
    _ = Real.exp 0 := by
      congr 1
      simp only [Fin.sum_univ_three]
      linarith
    _ = 1 := Real.exp_zero

theorem cartanTorusCoordinates_log_sum_eq_zero
    {t : Fin 3 → ℝ} (ht : cartanTraceZero t) :
    ∑ i : Fin 3, Real.log (cartanTorusCoordinates t i) = 0 := by
  rw [Fin.sum_univ_three]
  rw [cartanTorusCoordinates_log, cartanTorusCoordinates_log,
    cartanTorusCoordinates_log]
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [cartanTraceZero, Fin.sum_univ_three] using ht
  linarith

theorem hasDerivAt_cartanTorusCoordinate
    (t : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun x : ℝ => Real.exp (2 * x))
      (2 * cartanTorusCoordinates t i) (t i) := by
  simpa [cartanTorusCoordinates, Function.comp_def, mul_comm,
    mul_left_comm, mul_assoc] using
    ((Real.hasDerivAt_exp (2 * t i)).comp (t i)
      ((hasDerivAt_id (t i)).const_mul 2))

theorem hasDerivAt_log_cartanTorusCoordinate
    (t : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun x : ℝ => Real.log (Real.exp (2 * x)))
      2 (t i) := by
  have hfun : (fun x : ℝ => Real.log (Real.exp (2 * x))) =
      (fun x : ℝ => 2 * x) := by
    funext x
    simp
  rw [hfun]
  simpa using (hasDerivAt_id (t i)).const_mul 2

theorem cartanTorusCoordinates_unique
    {t s : Fin 3 → ℝ}
    (h : cartanTorusCoordinates t = cartanTorusCoordinates s) :
    t = s := by
  exact cartanTorusCoordinates_injective h

theorem cartanCoordinates_third (u v : ℝ) :
    cartanCoordinates u v 2 = -u - v := by
  rfl

theorem cartanTorusCoordinates_cartanCoordinates_explicit
    (u v : ℝ) :
    cartanTorusCoordinates (cartanCoordinates u v) 0 = Real.exp (2 * u) ∧
      cartanTorusCoordinates (cartanCoordinates u v) 1 = Real.exp (2 * v) ∧
      cartanTorusCoordinates (cartanCoordinates u v) 2 =
        Real.exp (-2 * (u + v)) := by
  simp [cartanTorusCoordinates, cartanCoordinates]
  ring

theorem exists_cartanTorusCoordinates_of_pos_product_eq_one
    {z : Fin 3 → ℝ}
    (hz : ∀ i, 0 < z i)
    (hprod : ∏ i : Fin 3, z i = 1) :
    ∃ t : Fin 3 → ℝ,
      cartanTraceZero t ∧ cartanTorusCoordinates t = z := by
  have h0 : 0 < z 0 := hz 0
  have h1 : 0 < z 1 := hz 1
  have h2 : 0 < z 2 := hz 2
  have hprod' : z 0 * z 1 * z 2 = 1 := by
    simpa [Fin.prod_univ_three] using hprod
  have hlog : Real.log (z 0) + Real.log (z 1) + Real.log (z 2) = 0 := by
    rw [← Real.log_mul (ne_of_gt h0) (ne_of_gt h1)]
    rw [← Real.log_mul
      (mul_ne_zero (ne_of_gt h0) (ne_of_gt h1)) (ne_of_gt h2)]
    rw [hprod', Real.log_one]
  refine ⟨fun i => Real.log (z i) / 2, ?_, ?_⟩
  · rw [cartanTraceZero, Fin.sum_univ_three]
    nlinarith [hlog]
  · funext i
    rw [cartanTorusCoordinates]
    convert Real.exp_log (hz i) using 1
    ring_nf

theorem cartanTorusCoordinates_range_iff (z : Fin 3 → ℝ) :
    (∃ t : Fin 3 → ℝ,
      cartanTraceZero t ∧ cartanTorusCoordinates t = z) ↔
      (∀ i, 0 < z i) ∧ ∏ i : Fin 3, z i = 1 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨cartanTorusCoordinates_pos t, cartanTorusCoordinates_product_eq_one ht⟩
  · rintro ⟨hz, hprod⟩
    exact exists_cartanTorusCoordinates_of_pos_product_eq_one hz hprod

theorem cartanTorusCoordinates_bijOn_traceZero :
    Set.BijOn cartanTorusCoordinates
      {t : Fin 3 → ℝ | cartanTraceZero t}
      {z : Fin 3 → ℝ | (∀ i, 0 < z i) ∧ ∏ i : Fin 3, z i = 1} := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact ⟨cartanTorusCoordinates_pos t,
      cartanTorusCoordinates_product_eq_one ht⟩
  · intro s hs t ht hst
    exact cartanTorusCoordinates_injective hst
  · intro z hz
    exact exists_cartanTorusCoordinates_of_pos_product_eq_one hz.1 hz.2

theorem cartanTorusCoordinates_cartanCoordinates_inverse_product
    (u v : ℝ) :
    cartanTorusCoordinates (cartanCoordinates u v) 2 =
      (cartanTorusCoordinates (cartanCoordinates u v) 0 *
        cartanTorusCoordinates (cartanCoordinates u v) 1)⁻¹ := by
  simp [cartanTorusCoordinates, cartanCoordinates]
  rw [← mul_inv_rev]
  rw [← Real.exp_add]
  rw [← Real.exp_neg]
  congr 1
  ring

noncomputable def cartanLaplaceKernel (s t : Fin 3 → ℝ) : ℝ :=
  Real.exp (-(∑ i : Fin 3, s i * t i))

noncomputable def cartanLogarithmicMellinKernel (s t : Fin 3 → ℝ) : ℝ :=
  Real.exp (∑ i : Fin 3,
    (-s i / 2) * Real.log (cartanTorusCoordinates t i))

theorem cartanLaplace_eq_logarithmicMellin (s t : Fin 3 → ℝ) :
    cartanLogarithmicMellinKernel s t = cartanLaplaceKernel s t := by
  unfold cartanLogarithmicMellinKernel cartanLaplaceKernel
  simp only [cartanTorusCoordinates, Real.log_exp]
  simp only [Fin.sum_univ_three]
  ring_nf

theorem cartanLaplaceKernel_eq_mellin_character_product
    (s t : Fin 3 → ℝ) :
    cartanLaplaceKernel s t =
      ∏ i : Fin 3,
        Real.exp ((-s i / 2) * Real.log (cartanTorusCoordinates t i)) := by
  unfold cartanLaplaceKernel cartanTorusCoordinates
  rw [Fin.prod_univ_three]
  simp only [Real.log_exp]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Fin.sum_univ_three]
  ring

theorem cartanLaplaceKernel_traceZero_mellin_character_product
    (s t : Fin 3 → ℝ) :
    cartanLaplaceKernel s t =
      (cartanTorusCoordinates t 0) ^ (-s 0 / 2 : ℝ) *
        (cartanTorusCoordinates t 1) ^ (-s 1 / 2 : ℝ) *
        (cartanTorusCoordinates t 2) ^ (-s 2 / 2 : ℝ) := by
  rw [cartanLaplaceKernel_eq_mellin_character_product]
  rw [Fin.prod_univ_three]
  simp only [Real.rpow_def_of_pos (cartanTorusCoordinates_pos t 0),
    Real.rpow_def_of_pos (cartanTorusCoordinates_pos t 1),
    Real.rpow_def_of_pos (cartanTorusCoordinates_pos t 2)]
  congr 1 <;> ring_nf

theorem cartanLaplaceKernel_additive_character
    (s t u : Fin 3 → ℝ) :
    cartanLaplaceKernel s (fun i => t i + u i) =
      cartanLaplaceKernel s t * cartanLaplaceKernel s u := by
  unfold cartanLaplaceKernel
  rw [← Real.exp_add]
  congr 1
  simp only [Fin.sum_univ_three]
  ring

theorem cartanLaplaceKernel_neg
    (s t : Fin 3 → ℝ) :
    cartanLaplaceKernel s (fun i => -t i) =
      (cartanLaplaceKernel s t)⁻¹ := by
  unfold cartanLaplaceKernel
  rw [show -(∑ i : Fin 3, s i * -t i) =
      ∑ i : Fin 3, s i * t i by
    simp only [Fin.sum_univ_three]
    ring]
  rw [← Real.exp_neg]
  congr 1
  ring

theorem cartanLogarithmicMellinKernel_additive_character
    (s t u : Fin 3 → ℝ) :
    cartanLogarithmicMellinKernel s (fun i => t i + u i) =
      cartanLogarithmicMellinKernel s t *
        cartanLogarithmicMellinKernel s u := by
  rw [cartanLaplace_eq_logarithmicMellin,
    cartanLaplace_eq_logarithmicMellin,
    cartanLaplace_eq_logarithmicMellin,
    cartanLaplaceKernel_additive_character]

theorem cartanLogarithmicMellinKernel_neg
    (s t : Fin 3 → ℝ) :
    cartanLogarithmicMellinKernel s (fun i => -t i) =
      (cartanLogarithmicMellinKernel s t)⁻¹ := by
  rw [cartanLaplace_eq_logarithmicMellin,
    cartanLaplace_eq_logarithmicMellin,
    cartanLaplaceKernel_neg]

theorem cartanLaplaceKernel_coordinates
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) := by
  unfold cartanLaplaceKernel
  have h0 : cartanCoordinates u v 0 = u := by rfl
  have h1 : cartanCoordinates u v 1 = v := by rfl
  have h2 : cartanCoordinates u v 2 = -u - v :=
    cartanCoordinates_third u v
  rw [Fin.sum_univ_three, h0, h1, h2]
  congr 1
  ring

theorem cartanLogarithmicMellinKernel_coordinates
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLogarithmicMellinKernel s (cartanCoordinates u v) =
      Real.exp (-((s 0 - s 2) * u + (s 1 - s 2) * v)) := by
  rw [cartanLaplace_eq_logarithmicMellin,
    cartanLaplaceKernel_coordinates]

theorem cartanLaplaceKernel_traceZero_coordinates
    (s t : Fin 3 → ℝ)
    (ht : cartanTraceZero t) :
    cartanLaplaceKernel s t =
      Real.exp (-((s 0 - s 2) * t 0 + (s 1 - s 2) * t 1)) := by
  obtain ⟨u, v, h⟩ := exists_cartanCoordinates_of_traceZero ht
  have h0 : t 0 = u := by
    simpa [cartanCoordinates] using (congrFun h 0).symm
  have h1 : t 1 = v := by
    simpa [cartanCoordinates] using (congrFun h 1).symm
  rw [h0, h1]
  rw [← h]
  exact cartanLaplaceKernel_coordinates s u v

theorem cartanLogarithmicMellinKernel_traceZero_coordinates
    (s t : Fin 3 → ℝ)
    (ht : cartanTraceZero t) :
    cartanLogarithmicMellinKernel s t =
      Real.exp (-((s 0 - s 2) * t 0 + (s 1 - s 2) * t 1)) := by
  rw [cartanLaplace_eq_logarithmicMellin,
    cartanLaplaceKernel_traceZero_coordinates s t ht]

theorem cartanLaplaceKernel_traceZero_spectral_differences
    (s t : Fin 3 → ℝ)
    (ht : cartanTraceZero t) :
    cartanLaplaceKernel s t =
      Real.exp (-((s 0 - s 2) * t 0 + (s 1 - s 2) * t 1)) := by
  exact cartanLaplaceKernel_traceZero_coordinates s t ht

theorem cartanLaplaceKernel_traceZero_spectral_shift
    (s t : Fin 3 → ℝ) (c : ℝ)
    (ht : cartanTraceZero t) :
    cartanLaplaceKernel (fun i => s i + c) t =
      cartanLaplaceKernel s t := by
  unfold cartanLaplaceKernel
  congr 1
  simp only [Fin.sum_univ_three]
  unfold cartanTraceZero at ht
  simp only [Fin.sum_univ_three] at ht
  ring_nf
  linear_combination -c * ht

theorem cartanLaplaceKernel_cartanCoordinates_rpow
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      (Real.exp (2 * u)) ^ (-(s 0 - s 2) / 2 : ℝ) *
        (Real.exp (2 * v)) ^ (-(s 1 - s 2) / 2 : ℝ) := by
  rw [cartanLaplaceKernel_coordinates]
  rw [Real.rpow_def_of_pos (Real.exp_pos (2 * u)),
    Real.rpow_def_of_pos (Real.exp_pos (2 * v))]
  simp only [Real.log_exp]
  rw [← Real.exp_add]
  congr 1
  ring

theorem cartanTorusCoordinates_cartanCoordinates_product_eq_one_explicit
    (u v : ℝ) :
    ∏ i : Fin 3, cartanTorusCoordinates (cartanCoordinates u v) i = 1 := by
  exact cartanTorusCoordinates_product_eq_one
    (cartanCoordinates_traceZero u v)

theorem cartanLaplaceKernel_cartanCoordinates_mellin_character
    (s : Fin 3 → ℝ) (u v : ℝ) :
    cartanLaplaceKernel s (cartanCoordinates u v) =
      (cartanTorusCoordinates (cartanCoordinates u v) 0) ^
          (-(s 0 - s 2) / 2 : ℝ) *
        (cartanTorusCoordinates (cartanCoordinates u v) 1) ^
          (-(s 1 - s 2) / 2 : ℝ) := by
  rcases cartanTorusCoordinates_cartanCoordinates_explicit u v with ⟨h0, h1, h2⟩
  rw [h0, h1]
  exact cartanLaplaceKernel_cartanCoordinates_rpow s u v

end InfoGeometry.Canonical
