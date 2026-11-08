import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Abel

open BigOperators Finset

namespace InfoGeometry

/-! ### 1. Superspace Structure and Derivation Axioms -/

/-- Abstract coordinate superalgebra for 4D N=1 superspace.
    S is an associative ring (non-commutative due to Grassmann coordinates). -/
structure Superspace (S : Type*) [Ring S] where
  -- Coordinates
  x : Fin 4 → S
  theta : Fin 2 → S
  thetaBar : Fin 2 → S
  -- Imaginary unit and Pauli 4-vector matrices
  I : S
  sigma : Fin 4 → Fin 2 → Fin 2 → S
  -- Centrality: I and Pauli coefficients commute with all elements
  I_comm : ∀ s, I * s = s * I
  sigma_comm : ∀ μ α β s, sigma μ α β * s = s * sigma μ α β
  -- Derivations: spacetime derivative ∂_ν and odd spinor derivative ∂̄_α̇
  del_x : Fin 4 → S → S
  del_thetaBar : Fin 2 → S → S
  -- Linearity of ∂_ν
  del_x_add : ∀ ν a b, del_x ν (a + b) = del_x ν a + del_x ν b
  del_x_I_mul : ∀ ν a, del_x ν (I * a) = I * del_x ν a
  del_x_sigma_mul : ∀ ν μ α β a, del_x ν (sigma μ α β * a) = sigma μ α β * del_x ν a
  del_x_sum_Fin2 : ∀ ν (f : Fin 2 → S), del_x ν (∑ i, f i) = ∑ i, del_x ν (f i)
  -- Evaluation of ∂_ν on coordinates
  del_x_coord : ∀ ν μ, del_x ν (x μ) = if ν = μ then 1 else 0
  del_x_theta : ∀ ν α, del_x ν (theta α) = 0
  del_x_fermion : ∀ ν α β, del_x ν (theta α * thetaBar β) = 0
  -- Linearity of ∂̄_α̇
  del_thetaBar_add : ∀ α a b, del_thetaBar α (a + b) = del_thetaBar α a + del_thetaBar α b
  del_thetaBar_I_mul : ∀ α a, del_thetaBar α (I * a) = I * del_thetaBar α a
  del_thetaBar_sigma_mul : ∀ α μ β γ a, del_thetaBar α (sigma μ β γ * a) = sigma μ β γ * del_thetaBar α a
  del_thetaBar_sum_Fin2 : ∀ α (f : Fin 2 → S), del_thetaBar α (∑ i, f i) = ∑ i, del_thetaBar α (f i)
  -- Evaluation of ∂̄_α̇ on coordinates:
  -- ∂̄_α̇ (x^μ) = 0
  del_thetaBar_coord : ∀ α μ, del_thetaBar α (x μ) = 0
  del_thetaBar_theta : ∀ α β, del_thetaBar α (theta β) = 0
  -- Graded Leibniz sign: ∂̄_α̇ (θ^β θ̄^γ) = - θ^β δ_α̇^γ
  del_thetaBar_fermion : ∀ α β γ, del_thetaBar α (theta β * thetaBar γ) =
    if γ = α then - theta β else 0

namespace Superspace

variable {S : Type*} [Ring S] (ss : Superspace S)

/-! ### 2. The Chiral Coordinate and SUSY Covariant Derivative -/

/-- The supersymmetric chiral coordinate: y^μ = x^μ + i θ σ^μ θ̄. -/
def y (μ : Fin 4) : S :=
  ss.x μ + ss.I * ∑ β : Fin 2, ∑ γ : Fin 2, ss.sigma μ β γ * (ss.theta β * ss.thetaBar γ)

/-- The SUSY covariant derivative: D̄_α̇ = - ∂̄_α̇ - i ∑_β θ^β ∑_ν σ^ν_{β α̇} ∂_ν. -/
def DBar (α : Fin 2) (f : S) : S :=
  - ss.del_thetaBar α f - ss.I * ∑ β : Fin 2, ss.theta β * ∑ ν : Fin 4, ss.sigma ν β α * ss.del_x ν f

/-! ### 3. Intermediate Evaluation Lemmas -/

/-- Action of spacetime derivative ∂_ν on chiral coordinate y^μ:
    ∂_ν (y^μ) = δ_ν^μ. -/
theorem del_x_y (μ ν : Fin 4) :
    ss.del_x ν (ss.y μ) = if ν = μ then 1 else 0 := by
  dsimp [y]
  rw [ss.del_x_add, ss.del_x_coord]
  rw [ss.del_x_I_mul, ss.del_x_sum_Fin2]
  have h_fermion_vanish : (∑ i : Fin 2, ss.del_x ν (∑ γ : Fin 2, ss.sigma μ i γ * (ss.theta i * ss.thetaBar γ))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ss.del_x_sum_Fin2]
    have h_inner : (∑ γ : Fin 2, ss.del_x ν (ss.sigma μ i γ * (ss.theta i * ss.thetaBar γ))) = 0 := by
      apply Finset.sum_eq_zero
      intro γ _
      rw [ss.del_x_sigma_mul, ss.del_x_fermion, mul_zero]
    exact h_inner
  rw [h_fermion_vanish, mul_zero, add_zero]

/-- Action of odd derivative ∂̄_α̇ on chiral coordinate y^μ:
    ∂̄_α̇ (y^μ) = - i ∑_β θ^β σ^μ_{β α̇}. -/
theorem del_thetaBar_y (α : Fin 2) (μ : Fin 4) :
    ss.del_thetaBar α (ss.y μ) = - (ss.I * ∑ β : Fin 2, ss.theta β * ss.sigma μ β α) := by
  dsimp [y]
  rw [ss.del_thetaBar_add, ss.del_thetaBar_coord, zero_add]
  rw [ss.del_thetaBar_I_mul, ss.del_thetaBar_sum_Fin2]
  have h_inner_eval : ∀ β : Fin 2,
      ss.del_thetaBar α (∑ γ : Fin 2, ss.sigma μ β γ * (ss.theta β * ss.thetaBar γ)) =
      - (ss.theta β * ss.sigma μ β α) := by
    intro β
    rw [ss.del_thetaBar_sum_Fin2]
    have h_term : (∑ γ : Fin 2, ss.del_thetaBar α (ss.sigma μ β γ * (ss.theta β * ss.thetaBar γ))) =
        ∑ γ : Fin 2, if γ = α then ss.sigma μ β γ * (- ss.theta β) else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [ss.del_thetaBar_sigma_mul, ss.del_thetaBar_fermion]
      split_ifs with h
      · rfl
      · rw [mul_zero]
    rw [h_term]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_neg, ss.sigma_comm]
  have h_sum : (∑ β : Fin 2, ss.del_thetaBar α (∑ γ : Fin 2, ss.sigma μ β γ * (ss.theta β * ss.thetaBar γ))) =
      ∑ β : Fin 2, - (ss.theta β * ss.sigma μ β α) := by
    apply Finset.sum_congr rfl
    intro β _
    exact h_inner_eval β
  rw [h_sum, Finset.sum_neg_distrib, mul_neg]

/-! ### 4. Main Invariance Theorem -/

/-- **Theorem (Chiral Superspace Invariance):**
    The chiral coordinate y^μ is strictly annihilated by the SUSY covariant derivative D̄_α̇:
        D̄_α̇ (y^μ) = 0. -/
theorem DBar_y (α : Fin 2) (μ : Fin 4) :
    ss.DBar α (ss.y μ) = 0 := by
  dsimp [DBar]
  rw [del_thetaBar_y]
  simp_rw [ss.del_x_y μ]
  have h_spacetime_sum : ∀ β : Fin 2,
      (∑ ν : Fin 4, ss.sigma ν β α * if ν = μ then 1 else 0) = ss.sigma μ β α := by
    intro β
    have h_ite : (∑ ν : Fin 4, ss.sigma ν β α * if ν = μ then (1 : S) else 0) =
        ∑ ν : Fin 4, if ν = μ then ss.sigma ν β α else 0 := by
      apply Finset.sum_congr rfl
      intro ν _
      split_ifs with h
      · rw [mul_one]
      · rw [mul_zero]
    rw [h_ite]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h_rewrite_second : (ss.I * ∑ β : Fin 2, ss.theta β * ∑ ν : Fin 4, ss.sigma ν β α * if ν = μ then 1 else 0) =
      ss.I * ∑ β : Fin 2, ss.theta β * ss.sigma μ β α := by
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    rw [h_spacetime_sum β]
  rw [h_rewrite_second]
  rw [neg_neg, sub_self]

/-- Additivity of the SUSY covariant derivative D̄_α̇. -/
theorem DBar_add (α : Fin 2) (a b : S) :
    ss.DBar α (a + b) = ss.DBar α a + ss.DBar α b := by
  dsimp [DBar]
  rw [ss.del_thetaBar_add]
  have h_del_x : ∀ ν, ss.del_x ν (a + b) = ss.del_x ν a + ss.del_x ν b := fun ν => ss.del_x_add ν a b
  simp_rw [h_del_x]
  have h_sigma : ∀ β ν, ss.sigma ν β α * (ss.del_x ν a + ss.del_x ν b) =
      ss.sigma ν β α * ss.del_x ν a + ss.sigma ν β α * ss.del_x ν b := by
    intro β ν
    rw [mul_add]
  simp_rw [h_sigma]
  simp_rw [Finset.sum_add_distrib]
  have h_theta : ∀ β, ss.theta β * (∑ ν : Fin 4, ss.sigma ν β α * ss.del_x ν a +
      ∑ ν : Fin 4, ss.sigma ν β α * ss.del_x ν b) =
      ss.theta β * (∑ ν : Fin 4, ss.sigma ν β α * ss.del_x ν a) +
      ss.theta β * (∑ ν : Fin 4, ss.sigma ν β α * ss.del_x ν b) := by
    intro β
    rw [mul_add]
  simp_rw [h_theta]
  rw [Finset.sum_add_distrib, mul_add]
  abel

/-- Sum distribution for D̄_α̇ over 2-component spinor indices. -/
theorem DBar_sum_Fin2 (α : Fin 2) (f : Fin 2 → S) :
    ss.DBar α (∑ i, f i) = ∑ i, ss.DBar α (f i) := by
  simp only [Fin.sum_univ_two, ss.DBar_add]

/-- Sum distribution for D̄_α̇ over 4-component spacetime indices. -/
theorem DBar_sum_Fin4 (α : Fin 2) (f : Fin 4 → S) :
    ss.DBar α (∑ i, f i) = ∑ i, ss.DBar α (f i) := by
  simp only [Fin.sum_univ_four, ss.DBar_add]

end Superspace

end InfoGeometry
