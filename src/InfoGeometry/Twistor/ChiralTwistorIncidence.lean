import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Superspace

open BigOperators Finset

namespace InfoGeometry.Twistor

variable {S : Type*} [Ring S] (ss : Superspace S)

/-! ### 1. Supertwistor Coordinates from Chiral Shift -/

/-- A Supertwistor Z^I = (λ_α, μ^adot, χ) where μ is determined by the
    chiral incidence relation μ^adot = y^{α adot} λ_α and χ = θ^α λ_α. -/
structure Supertwistor where
  lambda : Fin 2 → S
  -- Centrality assumption: reference spinor components commute with coordinates
  lambda_comm : ∀ α s, lambda α * s = s * lambda α
  -- Derivation product rule for constant reference spinor
  del_x_mul_lambda : ∀ ν a α, ss.del_x ν (a * lambda α) = ss.del_x ν a * lambda α
  del_thetaBar_mul_lambda : ∀ adot a α, ss.del_thetaBar adot (a * lambda α) = ss.del_thetaBar adot a * lambda α

variable (Z : Supertwistor ss)

/-- The fermionic supertwistor coordinate: χ = ∑_α θ^α λ_α. -/
def chi : S :=
  ∑ α : Fin 2, ss.theta α * Z.lambda α

/-- The chiral twistor incidence relation:
    μ^adot = ∑_ν σ^ν_{β adot} y_ν λ^β (represented via the chiral coordinate y). -/
def mu (adot : Fin 2) : S :=
  ∑ β : Fin 2, ∑ ν : Fin 4, ss.sigma ν β adot * (ss.y ν * Z.lambda β)

/-! ### 2. Holomorphic Invariance of Supertwistor Space -/

/-- The covariant derivative annihilates each bosonic incidence summand.
    This follows from the two derivative actions on the chiral coordinate and
    the constant-spinor product rule; it is not an extra field of `Supertwistor`. -/
theorem DBar_incidence_term (adot β bdot : Fin 2) (μ ν : Fin 4) :
    ss.DBar adot (ss.sigma μ β bdot * (ss.y ν * Z.lambda β)) = 0 := by
  have hspatial (γ : Fin 2) :
      (∑ ρ : Fin 4,
        ss.sigma ρ γ adot *
          (ss.sigma μ β bdot * ((if ρ = ν then (1 : S) else 0) * Z.lambda β))) =
        ss.sigma ν γ adot * (ss.sigma μ β bdot * Z.lambda β) := by
    calc
      _ = ∑ ρ : Fin 4,
          if ρ = ν then ss.sigma ρ γ adot *
            (ss.sigma μ β bdot * Z.lambda β) else 0 := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        by_cases h : ρ = ν <;> simp [h]
      _ = ss.sigma ν γ adot * (ss.sigma μ β bdot * Z.lambda β) := by
        simp [Finset.sum_ite_eq']
  unfold Superspace.DBar
  rw [ss.del_thetaBar_sigma_mul, Z.del_thetaBar_mul_lambda,
    ss.del_thetaBar_y]
  simp_rw [ss.del_x_sigma_mul, Z.del_x_mul_lambda, ss.del_x_y]
  simp_rw [hspatial]
  simp only [neg_mul, mul_neg, neg_neg]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply sub_eq_zero.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hsigma : ss.sigma μ β bdot * ss.theta γ =
      ss.theta γ * ss.sigma μ β bdot := ss.sigma_comm μ β bdot (ss.theta γ)
  have hpair : ss.sigma μ β bdot * ss.sigma ν γ adot =
      ss.sigma ν γ adot * ss.sigma μ β bdot :=
    ss.sigma_comm μ β bdot (ss.sigma ν γ adot)
  have hI_move (t : S) :
      ss.sigma μ β bdot * (ss.I * t) = ss.I * (ss.sigma μ β bdot * t) := by
    calc
      ss.sigma μ β bdot * (ss.I * t) =
          (ss.sigma μ β bdot * ss.I) * t := by rw [← mul_assoc]
      _ = (ss.I * ss.sigma μ β bdot) * t := by
        rw [(ss.I_comm (ss.sigma μ β bdot)).symm]
      _ = ss.I * (ss.sigma μ β bdot * t) := by rw [mul_assoc]
  have hsigma_move (t : S) :
      ss.sigma μ β bdot * (ss.theta γ * t) =
        ss.theta γ * (ss.sigma μ β bdot * t) := by
    calc
      ss.sigma μ β bdot * (ss.theta γ * t) =
          (ss.sigma μ β bdot * ss.theta γ) * t := by rw [← mul_assoc]
      _ = (ss.theta γ * ss.sigma μ β bdot) * t := by rw [hsigma]
      _ = ss.theta γ * (ss.sigma μ β bdot * t) := by rw [mul_assoc]
  have hpair_move (t : S) :
      ss.sigma μ β bdot * (ss.sigma ν γ adot * t) =
        ss.sigma ν γ adot * (ss.sigma μ β bdot * t) := by
    calc
      ss.sigma μ β bdot * (ss.sigma ν γ adot * t) =
          (ss.sigma μ β bdot * ss.sigma ν γ adot) * t := by rw [← mul_assoc]
      _ = (ss.sigma ν γ adot * ss.sigma μ β bdot) * t := by rw [hpair]
      _ = ss.sigma ν γ adot * (ss.sigma μ β bdot * t) := by rw [mul_assoc]
  calc
    ss.sigma μ β bdot *
        (ss.I * (ss.theta γ * ss.sigma ν γ adot) * Z.lambda β) =
        ss.I * (ss.sigma μ β bdot *
          (ss.theta γ * (ss.sigma ν γ adot * Z.lambda β))) := by
      simpa [mul_assoc] using
        hI_move (ss.theta γ * (ss.sigma ν γ adot * Z.lambda β))
    _ = ss.I * (ss.theta γ *
        (ss.sigma μ β bdot * (ss.sigma ν γ adot * Z.lambda β))) :=
      congrArg (fun t => ss.I * t)
        (hsigma_move (ss.sigma ν γ adot * Z.lambda β))
    _ = ss.I * (ss.theta γ *
        (ss.sigma ν γ adot * (ss.sigma μ β bdot * Z.lambda β))) :=
      congrArg (fun t => ss.I * (ss.theta γ * t)) (hpair_move (Z.lambda β))

theorem del_x_mu (bdot : Fin 2) (ν : Fin 4) :
    ss.del_x ν (mu ss Z bdot) =
      ∑ β : Fin 2, ss.sigma ν β bdot * Z.lambda β := by
  dsimp [mu]
  rw [ss.del_x_sum_Fin2]
  have h_inner : ∀ β : Fin 2,
      ss.del_x ν (∑ μ : Fin 4, ss.sigma μ β bdot * (ss.y μ * Z.lambda β)) =
      ss.sigma ν β bdot * Z.lambda β := by
    intro β
    have h_sum4 : ss.del_x ν (∑ μ : Fin 4, ss.sigma μ β bdot * (ss.y μ * Z.lambda β)) =
        ∑ μ : Fin 4, ss.sigma μ β bdot * (if ν = μ then (1 : S) else 0) * Z.lambda β := by
      have h1 : ss.del_x ν (∑ μ : Fin 4, ss.sigma μ β bdot * (ss.y μ * Z.lambda β)) =
          ∑ μ : Fin 4, ss.del_x ν (ss.sigma μ β bdot * (ss.y μ * Z.lambda β)) := by
        simp only [Fin.sum_univ_four, ss.del_x_add]
      rw [h1]
      apply Finset.sum_congr rfl
      intro μ _
      rw [ss.del_x_sigma_mul, Z.del_x_mul_lambda]
      simp_rw [ss.del_x_y]
      rw [mul_assoc]
    rw [h_sum4]
    have h_collapse : (∑ μ : Fin 4, ss.sigma μ β bdot * (if ν = μ then (1 : S) else 0) * Z.lambda β) =
        ss.sigma ν β bdot * Z.lambda β := by
      have h_ite : (∑ μ : Fin 4, ss.sigma μ β bdot * (if ν = μ then (1 : S) else 0) * Z.lambda β) =
          ∑ μ : Fin 4, if ν = μ then ss.sigma μ β bdot * Z.lambda β else 0 := by
        apply Finset.sum_congr rfl
        intro μ _
        split_ifs with h
        · rw [mul_one]
        · rw [mul_zero, zero_mul]
      rw [h_ite]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact h_collapse
  apply Finset.sum_congr rfl
  intro β _
  exact h_inner β

/-- The bosonic twistor coordinate μ^bdot is strictly chiral: D̄_adot (μ^bdot) = 0. -/
theorem DBar_mu (adot bdot : Fin 2) :
    ss.DBar adot (mu ss Z bdot) = 0 := by
  dsimp [mu]
  rw [ss.DBar_sum_Fin2]
  simp_rw [ss.DBar_sum_Fin4]
  apply Finset.sum_eq_zero
  intro β _
  apply Finset.sum_eq_zero
  intro ν _
  exact DBar_incidence_term ss Z adot β bdot ν ν

/-- The fermionic twistor coordinate χ is strictly chiral: D̄_adot (χ) = 0. -/
theorem DBar_chi (adot : Fin 2) :
    ss.DBar adot (chi ss Z) = 0 := by
  dsimp [chi]
  unfold Superspace.DBar
  have h_del_thetaBar : ss.del_thetaBar adot (∑ α : Fin 2, ss.theta α * Z.lambda α) = 0 := by
    rw [ss.del_thetaBar_sum_Fin2]
    apply Finset.sum_eq_zero
    intro α _
    rw [Z.del_thetaBar_mul_lambda, ss.del_thetaBar_theta]
    exact zero_mul _
  have h_del_x : ∀ ν : Fin 4, ss.del_x ν (∑ α : Fin 2, ss.theta α * Z.lambda α) = 0 := by
    intro ν
    rw [ss.del_x_sum_Fin2]
    apply Finset.sum_eq_zero
    intro α _
    rw [Z.del_x_mul_lambda, ss.del_x_theta]
    exact zero_mul _
  rw [h_del_thetaBar, neg_zero]
  have h_inner_zero : ∀ β : Fin 2, (∑ ν : Fin 4, ss.sigma ν β adot * ss.del_x ν (∑ α : Fin 2, ss.theta α * Z.lambda α)) = 0 := by
    intro β
    apply Finset.sum_eq_zero
    intro ν _
    rw [h_del_x ν, mul_zero]
  have h_outer_zero : (∑ β : Fin 2, ss.theta β * ∑ ν : Fin 4, ss.sigma ν β adot * ss.del_x ν (∑ α : Fin 2, ss.theta α * Z.lambda α)) = 0 := by
    apply Finset.sum_eq_zero
    intro β _
    rw [h_inner_zero β, mul_zero]
  rw [h_outer_zero, mul_zero, sub_zero]

/-! ### 3. Neutral Krein Form on Twistor Space -/

/-- The canonical neutral Krein form Σ(Z₁, Z₂) on twistor space (signature (2, 2)). -/
def twistorKreinForm (_Z1 Z2 : Supertwistor ss) (bar_mu1 bar_lambda1 : Fin 2 → S) : S :=
  (∑ adot : Fin 2, bar_lambda1 adot * mu ss Z2 adot) +
  (∑ α : Fin 2, bar_mu1 α * Z2.lambda α)

end InfoGeometry.Twistor
