import InfoGeometry.Dynamics.MoebiusTrifactorFlows

/-!
# Hypercomplex one-parameter flows

The three KAN model flows are packaged as group-valued algebraic readouts.
This is deliberately weaker than an analytic Laplace transform and stronger
than a bare function: a real parameter acts through the unit group of the
ambient algebra.
-/

namespace InfoGeometry.Dynamics.HypercomplexOneParameterFlows

open InfoGeometry.Dynamics.MoebiusFlow

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- A purely algebraic real one-parameter flow. -/
structure RealOneParameterFlow where
  flow : Multiplicative ℝ →* Aˣ

namespace RealOneParameterFlow

variable (F : RealOneParameterFlow (A := A))

@[simp] theorem flow_one : F.flow 1 = 1 := by
  exact F.flow.map_one

theorem flow_mul (s t : ℝ) :
    F.flow (Multiplicative.ofAdd (s + t)) =
      F.flow (Multiplicative.ofAdd s) * F.flow (Multiplicative.ofAdd t) := by
  exact F.flow.map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

end RealOneParameterFlow

private def unitOfFlow
    (f : ℝ → A) (hf0 : f 0 = 1)
    (hfmul : ∀ s t : ℝ, f s * f t = f (s + t))
    (hinv : ∀ t : ℝ, f (-t) * f t = 1) (t : ℝ) : Aˣ where
  val := f t
  inv := f (-t)
  val_inv := by
    rw [hfmul, add_neg_cancel, hf0]
  inv_val := hinv t

private def flowToUnits
    (f : ℝ → A) (hf0 : f 0 = 1)
    (hfmul : ∀ s t : ℝ, f s * f t = f (s + t))
    (hinv : ∀ t : ℝ, f (-t) * f t = 1) :
    Multiplicative ℝ →* Aˣ where
  toFun t := unitOfFlow f hf0 hfmul hinv t
  map_one' := by
    apply Units.ext
    exact hf0
  map_mul' s t := by
    apply Units.ext
    exact (hfmul s t).symm

def ellipticFlow_of_sq_eq_neg_one (J : A) (hJ : J * J = -1) :
    RealOneParameterFlow (A := A) :=
  ⟨flowToUnits (ellipticFlow J) (ellipticFlow_zero J)
      (ellipticFlow_mul J hJ)
      (ellipticFlow_inv J hJ)⟩

def hyperbolicFlow_of_sq_eq_one (H : A) (hH : H * H = 1) :
    RealOneParameterFlow (A := A) :=
  ⟨flowToUnits (hyperbolicFlow H) (hyperbolicFlow_zero H)
      (hyperbolicFlow_mul H hH)
      (hyperbolicFlow_inv H hH)⟩

def parabolicFlow_of_sq_eq_zero (N : A) (hN : N * N = 0) :
    RealOneParameterFlow (A := A) :=
  ⟨flowToUnits (parabolicFlow N) (parabolicFlow_zero N)
      (parabolicFlow_mul N hN)
      (parabolicFlow_inv N hN)⟩

@[simp] theorem ellipticFlow_of_sq_eq_neg_one_apply
    (J : A) (hJ : J * J = -1) (t : ℝ) :
    ((ellipticFlow_of_sq_eq_neg_one J hJ).flow (Multiplicative.ofAdd t) : A) =
      ellipticFlow J t := rfl

@[simp] theorem hyperbolicFlow_of_sq_eq_one_apply
    (H : A) (hH : H * H = 1) (t : ℝ) :
    ((hyperbolicFlow_of_sq_eq_one H hH).flow (Multiplicative.ofAdd t) : A) =
      hyperbolicFlow H t := rfl

@[simp] theorem parabolicFlow_of_sq_eq_zero_apply
    (N : A) (hN : N * N = 0) (t : ℝ) :
    ((parabolicFlow_of_sq_eq_zero N hN).flow (Multiplicative.ofAdd t) : A) =
      parabolicFlow N t := rfl

end
end InfoGeometry.Dynamics.HypercomplexOneParameterFlows
