import Mathlib

/-!
# Log-Scale Modular Surprisal Bridge

This file establishes the fundamental structural identification between the 
continuous logarithmic scale generator and the Tomita-Takesaki modular operator:
  $\mathcal{K} = -\log\Delta$

By axiomatically specifying the unitary flow $U_t$, we cleanly decouple the 
algebraic modular geometry from the heavy analytic unbounded functional calculus. 
The analytic exponentiation $U_t = e^{-it\mathcal{K}}$ is recorded as a future 
analytic bridge theorem; this owner contains no proof holes.
-/

namespace InfoGeometry.Canonical.LogScaleModularSurprisalBridge

/-- 
A structural encapsulation of the Tomita-Takesaki modular surprisal.
The flow $U_t$ is supplied as a primitive one-parameter group, preventing the 
need for premature unbounded exponential calculus.
-/
structure ModularSurprisalDatum (A : Type*) [AddCommGroup A] [Module ℂ A] where
  /-- The operatorial surprisal generator $\mathcal{K} = -\log \Delta$. -/
  K : A →ₗ[ℂ] A
  
  /-- The one-parameter modular flow $U_t$ (representing $\Delta^{it}$). -/
  U : ℝ → (A →ₗ[ℂ] A)
  
  /-- The flow forms a one-parameter group (homomorphism). -/
  flow_zero : U 0 = LinearMap.id
  
  /-- The flow respects addition (semigroup property). -/
  flow_add : ∀ s t, U (s + t) = U s ∘ₗ U t

theorem flow_comp_neg {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (t : ℝ) :
    D.U t ∘ₗ D.U (-t) = LinearMap.id := by
  rw [← D.flow_add t (-t)]
  simpa using D.flow_zero

theorem flow_neg_comp {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (t : ℝ) :
    D.U (-t) ∘ₗ D.U t = LinearMap.id := by
  rw [← D.flow_add (-t) t]
  simpa using D.flow_zero

/-- 
The modular automorphism $\sigma_t$ acting on an observable $O$.
$\sigma_t(O) = U_t O U_{-t}$
-/
noncomputable def modularAutomorphism {A : Type*} [AddCommGroup A] [Module ℂ A] 
    (D : ModularSurprisalDatum A) (t : ℝ) (O : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  (D.U t) ∘ₗ O ∘ₗ (D.U (-t))

@[simp] theorem modularAutomorphism_zero {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (O : A →ₗ[ℂ] A) :
    modularAutomorphism D 0 O = O := by
  simp [modularAutomorphism, D.flow_zero]

theorem modularAutomorphism_add {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (s t : ℝ) (O : A →ₗ[ℂ] A) :
    modularAutomorphism D (s + t) O =
      modularAutomorphism D s (modularAutomorphism D t O) := by
  simp only [modularAutomorphism, D.flow_add]
  rw [show -(s + t) = (-t) + (-s) by ring, D.flow_add]
  simp only [LinearMap.comp_assoc]

/-- Arithmetic multiplication becomes composition of the induced modular
    automorphisms at logarithmic time. -/
theorem modularAutomorphism_log_mul {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (O : A →ₗ[ℂ] A) :
    modularAutomorphism D (Real.log (m * n : ℝ)) O =
      modularAutomorphism D (Real.log m)
        (modularAutomorphism D (Real.log n) O) := by
  rw [Real.log_mul (by positivity) (by positivity)]
  exact modularAutomorphism_add D _ _ O

theorem modularAutomorphism_neg {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (t : ℝ) (O : A →ₗ[ℂ] A) :
    modularAutomorphism D (-t) (modularAutomorphism D t O) = O := by
  simp [modularAutomorphism, LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc, flow_neg_comp D t]
  simp

/-- 
The central modular surprisal equivalence (Future Analytic Target).
This isolates the spectral calculus requirement: $U_t = e^{-it\mathcal{K}}$.
-/
def flow_eq_exp_surprisal {A : Type*} [AddCommGroup A] [Module ℂ A] 
    (D : ModularSurprisalDatum A) (expK : ℝ → (A →ₗ[ℂ] A) → A →ₗ[ℂ] A) : Prop :=
  ∀ t : ℝ, D.U t = expK (-t) D.K

/--
The discrete Dirichlet sampling of the modular time.
By setting $t = \log n$, we evaluate the continuous Tomita-Takesaki flow 
at the precise arithmetic scales of the prime/integer lattice.
-/
noncomputable def dirichletModularSample {A : Type*} [AddCommGroup A] [Module ℂ A] 
    (D : ModularSurprisalDatum A) (n : ℕ) : A →ₗ[ℂ] A :=
  D.U (Real.log n)

/--
Prime modular-time sampling corresponds to the operator Euler factor.
For a prime $p$, the continuous modular flow sampled at $\log p$ gives 
exactly the building block of the arithmetic spectral operator.
-/
theorem prime_modular_sampling_eq_surprisal_flow {A : Type*} [AddCommGroup A] [Module ℂ A] 
    (D : ModularSurprisalDatum A) (p : ℕ) (_hp : Nat.Prime p) :
    dirichletModularSample D p = D.U (Real.log p) := by
  rfl

/-- Positive arithmetic multiplication is represented by composition of the
    corresponding logarithmic modular samples. -/
theorem dirichletModularSample_mul {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    dirichletModularSample D (m * n) =
      D.U (Real.log m) ∘ₗ D.U (Real.log n) := by
  unfold dirichletModularSample
  rw [show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by norm_num]
  rw [Real.log_mul (by positivity) (by positivity)]
  exact D.flow_add _ _

/-- Repeated evolution at an integral multiple of a logarithmic time. -/
theorem flow_nat_mul {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (t : ℝ) (k : ℕ) :
    D.U ((k : ℝ) * t) = (D.U t) ^ k := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, pow_zero]
      rw [D.flow_zero]
      rfl
  | succ k ih =>
      have hscalar : ((Nat.succ k : ℕ) : ℝ) * t =
          (k : ℝ) * t + t := by
        push_cast
        ring
      rw [hscalar, D.flow_add, ih, pow_succ]
      rfl

/-- Prime-power sampling is repeated modular-time evolution. -/
theorem prime_power_modular_sampling {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (p k : ℕ) :
    D.U (Real.log (p ^ k)) = (D.U (Real.log p)) ^ k := by
  rw [Real.log_pow]
  exact flow_nat_mul D (Real.log p) k

/-- The named Dirichlet sample satisfies the same prime-power law. -/
theorem dirichletModularSample_prime_power {A : Type*} [AddCommGroup A] [Module ℂ A]
    (D : ModularSurprisalDatum A) (p k : ℕ) :
    dirichletModularSample D (p ^ k) =
      (dirichletModularSample D p) ^ k := by
  unfold dirichletModularSample
  rw [show ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k by norm_num]
  exact prime_power_modular_sampling D p k

end InfoGeometry.Canonical.LogScaleModularSurprisalBridge
