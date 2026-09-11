import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge

set_option linter.unusedSimpArgs false

/-!
# Poincaré Casimir Centrality and Type-Safe Duality Bridge

This owner module formalizes the structural Poincaré Casimir centrality and type-safe
tangent/cotangent distinctions:

1. **Type-Safe FourVector and FourCovector Carrier:**
   $V \in TM \cong \text{Fin } 4 \to \mathbb{R}$, $P \in T^*M \cong \text{Fin } 4 \to \mathbb{R}$
   with musical isomorphisms $\eta^\flat : TM \to T^*M$ and $\eta^\sharp : T^*M \to TM$.

2. **Invariance and Reversibility of Musical Isomorphisms:**
   $\eta^\sharp \circ \eta^\flat = \mathrm{id}_{TM}$ and $\eta^\flat \circ \eta^\sharp = \mathrm{id}_{T^*M}$.

3. **Minkowski Pairing Matching Vector-Covector Evaluation:**
   $v \cdot w = (\eta^\flat v)(w) = v_0 w_0 - (v_1 w_1 + v_2 w_2 + v_3 w_3)$.

4. **First Casimir Centrality ($[C_1, P_\mu] = 0$ and $[C_1, M_{\mu\nu}] = 0$):**
   In any associative ring $A$ equipped with Poincaré brackets:
   - $[C_1, P_\mu] = 0$ for all $\mu \in \text{Fin } 4$.
   - $[C_1, M_{\mu\nu}] = 0$ for all $\mu, \nu \in \text{Fin } 4$ (mass-shell Lorentz invariance).

5. **Second Casimir Centrality ($[C_2, P_\alpha] = 0$):**
   $[C_2, P_\alpha] = 0$ for the Pauli-Lubański spin invariant $C_2 = W_0^2 - W_1^2 - W_2^2 - W_3^2$.

6. **Pauli-Lubański Orthogonality with Lowered Covectors ($p_\mu W^\mu = 0$):**
   For $W^\mu = \frac{1}{2} \epsilon^{\mu\nu\rho\sigma} p_\nu M_{\rho\sigma}$ where $p = \eta^\flat P$,
   $p_\mu W^\mu \equiv 0$ due to the contraction of symmetric $p_\mu p_\nu$ with antisymmetric $\epsilon^{\mu\nu\rho\sigma}$.
-/

noncomputable section

namespace InfoGeometry.Physics.PoincareCasimirCentralityBridge

open InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge

abbrev FourVector := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev FourCovector := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- Musical isomorphism $\eta^\flat : TM \to T^*M$ (lowering indices). -/
def minkowskiLower (v : FourVector) : FourCovector :=
  fun μ =>
    match μ with
    | 0 => v 0
    | 1 => - v 1
    | 2 => - v 2
    | 3 => - v 3

/-- Musical isomorphism $\eta^\sharp : T^*M \to TM$ (raising indices). -/
def minkowskiRaise (p : FourCovector) : FourVector :=
  fun μ =>
    match μ with
    | 0 => p 0
    | 1 => - p 1
    | 2 => - p 2
    | 3 => - p 3

/-- 🏆 THEOREM 1: $\eta^\sharp \circ \eta^\flat = \mathrm{id}$ and $\eta^\flat \circ \eta^\sharp = \mathrm{id}$. -/
theorem minkowski_musical_iso_involutive (v : FourVector) :
    minkowskiRaise (minkowskiLower v) = v := by
  ext μ
  fin_cases μ <;> simp [minkowskiRaise, minkowskiLower]

theorem minkowski_musical_iso_covector_involutive (p : FourCovector) :
    minkowskiLower (minkowskiRaise p) = p := by
  ext μ
  fin_cases μ <;> simp [minkowskiRaise, minkowskiLower]

/-- 🏆 THEOREM 2: The Minkowski inner product matches the vector-covector pairing:
    $v \cdot w = (\eta^\flat v)(w) = v_0 w_0 - (v_1 w_1 + v_2 w_2 + v_3 w_3)$. -/
theorem minkowski_inner_eq_covector_pairing (v w : FourVector) :
    (v 0 * w 0 - (v 1 * w 1 + v 2 * w 2 + v 3 * w 3)) =
      (minkowskiLower v 0 * w 0 + minkowskiLower v 1 * w 1 +
       minkowskiLower v 2 * w 2 + minkowskiLower v 3 * w 3) := by
  dsimp [minkowskiLower]
  ring

/-- Commutator of two elements in an associative ring. -/
def bracket {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- Minkowski metric sign function: +1 for 0, -1 for 1,2,3. -/
def etaSign (μ : Fin 4) : ℝ :=
  match μ with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1

/-- Minkowski metric tensor $\eta_{\mu\nu}$. -/
def eta (μ ν : Fin 4) : ℝ :=
  if μ = ν then etaSign μ else 0

/-- Abstract Poincaré algebra generators and relations. -/
structure PoincareAlgebra (A : Type*) [Ring A] [Algebra ℝ A] where
  P : Fin 4 → A
  M : Fin 4 → Fin 4 → A
  P_comm : ∀ μ ν, bracket (P μ) (P ν) = 0
  M_antisymm : ∀ μ ν, M μ ν = - M ν μ
  MP_bracket : ∀ μ ν ρ, bracket (M μ ν) (P ρ) =
    (eta ν ρ • P μ) - (eta μ ρ • P ν)

/-- First Casimir element $C_1 = P_0^2 - P_1^2 - P_2^2 - P_3^2 = \sum_\mu \eta^{\mu\mu} P_\mu^2$. -/
def casimir1 {A : Type*} [Ring A] (P : Fin 4 → A) : A :=
  P 0 ^ 2 - P 1 ^ 2 - P 2 ^ 2 - P 3 ^ 2

/-- Leibniz rule for commutator with square. -/
theorem bracket_sq {A : Type*} [Ring A] (x y : A) :
    bracket x (y ^ 2) = bracket x y * y + y * bracket x y := by
  dsimp [bracket]
  rw [pow_two]
  noncomm_ring

/-- 🏆 THEOREM 3: $[C_1, P_\mu] = 0$ for all $\mu$. -/
theorem casimir1_comm_P {A : Type*} [Ring A] [Algebra ℝ A] (poinc : PoincareAlgebra A) (μ : Fin 4) :
    bracket (casimir1 poinc.P) (poinc.P μ) = 0 := by
  dsimp [casimir1, bracket]
  have hcomm (i : Fin 4) : (poinc.P i ^ 2) * poinc.P μ = poinc.P μ * (poinc.P i ^ 2) := by
    have hp := poinc.P_comm i μ
    dsimp [bracket] at hp
    have hp' : poinc.P i * poinc.P μ = poinc.P μ * poinc.P i := by
      calc
        poinc.P i * poinc.P μ = poinc.P i * poinc.P μ - poinc.P μ * poinc.P i + poinc.P μ * poinc.P i := by abel
        _ = 0 + poinc.P μ * poinc.P i := by rw [hp]
        _ = poinc.P μ * poinc.P i := by abel
    calc
      (poinc.P i ^ 2) * poinc.P μ = poinc.P i * (poinc.P i * poinc.P μ) := by rw [pow_two, mul_assoc]
      _ = poinc.P i * (poinc.P μ * poinc.P i) := by rw [hp']
      _ = (poinc.P i * poinc.P μ) * poinc.P i := by rw [mul_assoc]
      _ = (poinc.P μ * poinc.P i) * poinc.P i := by rw [hp']
      _ = poinc.P μ * (poinc.P i ^ 2) := by rw [pow_two, mul_assoc]
  simp only [sub_mul, mul_sub, hcomm]
  abel

/-- Explicit expansion of bracket of M with C1. -/
theorem bracket_M_P_sq {A : Type*} [Ring A] [Algebra ℝ A] (poinc : PoincareAlgebra A) (μ ν i : Fin 4) :
    bracket (poinc.M μ ν) (poinc.P i ^ 2) =
      ((eta ν i • poinc.P μ) - (eta μ i • poinc.P ν)) * poinc.P i +
      poinc.P i * ((eta ν i • poinc.P μ) - (eta μ i • poinc.P ν)) := by
  rw [bracket_sq, poinc.MP_bracket]

theorem p_comm_eq {A : Type*} [Ring A] [Algebra ℝ A] (poinc : PoincareAlgebra A) (μ ν : Fin 4) :
    poinc.P μ * poinc.P ν = poinc.P ν * poinc.P μ := by
  have hp := poinc.P_comm μ ν
  dsimp [bracket] at hp
  calc
    poinc.P μ * poinc.P ν = (poinc.P μ * poinc.P ν - poinc.P ν * poinc.P μ) + poinc.P ν * poinc.P μ := by abel
    _ = 0 + poinc.P ν * poinc.P μ := by rw [hp]
    _ = poinc.P ν * poinc.P μ := by abel

/-- 🏆 THEOREM 4: $[C_1, M_{\mu\nu}] = 0$ for all $\mu, \nu \in \text{Fin } 4$.
    Rotational and boost invariance of the mass-shell Casimir. -/
theorem casimir1_comm_M {A : Type*} [Ring A] [Algebra ℝ A] (poinc : PoincareAlgebra A) (μ ν : Fin 4) :
    bracket (casimir1 poinc.P) (poinc.M μ ν) = 0 := by
  have h_anti : bracket (casimir1 poinc.P) (poinc.M μ ν) = - bracket (poinc.M μ ν) (casimir1 poinc.P) := by
    dsimp [bracket]; abel
  rw [h_anti]
  have h_cas : bracket (poinc.M μ ν) (casimir1 poinc.P) =
      bracket (poinc.M μ ν) (poinc.P 0 ^ 2) -
      bracket (poinc.M μ ν) (poinc.P 1 ^ 2) -
      bracket (poinc.M μ ν) (poinc.P 2 ^ 2) -
      bracket (poinc.M μ ν) (poinc.P 3 ^ 2) := by
    dsimp [casimir1, bracket]
    simp only [mul_sub, sub_mul]
    abel
  rw [h_cas]
  simp only [bracket_M_P_sq]
  fin_cases μ <;> fin_cases ν
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 0 1
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 0 2
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 0 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 1 0
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 1 2
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 1 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 2 0
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 2 1
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 2 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 3 0
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 3 1
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := p_comm_eq poinc 3 2
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]

/-! Package the two first-Casimir commutator consumers into a single
Poincare-facing statement.  The hypotheses remain exactly those stored in
`PoincareAlgebra`; this is conditional algebraic centrality, not an irrep
classification theorem. -/
theorem casimir1_central_poincare
    {A : Type*} [Ring A] [Algebra ℝ A]
    (poinc : PoincareAlgebra A) :
    (∀ μ, bracket (casimir1 poinc.P) (poinc.P μ) = 0) ∧
      (∀ μ ν, bracket (casimir1 poinc.P) (poinc.M μ ν) = 0) := by
  constructor
  · intro μ
    exact casimir1_comm_P poinc μ
  · intro μ ν
    exact casimir1_comm_M poinc μ ν

/-- Second Casimir element $C_2 = W_0^2 - W_1^2 - W_2^2 - W_3^2$. -/
def casimir2 {A : Type*} [Ring A] (W : Fin 4 → A) : A :=
  W 0 ^ 2 - W 1 ^ 2 - W 2 ^ 2 - W 3 ^ 2

/-- 🏆 THEOREM 5: $[C_2, P_\alpha] = 0$ when $[W_\mu, P_\alpha] = 0$ for all $\mu$. -/
theorem casimir2_comm_P {A : Type*} [Ring A] (W : Fin 4 → A) (P : A)
    (hWP : ∀ μ, bracket (W μ) P = 0) :
    bracket (casimir2 W) P = 0 := by
  dsimp [casimir2, bracket]
  have hcomm (i : Fin 4) : (W i ^ 2) * P = P * (W i ^ 2) := by
    have hw := hWP i
    dsimp [bracket] at hw
    have hw' : W i * P = P * W i := by
      calc
        W i * P = W i * P - P * W i + P * W i := by abel
        _ = 0 + P * W i := by rw [hw]
        _ = P * W i := by abel
    calc
      (W i ^ 2) * P = W i * (W i * P) := by rw [pow_two, mul_assoc]
      _ = W i * (P * W i) := by rw [hw']
      _ = (W i * P) * W i := by rw [mul_assoc]
      _ = (P * W i) * W i := by rw [hw']
      _ = P * (W i ^ 2) := by rw [pow_two, mul_assoc]
  simp only [sub_mul, mul_sub, hcomm]
  abel

/-! Lorentz-side centrality has the same algebraic reduction as the
translation-side statement above.  The representation-specific input is
exactly the component-wise commutation of the Pauli--Lubanski components with
the chosen Lorentz generator; no irreducibility or classification theorem is
being smuggled in here. -/
theorem casimir2_comm_M_of_component_comm
    {A : Type*} [Ring A] (W : Fin 4 → A)
    (M : A) (hWM : ∀ μ, bracket (W μ) M = 0) :
    bracket (casimir2 W) M = 0 := by
  exact casimir2_comm_P W M hWM

/-! Pack the two conditional component-wise consumers into the exact
Poincare-facing centrality statement. -/
theorem casimir2_central_poincare_of_component_comm
    {A : Type*} [Ring A] (W : Fin 4 → A)
    (P : Fin 4 → A) (M : Fin 4 → Fin 4 → A)
    (hWP : ∀ α μ, bracket (W μ) (P α) = 0)
    (hWM : ∀ α β μ, bracket (W μ) (M α β) = 0) :
    (∀ α, bracket (casimir2 W) (P α) = 0) ∧
      (∀ α β, bracket (casimir2 W) (M α β) = 0) := by
  constructor
  · intro α
    exact casimir2_comm_P W (P α) (hWP α)
  · intro α β
    exact casimir2_comm_M_of_component_comm W (M α β) (hWM α β)

/-- 🏆 THEOREM 6: Pauli-Lubański orthogonality with lowered covector $p = \eta^\flat P$:
    $p_\mu W^\mu = \frac{1}{2} \epsilon^{\mu\nu\rho\sigma} p_\mu p_\nu M_{\rho\sigma} = 0$. -/
theorem pauliLubanski_orthogonal_lowered (ε : AntisymmetricTensor4) (P : FourVector) (M : Fin 4 → Fin 4 → ℝ) :
    let p := minkowskiLower P
    (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ε.val μ ν ρ σ * (p μ * p ν) * M ρ σ) = 0 := by
  intro p
  have h_pair : ∀ ρ σ μ ν, ε.val μ ν ρ σ * (p μ * p ν) + ε.val ν μ ρ σ * (p ν * p μ) = 0 := by
    intro ρ σ μ ν
    rw [ε.antisymm_12 μ ν ρ σ]
    have hcomm : p ν * p μ = p μ * p ν := mul_comm (p ν) (p μ)
    rw [hcomm]
    ring
  have h_inner : ∀ ρ σ, (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν) * M ρ σ) = 0 := by
    intro ρ σ
    have h_symm : (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) =
                  (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val ν μ ρ σ * (p ν * p μ)) := by
      rw [Finset.sum_comm]
    have h_sum_zero : (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) = 0 := by
      have h2 : 2 * (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) = 0 := by
        calc
          2 * (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν))
            = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) +
              (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) := by ring
          _ = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) +
              (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val ν μ ρ σ * (p ν * p μ)) := by rw [h_symm]
          _ = ∑ μ : Fin 4, ∑ ν : Fin 4, (ε.val μ ν ρ σ * (p μ * p ν) +
                                         ε.val ν μ ρ σ * (p ν * p μ)) := by
            simp only [← Finset.sum_add_distrib]
          _ = ∑ μ : Fin 4, ∑ ν : Fin 4, (0 : ℝ) := by
            simp only [h_pair]
          _ = 0 := by simp
      linarith
    calc
      (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν) * M ρ σ)
        = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (p μ * p ν)) * M ρ σ := by
          simp only [← Finset.sum_mul]
      _ = 0 * M ρ σ := by rw [h_sum_zero]
      _ = 0 := by ring
  calc
    (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ε.val μ ν ρ σ * (p μ * p ν) * M ρ σ)
      = ∑ ρ : Fin 4, ∑ σ : Fin 4, (0 : ℝ) := by
        simp only [h_inner]
    _ = 0 := by simp

end InfoGeometry.Physics.PoincareCasimirCentralityBridge
