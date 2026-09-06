import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Probability.ExpLogRNDerivation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Non-Commutative dlog Cocycle to KMS Modular Flow Bridge

This module establishes the formal bridge connecting the non-commutative logarithmic
Radon–Nikodym derivation `dlogL` (Maurer–Cartan forms) from `ExpLogRNDerivation.lean` to the
Tomita–Takesaki / KMS modular Hamiltonian automorphism flows.

## Mathematical Architecture:
1. **Infinitesimal Connes Cocycle Shift**:
   For an inner Hamiltonian derivation $\operatorname{ad}_K(X) = [K, X]$, the logarithmic derivative
   measures the discrete perturbation between the bare and transformed modular Hamiltonians:
   $$\operatorname{dlogL}_{\operatorname{ad}_K}(u) = u^{-1} [K, u] = u^{-1} K u - K = K_u - K$$
   equivalently $K_u = K + \operatorname{dlogL}_{\operatorname{ad}_K}(u)$.
2. **Modular Flow Generator Intertwining**:
   $$\operatorname{ad}_{K_u}(X) = u^{-1} \operatorname{ad}_K(u X u^{-1}) u$$
3. **Double Shift & 2-Cocycle Identity**:
   $$K_{u \cdot v} = (K_u)_v, \qquad \operatorname{dlogL}_{\operatorname{ad}_K}(u \cdot v) = \operatorname{dlogL}_{\operatorname{ad}_{K_u}}(v) + \operatorname{dlogL}_{\operatorname{ad}_K}(u)$$
   $$\operatorname{dlogL}_{\operatorname{ad}_K}(u \cdot v) = v^{-1} \operatorname{dlogL}_{\operatorname{ad}_K}(u) v + \operatorname{dlogL}_{\operatorname{ad}_K}(v)$$
4. **$n$-Fold Generalized Chain Rule for Unit Lists (`List Aˣ`)**:
   - Telescoping sequential accumulation: $\operatorname{dlogL}_{\operatorname{ad}_K}(\prod L) = \sum_{i=1}^n \operatorname{dlogL}_{\operatorname{ad}_{K_{i-1}}}(u_i)$
   - Non-abelian gauge cocycle expansion: $\operatorname{dlogL}_{\operatorname{ad}_K}(\prod L) = \sum_{i=1}^n (u_{i+1}\cdots u_n)^{-1} \operatorname{dlogL}_{\operatorname{ad}_K}(u_i) (u_{i+1}\cdots u_n)$
5. **KMS Thermal State Stationarity**:
   For any density matrix $\rho$ commuting with the modular Hamiltonian $K$ ($\rho = e^{-K}$),
   the thermal expectation of any modular flow generator vanishes:
   $$\operatorname{Tr}(\rho [K, X]) = 0$$

All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
-/

namespace InfoGeometry.Information.ModularCocycleKMSBridge

open InfoGeometry.Probability.ExpLogRNDerivation

variable {A : Type*} [Ring A]

/-- The standard Lie commutator bracket on a ring: `[X, Y] = X * Y - Y * X`. -/
def ringBracket (X Y : A) : A := X * Y - Y * X

/-- Inner derivation `ad_K(X) = [K, X]`. -/
def adOp (K : A) (X : A) : A := ringBracket K X

/-- Left non-commutative logarithmic derivation: `dlogL_D(u) = u⁻¹ * D(u)`. -/
def dlogL (D : A → A) (u : Aˣ) : A := (↑u⁻¹ : A) * D (u : A)

/-- Perturbed Modular Hamiltonian under inner adjoint shift: `K_u = u⁻¹ * K * u`. -/
def perturbedHamiltonian (K : A) (u : Aˣ) : A :=
  (↑u⁻¹ : A) * K * (u : A)

/-- Perturbed modular Hamiltonian alias. -/
def perturbedModularHamiltonian (K : A) (u : Aˣ) : A :=
  perturbedHamiltonian K u

/-- Infinitesimal modular generator (Heisenberg time derivative). -/
def modularDeriv (K X : A) : A := -adOp K X

/-!
=============================================================================
PART 1: Cocycle-to-Hamiltonian Shift Identities
=============================================================================
-/

/-- Identity perturbation leaves the modular Hamiltonian invariant: `K_1 = K`. -/
@[simp]
theorem perturbedHamiltonian_one (K : A) :
    perturbedHamiltonian K 1 = K := by
  dsimp [perturbedHamiltonian]
  simp only [Units.val_one, inv_one, mul_one, one_mul]

/--
  THEOREM: The inner logarithmic derivation computes the discrete modular shift:
  `dlogL_{ad_K}(u) = K_u - K`
-/
theorem dlogL_ad_eq_sub (K : A) (u : Aˣ) :
    dlogL (adOp K) u = perturbedHamiltonian K u - K := by
  dsimp [dlogL, adOp, ringBracket, perturbedHamiltonian]
  calc
    (↑u⁻¹ : A) * (K * (u : A) - (u : A) * K)
      = (↑u⁻¹ : A) * (K * (u : A)) - (↑u⁻¹ : A) * ((u : A) * K) := by
        rw [mul_sub]
    _ = (↑u⁻¹ : A) * K * (u : A) - ((↑u⁻¹ : A) * (u : A)) * K := by
        rw [mul_assoc (↑u⁻¹ : A) K (u : A), mul_assoc (↑u⁻¹ : A) (u : A) K]
    _ = (↑u⁻¹ : A) * K * (u : A) - 1 * K := by
        rw [Units.inv_mul]
    _ = (↑u⁻¹ : A) * K * (u : A) - K := by
        rw [one_mul]

/--
  THEOREM: The perturbed modular Hamiltonian equals the bare Hamiltonian
  shifted by the logarithmic Radon–Nikodym derivation:
  `K_u = K + dlogL_{ad_K}(u)`
-/
theorem perturbed_hamiltonian_eq_add_dlogL (K : A) (u : Aˣ) :
    perturbedModularHamiltonian K u = K + dlogL (adOp K) u := by
  dsimp [perturbedModularHamiltonian]
  rw [dlogL_ad_eq_sub]
  abel

/-!
=============================================================================
PART 2: Infinitesimal Intertwining of Modular Flows
=============================================================================
-/

/--
  THEOREM: The modular flow generator transforms under the adjoint cocycle action:
  `ad_{K_u}(X) = u⁻¹ * ad_K(u * X * u⁻¹) * u`
-/
theorem modular_generator_intertwining (K : A) (u : Aˣ) (X : A) :
    adOp (perturbedModularHamiltonian K u) X =
      (↑u⁻¹ : A) * adOp K ((u : A) * X * (↑u⁻¹ : A)) * (u : A) := by
  dsimp [perturbedModularHamiltonian, perturbedHamiltonian, adOp, ringBracket]
  have h1 : ((↑u⁻¹ : A) * K * (u : A)) * X * ((↑u⁻¹ : A) * (u : A)) =
      (↑u⁻¹ : A) * (K * ((u : A) * X * (↑u⁻¹ : A))) * (u : A) := by
    simp only [mul_assoc]
  have h2 : ((↑u⁻¹ : A) * (u : A)) * X * ((↑u⁻¹ : A) * K * (u : A)) =
      (↑u⁻¹ : A) * (((u : A) * X * (↑u⁻¹ : A)) * K) * (u : A) := by
    simp only [mul_assoc]
  calc
    ((↑u⁻¹ : A) * K * (u : A)) * X - X * ((↑u⁻¹ : A) * K * (u : A))
      = ((↑u⁻¹ : A) * K * (u : A)) * X * 1 - 1 * X * ((↑u⁻¹ : A) * K * (u : A)) := by
        simp only [mul_one, one_mul]
    _ = ((↑u⁻¹ : A) * K * (u : A)) * X * ((↑u⁻¹ : A) * (u : A)) -
          ((↑u⁻¹ : A) * (u : A)) * X * ((↑u⁻¹ : A) * K * (u : A)) := by
        rw [Units.inv_mul]
    _ = (↑u⁻¹ : A) * (K * ((u : A) * X * (↑u⁻¹ : A))) * (u : A) -
          (↑u⁻¹ : A) * (((u : A) * X * (↑u⁻¹ : A)) * K) * (u : A) := by
        rw [h1, h2]
    _ = ((↑u⁻¹ : A) * (K * ((u : A) * X * (↑u⁻¹ : A))) -
          (↑u⁻¹ : A) * (((u : A) * X * (↑u⁻¹ : A)) * K)) * (u : A) := by
        rw [sub_mul]
    _ = (↑u⁻¹ : A) * (K * ((u : A) * X * (↑u⁻¹ : A)) -
          ((u : A) * X * (↑u⁻¹ : A)) * K) * (u : A) := by
        rw [mul_sub]

/-!
=============================================================================
PART 3: Double Shift Functoriality & 2-Cocycle Identities
=============================================================================
-/

/--
  THEOREM: Modular Hamiltonian transformations form an associative left action:
  `K_{u * v} = (K_u)_v`
-/
theorem perturbedHamiltonian_mul (K : A) (u v : Aˣ) :
    perturbedHamiltonian K (u * v) = perturbedHamiltonian (perturbedHamiltonian K u) v := by
  dsimp [perturbedHamiltonian]
  rw [mul_inv_rev, Units.val_mul]
  simp only [mul_assoc]

/--
  THEOREM: Iterated Modular Shift (Telescoping Sum).
  The combined shift decomposes into the shift relative to `K_u` plus the shift of `K`:
  `dlogL_{ad_K}(u * v) = dlogL_{ad_{K_u}}(v) + dlogL_{ad_K}(u)`
-/
theorem dlogL_ad_mul_double_shift (K : A) (u v : Aˣ) :
    dlogL (adOp K) (u * v) =
      dlogL (adOp (perturbedHamiltonian K u)) v + dlogL (adOp K) u := by
  rw [dlogL_ad_eq_sub, dlogL_ad_eq_sub, dlogL_ad_eq_sub, perturbedHamiltonian_mul]
  abel

/--
  THEOREM: Non-Commutative 2-Cocycle / Twisted Gauge Identity.
  Decomposes the composite shift into a twisted conjugate of the first shift and the second shift:
  `dlogL_{ad_K}(u * v) = v⁻¹ * dlogL_{ad_K}(u) * v + dlogL_{ad_K}(v)`
-/
theorem dlogL_ad_mul_cocycle (K : A) (u v : Aˣ) :
    dlogL (adOp K) (u * v) =
      (↑v⁻¹ : A) * dlogL (adOp K) u * (v : A) + dlogL (adOp K) v := by
  rw [dlogL_ad_eq_sub, dlogL_ad_eq_sub, dlogL_ad_eq_sub, perturbedHamiltonian_mul]
  dsimp [perturbedHamiltonian]
  calc
    (↑v⁻¹ : A) * ((↑u⁻¹ : A) * K * (u : A)) * (v : A) - K
      = (↑v⁻¹ : A) * ((↑u⁻¹ : A) * K * (u : A)) * (v : A) - (↑v⁻¹ : A) * K * (v : A) +
        ((↑v⁻¹ : A) * K * (v : A) - K) := by
        abel
    _ = ((↑v⁻¹ : A) * ((↑u⁻¹ : A) * K * (u : A)) - (↑v⁻¹ : A) * K) * (v : A) +
        ((↑v⁻¹ : A) * K * (v : A) - K) := by
        rw [sub_mul]
    _ = (↑v⁻¹ : A) * (((↑u⁻¹ : A) * K * (u : A)) - K) * (v : A) +
        ((↑v⁻¹ : A) * K * (v : A) - K) := by
        rw [mul_sub]

/-- Invariance under identity composition: `dlogL_{ad_K}(u * u⁻¹) = 0`. -/
theorem dlogL_ad_mul_inv_self (K : A) (u : Aˣ) :
    dlogL (adOp K) (u * u⁻¹) = 0 := by
  rw [mul_inv_cancel u, dlogL_ad_eq_sub, perturbedHamiltonian_one, sub_self]

/-- Inversion formula for the modular logarithmic shift:
    `dlogL_{ad_K}(u⁻¹) = - (u * dlogL_{ad_K}(u) * u⁻¹)`. -/
theorem dlogL_ad_inv (K : A) (u : Aˣ) :
    dlogL (adOp K) (u⁻¹) = - ((u : A) * dlogL (adOp K) u * (↑u⁻¹ : A)) := by
  have h := dlogL_ad_mul_cocycle K (u⁻¹) u
  rw [inv_mul_cancel u, dlogL_ad_eq_sub, perturbedHamiltonian_one, sub_self] at h
  have h_shift : (↑u⁻¹ : A) * dlogL (adOp K) (u⁻¹) * (u : A) = - dlogL (adOp K) u :=
    eq_neg_of_add_eq_zero_left h.symm
  have h_cancel : (u : A) * ((↑u⁻¹ : A) * dlogL (adOp K) (u⁻¹) * (u : A)) * (↑u⁻¹ : A) =
      dlogL (adOp K) (u⁻¹) := by
    calc
      (u : A) * ((↑u⁻¹ : A) * dlogL (adOp K) (u⁻¹) * (u : A)) * (↑u⁻¹ : A)
        = ((u : A) * (↑u⁻¹ : A)) * dlogL (adOp K) (u⁻¹) * ((u : A) * (↑u⁻¹ : A)) := by
          simp only [mul_assoc]
      _ = 1 * dlogL (adOp K) (u⁻¹) * 1 := by rw [Units.mul_inv u]
      _ = dlogL (adOp K) (u⁻¹) := by rw [one_mul, mul_one]
  calc
    dlogL (adOp K) (u⁻¹)
      = (u : A) * ((↑u⁻¹ : A) * dlogL (adOp K) (u⁻¹) * (u : A)) * (↑u⁻¹ : A) := h_cancel.symm
    _ = (u : A) * (- dlogL (adOp K) u) * (↑u⁻¹ : A) := by rw [h_shift]
    _ = - ((u : A) * dlogL (adOp K) u * (↑u⁻¹ : A)) := by rw [mul_neg, neg_mul]

/-!
=============================================================================
PART 4: n-Fold Generalized Chain Rules on Unit Lists (`List Aˣ`)
=============================================================================
-/

/--
  THEOREM: The modular action on a list product `L.prod` corresponds to the left fold
  of `perturbedHamiltonian` across the sequence:
  `K_{u₁ * u₂ * ⋯ * uₙ} = List.foldl perturbedHamiltonian K [u₁, u₂, ⋯, uₙ]`
-/
theorem perturbedHamiltonian_list_prod (K : A) (L : List Aˣ) :
    perturbedHamiltonian K L.prod = L.foldl perturbedHamiltonian K := by
  induction L generalizing K with
  | nil =>
    simp only [List.prod_nil, List.foldl_nil, perturbedHamiltonian_one]
  | cons u us ih =>
    simp only [List.prod_cons, List.foldl_cons]
    rw [perturbedHamiltonian_mul, ih]

/-- Sequential accumulation of modular Hamiltonian shifts along an orbit. -/
def iteratedModularShifts (K : A) : List Aˣ → A
  | [] => 0
  | u :: us => dlogL (adOp K) u + iteratedModularShifts (perturbedHamiltonian K u) us

/--
  THEOREM: The sequential modular shift accumulation telescopes identically to `K_{L.prod} - K`.
-/
theorem iteratedModularShifts_eq_sub (K : A) (L : List Aˣ) :
    iteratedModularShifts K L = perturbedHamiltonian K L.prod - K := by
  induction L generalizing K with
  | nil =>
    simp only [iteratedModularShifts, List.prod_nil, perturbedHamiltonian_one, sub_self]
  | cons u us ih =>
    simp only [iteratedModularShifts, List.prod_cons]
    rw [dlogL_ad_eq_sub, ih (perturbedHamiltonian K u), perturbedHamiltonian_mul]
    abel

/--
  THEOREM (n-Fold Telescoping Chain Rule):
  The logarithmic derivation of an arbitrary finite product of units equals
  the iterated sequential shift along the trajectory:
  `dlogL_{ad_K}(∏ L) = ∑_{i=1}^n dlogL_{ad_{K_{i-1}}}(uᵢ)`
-/
theorem dlogL_ad_list_prod_eq_iteratedModularShifts (K : A) (L : List Aˣ) :
    dlogL (adOp K) L.prod = iteratedModularShifts K L := by
  rw [dlogL_ad_eq_sub, iteratedModularShifts_eq_sub]

/-- Non-abelian gauge cocycle sum over unit list representations. -/
def twistedCocycleSum (K : A) : List Aˣ → A
  | [] => 0
  | u :: us => (↑us.prod⁻¹ : A) * dlogL (adOp K) u * (us.prod : A) + twistedCocycleSum K us

/--
  THEOREM (n-Fold Maurer-Cartan / Gauge Cocycle Chain Rule):
  The composite logarithmic derivation expands into the adjoint-twisted sum of individual shifts:
  `dlogL_{ad_K}(u₁ ⋯ uₙ) = ∑_{i=1}^n (u_{i+1} ⋯ uₙ)⁻¹ · dlogL_{ad_K}(uᵢ) · (u_{i+1} ⋯ uₙ)`
-/
theorem dlogL_ad_list_prod_eq_twistedCocycleSum (K : A) (L : List Aˣ) :
    dlogL (adOp K) L.prod = twistedCocycleSum K L := by
  induction L with
  | nil =>
    simp only [List.prod_nil, twistedCocycleSum, dlogL_ad_eq_sub, perturbedHamiltonian_one, sub_self]
  | cons u us ih =>
    simp only [List.prod_cons, twistedCocycleSum]
    rw [dlogL_ad_mul_cocycle, ih]

/-!
=============================================================================
PART 5: KMS Thermal State Stationarity
=============================================================================
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cyclic trace state evaluation: `ω_rho(X) = Tr(rho * X)`. -/
def traceState (rho X : Matrix n n ℝ) : ℝ :=
  Matrix.trace (rho * X)

/--
  THEOREM: First-order KMS stationarity condition under the modular flow.
  Commutator expectation with the modular Hamiltonian vanishes in the thermal state:
  `Tr(ρ * [K, X]) = 0` whenever `ρ` and `K` commute (e.g. `ρ = exp(-K)`).
-/
theorem kms_stationarity_commutator_zero (rho K X : Matrix n n ℝ)
    (h_comm : rho * K = K * rho) :
    traceState rho (ringBracket K X) = 0 := by
  dsimp [traceState, ringBracket]
  have h_tr_comm : Matrix.trace (rho * (K * X)) = Matrix.trace (rho * (X * K)) := by
    calc
      Matrix.trace (rho * (K * X)) = Matrix.trace ((rho * K) * X) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((K * rho) * X) := by rw [h_comm]
      _ = Matrix.trace (K * (rho * X)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((rho * X) * K) := by rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (rho * (X * K)) := by rw [Matrix.mul_assoc]
  calc
    Matrix.trace (rho * (K * X - X * K))
      = Matrix.trace (rho * (K * X) - rho * (X * K)) := by rw [Matrix.mul_sub]
    _ = Matrix.trace (rho * (K * X)) - Matrix.trace (rho * (X * K)) := by rw [Matrix.trace_sub]
    _ = 0 := sub_eq_zero.mpr h_tr_comm

/-- Stationarity of KMS trace state under transformed observable vectors. -/
theorem kms_stationarity_commutator_perturbed
    (rho K X : Matrix n n ℝ) (u : (Matrix n n ℝ)ˣ)
    (h_comm : rho * K = K * rho) :
    traceState rho (ringBracket K ((u : Matrix n n ℝ) * X * (↑u⁻¹ : Matrix n n ℝ))) = 0 :=
  kms_stationarity_commutator_zero rho K ((u : Matrix n n ℝ) * X * (↑u⁻¹ : Matrix n n ℝ)) h_comm

end InfoGeometry.Information.ModularCocycleKMSBridge
