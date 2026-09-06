import Mathlib
import proofs.ChiralParitySuperalgebra

/-!
# UHF Colimit Supercharge Bridge

This file mathematically projects the finite algebraic super-geometry 
(Chiral Parity Superalgebra) into the infinite thermodynamic continuum limit.

It proves that the chiral grading involution, supercharge parities, and the 
fundamental theorem of the Lie superalgebra are perfectly preserved across 
topological boundaries via direct inductive colimits (represented abstractly
via ring homomorphisms `psi : A → A_inf`).
-/

namespace InfoGeometry.UHFColimitSuperchargeBridge

open InfoGeometry.ChiralParitySuperalgebra

variable {A : Type*} [Ring A]
variable {A_inf : Type*} [Ring A_inf]
variable (psi : A →+* A_inf)

-- 1. colimit_grading_survival
/-- The operator chirality (Γₙ)² = 1 survives as an exact involution in the continuum colimit. -/
theorem colimit_grading_survival (Gamma : A) (h : Gamma^2 = 1) : 
    (psi Gamma)^2 = 1 := by
  rw [← map_pow, h, map_one]

-- 2. colimit_odd_survival
/-- The topological mapping strictly respects the super-grading; odd operators in Aₙ remain formally odd in the continuum limit. -/
theorem colimit_odd_survival (Gamma Q : A) [hQ : IsChiralSupercharge Gamma Q] :
    IsChiralSupercharge (psi Gamma) (psi Q) := by
  constructor
  have h1 : Gamma * Q = - (Q * Gamma) := hQ.odd_comm
  have h2 : psi (Gamma * Q) = psi (- (Q * Gamma)) := by rw [h1]
  rw [map_mul, map_neg, map_mul] at h2
  exact h2

-- 3. colimit_even_survival
/-- Even operators unconditionally preserve their parity constraint across the limit map. -/
theorem colimit_even_survival (Gamma Z : A) (hZ : isEven Gamma Z) :
    isEven (psi Gamma) (psi Z) := by
  dsimp [isEven] at hZ ⊢
  have h2 : psi (Gamma * Z) = psi (Z * Gamma) := by rw [hZ]
  rw [map_mul, map_mul] at h2
  exact h2

-- 4. continuum_superalgebra_closure
/-- The defining theorem. It proves that the anticommutator of the chiral supercharges Q and Q' 
    seamlessly translates into the colimit, guaranteeing that {ψₙ(Q),ψₙ(Q')} = ψₙ(Z) unconditionally 
    preserves its even parity constraint as it reaches A_∞. -/
theorem continuum_superalgebra_closure (Gamma Q Q' : A) 
    [hQ : IsChiralSupercharge Gamma Q] [hQ' : IsChiralSupercharge Gamma Q'] :
    isEven (psi Gamma) (psi (anticomm Q Q')) := by
  have h_even : isEven Gamma (anticomm Q Q') := superalgebra_closure Gamma Q Q'
  exact colimit_even_survival psi Gamma (anticomm Q Q') h_even

/-- Explicit translation showing the superalgebra commutes directly with the topological inclusion. -/
theorem continuum_superalgebra_closure_explicit (Gamma Q Q' : A) 
    [hQ : IsChiralSupercharge Gamma Q] [hQ' : IsChiralSupercharge Gamma Q'] :
    isEven (psi Gamma) (anticomm (psi Q) (psi Q')) := by
  have h_even_colimit := continuum_superalgebra_closure psi Gamma Q Q'
  have h_comm : psi (anticomm Q Q') = anticomm (psi Q) (psi Q') := by
    dsimp [anticomm]
    rw [map_add, map_mul, map_mul]
  rw [← h_comm]
  exact h_even_colimit

end InfoGeometry.UHFColimitSuperchargeBridge
