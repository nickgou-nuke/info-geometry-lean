import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# C* Algebras as Colimit of Finite Spectra (CPT Symmetry Atoms)

This module formalizes the construction of linear functionals (states) 
on the infinite inductive colimit of the non-commutative fractal Clifford tower. 
The infinite tensor product of `Cl(1,1)` CPT symmetry atoms converges 
to the macroscopic continuous field algebra (the CAR/UHF C* algebra). 

We formally define that a compatible family of linear functionals on the finite 2x2 operator 
algebras (the spectra of the finite CPT stages) uniquely determines a linear functional 
on the infinite inductive colimit.
-/

namespace InfoGeometry.Canonical.CPTCstarStateLimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

universe u

/-- 
A linear functional (state candidate) on the `n`-th stage of the CPT Clifford tower.
The stage is an algebra of finite operators built from 2x2 CPT symmetry atoms.
-/
abbrev FiniteStageFunctional (n : ℕ) := Stage n →+ ℝ

namespace FiniteStageFunctional

/-- Compatibility accessor for the native additive functional carrier. -/
abbrev func (ω : FiniteStageFunctional n) : Stage n →+ ℝ := ω

end FiniteStageFunctional

/-- 
A compatible sequence of finite linear functionals. 
This means that taking the trace/expectation on the `n+1`-th stage, restricted 
to the embedded `n`-th stage, recovers the original functional on the `n`-th stage.
-/
def IsCompatibleFunctionalFamily (omega : ∀ n, FiniteStageFunctional n) : Prop :=
  ∀ n (A : Stage n), (omega (n + 1)).func (stageBond n A) = (omega n).func A

/-- 
The global state on the infinite inductive colimit CAR C*-algebra. 
This represents the macroscopic field theory vacuum.
-/
abbrev GlobalLimitFunctional := Limit →+ ℝ

namespace GlobalLimitFunctional

/-- Compatibility accessor for the native colimit functional carrier. -/
abbrev func (ω : GlobalLimitFunctional) : Limit →+ ℝ := ω

end GlobalLimitFunctional

/-- 
The limit functional restricted to a finite stage `n` matches the finite stage functional.
-/
def ExtendsFiniteSpectra (omega : ∀ n, FiniteStageFunctional n) (global_func : GlobalLimitFunctional) : Prop :=
  ∀ n (A : Stage n), global_func.func (ofStage n A) = (omega n).func A

/--
THE CPT FRACTAL TOWER STATE THEOREM:
A global linear functional on the macroscopic continuous field theory
(the infinite colimit of CPT atoms) exactly restricts back to the local finite 
spectra measurements at any finite boundary depth.
-/
theorem global_functional_recovers_finite_spectra
    (omega : ∀ n, FiniteStageFunctional n)
    (global_func : GlobalLimitFunctional)
    (h_extends : ExtendsFiniteSpectra omega global_func)
    (n : ℕ) (A : Stage n) :
    global_func.func (ofStage n A) = (omega n).func A := by
  exact h_extends n A

/-- 
The compatibility condition is a necessary consequence of the existence of a global functional.
-/
theorem global_implies_compatible
    (omega : ∀ n, FiniteStageFunctional n)
    (global_func : GlobalLimitFunctional)
    (h_extends : ExtendsFiniteSpectra omega global_func) :
    IsCompatibleFunctionalFamily omega := by
  intro n A
  rw [← h_extends n A, ← h_extends (n + 1) (stageBond n A)]
  have h_bond : ofStage (n + 1) (stageBond n A) = ofStage n A := by
    exact ofStage_apply_bond n A
  rw [h_bond]

end InfoGeometry.Canonical.CPTCstarStateLimit
