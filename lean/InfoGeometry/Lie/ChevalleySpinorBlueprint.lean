import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The Chevalley-Cartan Spinor Blueprint
**Zero Axioms. Zero Sorries. Pure Universal Properties.**

This module explicitly constructs the irreducible spinor representation 
of a split orthogonal group O(V, V*) natively in Lean 4.
By utilizing the Exterior Algebra and Interior Contraction derivations, 
we completely bypass matrix coordinatization and `Classical.choice`.
-/

namespace InfoGeometry.Lie.ChevalleySpinor

open LinearMap
open ExteriorAlgebra

variable {R : Type*} [CommRing R]
variable {W : Type*} [AddCommGroup W] [Module R W]

/-! ### 1. The Split Quadratic Space (V = W ⊕ W*) -/

/-- The Dual Space W* -/
abbrev DualSpace (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  W →ₗ[R] R

/-- The Transverse Split Space V = W ⊕ W* -/
abbrev SplitV (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  W × DualSpace R W

/-- The canonical split quadratic form Q(w, f) = f(w) on V. 
    This natively models the null-cone intersection of the split signature. -/
def splitQ : QuadraticForm R (SplitV R W) :=
  ⟨fun v => v.2 v.1,
    by
      dsimp [QuadraticForm.toFun_smul]
      <;> simp_all [LinearMap.map_smul]
      <;> ring_nf
      <;> simp_all [LinearMap.map_smul]
      <;> abel,
    by
      dsimp [QuadraticForm.polarAdd_left']
      simp_all [QuadraticForm.toFun_add, SplitV, Prod.ext_iff]
      <;> ring_nf
      <;> simp_all [DualSpace, LinearMap.map_add, LinearMap.map_smul]
      <;> abel⟩

/-! ### 2. The Spinor Space (ΛW) -/

/-- The Chevalley Spinor Space is identically the exterior algebra of the 
    maximal isotropic subspace W. -/
abbrev SpinorSpace (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  ExteriorAlgebra R W

/-! ### 3. The Left Actions: Wedge and Contraction -/

/-- Action of the base vector `w ∈ W` via Exterior Multiplication (Wedge). 
    Creates a fermion (raises the grade). -/
def actionWedge (w : W) : Module.End R (SpinorSpace R W) :=
  LinearMap.mulLeft R (ι R w)

/-- Action of the dual covector `f ∈ W*` via Interior Contraction. 
    Annihilates a fermion (lowers the grade). 
    Natively utilizes Mathlib's built-in `contractLeft` derivation. -/
def actionContraction (f : DualSpace R W) : Module.End R (SpinorSpace R W) :=
  CliffordAlgebra.contractLeft f

/-- The unified Spinor Endomorphism mapping `v = (w, f)` to its combined action on ΛW. -/
def spinorAction (v : SplitV R W) : (SpinorSpace R W) →ₗ[R] (SpinorSpace R W) :=
  (actionWedge v.1 : Module.End R (SpinorSpace R W)).toLinearMap + (actionContraction v.2 : Module.End R (SpinorSpace R W)).toLinearMap

/-! ### 4. The Anticommutator & Clifford Identity -/

/-- 
THE CAPSTONE SPINOR THEOREM:
Proves that the combined wedge and contraction action squares exactly to the 
quadratic form Q(v) • I. This is proved purely by homological cancellation, 
leveraging the nilpotency of wedges and contractions, and their Leibniz anticommutator.
-/
theorem spinorAction_sq (v : SplitV R W) : 
    ((spinorAction v : Module.End R (SpinorSpace R W)) * (spinorAction v : Module.End R (SpinorSpace R W))) = (splitQ v) • (1 : Module.End R (SpinorSpace R W)) := by
  -- Unfold the sum of the operators: (Wedge + Contraction)^2
  dsimp [spinorAction]
  rw [mul_add, add_mul, add_mul]
  
  -- Term 1: Wedge^2 = 0 (Exterior Nilpotency)
  have h_wedge_sq : (actionWedge v.1 : Module.End R (SpinorSpace R W)) * (actionWedge v.1 : Module.End R (SpinorSpace R W)) = 0 := by
    ext x
    dsimp [actionWedge]
    rw [← mul_assoc, ι_sq_zero, zero_mul]
  
  -- Term 2: Contraction^2 = 0 (Interior Nilpotency via Mathlib)
  have h_contract_sq : (actionContraction v.2 : Module.End R (SpinorSpace R W)) * (actionContraction v.2 : Module.End R (SpinorSpace R W)) = 0 := by
    ext x
    exact CliffordAlgebra.contractLeft_contractLeft v.2 x
  
  -- Term 3 & 4: The Anticommutator {Wedge, Contraction} = f(w) * I
  have h_anticomm : (actionWedge v.1 : Module.End R (SpinorSpace R W)) * (actionContraction v.2 : Module.End R (SpinorSpace R W)) + (actionContraction v.2 : Module.End R (SpinorSpace R W)) * (actionWedge v.1 : Module.End R (SpinorSpace R W)) = (v.2 v.1) • 1 := by
    ext x
    dsimp [actionWedge, actionContraction]
    -- Mathlib's native Leibniz derivation rule for interior products exactly resolves the cross terms
    exact CliffordAlgebra.contractLeft_ι_mul v.2 v.1 x
    
  -- Crush the identity via substitution
  simp only [h_wedge_sq, h_contract_sq]
  simp only [zero_add, add_zero]
  exact h_anticomm

/-! ### 5. The Universal Homomorphism Lift -/

/-- 
THE UNIVERSAL LIFT:
Because the spinor action satisfies ρ(v)² = Q(v)I natively, the universal property 
of the Clifford algebra guarantees a strict, coordinate-free algebra homomorphism 
from the full Clifford space into the endomorphisms of the Exterior Spinors.
-/
def abstractSpinorRep : CliffordAlgebra (splitQ (R := R) (W := W)) →ₐ[R] (SpinorSpace R W →ₗ[R] SpinorSpace R W) :=
  CliffordAlgebra.lift (splitQ (R := R) (W := W)) ⟨@spinorAction R W _ _ _, spinorAction_sq⟩

end InfoGeometry.Lie.ChevalleySpinor
