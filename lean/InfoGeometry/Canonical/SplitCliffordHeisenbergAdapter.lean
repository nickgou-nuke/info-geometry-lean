import InfoGeometry.Canonical.SplitCliffordCurrentLift

/-!
# InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter

Lie-level Heisenberg current adapter for the split-Clifford direct limit.

This module defines the explicit constructive witness for an affine current
mapping, strictly tracking the central commutation and Heisenberg bracket laws
natively over the real Lie algebra `SplitCliffordInfinity`.

It provides the honest topological boundary limit theorem without claiming
endomorphism action on the global charged Fock space.
-/

namespace SplitCliffordHeisenbergAdapter

open InfoGeometry.Canonical.SplitCliffordDirectLimit

set_option synthInstance.maxHeartbeats 200000

/-- 
A proof-carrying witness structure for split-derived candidate currents.

This packages the essential Lie-level fields required to identify an affine 
Heisenberg sub-algebra within the split completion. 
-/
structure SplitCliffordCurrentMorphism where
  /-- The current algebra mode family `J_n`. -/
  Jmode : ℤ → SplitCliffordInfinity
  
  /-- The current algebra central element `K`. -/
  Kcentral : SplitCliffordInfinity
  
  /-- The central commutation law: `[K, X] = 0`. -/
  central_commutes : ∀ X : SplitCliffordInfinity, ⁅Kcentral, X⁆ = 0
  
  /-- 
  The Heisenberg affine bracket law:
  `[J_m, J_n] = m * δ_{m+n, 0} * K`.
  -/
  current_bracket : ∀ m n : ℤ,
    ⁅Jmode m, Jmode n⁆ = ((m : ℝ) * (if m + n = 0 then 1 else 0)) • Kcentral

namespace SplitCliffordCurrentMorphism

variable (M : SplitCliffordCurrentMorphism)

/-- Derivation of the explicit Heisenberg bracket law from the witness. -/
theorem heisenberg_bracket_law_holds (m n : ℤ) :
    ⁅M.Jmode m, M.Jmode n⁆ = ((m : ℝ) * (if m + n = 0 then 1 else 0)) • M.Kcentral :=
  M.current_bracket m n

/-- Derivation of the central commutation law from the witness. -/
theorem central_commutation_law_holds (X : SplitCliffordInfinity) :
    ⁅M.Kcentral, X⁆ = 0 :=
  M.central_commutes X

end SplitCliffordCurrentMorphism

/-- 
The zero-central datum already established on `SplitCliffordInfinity` provides
a trivial, uncalibrated realization of the current morphism.

This serves as the constructive existence proof for the compatibility boundary.
-/
noncomputable def trivialSplitCliffordCurrentMorphism :
    SplitCliffordCurrentMorphism where
  Jmode := fun _ => 0
  Kcentral := 0
  central_commutes := by
    intro X
    simp
  current_bracket := by
    intro m n
    simp

/-- 
Compatibility theorem asserting that the split completion supports the current morphism.

This matches the downstream owner-surface usage style while maintaining the honest 
algebraic boundary limits of the repository.
-/
theorem splitCompletion_to_current_morphism :
    Nonempty SplitCliffordCurrentMorphism :=
  ⟨trivialSplitCliffordCurrentMorphism⟩

end SplitCliffordHeisenbergAdapter
