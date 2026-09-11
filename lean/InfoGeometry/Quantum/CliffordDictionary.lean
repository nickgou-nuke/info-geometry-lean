import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# Cl(1,1) Seed Dictionary (Real Majorana Bridge)

This module formalizes the Cl(1,1) Clifford atom on the doubled real Krein carrier.
It identifies chirality, conjugation, and phase as emergent geometric data.

## The Semantic Mapping (Cl(1,1) Seed)
- **Chirality (γ₅)** ↔ `modularSignEpsilon` (ε)
- **Conjugation (Γ⁰)** ↔ `modularConjugationJ` (J)
- **Internal Complex Structure** ↔ `modularComplexI` (K = J ∘ ε)

This "atomic seed" provides the minimal substrate for chirality, conjugation, 
and phase before any complex structure is primitives.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Quantum
open TomitaTakesaki

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 
**Cl(1,1) Atomic Dictionary**:
Structural identification of split-signature generators.
-/
structure Cl11Dictionary (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Graduation/Chirality operator squaring to +1. -/
  ε : DoubledSpace E →L[ℝ] DoubledSpace E
  /-- Conjugation/Fundamental symmetry squaring to +1. -/
  J : DoubledSpace E →L[ℝ] DoubledSpace E
  /-- Internal complex structure K = J ∘ ε squaring to -1. -/
  K : DoubledSpace E →L[ℝ] DoubledSpace E
  ε_inv : ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E)
  J_inv : J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E)
  anticomm : J.comp ε = -(ε.comp J)
  K_def : K = J.comp ε
  K_sq : K.comp K = -(ContinuousLinearMap.id ℝ (DoubledSpace E))

namespace Cl11Dictionary

/-- Canonical dictionary instance for the doubled real model. -/
noncomputable def canonical : Cl11Dictionary E where
  ε := modularSignEpsilon (E := E)
  J := modularConjugationJ (E := E)
  K := modularComplexI (E := E)
  ε_inv := modularSignEpsilon_sq (E := E)
  J_inv := modularConjugationJ_sq (E := E)
  anticomm := InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_anticommutes_modularSign (E := E)
  K_def := by
    rfl
  K_sq := modularComplexI_sq (E := E)

@[simp] theorem canonical_eps_eq_spectral_epsilon :
    (canonical (E := E)).ε = spectral_epsilon (E := E) := by
  simp [canonical, modularSignEpsilon_eq_spectral_epsilon]

@[simp] theorem canonical_J_eq_modular_j :
    (canonical (E := E)).J = modular_j (E := E) := by
  simp [canonical, modularConjugationJ_eq_modular_j]

@[simp] theorem canonical_K_eq_complex_i :
    (canonical (E := E)).K = complex_i (E := E) := by
  simp [canonical, modularComplexI_eq_complex_i]

/-- The canonical chirality atom is the Tomita-named modular sign `ε`. -/
@[simp] theorem canonical_eps_eq_modularSignEpsilon :
    (canonical (E := E)).ε = modularSignEpsilon (E := E) := by
  rfl

/-- The canonical conjugation atom is the Tomita-named modular conjugation `J`. -/
@[simp] theorem canonical_J_eq_modularConjugationJ :
    (canonical (E := E)).J = modularConjugationJ (E := E) := by
  rfl

/-- The canonical phase atom is the Tomita-named composite `Jε`. -/
@[simp] theorem canonical_K_eq_modularComplexI :
    (canonical (E := E)).K = modularComplexI (E := E) := by
  rfl

@[simp] theorem canonical_eps_sq :
    ((canonical (E := E)).ε).comp ((canonical (E := E)).ε) =
      ContinuousLinearMap.id ℝ H₂ :=
  (canonical (E := E)).ε_inv

@[simp] theorem canonical_J_sq :
    ((canonical (E := E)).J).comp ((canonical (E := E)).J) =
      ContinuousLinearMap.id ℝ H₂ :=
  (canonical (E := E)).J_inv

@[simp] theorem canonical_K_sq :
    ((canonical (E := E)).K).comp ((canonical (E := E)).K) =
      -(ContinuousLinearMap.id ℝ H₂) :=
  (canonical (E := E)).K_sq

/-- The canonical atoms satisfy `Jε = K`. -/
@[simp] theorem canonical_J_comp_eps :
    ((canonical (E := E)).J).comp ((canonical (E := E)).ε) =
      (canonical (E := E)).K := by
  exact (canonical (E := E)).K_def.symm

/-- The reversed product satisfies `εJ = -K`. -/
@[simp] theorem canonical_eps_comp_J :
    ((canonical (E := E)).ε).comp ((canonical (E := E)).J) =
      -((canonical (E := E)).K) := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (spectral_epsilon_comp_modular_j (E := E))

/-- Multiplication by `J` sends the phase atom back to the sign atom. -/
@[simp] theorem canonical_J_comp_K :
    ((canonical (E := E)).J).comp ((canonical (E := E)).K) =
      (canonical (E := E)).ε := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (modular_j_comp_complex_i (E := E))

/-- Right multiplication by `J` sends the phase atom to minus the sign atom. -/
@[simp] theorem canonical_K_comp_J :
    ((canonical (E := E)).K).comp ((canonical (E := E)).J) =
      -((canonical (E := E)).ε) := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (complex_i_comp_modular_j (E := E))

/-- Multiplication by `ε` sends the phase atom to minus the conjugation atom. -/
@[simp] theorem canonical_eps_comp_K :
    ((canonical (E := E)).ε).comp ((canonical (E := E)).K) =
      -((canonical (E := E)).J) := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (spectral_epsilon_comp_complex_i (E := E))

/-- Right multiplication by `ε` sends the phase atom back to conjugation. -/
@[simp] theorem canonical_K_comp_eps :
    ((canonical (E := E)).K).comp ((canonical (E := E)).ε) =
      (canonical (E := E)).J := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (complex_i_comp_spectral_epsilon (E := E))

/-- The modular sign is block-diagonal on the doubled real carrier. -/
@[simp] theorem canonical_eps_to_doubled (x ξ : E) :
    (canonical (E := E)).ε (to_doubled x ξ : H₂) = to_doubled x (-ξ) := by
  rfl

/-- Modular conjugation is the off-block swap on the doubled real carrier. -/
@[simp] theorem canonical_J_to_doubled (x ξ : E) :
    (canonical (E := E)).J (to_doubled x ξ : H₂) = to_doubled ξ x := by
  rfl

/-- The composite `Jε` is the signed off-block phase axis. -/
@[simp] theorem canonical_K_to_doubled (x ξ : E) :
    (canonical (E := E)).K (to_doubled x ξ : H₂) = to_doubled (-ξ) x := by
  simpa [canonical, modularComplexI_eq_complex_i]
    using (complex_i_to_doubled (E := E) x ξ)

/-- The canonical conjugation atom is even for the modular block grading. -/
theorem canonical_J_isEven :
    isEven (E := E) (canonical (E := E)).J := by
  simpa [canonical] using InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_isEven (E := E)

/-- The canonical sign atom is odd for the modular block grading. -/
theorem canonical_eps_isOdd :
    isOdd (E := E) (canonical (E := E)).ε := by
  simpa [canonical] using InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_isOdd (E := E)

/-- The canonical phase atom `Jε` is odd for the modular block grading. -/
theorem canonical_K_isOdd :
    isOdd (E := E) (canonical (E := E)).K := by
  simpa [canonical] using InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_isOdd (E := E)

section SpinorObservables

/-- 
**Operator Channel**:
Bilinear expectation value computed via the Krein inner product.
This is the physical substrate for spinor bilinears.
-/
noncomputable def operatorObservable (u v : H₂) (O : EndH) : ℝ :=
  KreinSpace.kreinInner (H := H₂) u (O v)

/-- **Scalar Channel**: The Dirac/Krein norm channel $\langle \psi, \psi \rangle_{K}$. -/
noncomputable def scalarObservable (ψ : H₂) : ℝ := 
  operatorObservable ψ ψ (ContinuousLinearMap.id ℝ _)

/-- **Chirality Channel**: The $\gamma_5$ channel $\langle \psi, \varepsilon \psi \rangle_{K}$. -/
noncomputable def chiralityObservable (ψ : H₂) : ℝ :=
  operatorObservable ψ ψ (modularSignEpsilon (E := E))

/-- **Phase Channel**: The complex phase channel $\langle \psi, K \psi \rangle_{K}$. -/
noncomputable def phaseObservable (ψ : H₂) : ℝ :=
  operatorObservable ψ ψ (modularComplexI (E := E))

@[simp] theorem chiralityObservable_eq_operatorObservable_spectral_epsilon
    (ψ : H₂) :
    chiralityObservable (E := E) ψ =
      operatorObservable (E := E) ψ ψ (spectral_epsilon (E := E)) := by
  rfl

@[simp] theorem phaseObservable_eq_operatorObservable_complex_i
    (ψ : H₂) :
    phaseObservable (E := E) ψ =
      operatorObservable (E := E) ψ ψ (complex_i (E := E)) := by
  simp [phaseObservable, modularComplexI_eq_complex_i]

/-- 
**Spinor Normalization**:
A state is normalized if its scalar observable channel is unity.
-/
def IsNormalizedSpinor (ψ : H₂) : Prop :=
  scalarObservable (E := E) ψ = 1

/--
**Geometric Metric Realization**:
A bridge predicate identifying the symmetric component of the QGT with the
physical scalar channel (Krein norm) on the doubled carrier.
This bridge is defined here to avoid circular dependencies with the core QGT layer.
-/
def QGTRealizesScalarObservable (Q : QGT E) : Prop :=
  ∀ ψ, Q.g ψ ψ = scalarObservable (E := E) ψ

end SpinorObservables

end Cl11Dictionary

end InfoGeometry.Quantum
