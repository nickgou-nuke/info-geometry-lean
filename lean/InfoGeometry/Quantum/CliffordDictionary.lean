import InfoGeometry.Krein.DoubledSpace
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
open InfoGeometry.Canonical.TomitaTakesaki

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
  anticomm := modularConjugationJ_anticommutes_modularSign (E := E)
  K_def := by
    rfl
  K_sq := modularComplexI_sq (E := E)

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
