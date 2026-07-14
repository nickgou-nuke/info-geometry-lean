import InfoGeometry.Quantum.CliffordDictionary
import InfoGeometry.Quantum.GeometricTensor

/-!
# Verification: Cl(1,1) Seed Dictionary

This module verifies the structural identities of the Cl(1,1) atom and 
the QGT identifies derived from the Kähler compatibility.
-/

namespace CliffordDictionaryTest

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Quantum.Cl11Dictionary
open InfoGeometry.Canonical.TomitaTakesaki

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 
**Structural Verification**:
Verify the anticommutation of chirality and conjugation and its synthesis 
of the complex structure.
-/
theorem cl11_structural_identities :
    let d := Cl11Dictionary.canonical (E := E)
    d.ε.comp d.ε = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    d.J.comp d.J = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    d.J.comp d.ε = -(d.ε.comp d.J) ∧
    d.K.comp d.K = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  let d := Cl11Dictionary.canonical (E := E)
  exact ⟨d.ε_inv, d.J_inv, d.anticomm, d.K_sq⟩

/--
**Berry Phase Theorem**:
On the diagonal channel $\psi$, the Berry curvature evaluated on the 
phase-shifted state $K\psi$ is exactly the value of the metric.
This is the core QGT/Kähler identity for the real doubled carrier.
-/
theorem berry_on_phase_eq_metric_diag
    (Q : QGT E)
    (h_skew : ∀ u v, Q.g (modularComplexI (E := E) u) v = - Q.g u (modularComplexI (E := E) v))
    (ψ : H₂) :
    Q.Ω ψ (modularComplexI (E := E) ψ) = Q.g ψ ψ := by
  calc
    Q.Ω ψ (modularComplexI (E := E) ψ)
        = Q.g (modularComplexI (E := E) ψ) (modularComplexI (E := E) ψ) :=
          Q.compat ψ (modularComplexI (E := E) ψ)
    _ = - Q.g ψ (modularComplexI (E := E) (modularComplexI (E := E) ψ)) := by
          simpa using h_skew ψ (modularComplexI (E := E) ψ)
    _ = - Q.g ψ (-ψ) := by
          have hsq : modularComplexI (E := E) (modularComplexI (E := E) ψ) = -ψ := by
            apply DoubledSpace.ext <;> simp [modularComplexI]
          rw [hsq]
    _ = Q.g ψ ψ := by simp

/--
**Phase Channel Formula**:
On the canonical doubled Krein carrier `ψ = (x, ξ)`, the phase observable is the
real off-diagonal cross term `-2 ⟪x, ξ⟫`.
-/
theorem phase_observable_eq_neg_two_mul_inner_fst_snd (ψ : H₂) :
    phaseObservable (E := E) ψ
      = -(2 : ℝ) * @inner ℝ E _ (WithLp.fst ψ) (WithLp.snd ψ) := by
  rw [phaseObservable, operatorObservable, krein_inner_prod_l2]
  simp [modularComplexI, InfoGeometry.Krein.complex_i_apply,
    sub_eq_add_neg, real_inner_comm, two_mul]

end CliffordDictionaryTest
