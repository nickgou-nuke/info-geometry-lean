/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MetriplecticChiralCl11

/-!
# Concrete Integer Instantiation & Audit for Section 117b: Metriplectic Chiral `Cl(1,1)`
Target: `InfoGeometry/QuantumContext/MetriplecticChiralCl11Audit.lean`

Verifies over `ℤ` (`decide`) and via `#print axioms` that `Cl11Matrix.action`,
`poissonBracket`, `metricBracket`, and `metric_energy_preservation_manifold` evaluate
to exact non-trivial values.
-/

namespace InfoGeometry.QuantumContext.MetriplecticCl11Audit

open InfoGeometry.QuantumContext.MetriplecticCl11
open InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix
open InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem

/-- Concrete verification of `Cl11Matrix.action` associativity on the hyper-spinor sector over `ℤ`. -/
theorem sample_majorana_spinor_action_int :
    let A : Cl11Matrix ℤ := ⟨2, 3, 1, 4⟩
    let B : Cl11Matrix ℤ := ⟨1, -1, 2, 3⟩
    let ψ : MajoranaSpinor ℤ := ⟨5, 2, 3⟩
    action A ψ = ⟨30, 13, 14⟩ ∧
    (action (mul A B) ψ).hyper_left = (action A (action B ψ)).hyper_left ∧
    (action (mul A B) ψ).hyper_right = (action A (action B ψ)).hyper_right := by
  decide

/-- Concrete verification of `poissonBracket`, `metricBracket`, and `canonicalSystem` over `ℤ`. -/
theorem sample_metriplectic_brackets_int :
    let A : Cl11Matrix ℤ := ⟨2, 5, 1, 3⟩
    let B : Cl11Matrix ℤ := ⟨1, 2, 4, 6⟩
    poissonBracket A B = 27 ∧
    poissonBracket B A = -27 ∧
    metricBracket A B = -23 ∧
    metricBracket canonicalSystem.Hamiltonian canonicalSystem.Hamiltonian = 0 ∧
    metricBracket canonicalSystem.Hamiltonian canonicalSystem.Entropy = 0 ∧
    poissonBracket canonicalSystem.Hamiltonian canonicalSystem.Entropy = 0 := by
  decide

#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix.matrix_id_ne_zero
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix.mul_noncommutative
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix.canonicalSpinor_ne_zero
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix.action_hyper_mul_and_singlet_trace
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.Cl11Matrix.yin_yang_reconstruction
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.canonicalSystem_ne_zero
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.poissonBracket_antisymm
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.metricBracket_symm
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.metricBracket_indefinite_over_reals
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.metricBracket_not_positiveSemidefinite
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.poisson_self_null
#print axioms InfoGeometry.QuantumContext.MetriplecticCl11.MetriplecticSystem.metric_energy_preservation_manifold

end InfoGeometry.QuantumContext.MetriplecticCl11Audit
