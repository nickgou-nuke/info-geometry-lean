import Mathlib

namespace InfoGeometry.Physics

/-! A small algebraic owner for a supergraded Dirac symbol.  It records only
the parity, oddness, and square relations; no spectral or topological claim is
encoded here. -/

structure SupergradedDiracSystem (V : Type*) [AddCommGroup V] [Module ℚ V] where
  Gamma : V →ₗ[ℚ] V
  Q : V →ₗ[ℚ] V
  H : V →ₗ[ℚ] V
  gamma_sq : Gamma.comp Gamma = LinearMap.id
  witten_odd : Gamma.comp Q = - Q.comp Gamma
  susy_algebra : Q.comp Q = H

namespace SupergradedDiracSystem

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (data : SupergradedDiracSystem V)

theorem hamiltonian_even :
    data.Gamma.comp data.H = data.H.comp data.Gamma := by
  rw [← data.susy_algebra]
  calc
    data.Gamma.comp (data.Q.comp data.Q) =
        (data.Gamma.comp data.Q).comp data.Q := by
          rw [LinearMap.comp_assoc]
    _ = (- data.Q.comp data.Gamma).comp data.Q := by
          rw [data.witten_odd]
    _ = - (data.Q.comp (data.Gamma.comp data.Q)) := by
          simp only [LinearMap.neg_comp, LinearMap.comp_assoc]
    _ = - (data.Q.comp (- data.Q.comp data.Gamma)) := by
          rw [data.witten_odd]
    _ = data.Q.comp (data.Q.comp data.Gamma) := by
          simp only [LinearMap.comp_neg, neg_neg]

def parityWeightedHamiltonian : V →ₗ[ℚ] V := data.Gamma.comp data.H

theorem parityWeightedHamiltonian_odd :
    (parityWeightedHamiltonian data).comp data.Q =
      - data.Q.comp (parityWeightedHamiltonian data) := by
  rw [parityWeightedHamiltonian, ← data.susy_algebra]
  calc
    (data.Gamma.comp (data.Q.comp data.Q)).comp data.Q =
        (data.Gamma.comp data.Q).comp (data.Q.comp data.Q) := by
          simp only [LinearMap.comp_assoc]
    _ = (- data.Q.comp data.Gamma).comp (data.Q.comp data.Q) := by
          rw [data.witten_odd]
    _ = - data.Q.comp (data.Gamma.comp (data.Q.comp data.Q)) := by
          simp only [LinearMap.neg_comp, LinearMap.comp_assoc]

end SupergradedDiracSystem
end InfoGeometry.Physics
