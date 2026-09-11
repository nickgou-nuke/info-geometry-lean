import InfoGeometry.Quantum.InvolutionCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Anticommuting Involution Core

The split-Clifford / Majorana branch of the doubled-space algebra: two
involutions that anticommute. Their product is the derived square-minus-one axis.
-/

namespace InfoGeometry.Quantum

/-- Two anticommuting involutions on a real-linear carrier. -/
structure AnticommutingInvolutionCore extends InvolutionCore where
  J_eps_anticomm : toInvolutionCore.J.comp toInvolutionCore.eps
    = -(toInvolutionCore.eps.comp toInvolutionCore.J)

namespace AnticommutingInvolutionCore

instance : CoeSort AnticommutingInvolutionCore (Type u) :=
  ⟨fun X => X.toInvolutionCore.V⟩

instance instAddCommGroupCarrier (X : AnticommutingInvolutionCore) : AddCommGroup X :=
  X.toInvolutionCore.instAddCommGroup

instance instModuleCarrier (X : AnticommutingInvolutionCore) : Module ℝ X :=
  X.toInvolutionCore.instModule

/-- The derived square-minus-one axis `K := J ∘ ε`. -/
noncomputable def K (X : AnticommutingInvolutionCore) : X →ₗ[ℝ] X :=
  X.toInvolutionCore.je

@[simp] theorem K_def (X : AnticommutingInvolutionCore) :
    X.K = X.J.comp X.eps := rfl

lemma eps_comp_J (X : AnticommutingInvolutionCore) :
    X.eps.comp X.J = -(X.J.comp X.eps) := by
  have hneg : -(X.J.comp X.eps) = X.eps.comp X.J := by
    simpa using congrArg Neg.neg X.J_eps_anticomm
  simpa [eq_comm] using hneg

/-- The derived axis squares to `-Id`. -/
lemma K_sq (X : AnticommutingInvolutionCore) :
    X.K.comp X.K = -((LinearMap.id : X →ₗ[ℝ] X)) := by
  unfold K InvolutionCore.je
  calc
    (X.J.comp X.eps).comp (X.J.comp X.eps)
        = X.J.comp ((X.eps.comp X.J).comp X.eps) := by
            simp [LinearMap.comp_assoc]
    _ = X.J.comp ((-(X.J.comp X.eps)).comp X.eps) := by rw [X.eps_comp_J]
    _ = -((X.J.comp X.J).comp (X.eps.comp X.eps)) := by
          ext x
          simp [LinearMap.comp_assoc]
    _ = -((LinearMap.id : X →ₗ[ℝ] X)) := by
          simp [X.J_sq, X.eps_sq]

lemma j_comp_k (X : AnticommutingInvolutionCore) :
    X.J.comp X.K = X.eps := by
  unfold K InvolutionCore.je
  calc
    X.J.comp (X.J.comp X.eps) = (X.J.comp X.J).comp X.eps := by
      simp [LinearMap.comp_assoc]
    _ = X.eps := by simp [X.J_sq]

lemma k_comp_j (X : AnticommutingInvolutionCore) :
    X.K.comp X.J = -X.eps := by
  unfold K InvolutionCore.je
  calc
    (X.J.comp X.eps).comp X.J = X.J.comp (X.eps.comp X.J) := by
      simp [LinearMap.comp_assoc]
    _ = X.J.comp (-(X.J.comp X.eps)) := by rw [X.eps_comp_J]
    _ = -((X.J.comp X.J).comp X.eps) := by
          ext x
          simp [LinearMap.comp_assoc]
    _ = -X.eps := by simp [X.J_sq]

lemma eps_comp_k (X : AnticommutingInvolutionCore) :
    X.eps.comp X.K = -X.J := by
  unfold K InvolutionCore.je
  calc
    X.eps.comp (X.J.comp X.eps) = (X.eps.comp X.J).comp X.eps := by
      simp [LinearMap.comp_assoc]
    _ = (-(X.J.comp X.eps)).comp X.eps := by rw [X.eps_comp_J]
    _ = -(X.J.comp (X.eps.comp X.eps)) := by
          ext x
          simp [LinearMap.comp_assoc]
    _ = -X.J := by simp [X.eps_sq]

lemma k_comp_eps (X : AnticommutingInvolutionCore) :
    X.K.comp X.eps = X.J := by
  unfold K InvolutionCore.je
  calc
    (X.J.comp X.eps).comp X.eps = X.J.comp (X.eps.comp X.eps) := by
      simp [LinearMap.comp_assoc]
    _ = X.J := by simp [X.eps_sq]

end AnticommutingInvolutionCore

end InfoGeometry.Quantum
