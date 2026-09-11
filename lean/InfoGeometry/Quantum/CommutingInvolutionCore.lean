import InfoGeometry.Quantum.InvolutionCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Commuting Involution Core

The Boolean/discrete branch of the doubled-space algebra: two involutions that
commute. Their product is again an involution and gives the fourth corner of
the Klein-four skeleton.
-/

namespace InfoGeometry.Quantum

/-- Two commuting involutions on a real-linear carrier. -/
structure CommutingInvolutionCore extends InvolutionCore where
  J_eps_comm : toInvolutionCore.J.comp toInvolutionCore.eps
    = toInvolutionCore.eps.comp toInvolutionCore.J

namespace CommutingInvolutionCore

instance : CoeSort CommutingInvolutionCore (Type u) :=
  ⟨fun X => X.toInvolutionCore.V⟩

instance instAddCommGroupCarrier (X : CommutingInvolutionCore) : AddCommGroup X :=
  X.toInvolutionCore.instAddCommGroup

instance instModuleCarrier (X : CommutingInvolutionCore) : Module ℝ X :=
  X.toInvolutionCore.instModule

/-- The fourth Klein-four corner `Jε`. -/
noncomputable def je (X : CommutingInvolutionCore) : X →ₗ[ℝ] X :=
  X.toInvolutionCore.je

@[simp] theorem je_def (X : CommutingInvolutionCore) :
    X.je = X.J.comp X.eps := rfl

@[simp] theorem je_comm (X : CommutingInvolutionCore) :
    X.J.comp X.eps = X.eps.comp X.J :=
  X.J_eps_comm

@[simp] theorem je_comm_apply (X : CommutingInvolutionCore) (x : X) :
    X.J (X.eps x) = X.eps (X.J x) := by
  exact congrArg (fun f : X →ₗ[ℝ] X => f x) X.J_eps_comm

/-- The product of two commuting involutions is again an involution. -/
lemma je_sq (X : CommutingInvolutionCore) :
    X.je.comp X.je = (LinearMap.id : X →ₗ[ℝ] X) := by
  ext x
  change X.J (X.eps (X.J (X.eps x))) = x
  rw [X.je_comm_apply]
  simp

lemma j_comp_je (X : CommutingInvolutionCore) :
    X.J.comp X.je = X.eps := by
  ext x
  change X.J (X.J (X.eps x)) = X.eps x
  simp

lemma je_comp_j (X : CommutingInvolutionCore) :
    X.je.comp X.J = X.eps := by
  ext x
  change X.J (X.eps (X.J x)) = X.eps x
  rw [X.je_comm_apply]
  simp

lemma eps_comp_je (X : CommutingInvolutionCore) :
    X.eps.comp X.je = X.J := by
  ext x
  change X.eps (X.J (X.eps x)) = X.J x
  rw [X.je_comm_apply]
  simp

lemma je_comp_eps (X : CommutingInvolutionCore) :
    X.je.comp X.eps = X.J := by
  ext x
  change X.J (X.eps (X.eps x)) = X.J x
  simp

/-- The four canonical corners `{1, J, ε, Jε}` are closed under the expected actions. -/
theorem commuting_involution_four_corners (X : CommutingInvolutionCore) :
    X.J.comp X.je = X.eps
      ∧ X.je.comp X.J = X.eps
      ∧ X.eps.comp X.je = X.J
      ∧ X.je.comp X.eps = X.J := by
  exact ⟨X.j_comp_je, X.je_comp_j, X.eps_comp_je, X.je_comp_eps⟩

end CommutingInvolutionCore

end InfoGeometry.Quantum
