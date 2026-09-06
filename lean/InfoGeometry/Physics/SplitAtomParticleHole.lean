import InfoGeometry.Clifford.SplitAtomInvolutions
import Mathlib.Data.Complex.Basic

/-!
# Particle-hole conjugation is antilinear, not a signed algebra automorphism

On C², swap followed by scalar conjugation defines a real-linear involution
and preserves the Hermitian pairing with conjugation.  The diagonal two-level
Hamiltonian provides an explicit particle-hole-symmetric family.  This is not
an identification with a relativistic CPT operator or a general BdG model.
-/

noncomputable section

namespace InfoGeometry.Physics.SplitAtomParticleHole

abbrev Spinor := Fin 2 → ℂ
abbrev CMat2 := Matrix (Fin 2) (Fin 2) ℂ

def particleHole (v : Spinor) : Spinor := ![star (v 1), star (v 0)]

@[simp] theorem particleHole_twice (v : Spinor) :
    particleHole (particleHole v) = v := by
  funext i
  fin_cases i <;> simp [particleHole]

def particleHoleRealLinear : Spinor →ₗ[ℝ] Spinor where
  toFun := particleHole
  map_add' u v := by
    funext i
    fin_cases i <;> simp [particleHole]
  map_smul' r v := by
    funext i
    fin_cases i <;> simp [particleHole]

/-- The real-linear equivalence retains, rather than erases, antilinearity. -/
def particleHoleEquiv : Spinor ≃ₗ[ℝ] Spinor :=
  LinearEquiv.ofInvolutive particleHoleRealLinear particleHole_twice

theorem particleHole_complex_smul (z : ℂ) (v : Spinor) :
    particleHole (z • v) = star z • particleHole v := by
  funext i
  fin_cases i <;> simp [particleHole, mul_comm]

theorem particleHole_pairing (u v : Spinor) :
    dotProduct (star (particleHole u)) (particleHole v) =
      star (dotProduct (star u) v) := by
  simp [particleHole, dotProduct, Fin.sum_univ_two, mul_comm, add_comm]

def hamiltonian (energy : ℝ) : CMat2 :=
  !![(energy : ℂ), 0; 0, -(energy : ℂ)]

theorem hamiltonian_self_adjoint (energy : ℝ) :
    (hamiltonian energy).conjTranspose = hamiltonian energy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, Matrix.conjTranspose_apply, Complex.star_def]

theorem particleHole_hamiltonian (energy : ℝ) (v : Spinor) :
    particleHole (Matrix.mulVec (hamiltonian energy) v) =
      -(Matrix.mulVec (hamiltonian energy) (particleHole v)) := by
  funext i
  fin_cases i <;>
    simp [particleHole, hamiltonian, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.star_def, mul_comm]

/-- A real eigenvalue is paired with its negative on the concrete family. -/
theorem particleHole_eigenpair (energy eigenvalue : ℝ) (v : Spinor)
    (hv : v ≠ 0)
    (heig : Matrix.mulVec (hamiltonian energy) v = (eigenvalue : ℂ) • v) :
    particleHole v ≠ 0 ∧
      Matrix.mulVec (hamiltonian energy) (particleHole v) =
        (-eigenvalue : ℂ) • particleHole v := by
  constructor
  · intro h
    apply hv
    have ht := congrArg particleHole h
    have ht' : v 0 = 0 ∧ v 1 = 0 := by
      simpa [particleHole] using ht
    funext i
    fin_cases i
    · exact ht'.1
    · exact ht'.2
  · have h := congrArg particleHole heig
    rw [particleHole_hamiltonian, particleHole_complex_smul] at h
    have hn := congrArg (fun w : Spinor => -w) h
    simpa [Complex.star_def] using hn

end InfoGeometry.Physics.SplitAtomParticleHole
