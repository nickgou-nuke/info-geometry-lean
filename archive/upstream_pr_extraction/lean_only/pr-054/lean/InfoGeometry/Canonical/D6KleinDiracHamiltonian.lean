import InfoGeometry.Canonical.D6KleinBrillouinBands
import InfoGeometry.Canonical.D6DiracSpectralBridge
import Mathlib.Tactic

/-!
# Glide-invariant finite Hamiltonian readout

The orbit sum is the minimal honest way to obtain a Hamiltonian on the finite
Klein quotient: it is invariant under the generating glide before any band
readout is taken.
-/

namespace InfoGeometry.Canonical.D6KleinDiracHamiltonian

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
open InfoGeometry.Canonical.D6DiracSpectralBridge

def orbitSum {α : Type*} [AddCommMonoid α]
    (H : TorusCell → α) (p : TorusCell) : α :=
  H p + H (glide p) + H (glide2 p) + H (glide3 p)

theorem orbitSum_glide {α : Type*} [AddCommMonoid α]
    (H : TorusCell → α) (p : TorusCell) :
    orbitSum H (glide p) = orbitSum H p := by
  unfold orbitSum
  have h₁ : glide (glide p) = glide2 p := rfl
  have h₂ : glide2 (glide p) = glide3 p := rfl
  rw [h₁, h₂, glide3_glide]
  simp only [add_assoc, add_comm]

def finiteDiracHamiltonian (p : TorusCell) : H2 :=
  diracBlock 0 (p.1.val : ℝ) (p.2.val : ℝ)

def glideInvariantDiracHamiltonian (p : TorusCell) : H2 :=
  orbitSum finiteDiracHamiltonian p

def orbitX (p : TorusCell) : ℝ :=
  (p.1.val : ℝ) + (glide p).1.val + (glide2 p).1.val + (glide3 p).1.val

def orbitY (p : TorusCell) : ℝ :=
  (p.2.val : ℝ) + (glide p).2.val + (glide2 p).2.val + (glide3 p).2.val

theorem glideInvariantDiracHamiltonian_eq_diracBlock (p : TorusCell) :
    glideInvariantDiracHamiltonian p = diracBlock 0 (orbitX p) (orbitY p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glideInvariantDiracHamiltonian, orbitSum, finiteDiracHamiltonian,
      orbitX, orbitY, diracBlock, Matrix.add_apply]

theorem glideInvariantDiracHamiltonian_shiftedDeterminant
    (p : TorusCell) (lam : ℝ) :
    shiftedDeterminant (glideInvariantDiracHamiltonian p) lam =
      lam ^ 2 - orbitX p * orbitY p := by
  rw [glideInvariantDiracHamiltonian_eq_diracBlock]
  simpa [pow_two] using
    (diracBlock_shiftedDeterminant 0 (orbitX p) (orbitY p) lam)

theorem glideInvariantDiracHamiltonian_glide (p : TorusCell) :
    glideInvariantDiracHamiltonian (glide p) =
      glideInvariantDiracHamiltonian p := by
  exact orbitSum_glide finiteDiracHamiltonian p

end InfoGeometry.Canonical.D6KleinDiracHamiltonian
