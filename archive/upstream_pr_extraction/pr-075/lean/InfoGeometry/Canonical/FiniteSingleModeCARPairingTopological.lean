import InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Finite CAR Hermitian pairing and its topological readout

The owner uses `Bool → ℂ`, for which Mathlib does not install an
`InnerProductSpace ℂ` instance.  We therefore state the finite Hermitian
pairing explicitly and prove the creation/annihilation adjoint identity
relative to that pairing, without pretending it is a bundled Hilbert adjoint.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCARPairingTopological

open InfoGeometry.Algebra.FiniteSingleModeCAR
open CategoryTheory

def oneModePairing (ψ φ : OneModeVec) : ℂ :=
  star (ψ false) * φ false + star (ψ true) * φ true

theorem ann_cre_adjoint_pairing (ψ φ : OneModeVec) :
    oneModePairing (ann ψ) φ = oneModePairing ψ (cre φ) := by
  simp [oneModePairing, ann, cre]

theorem oneModePairing_conj_symm (ψ φ : OneModeVec) :
    star (oneModePairing ψ φ) = oneModePairing φ ψ := by
  simp [oneModePairing, mul_comm]

theorem oneModePairing_self_nonneg (ψ : OneModeVec) :
    0 ≤ (oneModePairing ψ ψ).re := by
  have h0 : (star (ψ false) * ψ false).re = Complex.normSq (ψ false) := by
    rw [mul_comm]
    exact congrArg Complex.re (Complex.mul_conj (ψ false))
  have h1 : (star (ψ true) * ψ true).re = Complex.normSq (ψ true) := by
    rw [mul_comm]
    exact congrArg Complex.re (Complex.mul_conj (ψ true))
  rw [oneModePairing, Complex.add_re, h0, h1]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

def oneModePairingContinuousMap :
    ContinuousMap (OneModeVec × OneModeVec) ℂ :=
  { toFun := fun p => oneModePairing p.1 p.2
    continuous_toFun := by
      have hψ0 : Continuous (fun p : OneModeVec × OneModeVec => star (p.1 false)) :=
        Complex.continuous_conj.comp ((continuous_apply false).comp continuous_fst)
      have hφ0 : Continuous (fun p : OneModeVec × OneModeVec => p.2 false) :=
        (continuous_apply false).comp continuous_snd
      have hψ1 : Continuous (fun p : OneModeVec × OneModeVec => star (p.1 true)) :=
        Complex.continuous_conj.comp ((continuous_apply true).comp continuous_fst)
      have hφ1 : Continuous (fun p : OneModeVec × OneModeVec => p.2 true) :=
        (continuous_apply true).comp continuous_snd
      exact (hψ0.mul hφ0).add (hψ1.mul hφ1) }

def oneModePairingTopCatHom :
    TopCat.of (OneModeVec × OneModeVec) ⟶ TopCat.of ℂ :=
  TopCat.ofHom oneModePairingContinuousMap

@[simp] theorem oneModePairingContinuousMap_apply (ψ φ : OneModeVec) :
    oneModePairingContinuousMap (ψ, φ) =
      oneModePairing ψ φ :=
  rfl

end InfoGeometry.Canonical.FiniteSingleModeCARPairingTopological
