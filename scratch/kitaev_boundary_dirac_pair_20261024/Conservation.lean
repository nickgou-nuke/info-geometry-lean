/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryDiracPair
import InfoGeometry.Canonical.KitaevChainOwnerTransport
import InfoGeometry.Canonical.CARMajoranaOwnerAdapters

/-! Conservation of the actual native boundary Dirac pair. The complex scalar
is the entire bond coefficient; neither self-adjointness nor a spectral phase
classification is inferred. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryDiracConservation

open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair

variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}

theorem endpoint_commutes (ops : MajoranaCliffordOperators N A) (t : ℂ)
    (q : Fin (2 * N)) (hq : q.val = 0 ∨ q.val + 1 = 2 * N) :
    Commute (ops.γ q) (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  rw [sweetSpotHamiltonian_eq_canonical]
  exact sub_eq_zero.mp (CARMajoranaOwnerAdapters.sweetSpot_boundary_commutes
    ops.isMajoranaBasis (algebraMap ℂ A t) q hq (Algebra.commutes t (ops.γ q)).symm)

theorem boundaryAnnihilation_commutes (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (t : ℂ) :
    Commute (boundaryAnnihilation hN ops)
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  have hl := endpoint_commutes ops t ⟨0, by omega⟩ (Or.inl rfl)
  have hr := endpoint_commutes ops t ⟨2 * N - 1, by omega⟩ (Or.inr (by dsimp; omega))
  unfold boundaryAnnihilation boundaryDiracFermion
  exact (Algebra.commutes (1 / 2 : ℂ) _).mul_left
    (hl.add_left ((Algebra.commutes Complex.I _).mul_left hr))

theorem boundaryCreation_commutes (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (t : ℂ) :
    Commute (boundaryCreation hN ops)
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  have hl := endpoint_commutes ops t ⟨0, by omega⟩ (Or.inl rfl)
  have hr := endpoint_commutes ops t ⟨2 * N - 1, by omega⟩ (Or.inr (by dsimp; omega))
  unfold boundaryCreation boundaryDiracFermion
  exact (Algebra.commutes (1 / 2 : ℂ) _).mul_left
    (hl.add_left ((Algebra.commutes (-Complex.I) _).mul_left hr))

theorem boundaryWeylUnit_commutes (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (t : ℂ) :
    Commute (boundaryWeylUnit hN ops : A)
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  rw [boundaryWeylUnit_val, Algebra.smul_def]
  exact (Algebra.commutes Complex.I _).mul_left
    (endpoint_commutes ops t ⟨2 * N - 1, by omega⟩ (Or.inr (by dsimp; omega)))

end InfoGeometry.Canonical.KitaevBoundaryDiracConservation
