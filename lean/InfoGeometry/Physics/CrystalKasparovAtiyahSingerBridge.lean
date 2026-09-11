import InfoGeometry.Physics.AlgebraicAtiyahSingerIndex
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SupergradedDiracCrystal

namespace InfoGeometry.Physics

/-!
# Dirac-crystal bridge to the algebraic index shadow

This file identifies the finite algebraic data shared by a supergraded Dirac
crystal and an idempotent supertrace pairing.  It does not assert a spectral
gap, a Fredholm index, or the analytic Atiyah--Singer theorem.
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

structure RealDiracCrystal (A : Type*) [Ring A] [Algebra ℝ A] where
  Gamma : A
  Gamma_sq : Gamma * Gamma = 1
  Q : A
  Q_odd : Gamma * Q = -(Q * Gamma)
  H : A
  susy_algebra : Q * Q = H
  Tr : A →ₗ[ℝ] ℝ
  Tr_comm : ∀ X Y, Tr (X * Y) = Tr (Y * X)

def crystalIndexData (cryst : RealDiracCrystal A) : AlgebraicIndexData A :=
  { Tr := cryst.Tr
    Gamma := cryst.Gamma }

theorem crystal_witten_index_zero (cryst : RealDiracCrystal A) :
    superTrace cryst.Tr cryst.Gamma cryst.H = 0 := by
  have hQ_odd : cryst.Gamma * cryst.Q = -cryst.Q * cryst.Gamma := by
    simpa only [neg_mul] using cryst.Q_odd
  simpa [superTrace, cryst.susy_algebra] using
    (mckean_singer_cancellation cryst.Tr cryst.Tr_comm
      cryst.Gamma cryst.Q hQ_odd)

def ValenceBandBundle
    (cryst : RealDiracCrystal A) (E : A)
    (hE_sq : E * E = E)
    (hE_even : cryst.Gamma * E = E * cryst.Gamma) :
    KTheoryVectorBundle A (crystalIndexData cryst) :=
  ⟨E, ⟨hE_sq, hE_even⟩⟩

theorem crystal_valence_band_pairing_identity
    (cryst : RealDiracCrystal A) (E : A)
    (hE_sq : E * E = E)
    (hE_even : cryst.Gamma * E = E * cryst.Gamma) :
    analyticTwistedIndex (crystalIndexData cryst)
        (ValenceBandBundle cryst E hE_sq hE_even) =
      topologicalChernIndex (crystalIndexData cryst)
        (ValenceBandBundle cryst E hE_sq hE_even) :=
  algebraic_index_pairing_identity (crystalIndexData cryst)
    (ValenceBandBundle cryst E hE_sq hE_even)

theorem crystal_atiyah_singer_algebraic_synthesis
    (cryst : RealDiracCrystal A) (E : A)
    (hE_sq : E * E = E)
    (hE_even : cryst.Gamma * E = E * cryst.Gamma) :
    (superTrace cryst.Tr cryst.Gamma cryst.H = 0) ∧
    (analyticTwistedIndex (crystalIndexData cryst)
        (ValenceBandBundle cryst E hE_sq hE_even) =
      topologicalChernIndex (crystalIndexData cryst)
        (ValenceBandBundle cryst E hE_sq hE_even)) :=
  ⟨crystal_witten_index_zero cryst,
    crystal_valence_band_pairing_identity cryst E hE_sq hE_even⟩

end InfoGeometry.Physics
