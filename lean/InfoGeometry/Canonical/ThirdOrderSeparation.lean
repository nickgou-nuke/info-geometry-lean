import InfoGeometry.Canonical.DualConnectionsCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.InformationTorsion

/-!
# Theorem-honest third-order separation

This owner records the exact finite identities shared by the three layers that
are often described together: the Amari--Chentsov tensor, connection torsion,
and the Zorn associator.  It deliberately proves no identification between
these different objects.
-/

namespace InfoGeometry.Canonical.ThirdOrderSeparation

open InfoGeometry.Canonical.DualConnections
open InfoGeometry.Canonical.InformationTorsion

variable {Θ α : Type*} [Fintype α]

theorem chentsovTensor_swap_right
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    chentsovTensor p θ u v w = chentsovTensor p θ u w v := by
  simp [chentsovTensor, mul_assoc, mul_comm, mul_left_comm]

theorem chentsovTensor_cyclic
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    chentsovTensor p θ u v w = chentsovTensor p θ v w u := by
  simp [chentsovTensor, mul_assoc, mul_comm, mul_left_comm]

theorem chentsovTensor_fully_symmetric
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    chentsovTensor p θ u v w = chentsovTensor p θ v u w ∧
      chentsovTensor p θ u v w = chentsovTensor p θ u w v := by
  exact ⟨chentsovTensor_swap_left p θ u v w,
    chentsovTensor_swap_right p θ u v w⟩

theorem informationTorsion_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (conn : Connection E) (u v : E) :
    informationTorsion conn v u = -informationTorsion conn u v := by
  simp [informationTorsion, sub_eq_add_neg, add_comm]

theorem alphaConnectionTensor_e_sub_m
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    eConnectionTensor Gamma0 p θ u v w -
        mConnectionTensor Gamma0 p θ u v w =
      -(chentsovTensor p θ u v w) := by
  simpa [eConnectionTensor, mConnectionTensor] using
    alphaConnectionTensor_dual_diff
      (Gamma0 := Gamma0) (p := p) (alphaC := (1 : ℝ))
      (θ := θ) (u := u) (v := v) (w := w)

end InfoGeometry.Canonical.ThirdOrderSeparation
