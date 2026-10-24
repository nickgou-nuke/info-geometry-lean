/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! The native boundary Dirac expression is an algebraic CAR pair.
The second partner is defined using the opposite scalar phase, not an adjoint. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryDiracPair

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge

variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}

abbrev leftEndpoint (hN : 0 < N) (ops : MajoranaCliffordOperators N A) : A :=
  ops.γ ⟨0, by omega⟩

abbrev rightEndpoint (hN : 0 < N) (ops : MajoranaCliffordOperators N A) : A :=
  ops.γ ⟨2 * N - 1, by omega⟩

abbrev boundaryAnnihilation (hN : 0 < N) (ops : MajoranaCliffordOperators N A) : A :=
  boundaryDiracFermion hN ops.toMajoranaOperators
    (algebraMap ℂ A (1 / 2)) (algebraMap ℂ A Complex.I)

abbrev boundaryCreation (hN : 0 < N) (ops : MajoranaCliffordOperators N A) : A :=
  boundaryDiracFermion hN ops.toMajoranaOperators
    (algebraMap ℂ A (1 / 2)) (algebraMap ℂ A (-Complex.I))

theorem leftEndpoint_sq (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    leftEndpoint hN ops * leftEndpoint hN ops = 1 := ops.h_sq _

theorem phased_rightEndpoint_sq (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    (Complex.I • rightEndpoint hN ops) * (Complex.I • rightEndpoint hN ops) = -1 := by
  rw [smul_mul_smul, ops.h_sq]
  simp [Complex.I_mul_I]

theorem endpoint_split_anticomm (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    leftEndpoint hN ops * (Complex.I • rightEndpoint hN ops) +
      (Complex.I • rightEndpoint hN ops) * leftEndpoint hN ops = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add]
  have hne : (⟨0, by omega⟩ : Fin (2 * N)) ≠ ⟨2 * N - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [ops.h_ortho _ _ hne, smul_zero]

theorem boundaryAnnihilation_eq_GPlus (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) :
    boundaryAnnihilation hN ops =
      GPlus (K := ℂ) (leftEndpoint hN ops) (Complex.I • rightEndpoint hN ops) := by
  simp [boundaryAnnihilation, boundaryDiracFermion, GPlus, Algebra.smul_def,
    div_eq_mul_inv]

theorem boundaryCreation_eq_GMinus (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) :
    boundaryCreation hN ops =
      GMinus (K := ℂ) (leftEndpoint hN ops) (Complex.I • rightEndpoint hN ops) := by
  simp [boundaryCreation, boundaryDiracFermion, GMinus, Algebra.smul_def,
    div_eq_mul_inv, sub_eq_add_neg]

theorem boundaryAnnihilation_sq (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    boundaryAnnihilation hN ops * boundaryAnnihilation hN ops = 0 := by
  rw [boundaryAnnihilation_eq_GPlus]
  exact GPlus_square_zero _ _ (leftEndpoint_sq hN ops)
    (phased_rightEndpoint_sq hN ops) (endpoint_split_anticomm hN ops)

theorem boundaryCreation_sq (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    boundaryCreation hN ops * boundaryCreation hN ops = 0 := by
  rw [boundaryCreation_eq_GMinus]
  exact GMinus_square_zero _ _ (leftEndpoint_sq hN ops)
    (phased_rightEndpoint_sq hN ops) (endpoint_split_anticomm hN ops)

theorem boundary_CAR (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    boundaryAnnihilation hN ops * boundaryCreation hN ops +
      boundaryCreation hN ops * boundaryAnnihilation hN ops = 1 := by
  rw [boundaryAnnihilation_eq_GPlus, boundaryCreation_eq_GMinus]
  exact GPlus_GMinus_CAR (by norm_num) _ _ _ (leftEndpoint_sq hN ops)
    (phased_rightEndpoint_sq hN ops)
    (eq_neg_of_add_eq_zero_right (endpoint_split_anticomm hN ops)) rfl

theorem boundary_reflexive (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    boundaryAnnihilation hN ops * boundaryCreation hN ops * boundaryAnnihilation hN ops =
      boundaryAnnihilation hN ops ∧
    boundaryCreation hN ops * boundaryAnnihilation hN ops * boundaryCreation hN ops =
      boundaryCreation hN ops := by
  have hsq : (-boundaryCreation hN ops) * (-boundaryCreation hN ops) = 0 := by
    simpa using boundaryCreation_sq hN ops
  have hcar : boundaryAnnihilation hN ops * (-boundaryCreation hN ops) +
      (-boundaryCreation hN ops) * boundaryAnnihilation hN ops = -1 := by
    simpa only [mul_neg, neg_mul, ← neg_add] using congrArg Neg.neg (boundary_CAR hN ops)
  simpa only [neg_neg] using ReflexiveNilpotentFlows.negative_car_reflexive
    (boundaryAnnihilation_sq hN ops) hsq hcar

theorem boundary_support (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    ReflexiveNilpotentFlows.support (boundaryAnnihilation hN ops) (boundaryCreation hN ops) = 1 :=
  boundary_CAR hN ops

theorem boundary_weyl (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    ReflexiveNilpotentFlows.weyl (boundaryAnnihilation hN ops) (boundaryCreation hN ops) =
      Complex.I • rightEndpoint hN ops := by
  unfold ReflexiveNilpotentFlows.weyl ReflexiveNilpotentFlows.complement
  rw [boundary_support, sub_self, zero_add,
    boundaryAnnihilation_eq_GPlus, boundaryCreation_eq_GMinus]
  unfold GPlus GMinus
  module

/-- The native unit, whose inverse is supplied by the reflexive-pair owner. -/
def boundaryWeylUnit (hN : 0 < N) (ops : MajoranaCliffordOperators N A) : Aˣ :=
  ReflexiveNilpotentFlows.weylUnit (boundaryAnnihilation_sq hN ops)
    (boundaryCreation_sq hN ops) (boundary_reflexive hN ops).1

theorem boundaryWeylUnit_val (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    (boundaryWeylUnit hN ops : A) = Complex.I • rightEndpoint hN ops :=
  boundary_weyl hN ops

end InfoGeometry.Canonical.KitaevBoundaryDiracPair
