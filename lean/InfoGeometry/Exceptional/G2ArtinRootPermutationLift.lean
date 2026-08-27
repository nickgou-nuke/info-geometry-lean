/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Exceptional.G2ArtinPresentation
import InfoGeometry.Exceptional.G2ArtinOperatorLift

namespace InfoGeometry.Exceptional.G2ArtinRootLift

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Exceptional.ArtinOperators

/-!
# Concrete $G_2$ Artin-Hecke Linear Operator Lift on the 12-Root Carrier

This module constructs the concrete linear representation of the $I_2(6)$ Artin group
on the 12-dimensional vector space of roots $\mathcal{H}_{12} = \mathbb{C}^{\Phi(G_2)}$
using the native $G_2$ coordinate root reflections $s_1Root$ and $s_2Root$.

Key Theorems:
1. Linear permutation operators: $P(s_1), P(s_2) \in \operatorname{End}(\mathbb{C}^{12})$.
2. 🏆 `perm_artin_six_relation`: Concrete 6-term Artin braid identity:
   $P(s_1) P(s_2) P(s_1) P(s_2) P(s_1) P(s_2) = P(s_2) P(s_1) P(s_2) P(s_1) P(s_2) P(s_1)$.
3. 🏆 `concreteRootArtinLift`: Packaging into the master `G2ArtinOperatorLift` structure.
4. 🏆 `coxeter_perm_pow_six`: The classical permutation Coxeter element $(s_1 s_2)^6 = I$.
5. 🏆 `spin_phase_lift_order`: Central phase twisted operator $C_{\text{spin}} = \zeta \cdot (P(s_1) P(s_2))$
   satisfying $C_{\text{spin}}^6 = -I$ and $C_{\text{spin}}^{12} = I$ for $\zeta^6 = -1$.
-/

abbrev RootCarrier := G2CoordinateRoot → ℂ

/-- Permutation linear operator $P(\pi) \in \operatorname{End}(\mathbb{C}^{12})$. -/
def permOp (π : Equiv.Perm G2CoordinateRoot) : Module.End ℂ RootCarrier where
  toFun f := fun r => f (π.symm r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permOp_apply (π : Equiv.Perm G2CoordinateRoot) (f : RootCarrier) (r : G2CoordinateRoot) :
    permOp π f r = f (π.symm r) := rfl

@[simp] theorem permOp_one :
    permOp (1 : Equiv.Perm G2CoordinateRoot) = 1 := by
  ext f r
  simp [permOp]

@[simp] theorem permOp_mul (σ τ : Equiv.Perm G2CoordinateRoot) :
    permOp (σ * τ) = permOp σ * permOp τ := by
  ext f r
  simp [permOp, Equiv.Perm.mul_def]

/-- Short simple root linear operator $B_s = P(s_1)$. -/
def BsPerm : Module.End ℂ RootCarrier := permOp s1Root

/-- Long simple root linear operator $B_\ell = P(s_2)$. -/
def BlPerm : Module.End ℂ RootCarrier := permOp s2Root

/-- 🏆 Permutation 6-term Artin braid relation on $G_2$ roots. -/
theorem s1_s2_artin_six_perm :
    s1Root * s2Root * s1Root * s2Root * s1Root * s2Root =
      s2Root * s1Root * s2Root * s1Root * s2Root * s1Root := by
  have h := simpleReflections_relation
  simp only [relation, map_mul, map_inv, FreeGroup.lift_apply_of, simpleReflections] at h
  exact mul_inv_eq_one.mp h

/-- 🏆 THEOREM 1: The concrete 6-term Artin braid relation on $\mathcal{H}_{12}$:
    $B_s B_\ell B_s B_\ell B_s B_\ell = B_\ell B_s B_\ell B_s B_\ell B_s$. -/
theorem perm_artin_six_relation :
    BsPerm * BlPerm * BsPerm * BlPerm * BsPerm * BlPerm =
      BlPerm * BsPerm * BlPerm * BsPerm * BlPerm * BsPerm := by
  dsimp [BsPerm, BlPerm]
  simp only [← permOp_mul]
  rw [s1_s2_artin_six_perm]

/-- 🏆 THEOREM 2: Packaging the concrete 12-dimensional root operator representation into `G2ArtinOperatorLift`. -/
def concreteRootArtinLift : G2ArtinOperatorLift where
  H := RootCarrier
  Bs := BsPerm
  Bl := BlPerm
  artin := perm_artin_six_relation

/-- Classical Coxeter rotation operator $C_{\text{perm}} = P(s_1) P(s_2)$. -/
def coxeterPermOp : Module.End ℂ RootCarrier :=
  BsPerm * BlPerm

/-- 🏆 THEOREM 3: The classical permutation Coxeter element has order 6 on $\mathcal{H}_{12}$: $C_{\text{perm}}^6 = I$. -/
theorem coxeter_perm_pow_six :
    coxeterPermOp ^ 6 = 1 := by
  dsimp [coxeterPermOp, BsPerm, BlPerm]
  simp only [← permOp_mul]
  have h6 : (s1Root * s2Root) ^ 6 = 1 := by
    have h12 : (s1Root * s2Root) ^ 6 =
        (s1Root * s2Root * s1Root * s2Root * s1Root * s2Root) *
        (s1Root * s2Root * s1Root * s2Root * s1Root * s2Root) := by
      calc
        (s1Root * s2Root) ^ 6 = (s1Root * s2Root) ^ (3 + 3) := rfl
        _ = (s1Root * s2Root) ^ 3 * (s1Root * s2Root) ^ 3 := by rw [pow_add]
        _ = _ := by
          have h3 : (s1Root * s2Root) ^ 3 =
              s1Root * s2Root * s1Root * s2Root * s1Root * s2Root := by
            calc
              (s1Root * s2Root) ^ 3 = (s1Root * s2Root) ^ (2 + 1) := rfl
              _ = (s1Root * s2Root) ^ 2 * (s1Root * s2Root) := by rw [pow_add, pow_one]
              _ = ((s1Root * s2Root) * (s1Root * s2Root)) * (s1Root * s2Root) := by rw [sq]
              _ = _ := by simp only [mul_assoc]
          rw [h3]
    have hs : s1Root * s1Root = 1 := s1Root_sq
    have ht : s2Root * s2Root = 1 := s2Root_sq
    rw [h12]
    nth_rw 1 [s1_s2_artin_six_perm]
    calc
      (s2Root * s1Root * s2Root * s1Root * s2Root * s1Root) *
          (s1Root * s2Root * s1Root * s2Root * s1Root * s2Root) =
        s2Root * s1Root * s2Root * s1Root * s2Root * (s1Root * s1Root) *
          (s2Root * s1Root * s2Root * s1Root * s2Root) := by
        simp only [mul_assoc]
      _ = s2Root * s1Root * s2Root * s1Root * (s2Root * s2Root) *
          (s1Root * s2Root * s1Root * s2Root) := by
        rw [hs]
        simp only [mul_one, mul_assoc]
      _ = s2Root * s1Root * s2Root * (s1Root * s1Root) *
          (s2Root * s1Root * s2Root) := by
        rw [ht]
        simp only [mul_one, mul_assoc]
      _ = s2Root * s1Root * (s2Root * s2Root) *
          (s1Root * s2Root) := by
        rw [hs]
        simp only [mul_one, mul_assoc]
      _ = s2Root * (s1Root * s1Root) * s2Root := by
        rw [ht]
        simp only [mul_one, mul_assoc]
      _ = s2Root * s2Root := by
        rw [hs]
        simp only [mul_one]
      _ = 1 := ht
  have h_pow : permOp ((s1Root * s2Root) ^ 6) = permOp (s1Root * s2Root) ^ 6 := by
    have h3 : (s1Root * s2Root) ^ 6 =
        (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) *
        (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) := by
      calc
        (s1Root * s2Root) ^ 6 = (s1Root * s2Root) ^ (5 + 1) := rfl
        _ = (s1Root * s2Root) ^ 5 * (s1Root * s2Root) := by rw [pow_add, pow_one]
        _ = (s1Root * s2Root) ^ (4 + 1) * (s1Root * s2Root) := rfl
        _ = ((s1Root * s2Root) ^ 4 * (s1Root * s2Root)) * (s1Root * s2Root) := by rw [pow_add, pow_one]
        _ = (((s1Root * s2Root) ^ 3 * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root) := by
          have h4 : (s1Root * s2Root) ^ 4 = (s1Root * s2Root) ^ (3 + 1) := rfl
          rw [h4, pow_add, pow_one]
        _ = ((((s1Root * s2Root) ^ 2 * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root) := by
          have h3' : (s1Root * s2Root) ^ 3 = (s1Root * s2Root) ^ (2 + 1) := rfl
          rw [h3', pow_add, pow_one]
        _ = (((((s1Root * s2Root) * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root)) * (s1Root * s2Root) := by
          rw [sq]
        _ = (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) * (s1Root * s2Root) := by
          simp only [mul_assoc]
    have h3_op : permOp (s1Root * s2Root) ^ 6 =
        permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) *
        permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) := by
      calc
        permOp (s1Root * s2Root) ^ 6 = permOp (s1Root * s2Root) ^ (5 + 1) := rfl
        _ = permOp (s1Root * s2Root) ^ 5 * permOp (s1Root * s2Root) := by rw [pow_add, pow_one]
        _ = (permOp (s1Root * s2Root) ^ 4 * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root) := by
          have h4 : permOp (s1Root * s2Root) ^ 5 = permOp (s1Root * s2Root) ^ (4 + 1) := rfl
          rw [h4, pow_add, pow_one]
        _ = (((permOp (s1Root * s2Root) ^ 3 * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) := by
          have h4 : permOp (s1Root * s2Root) ^ 4 = permOp (s1Root * s2Root) ^ (3 + 1) := rfl
          rw [h4, pow_add, pow_one]
        _ = ((((permOp (s1Root * s2Root) ^ 2 * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) := by
          have h3' : permOp (s1Root * s2Root) ^ 3 = permOp (s1Root * s2Root) ^ (2 + 1) := rfl
          rw [h3', pow_add, pow_one]
        _ = (((((permOp (s1Root * s2Root) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) * permOp (s1Root * s2Root)) := by
          rw [sq]
        _ = permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) * permOp (s1Root * s2Root) := by
          simp only [mul_assoc]
    rw [h3, h3_op]
    simp only [permOp_mul]
  rw [← h_pow, h6, permOp_one]

/-- 🏆 THEOREM 4: Spin Coxeter lift with central phase factor:
    Given a primitive 12th root of unity $\zeta$ with $\zeta^6 = -1$, the phase-twisted
    Coxeter operator $C_{\text{spin}} = \zeta \cdot C_{\text{perm}}$ satisfies $C_{\text{spin}}^6 = -I$ and $C_{\text{spin}}^{12} = I$. -/
theorem spin_phase_lift_order (zeta : ℂ) (h_zeta6 : zeta ^ 6 = -1) :
    let C_spin : Module.End ℂ RootCarrier := zeta • coxeterPermOp
    C_spin ^ 6 = -1 ∧ C_spin ^ 12 = 1 := by
  intro C_spin
  have h6 : C_spin ^ 6 = -1 := by
    dsimp [C_spin]
    rw [smul_pow, coxeter_perm_pow_six, h_zeta6, neg_one_smul]
  have h12 : C_spin ^ 12 = 1 := by
    calc
      C_spin ^ 12 = (C_spin ^ 6) ^ 2 := by
        have h_mul : (6 : ℕ) * 2 = 12 := rfl
        rw [← pow_mul, h_mul]
      _ = (-1 : Module.End ℂ RootCarrier) ^ 2 := by rw [h6]
      _ = 1 := by
        rw [sq]
        apply LinearMap.ext
        intro f
        simp
  exact ⟨h6, h12⟩

end InfoGeometry.Exceptional.G2ArtinRootLift
