/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin

/-!
# Normal Metrics and Anomaly Vanishing

The algebraic EP condition is the explicit commutation equation between an
operator and its Moore--Penrose inverse. Under that condition, the inverse is
a Drazin inverse of index one. The chiral commutator anomaly vanishes when
the Moore--Penrose and Drazin support projectors agree.

#### BUCKET 1: CLOSED ALGEBRAIC THEOREMS
The EP commutation equation and the four Moore--Penrose equations imply the
three Drazin equations at index one.

#### BUCKET 2: CONDITIONAL THEOREMS
Anomaly vanishing from projector agreement is conditional on that explicit
operator equality.

#### BUCKET 3: OPEN CLOSURE DEBT
No equivalence between algebraic EP and analytic normality is claimed here.
-/

namespace InfoGeometry.Singular.NormalAnomaly

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin

variable {R : Type*} [Ring R] [StarRing R]

/-- If an EP Moore--Penrose pair commutes, its Moore--Penrose inverse itself
satisfies the Drazin equations at index one. -/
theorem EP_implies_group_inverse
    (A B : R)
    (hMP : IsMoorePenroseInverse A B)
    (hEP : A * B = B * A) :
    IsDrazinInverse A B 1 := by
  refine ⟨hMP.2.1, hEP, ?_⟩
  calc
    A ^ 1 = A := pow_one _
    _ = A * B * A := hMP.1.symm
    _ = A * (B * A) := by rw [mul_assoc]
    _ = A * (A * B) := by rw [hEP]
    _ = A * A * B := by rw [← mul_assoc]
    _ = A ^ (1 + 1) * B := by rw [pow_two]

/-- EP commutation forces the chiral anomaly to vanish for every Drazin
inverse of the same operator. Drazin uniqueness identifies that inverse with
the Moore--Penrose inverse, so the two support projectors coincide. -/
theorem Anomaly_vanishes_if_EP
    (A B D : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEP : A * B = B * A) :
    ChiralAnomaly A B D k hMP hD = 0 := by
  have hDB : D = B :=
    Drazin_unique_of_indices hD (EP_implies_group_inverse A B hMP hEP)
  subst D
  unfold ChiralAnomaly
  unfold MP_Projector Drazin_Projector
  exact sub_self (A * B * (A * B))

def IsEP (A B : R) (_hMP : IsMoorePenroseInverse A B) : Prop :=
  A * B = B * A

theorem Anomaly_vanishes_if_projectors_eq
    (A B D : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEq : MP_Projector A B hMP = Drazin_Projector A D k hD) :
    ChiralAnomaly A B D k hMP hD = 0 := by
  unfold ChiralAnomaly
  rw [hEq]
  -- P_D * P_D - P_D * P_D = 0
  exact sub_self (Drazin_Projector A D k hD * Drazin_Projector A D k hD)

end InfoGeometry.Singular.NormalAnomaly
