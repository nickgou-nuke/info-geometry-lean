/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# The overlap operator of two involutions

In an arbitrary associative ring, put `D = 1 + Γ * ε`.  If `Γ * Γ = 1`,
the Ginsparg--Wilson defect of `D` is exactly `Γ * (1 - ε * ε)`.
Consequently, the unit-normalized Ginsparg--Wilson relation is equivalent
to the second involution law.  No commutation or anticommutation assumption
on the two factors is used.

For two existing `ChiralInvolution` values, `D` intertwines their already
constructed chiral projectors.  These are the same-sign projectors for `ε`
and `Γ`; the modified chirality `Γ * (1 - D)` equals `-ε`.

The construction is algebraic.  It does not construct a spectral sign
operator, a determinant line, an index, or a lattice Dirac operator.
-/

namespace InfoGeometry.OperatorAlgebra.OverlapDirac

variable {A : Type*} [Ring A]

/-- The unit-normalized overlap expression using the native ring multiplication. -/
def overlapOperator (Γ ε : A) : A := 1 + Γ * ε

/-- The exact Ginsparg--Wilson defect; only the first factor must be an involution. -/
theorem ginspargWilson_defect (Γ ε : A) (hΓ : Γ * Γ = 1) :
    Γ * overlapOperator Γ ε + overlapOperator Γ ε * Γ -
        overlapOperator Γ ε * Γ * overlapOperator Γ ε =
      Γ * (1 - ε * ε) := by
  calc
    Γ * overlapOperator Γ ε + overlapOperator Γ ε * Γ -
          overlapOperator Γ ε * Γ * overlapOperator Γ ε =
        Γ - (Γ * ε) * (Γ * Γ) * ε := by
      dsimp [overlapOperator]
      noncomm_ring
    _ = Γ * (1 - ε * ε) := by
      rw [hΓ]
      noncomm_ring

/-- Given the first involution, the overlap expression satisfies the
Ginsparg--Wilson relation exactly when the second factor is an involution. -/
theorem ginspargWilson_iff (Γ ε : A) (hΓ : Γ * Γ = 1) :
    Γ * overlapOperator Γ ε + overlapOperator Γ ε * Γ =
        overlapOperator Γ ε * Γ * overlapOperator Γ ε ↔
      ε * ε = 1 := by
  constructor
  · intro h
    have hzero : Γ * (1 - ε * ε) = 0 := by
      rw [← ginspargWilson_defect Γ ε hΓ, h, sub_self]
    have hzero' := congrArg (fun a : A => Γ * a) hzero
    have hdefect : 1 - ε * ε = 0 := by
      simpa only [← mul_assoc, hΓ, one_mul, mul_zero] using hzero'
    exact (sub_eq_zero.mp hdefect).symm
  · intro hε
    apply sub_eq_zero.mp
    rw [ginspargWilson_defect Γ ε hΓ, hε, sub_self, mul_zero]

/-- Two involutions produce the unit-normalized Ginsparg--Wilson relation. -/
theorem ginspargWilson (Γ ε : A) (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    Γ * overlapOperator Γ ε + overlapOperator Γ ε * Γ =
      overlapOperator Γ ε * Γ * overlapOperator Γ ε :=
  (ginspargWilson_iff Γ ε hΓ).2 hε

/-- The overlap operator intertwines the second involution with the first. -/
theorem chirality_intertwining (Γ ε : A) (hΓ : Γ * Γ = 1)
    (hε : ε * ε = 1) :
    Γ * overlapOperator Γ ε = overlapOperator Γ ε * ε := by
  calc
    Γ * overlapOperator Γ ε = Γ + ε := by
      simp only [overlapOperator, mul_add, mul_one, ← mul_assoc, hΓ, one_mul]
    _ = overlapOperator Γ ε * ε := by
      simp only [overlapOperator, add_mul, one_mul, mul_assoc, hε, mul_one]
      exact add_comm Γ ε

/-- The usual modified chirality for this normalization is the negative
of the second input involution. -/
theorem modified_chirality (Γ ε : A) (hΓ : Γ * Γ = 1) :
    Γ * (1 - overlapOperator Γ ε) = -ε := by
  calc
    Γ * (1 - overlapOperator Γ ε) = -(Γ * Γ) * ε := by
      dsimp [overlapOperator]
      noncomm_ring
    _ = -ε := by
      rw [hΓ, neg_one_mul]

section Star

variable [StarRing A]

/-- Self-adjoint input factors give `Γ`-Hermiticity.  Only the first factor
needs to square to one for this identity. -/
theorem gamma_hermitian (Γ ε : A) (hΓ : Γ * Γ = 1)
    (hΓstar : star Γ = Γ) (hεstar : star ε = ε) :
    star (overlapOperator Γ ε) = Γ * overlapOperator Γ ε * Γ := by
  calc
    star (overlapOperator Γ ε) = 1 + ε * Γ := by
      simp only [overlapOperator, star_add, star_one, star_mul, hΓstar, hεstar]
    _ = (Γ * Γ) + (Γ * Γ) * ε * Γ := by
      simp only [hΓ, one_mul]
    _ = Γ * overlapOperator Γ ε * Γ := by
      dsimp [overlapOperator]
      noncomm_ring

end Star

section ChiralProjectors

variable [Algebra ℝ A]

/-- Intertwining of the existing positive chiral projectors. -/
theorem mul_Pleft (C E : ChiralInvolution A) :
    overlapOperator C.chi E.chi * E.Pleft =
      C.Pleft * overlapOperator C.chi E.chi := by
  simp only [ChiralInvolution.Pleft, mul_smul_comm, smul_mul_assoc,
    mul_add, mul_one, add_mul, one_mul]
  rw [chirality_intertwining C.chi E.chi C.chi_sq E.chi_sq]

/-- Intertwining of the existing negative chiral projectors. -/
theorem mul_Pright (C E : ChiralInvolution A) :
    overlapOperator C.chi E.chi * E.Pright =
      C.Pright * overlapOperator C.chi E.chi := by
  simp only [ChiralInvolution.Pright, mul_smul_comm, smul_mul_assoc,
    mul_sub, mul_one, sub_mul, one_mul]
  rw [chirality_intertwining C.chi E.chi C.chi_sq E.chi_sq]

end ChiralProjectors

end InfoGeometry.OperatorAlgebra.OverlapDirac
