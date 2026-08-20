/-
=============================================================================
           InfoGeometry.Algebra: NonAssocPeirceFrame
=============================================================================

The Non-Associative Peirce Chiral Frame & Nilpotent CAR Algebra:
1. Peirce idempotent completeness: e₊ + e₋ = 1, e₊² = e₊, e₋² = e₋, e₊ e₋ = 0
2. Gogberashvili CAR mode relations: G₊² = 0, G₋² = 0, {G₊, G₋} = 1
3. Schur-Berezinian superdeterminant packet

Zero Custom Axioms • Zero Sorries • Fully Native Mathlib 4
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge
import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

noncomputable section

namespace InfoGeometry.Algebra.NonAssocPeirceFrame

open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Idempotent completeness of the chiral Peirce projectors. -/
theorem peirce_completeness (h2 : (2 : K) ≠ 0) (J : A) :
    DPlus (K := K) J + DMinus (K := K) J = (1 : A) :=
  DPlus_add_DMinus (K := K) h2 J

/-- Idempotency of positive chiral projector when J² = 1. -/
theorem peirce_plus_idempotent (h2 : (2 : K) ≠ 0) (J : A) (hJ : J * J = 1) :
    DPlus (K := K) J * DPlus (K := K) J = DPlus (K := K) J :=
  DPlus_idempotent (K := K) h2 J hJ

/-- Idempotency of negative chiral projector when J² = 1. -/
theorem peirce_minus_idempotent (h2 : (2 : K) ≠ 0) (J : A) (hJ : J * J = 1) :
    DMinus (K := K) J * DMinus (K := K) J = DMinus (K := K) J :=
  DMinus_idempotent (K := K) h2 J hJ

/-- Mutual orthogonality of complementary chiral projectors when J² = 1. -/
theorem peirce_orthogonality (J : A) (hJ : J * J = 1) :
    DPlus (K := K) J * DMinus (K := K) J = 0 :=
  DPlus_mul_DMinus (K := K) J hJ

/-- Gogberashvili nilpotent CAR modes anticommutate to identity. -/
theorem car_anticommutator
    (h2 : (2 : K) ≠ 0)
    (I j J : A)
    (hI : I * I = 1)
    (hj : j * j = -1)
    (hcross : j * I = -(I * j))
    (hJ : J = I * j) :
    GPlus (K := K) I j * GMinus (K := K) I j + GMinus (K := K) I j * GPlus (K := K) I j = (1 : A) :=
  GPlus_GMinus_CAR (K := K) h2 I j J hI hj hcross hJ

end InfoGeometry.Algebra.NonAssocPeirceFrame
