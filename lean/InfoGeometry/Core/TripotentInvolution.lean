/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentAdjoint
import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Star.Module

/-!
# Involutions and the existing adjoint grades

An ordinary self-adjoint grading element makes the involution reverse grades;
an ordinary skew-adjoint grading element makes it preserve grades. Consequently,
a nonzero real integer grade has trivial intersection with the ordinary skew
subspace in the self-adjoint case. These statements hold for every element of
an associative real star algebra and do not require tripotency.

The ordinary skew submodule and the skew space of the owned `Krein.sharp` are
bundled as native Lie subalgebras for the ordinary commutator. Their adjoint
invariance has an exact central-correction criterion. The final anticommutator
result records the obstruction to reading this Lie closure as superbracket
closure. No nonzero grade, fundamental symmetry, or physical classification is
asserted to exist.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra
open InfoGeometry.Canonical.SpinorialCore

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- For a self-adjoint grading element, ordinary star reverses the integer grade. -/
theorem star_mem_adGrade_neg_of_selfAdjoint {S x : A} {k : ℤ}
    (hS : star S = S) (hx : x ∈ adGrade S k) :
    star x ∈ adGrade S (-k) := by
  rw [mem_adGrade_iff] at hx ⊢
  change S * star x - star x * S = ((-k : ℤ) : ℝ) • star x
  have hs := congrArg star hx
  simp only [adOp, star_sub, star_mul, hS, star_intCast_smul] at hs
  calc
    S * star x - star x * S = -(star x * S - S * star x) := by abel
    _ = -((k : ℝ) • star x) := congrArg Neg.neg hs
    _ = ((-k : ℤ) : ℝ) • star x := by simp only [Int.cast_neg, neg_smul]

/-- Involutivity makes grade reversal an equivalence of membership conditions. -/
theorem star_mem_adGrade_neg_iff_of_selfAdjoint {S x : A} {k : ℤ}
    (hS : star S = S) :
    star x ∈ adGrade S (-k) ↔ x ∈ adGrade S k := by
  constructor
  · intro hx
    simpa only [star_star, neg_neg] using
      star_mem_adGrade_neg_of_selfAdjoint hS hx
  · exact star_mem_adGrade_neg_of_selfAdjoint hS

/-- For a skew-adjoint grading element, ordinary star preserves the integer grade. -/
theorem star_mem_adGrade_of_skewAdjoint {S x : A} {k : ℤ}
    (hS : star S = -S) (hx : x ∈ adGrade S k) :
    star x ∈ adGrade S k := by
  rw [mem_adGrade_iff]
  have hs := congrArg star (mem_adGrade_iff.mp hx)
  simpa only [adOp, star_sub, star_mul, hS, star_intCast_smul,
    mul_neg, neg_mul, neg_sub_neg] using hs

/-- Ordinary star restricts to each grade when the grading element is skew. -/
theorem star_mem_adGrade_iff_of_skewAdjoint {S x : A} {k : ℤ}
    (hS : star S = -S) : star x ∈ adGrade S k ↔ x ∈ adGrade S k := by
  constructor
  · intro hx
    simpa only [star_star] using star_mem_adGrade_of_skewAdjoint hS hx
  · exact star_mem_adGrade_of_skewAdjoint hS

/-- A nonzero grade contains no nonzero ordinary skew element when `S` is self-adjoint. -/
theorem adGrade_inf_skewAdjoint_eq_bot {S : A} {k : ℤ}
    (hS : star S = S) (hk : k ≠ 0) :
    adGrade S k ⊓ skewAdjoint.submodule ℝ A = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  rcases hx with ⟨hx, hskew⟩
  change star x = -x at hskew
  have hminus := star_mem_adGrade_neg_of_selfAdjoint hS hx
  rw [hskew] at hminus
  have hn := (adGrade S (-k)).neg_mem hminus
  simp only [neg_neg] at hn
  have hplus := mem_adGrade_iff.mp hx
  have hminusEq := mem_adGrade_iff.mp hn
  have hz : ((k : ℝ) - ((-k : ℤ) : ℝ)) • x = 0 := by
    rw [sub_smul, ← hplus, ← hminusEq, sub_self]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hcoeff : (k : ℝ) - ((-k : ℤ) : ℝ) ≠ 0 := by
    rw [Int.cast_neg]
    intro hc
    apply hkR
    linarith
  exact (smul_eq_zero.mp hz).resolve_left hcoeff

/-- The native ordinary skew-adjoint submodule is closed under the ordinary Lie bracket. -/
def skewAdjointLieSubalgebra : LieSubalgebra ℝ A where
  __ := skewAdjoint.submodule ℝ A
  lie_mem' := by
    intro x y hx hy
    change star x = -x at hx
    change star y = -y at hy
    change star (x * y - y * x) = -(x * y - y * x)
    simp only [star_sub, star_mul, hx, hy, neg_mul_neg]
    abel

@[simp] theorem mem_skewAdjointLieSubalgebra {x : A} :
    x ∈ skewAdjointLieSubalgebra (A := A) ↔ star x = -x := Iff.rfl

private theorem commutator_neg_iff_sum_commute (a b x : A) :
    b * x - x * b = -(a * x - x * a) ↔ Commute (a + b) x := by
  have hsum : (a + b) * x - x * (a + b) =
      (a * x - x * a) + (b * x - x * b) := by noncomm_ring
  constructor
  · intro h
    change (a + b) * x = x * (a + b)
    apply sub_eq_zero.mp
    rw [hsum, h, add_neg_cancel]
  · intro h
    have hz : (a * x - x * a) + (b * x - x * b) = 0 := by
      rw [← hsum, h.eq, sub_self]
    exact eq_neg_of_add_eq_zero_right hz

/-- The pointwise obstruction to preserving the ordinary skew submodule is central. -/
theorem ad_mem_skewAdjoint_iff {S x : A} (hx : star x = -x) :
    LieAlgebra.ad ℝ A S x ∈ skewAdjoint.submodule ℝ A ↔
      Commute (S + star S) x := by
  change star (S * x - x * S) = -(S * x - x * S) ↔ _
  simpa only [star_sub, star_mul, hx, neg_mul, mul_neg, neg_sub_neg] using
    commutator_neg_iff_sum_commute S (star S) x

/-- Exact adjoint-invariance criterion; skewness of `S` is sufficient but not necessary. -/
theorem ad_preserves_skewAdjoint_iff (S : A) :
    skewAdjoint.submodule ℝ A ≤
        (skewAdjoint.submodule ℝ A).comap (LieAlgebra.ad ℝ A S) ↔
      ∀ x : A, star x = -x → Commute (S + star S) x := by
  constructor
  · intro h x hx
    exact (ad_mem_skewAdjoint_iff (S := S) hx).mp (h hx)
  · intro h x hx
    exact (ad_mem_skewAdjoint_iff (S := S) hx).mpr (h x hx)

/-- A skew grading element preserves the ordinary skew submodule. -/
theorem ad_preserves_skewAdjoint_of_skew {S : A} (hS : star S = -S) :
    skewAdjoint.submodule ℝ A ≤
      (skewAdjoint.submodule ℝ A).comap (LieAlgebra.ad ℝ A S) := by
  apply (ad_preserves_skewAdjoint_iff S).mpr
  intro x _
  rw [hS, add_neg_cancel]
  exact Commute.zero_left x

private theorem sharp_smul (η : A) (r : ℝ) (x : A) :
    Krein.sharp η (r • x) = r • Krein.sharp η x := by
  simp only [Krein.sharp, star_smul, star_trivial,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- A self-adjoint element anticommuting with the symmetry is skew for its Krein adjoint. -/
theorem sharp_eq_neg_of_selfAdjoint_anticommute {η S : A}
    (hη : η * η = 1) (hS : star S = S) (hanti : η * S = -(S * η)) :
    Krein.sharp η S = -S := by
  rw [Krein.sharp, hS, hanti, neg_mul, mul_assoc, hη, mul_one]

/-- A Krein-self-adjoint grading element makes the Krein adjoint reverse grades. -/
theorem sharp_mem_adGrade_neg_of_selfAdjoint {η S x : A} {k : ℤ}
    (hη : η * η = 1) (hS : Krein.sharp η S = S)
    (hx : x ∈ adGrade S k) : Krein.sharp η x ∈ adGrade S (-k) := by
  rw [mem_adGrade_iff] at hx ⊢
  change S * Krein.sharp η x - Krein.sharp η x * S =
    ((-k : ℤ) : ℝ) • Krein.sharp η x
  have hs := congrArg (Krein.sharp η) hx
  simp only [adOp, Krein.sharp_sub, Krein.sharp_mul η S x hη,
    Krein.sharp_mul η x S hη, hS, sharp_smul] at hs
  calc
    S * Krein.sharp η x - Krein.sharp η x * S =
        -(Krein.sharp η x * S - S * Krein.sharp η x) := by abel
    _ = -((k : ℝ) • Krein.sharp η x) := congrArg Neg.neg hs
    _ = ((-k : ℤ) : ℝ) • Krein.sharp η x := by
      simp only [Int.cast_neg, neg_smul]

/-- A Krein-skew grading element makes the Krein adjoint preserve grades. -/
theorem sharp_mem_adGrade_of_skewAdjoint {η S x : A} {k : ℤ}
    (hη : η * η = 1) (hS : Krein.sharp η S = -S)
    (hx : x ∈ adGrade S k) : Krein.sharp η x ∈ adGrade S k := by
  rw [mem_adGrade_iff]
  have hs := congrArg (Krein.sharp η) (mem_adGrade_iff.mp hx)
  simpa only [adOp, Krein.sharp_sub, Krein.sharp_mul η S x hη,
    Krein.sharp_mul η x S hη, hS, sharp_smul, mul_neg, neg_mul,
    neg_sub_neg] using hs

/-- For a self-adjoint fundamental symmetry, Krein grade reversal is involutive. -/
theorem sharp_mem_adGrade_neg_iff_of_selfAdjoint {η S x : A} {k : ℤ}
    (hηstar : star η = η) (hη : η * η = 1) (hS : Krein.sharp η S = S) :
    Krein.sharp η x ∈ adGrade S (-k) ↔ x ∈ adGrade S k := by
  constructor
  · intro hx
    simpa only [Krein.sharp_involutive η hηstar hη x, neg_neg] using
      sharp_mem_adGrade_neg_of_selfAdjoint hη hS hx
  · exact sharp_mem_adGrade_neg_of_selfAdjoint hη hS

/-- For a self-adjoint fundamental symmetry, Krein star restricts to each grade of a skew `S`. -/
theorem sharp_mem_adGrade_iff_of_skewAdjoint {η S x : A} {k : ℤ}
    (hηstar : star η = η) (hη : η * η = 1) (hS : Krein.sharp η S = -S) :
    Krein.sharp η x ∈ adGrade S k ↔ x ∈ adGrade S k := by
  constructor
  · intro hx
    simpa only [Krein.sharp_involutive η hηstar hη x] using
      sharp_mem_adGrade_of_skewAdjoint hη hS hx
  · exact sharp_mem_adGrade_of_skewAdjoint hη hS

/-- The skew space of the owned Krein adjoint, with its ordinary commutator bracket. -/
def sharpSkewLieSubalgebra (η : A) (hη : η * η = 1) : LieSubalgebra ℝ A where
  carrier := {x | Krein.sharp η x = -x}
  zero_mem' := by simp [Krein.sharp]
  add_mem' := by
    intro x y hx hy
    change Krein.sharp η (x + y) = -(x + y)
    rw [Krein.sharp_add, hx, hy, neg_add]
  smul_mem' := by
    intro r x hx
    change Krein.sharp η (r • x) = -(r • x)
    rw [sharp_smul, hx, smul_neg]
  lie_mem' := by
    intro x y hx hy
    exact Krein.sharp_commutator η x y hη hx hy

@[simp] theorem mem_sharpSkewLieSubalgebra {η x : A} (hη : η * η = 1) :
    x ∈ sharpSkewLieSubalgebra η hη ↔ Krein.sharp η x = -x := Iff.rfl

/-- The exact pointwise Krein-skew obstruction uses the same central correction. -/
theorem ad_mem_sharpSkew_iff {η S x : A} (hη : η * η = 1)
    (hx : Krein.sharp η x = -x) :
    LieAlgebra.ad ℝ A S x ∈ sharpSkewLieSubalgebra η hη ↔
      Commute (S + Krein.sharp η S) x := by
  change Krein.sharp η (S * x - x * S) = -(S * x - x * S) ↔ _
  simpa only [Krein.sharp_sub, Krein.sharp_mul η S x hη,
    Krein.sharp_mul η x S hη, hx, neg_mul, mul_neg, neg_sub_neg] using
    commutator_neg_iff_sum_commute S (Krein.sharp η S) x

/-- Exact adjoint-invariance criterion for the native Krein-skew Lie subalgebra. -/
theorem ad_preserves_sharpSkew_iff (η S : A) (hη : η * η = 1) :
    (sharpSkewLieSubalgebra η hη).toSubmodule ≤
        (sharpSkewLieSubalgebra η hη).toSubmodule.comap (LieAlgebra.ad ℝ A S) ↔
      ∀ x : A, Krein.sharp η x = -x → Commute (S + Krein.sharp η S) x := by
  constructor
  · intro h x hx
    exact (ad_mem_sharpSkew_iff (S := S) hη hx).mp (h hx)
  · intro h x hx
    exact (ad_mem_sharpSkew_iff (S := S) hη hx).mpr (h x hx)

/-- Krein skewness of the grading element is a sufficient invariance condition. -/
theorem ad_preserves_sharpSkew_of_skew {η S : A} (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) :
    (sharpSkewLieSubalgebra η hη).toSubmodule ≤
      (sharpSkewLieSubalgebra η hη).toSubmodule.comap (LieAlgebra.ad ℝ A S) := by
  apply (ad_preserves_sharpSkew_iff η S hη).mpr
  intro x _
  rw [hS, add_neg_cancel]
  exact Commute.zero_left x

/-- Anticommutators of two Krein-skew elements are Krein-self-adjoint. -/
theorem sharp_anticommutator_of_skew {η x y : A} (hη : η * η = 1)
    (hx : Krein.sharp η x = -x) (hy : Krein.sharp η y = -y) :
    Krein.sharp η (x * y + y * x) = x * y + y * x := by
  rw [Krein.sharp_add, Krein.sharp_mul η x y hη,
    Krein.sharp_mul η y x hη, hx, hy]
  simp only [neg_mul_neg]
  exact add_comm _ _

/-- Ordinary Krein-skew Lie closure gives no odd-odd superclosure unless the
anticommutator vanishes. This is an exact criterion over the real ambient module. -/
theorem anticommutator_mem_sharpSkew_iff_eq_zero {η x y : A}
    (hη : η * η = 1) (hx : Krein.sharp η x = -x) (hy : Krein.sharp η y = -y) :
    x * y + y * x ∈ sharpSkewLieSubalgebra η hη ↔ x * y + y * x = 0 := by
  change Krein.sharp η (x * y + y * x) = -(x * y + y * x) ↔ _
  rw [sharp_anticommutator_of_skew hη hx hy]
  constructor
  · intro hz
    have hdouble : (2 : ℝ) • (x * y + y * x) = 0 := by
      rw [two_smul]
      calc
        (x * y + y * x) + (x * y + y * x) =
            -(x * y + y * x) + (x * y + y * x) :=
          congrArg (fun z : A => z + (x * y + y * x)) hz
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp hdouble).resolve_left (by norm_num)
  · intro hz
    rw [hz, neg_zero]

end InfoGeometry.Core.TripotentAdjoint
